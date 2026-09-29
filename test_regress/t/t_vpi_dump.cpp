// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2010-2011 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "svdpi.h"
#include "vpi_user.h"

#include <cinttypes>
#include <cstdio>

// These require the above. Comment prevents clang-format moving them
#include "TestCheck.h"
#include "TestSimulator.h"
#include "TestVpi.h"

#include <algorithm>
#include <atomic>
#include <cstdlib>
#include <cstring>
#include <map>
#include <mutex>
#include <string>
#include <vector>

int errors = 0;

// vpiType -> list of vpiTypes to iterate over
std::map<int32_t, std::vector<int32_t>> iterate_over = [] {
    // static decltype(iterate_over) iterate_over = [] {
    /* for reused lists */

    // vpiInstance is the base class for module, program, interface, etc.
    std::vector<int32_t> instance_options = {
        vpiNet,
        vpiNetArray,
        vpiReg,
        vpiRegArray,
    };

    std::vector<int32_t> module_options = {
        // vpiModule,  // Aldec SEGV on mixed language
        // vpiModuleArray,       // Aldec SEGV on mixed language
        // vpiIODecl,            // Don't care about these
        vpiMemory, vpiIntegerVar, vpiRealVar,
        // vpiRealNet, Vpi extension
        vpiStructVar, vpiStructNet, vpiNamedEvent, vpiNamedEventArray, vpiParameter,
        // vpiVariables, // parent of vpiReg, vpiRegArray, vpiIntegerVar, etc vars
        // vpiSpecParam,         // Don't care
        // vpiParamAssign,       // Aldec SEGV on mixed language
        // vpiDefParam,          // Don't care
        vpiPrimitive, vpiPrimitiveArray,
        // vpiContAssign,        // Don't care
        // vpiProcess,  // Don't care
        vpiModPath, vpiTchk, vpiAttribute, vpiPort, vpiInternalScope,
        // vpiInterface,         // Aldec SEGV on mixed language
        // vpiInterfaceArray,    // Aldec SEGV on mixed language
    };

    // append base class vpiInstance members
    module_options.insert(module_options.begin(), instance_options.begin(),
                          instance_options.end());

    std::vector<int32_t> struct_options = {
        vpiNet,       vpiReg,       vpiRegArray,       vpiMemory,
        vpiParameter, vpiPrimitive, vpiPrimitiveArray, vpiAttribute,
        vpiMember,
    };

    return decltype(iterate_over){
        {vpiModule, module_options},
        {vpiInterface, instance_options},
        {vpiGenScope, module_options},

        {vpiStructVar, struct_options},
        {vpiStructNet, struct_options},

        {vpiNet,
         {
             // vpiContAssign,        // Driver and load handled separately
             // vpiPrimTerm,
             // vpiPathTerm,
             // vpiTchkTerm,
             // vpiDriver,
             // vpiLocalDriver,
             // vpiLoad,
             // vpiLocalLoad,
             vpiNetBit,
         }},
        {vpiNetArray,
         {
             vpiNet,
         }},
        {vpiRegArray,
         {
             vpiReg,
         }},
        {vpiMemory,
         {
             vpiMemoryWord,
         }},
        {vpiPort,
         {
             vpiPortBit,
         }},
        {vpiGate,
         {
             vpiPrimTerm,
             vpiTableEntry,
             vpiUdpDefn,
         }},
        {vpiPackage,
         {
             vpiParameter,
         }},
    };
}();

#ifdef TEST_SAVABLE
#include "verilated_save.h"
#include VM_PREFIX_INCLUDE
extern VM_PREFIX* testVpiTopp;
#endif

// DPI-C API, so that a test's configuration lives in its design, where reducers and other
// simulators see it. With no calls only the structure dump at start of simulation is printed.
// Value dumps and the _rw operations are deferred to callbacks, to see and change the time
// step's settled values rather than those partway through the calling process's eval, and
// because Verilator allows VPI only from the main thread, not a --threads worker's process.
//   t_vpi_dump_values()    dump values changed since the last dump at the end of this time
//                          step, or at end of simulation if that comes first; the first
//                          dump also prints each vpiSize
//   t_vpi_dump_skip(name)  leave name out of value dumps
//   t_vpi_dump_cb(name)    print name on each cbValueChange, from the end of this time step
//   t_vpi_dump_value(name) print name now, so from the main thread only
//   t_vpi_dump_get(name)   return name's value now, likewise, as t_vpi_dump_value prints it
//   t_vpi_dump_put(name, value)  put now, likewise; value is hex, real=<r> or str=<s>
//   t_vpi_dump_put_rw(name, value, flag)  put at the next cbReadWriteSynch, then
//                          dump; flag is "", "force", "release" or "inertial"
//   t_vpi_dump_save(), t_vpi_dump_restore()  likewise, for a --savable model; a
//                          restore also dumps before it
//   t_vpi_dump_restores()  restores so far; a restore rewinds the design, not this count
//   t_vpi_dump_clock(name, halfperiod)  toggle name, for models without --timing
enum class OpKind : uint8_t { PUT, SAVE, RESTORE };
struct RwOp {
    OpKind kind;
    std::string name;
    std::string value;
    int flag;
};
std::mutex apiMutex;
std::vector<RwOp> rwOps;
std::vector<std::string> cbNames;
std::vector<std::string> skipNames;
std::map<std::string, std::string> lastValues;
std::atomic<bool> dumpPending{false};
bool sizesDumped = false;
int restores = 0;
std::string clockName;
int clockHalf = 0;
bool clockStarted = false;

bool hasValue(vpiHandle hndl, int type) {
    switch (type) {
    case vpiReg:
    case vpiNet:
    case vpiMemoryWord:
    case vpiIntegerVar:
    case vpiRealVar:
    case vpiStringVar:
    case vpiParameter:
    case vpiBitVar:
    case vpiByteVar:
    case vpiShortIntVar:
    case vpiIntVar:
    case vpiLongIntVar:
    case vpiEnumVar: return true;
    case vpiStructVar:
    case vpiStructNet: return vpi_get(vpiPacked, hndl);
    default: return false;
    }
}

std::string valueStr(vpiHandle hndl, int type) {
    s_vpi_value value{};
    value.format = vpiHexStrVal;
    if (type == vpiRealVar) value.format = vpiRealVal;
    if (type == vpiStringVar) value.format = vpiStringVal;
    if (type == vpiParameter) {
        const int ctype = vpi_get(vpiConstType, hndl);
        if (ctype == vpiRealConst) value.format = vpiRealVal;
        if (ctype == vpiStringConst) value.format = vpiStringVal;
    }
    vpi_get_value(hndl, &value);
    s_vpi_error_info info{};
    if (vpi_chk_error(&info) >= vpiError) return "<error>";
    char buf[64];
    switch (value.format) {
    case vpiRealVal: std::snprintf(buf, sizeof(buf), "%g", value.value.real); return buf;
    case vpiStringVal: return std::string{"\""} + (value.value.str ? value.value.str : "") + "\"";
    default: return value.value.str ? value.value.str : "<null>";
    }
}

void modDump(TestVpiHandle& it, int n, bool values) {

    if (n > 8) {
        if (!values) printf("going too deep\n");
        return;
    }

    while (const TestVpiHandle& hndl = vpi_scan(it)) {
        const int type = vpi_get(vpiType, hndl);
        // IEEE 1800-2023 38.11: the next vpi_get_str may overwrite the returned string
        const char* const fullnameP = vpi_get_str(vpiFullName, hndl);
        const std::string fullname = fullnameP ? fullnameP : "(null)";
        if (values) {
            if (hasValue(hndl, type)
                && std::find(skipNames.begin(), skipNames.end(), fullname) == skipNames.end()) {
                const std::string val = valueStr(hndl, type);
                std::string& last = lastValues[fullname];
                if (last != val) {
                    printf("%s = %s", fullname.c_str(), val.c_str());
                    if (!sizesDumped) printf(" vpiSize=%d", vpi_get(vpiSize, hndl));
                    printf("\n");
                    last = val;
                }
            }
        } else {
            for (int i = 0; i < n; i++) printf("    ");
            const char* name = vpi_get_str(vpiName, hndl);
            printf("%s (%s) %s ", name, strFromVpiObjType(type), fullname.c_str());
            if (type == vpiParameter || type == vpiConstType) {
                printf(" vpiConstType=%s", strFromVpiConstType(vpi_get(vpiConstType, hndl)));
            }
            if (type == vpiModule) printf(" vpiDefName=%s", vpi_get_str(vpiDefName, hndl));
            printf("\n");
        }

        if (iterate_over.find(type) == iterate_over.end()) continue;
        std::vector<int32_t> types = iterate_over.at(type);
        if ((TestSimulator::is_questa() || TestSimulator::is_mti())
            && (type == vpiModule || type == vpiInterface || type == vpiGenScope)) {
            // Questa lists some variable kinds only under vpiVariables (IEEE 1800-2023 37.17)
            const std::vector<int32_t> vars{vpiReg,        vpiRegArray, vpiMemory,
                                            vpiIntegerVar, vpiRealVar,  vpiStructVar};
            types.erase(std::remove_if(types.begin(), types.end(),
                                       [&](int32_t t) {
                                           return std::find(vars.begin(), vars.end(), t)
                                                  != vars.end();
                                       }),
                        types.end());
            types.push_back(vpiVariables);
        }
        for (int type : types) {
            if (values && (type == vpiNetBit || type == vpiPortBit)) continue;
            TestVpiHandle subIt = vpi_iterate(type, hndl);
            if (subIt) {
                if (!values) {
                    for (int i = 0; i < n + 1; i++) printf("    ");
                    printf("%s:\n", strFromVpiObjType(type));
                }
                modDump(subIt, n + 1, values);
            }
        }
    }
    it.freed();
}

uint64_t simTime() {
    s_vpi_time t{};
    t.type = vpiSimTime;
    vpi_get_time(NULL, &t);
    return (static_cast<uint64_t>(t.high) << 32) | t.low;
}

void valuesDump(const char* when) {
    printf("-- @%" PRIu64 " %s\n", simTime(), when);
    TestVpiHandle it = vpi_iterate(vpiModule, NULL);
    modDump(it, 0, true);
    sizesDumped = true;
}

void registerCb(PLI_INT32 reason, PLI_INT32 (*rtn)(t_cb_data*), vpiHandle obj,
                PLI_BYTE8* user_data, uint64_t delay = 0) {
    static s_vpi_time time_s;
    time_s.type = reason == cbValueChange ? vpiSuppressTime : vpiSimTime;
    time_s.high = static_cast<PLI_UINT32>(delay >> 32);
    time_s.low = static_cast<PLI_UINT32>(delay);
    static s_vpi_value value_s;
    value_s.format = vpiHexStrVal;
    s_cb_data cb_data{};
    cb_data.reason = reason;
    cb_data.cb_rtn = rtn;
    cb_data.obj = obj;
    cb_data.time = &time_s;
    cb_data.value = &value_s;
    cb_data.user_data = user_data;
    TestVpiHandle callback_h = vpi_register_cb(&cb_data);
    TEST_CHECK_NZ(callback_h);
}

PLI_INT32 value_change(t_cb_data* data) {
    printf("-- @%" PRIu64 " cb %s = %s\n", simTime(), data->user_data, data->value->value.str);
    return 0;
}

PLI_INT32 clock_toggle(t_cb_data* data);
PLI_INT32 next_sim_time(t_cb_data* data);

PLI_INT32 read_only_synch(t_cb_data* data) {
    if (dumpPending.exchange(false)) valuesDump("readonly");
    std::vector<std::string> names;
    {
        const std::lock_guard<std::mutex> lock{apiMutex};
        names = std::move(cbNames);
        cbNames.clear();
    }
    for (const std::string& name : names) {
        TestVpiHandle hndl = vpi_handle_by_name(const_cast<PLI_BYTE8*>(name.c_str()), NULL);
        TEST_CHECK_NZ(hndl);
        if (hndl) registerCb(cbValueChange, &value_change, hndl, strdup(name.c_str()));
    }
    if (!clockName.empty() && !clockStarted) {
        clockStarted = true;
        registerCb(cbAfterDelay, &clock_toggle, NULL, NULL, clockHalf);
    }
    registerCb(cbNextSimTime, &next_sim_time, NULL, NULL);
    return 0;
}

PLI_INT32 end_of_sim(t_cb_data* data) {
    if (dumpPending.exchange(false)) valuesDump("end");
    return 0;
}

PLI_INT32 clock_toggle(t_cb_data* data) {
    TestVpiHandle hndl = vpi_handle_by_name(const_cast<PLI_BYTE8*>(clockName.c_str()), NULL);
    s_vpi_value value{};
    value.format = vpiIntVal;
    vpi_get_value(hndl, &value);
    value.value.integer = !value.value.integer;
    vpi_put_value(hndl, &value, NULL, vpiNoDelay);
    registerCb(cbAfterDelay, &clock_toggle, NULL, NULL, clockHalf);
    return 0;
}

void doPut(const std::string& name, const std::string& valueArg, int flag) {
    TestVpiHandle hndl = vpi_handle_by_name(const_cast<PLI_BYTE8*>(name.c_str()), NULL);
    s_vpi_value value{};
    if (valueArg.rfind("real=", 0) == 0) {
        value.format = vpiRealVal;
        value.value.real = std::strtod(valueArg.c_str() + 5, NULL);
    } else {
        value.format = valueArg.rfind("str=", 0) == 0 ? vpiStringVal : vpiHexStrVal;
        value.value.str
            = const_cast<PLI_BYTE8*>(valueArg.c_str()) + (value.format == vpiStringVal ? 4 : 0);
    }
    s_vpi_time zeroDelay{vpiSimTime, 0, 0, 0};
    vpi_put_value(hndl, &value, flag == vpiInertialDelay ? &zeroDelay : NULL, flag);
    s_vpi_error_info info{};
    const bool ok = hndl && vpi_chk_error(&info) < vpiError;
    printf("-- put %s = %s flag=%d %s\n", name.c_str(), valueArg.c_str(), flag,
           ok ? "ok" : "rejected");
}

void doSaveRestore(OpKind kind) {
#ifdef TEST_SAVABLE
    const char* const path = VL_STRINGIFY(TEST_OBJ_DIR) "/saved.vltsv";
    if (kind == OpKind::SAVE) {
        VerilatedSave os;
        os.open(path);
        os << *testVpiTopp;
    } else {
        VerilatedRestore os;
        os.open(path);
        os >> *testVpiTopp;
    }
#endif
    printf("-- %s\n", kind == OpKind::SAVE ? "save" : "restore");
}

PLI_INT32 read_write_synch(t_cb_data* data) {
    std::vector<RwOp> ops;
    {
        const std::lock_guard<std::mutex> lock{apiMutex};
        ops = std::move(rwOps);
        rwOps.clear();
    }
    if (ops.empty()) return 0;
    const char* what = "after put";
    for (const RwOp& op : ops) {
        if (op.kind == OpKind::PUT) {
            doPut(op.name, op.value, op.flag);
            what = "after put";
        } else if (op.kind == OpKind::SAVE) {
            doSaveRestore(op.kind);
            what = "after save";
        } else {
            valuesDump("before restore");
            doSaveRestore(op.kind);
            ++restores;
            what = "after restore";
        }
    }
    valuesDump(what);
    return 0;
}

PLI_INT32 next_sim_time(t_cb_data* data) {
    registerCb(cbReadWriteSynch, &read_write_synch, NULL, NULL);
    registerCb(cbReadOnlySynch, &read_only_synch, NULL, NULL);
    return 0;
}

void pushRwOp(const RwOp& op) {
    const std::lock_guard<std::mutex> lock{apiMutex};
    // Event-driven: this step's cbReadWriteSynch may already have run (IEEE 1800-2023 4.4)
    if (rwOps.empty() && TestSimulator::is_event_driven())
        registerCb(cbReadWriteSynch, &read_write_synch, NULL, NULL);
    rwOps.push_back(op);
}

extern "C" void t_vpi_dump_values() { dumpPending = true; }

extern "C" void t_vpi_dump_skip(const char* name) {
    const std::lock_guard<std::mutex> lock{apiMutex};
    skipNames.push_back(name);
}

extern "C" void t_vpi_dump_cb(const char* name) {
    const std::lock_guard<std::mutex> lock{apiMutex};
    cbNames.push_back(name);
}

extern "C" void t_vpi_dump_value(const char* name) {
    TestVpiHandle hndl = vpi_handle_by_name(const_cast<PLI_BYTE8*>(name), NULL);
    printf("-- @%" PRIu64 " dpi %s = %s\n", simTime(), name,
           hndl ? valueStr(hndl, vpi_get(vpiType, hndl)).c_str() : "<null>");
}

extern "C" const char* t_vpi_dump_get(const char* name) {
    static std::string result;
    TestVpiHandle hndl = vpi_handle_by_name(const_cast<PLI_BYTE8*>(name), NULL);
    result = hndl ? valueStr(hndl, vpi_get(vpiType, hndl)) : "<null>";
    return result.c_str();
}

extern "C" void t_vpi_dump_put(const char* name, const char* value) {
    doPut(name, value, vpiNoDelay);
}

extern "C" void t_vpi_dump_put_rw(const char* name, const char* value, const char* flag) {
    const std::string f = flag;
    const int vflag = f == "force"      ? vpiForceFlag
                      : f == "release"  ? vpiReleaseFlag
                      : f == "inertial" ? vpiInertialDelay
                                        : vpiNoDelay;
    TEST_CHECK_LABEL(name, f, "", vflag != vpiNoDelay || f.empty());
    pushRwOp({OpKind::PUT, name, value, vflag});
}

extern "C" void t_vpi_dump_save() { pushRwOp({OpKind::SAVE, "", "", 0}); }

extern "C" void t_vpi_dump_restore() { pushRwOp({OpKind::RESTORE, "", "", 0}); }

extern "C" int t_vpi_dump_restores() { return restores; }

extern "C" void t_vpi_dump_clock(const char* name, int halfperiod) {
    const std::lock_guard<std::mutex> lock{apiMutex};
    clockName = name;
    clockHalf = halfperiod;
}

PLI_INT32 start_of_sim(t_cb_data* data) {
    TestVpiHandle it = vpi_iterate(vpiModule, NULL);
    TEST_CHECK_NZ(it);
    modDump(it, 0, false);
    next_sim_time(nullptr);
    registerCb(cbEndOfSimulation, &end_of_sim, NULL, NULL);
    return 0;
}

//cver, xcelium entry
void vpi_compat_bootstrap(void) {

    // We're able to call vpi_main() here on Verilator/Xcelium,
    // but Icarus complains (rightfully so)
    s_cb_data cb_data{};
    s_vpi_time vpi_time;

    vpi_time.high = 0;
    vpi_time.low = 0;
    vpi_time.type = vpiSimTime;

    cb_data.reason = cbStartOfSimulation;
    cb_data.cb_rtn = &start_of_sim;
    cb_data.obj = NULL;
    cb_data.time = &vpi_time;
    cb_data.value = NULL;
    cb_data.index = 0;
    cb_data.user_data = NULL;
    TestVpiHandle callback_h = vpi_register_cb(&cb_data);
}

// Verilator (via t_vpi_main.cpp), and standard LRM entry
void (*vlog_startup_routines[])() = {vpi_compat_bootstrap, 0};
