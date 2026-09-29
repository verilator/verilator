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
#include <cstdlib>
#include <cstring>
#include <map>
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

// Plusargs; with none, only the structure dump at start of simulation is printed.
//   +dump_values    also print sizes, then every value at each cbReadOnlySynch,
//                   printing only those changed since the previous dump
//   +dump_at=<name>[:<val>] dump values only in time steps where <name> changed (to <val>),
//                   and at the end of simulation
//   +dump_skip=<name> leave <name> out of the value dump
//   +dump_cb=<name> print <name> on each cbValueChange, from the end of the first time step
//   +dump_trigger=<name> +dump_put=[<trig>=]<trigval>:<name>:<value>[:<flag>]
//                   put when <trig> (default <name> of +dump_trigger) changes to <trigval>,
//                   then dump before the next eval. <value> is hex, real=<r> or str=<s>;
//                   <flag> is force, release, inertial, or rw to put at the next
//                   cbReadWriteSynch instead
//   +dump_save=<trigval> +dump_restore=<trigval> save or restore the model (--savable),
//                   dumping before a restore as well as after it
//   +dump_clock=<name>:<halfperiod> toggle <name>, for models without --timing
// Each put, save and restore runs once, on the first match of its trigger.
// A design may also import t_vpi_dump_value(name) and t_vpi_dump_put(name, value).
bool dumpValues = false;
std::vector<std::string> cbNames;
std::vector<std::string> skipNames;
std::string triggerName;
std::string atName;
int atVal = -1;
bool atHit = false;
std::string clockName;
int clockHalf = 0;
enum class OpKind : uint8_t { PUT, SAVE, RESTORE };
struct TriggerOp {
    OpKind kind;
    std::string trigName;
    int trigVal;
    std::string name;
    std::string value;
    int flag;
    bool rw;
    bool done;
};
std::vector<TriggerOp> triggerOps;
std::vector<TriggerOp> rwOps;
std::map<std::string, std::string> lastValues;

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
        const char* fullname = vpi_get_str(vpiFullName, hndl);
        if (values) {
            if (hasValue(hndl, type)
                && std::find(skipNames.begin(), skipNames.end(), fullname) == skipNames.end()) {
                const std::string val = valueStr(hndl, type);
                std::string& last = lastValues[fullname];
                if (last != val) {
                    printf("%s = %s\n", fullname, val.c_str());
                    last = val;
                }
            }
        } else {
            for (int i = 0; i < n; i++) printf("    ");
            const char* name = vpi_get_str(vpiName, hndl);
            printf("%s (%s) %s ", name, strFromVpiObjType(type), fullname);
            if (type == vpiParameter || type == vpiConstType) {
                printf(" vpiConstType=%s", strFromVpiConstType(vpi_get(vpiConstType, hndl)));
            }
            if (type == vpiModule) printf(" vpiDefName=%s", vpi_get_str(vpiDefName, hndl));
            if (dumpValues && hasValue(hndl, type)) printf(" vpiSize=%d", vpi_get(vpiSize, hndl));
            printf("\n");
        }

        if (iterate_over.find(type) == iterate_over.end()) continue;
        for (int type : iterate_over.at(type)) {
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
}

void registerCb(PLI_INT32 reason, PLI_INT32 (*rtn)(t_cb_data*), vpiHandle obj,
                PLI_BYTE8* user_data, uint64_t delay = 0) {
    static s_vpi_time time_s;
    time_s.type = delay ? vpiSimTime : vpiSuppressTime;
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

PLI_INT32 next_sim_time(t_cb_data* data);
PLI_INT32 value_change(t_cb_data* data);

void registerValueCbs() {
    for (const std::string& name : cbNames) {
        vpiHandle hndl = vpi_handle_by_name(const_cast<PLI_BYTE8*>(name.c_str()), NULL);
        TEST_CHECK_NZ(hndl);
        if (hndl) registerCb(cbValueChange, &value_change, hndl, strdup(name.c_str()));
    }
    cbNames.clear();
}

PLI_INT32 read_only_synch(t_cb_data* data) {
    static bool first = true;
    if (dumpValues && (first || atName.empty() || atHit)) valuesDump("readonly");
    first = false;
    atHit = false;
    registerValueCbs();
    if (dumpValues) registerCb(cbNextSimTime, &next_sim_time, NULL, NULL);
    return 0;
}

PLI_INT32 next_sim_time(t_cb_data* data) {
    registerCb(cbReadOnlySynch, &read_only_synch, NULL, NULL);
    return 0;
}

PLI_INT32 at_change(t_cb_data* data) {
    if (atVal < 0 || std::strtol(data->value->value.str, NULL, 16) == atVal) atHit = true;
    return 0;
}

PLI_INT32 end_of_sim(t_cb_data* data) {
    valuesDump("end");
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

void doPut(const TriggerOp& op) {
    TestVpiHandle hndl = vpi_handle_by_name(const_cast<PLI_BYTE8*>(op.name.c_str()), NULL);
    s_vpi_value value{};
    if (op.value.rfind("real=", 0) == 0) {
        value.format = vpiRealVal;
        value.value.real = std::strtod(op.value.c_str() + 5, NULL);
    } else {
        value.format = op.value.rfind("str=", 0) == 0 ? vpiStringVal : vpiHexStrVal;
        value.value.str
            = const_cast<PLI_BYTE8*>(op.value.c_str()) + (value.format == vpiStringVal ? 4 : 0);
    }
    vpi_put_value(hndl, &value, NULL, op.flag);
    s_vpi_error_info info{};
    const bool ok = hndl && vpi_chk_error(&info) < vpiError;
    printf("-- put %s = %s flag=%d %s\n", op.name.c_str(), op.value.c_str(), op.flag,
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
    const std::vector<TriggerOp> ops = std::move(rwOps);
    rwOps.clear();
    for (const TriggerOp& op : ops) doPut(op);
    valuesDump("after put");
    return 0;
}

PLI_INT32 value_change(t_cb_data* data) {
    const char* name = data->user_data;
    printf("-- @%" PRIu64 " cb %s = %s\n", simTime(), name, data->value->value.str);
    const int trigVal = static_cast<int>(std::strtol(data->value->value.str, NULL, 16));
    const char* what = nullptr;
    for (TriggerOp& op : triggerOps) {
        if (op.done || op.trigName != name || op.trigVal != trigVal) continue;
        op.done = true;
        if (op.kind != OpKind::PUT) {
            if (op.kind == OpKind::RESTORE) valuesDump("before restore");
            doSaveRestore(op.kind);
            what = op.kind == OpKind::SAVE ? "after save" : "after restore";
        } else if (op.rw) {
            if (rwOps.empty()) registerCb(cbReadWriteSynch, &read_write_synch, NULL, NULL);
            rwOps.push_back(op);
        } else {
            doPut(op);
            what = "after put";
        }
    }
    if (what) valuesDump(what);
    return 0;
}

extern "C" void t_vpi_dump_value(const char* name) {
    TestVpiHandle hndl = vpi_handle_by_name(const_cast<PLI_BYTE8*>(name), NULL);
    printf("-- @%" PRIu64 " dpi %s = %s\n", simTime(), name,
           hndl ? valueStr(hndl, vpi_get(vpiType, hndl)).c_str() : "<null>");
}

extern "C" void t_vpi_dump_put(const char* name, const char* value) {
    doPut({OpKind::PUT, "", 0, name, value, vpiNoDelay, false, true});
}

std::vector<std::string> splitColons(const std::string& arg, size_t pos) {
    std::vector<std::string> f;
    while (true) {
        const size_t next = arg.find(':', pos);
        f.push_back(arg.substr(pos, next - pos));
        if (next == std::string::npos) return f;
        pos = next + 1;
    }
}

int parseInt(const std::string& s) { return static_cast<int>(std::strtol(s.c_str(), NULL, 0)); }

void parseArgs() {
    s_vpi_vlog_info info{};
    if (!vpi_get_vlog_info(&info)) return;
    for (int i = 1; i < info.argc; ++i) {
        const std::string arg = info.argv[i];
        if (arg == "+dump_values") {
            dumpValues = true;
        } else if (arg.rfind("+dump_at=", 0) == 0) {
            const std::vector<std::string> f = splitColons(arg, 9);
            atName = f[0];
            if (f.size() > 1) atVal = parseInt(f[1]);
        } else if (arg.rfind("+dump_cb=", 0) == 0) {
            cbNames.push_back(arg.substr(9));
        } else if (arg.rfind("+dump_skip=", 0) == 0) {
            skipNames.push_back(arg.substr(11));
        } else if (arg.rfind("+dump_trigger=", 0) == 0) {
            triggerName = arg.substr(14);
        } else if (arg.rfind("+dump_clock=", 0) == 0) {
            const std::vector<std::string> f = splitColons(arg, 12);
            clockName = f[0];
            clockHalf = parseInt(f[1]);
        } else if (arg.rfind("+dump_save=", 0) == 0) {
            triggerOps.push_back(
                {OpKind::SAVE, "", parseInt(arg.substr(11)), "", "", 0, false, false});
        } else if (arg.rfind("+dump_restore=", 0) == 0) {
            triggerOps.push_back(
                {OpKind::RESTORE, "", parseInt(arg.substr(14)), "", "", 0, false, false});
        } else if (arg.rfind("+dump_put=", 0) == 0) {
            const std::vector<std::string> f = splitColons(arg, 10);
            std::string trig;
            std::string val = f[0];
            const size_t eq = val.find('=');
            if (eq != std::string::npos) {
                trig = val.substr(0, eq);
                val = val.substr(eq + 1);
            }
            int flag = vpiNoDelay;
            if (f.size() > 3 && f[3] == "force") flag = vpiForceFlag;
            if (f.size() > 3 && f[3] == "release") flag = vpiReleaseFlag;
            if (f.size() > 3 && f[3] == "inertial") flag = vpiInertialDelay;
            const bool rw = f.size() > 3 && f[3] == "rw";
            triggerOps.push_back({OpKind::PUT, trig, parseInt(val), f[1], f[2], flag, rw, false});
        }
    }
    for (TriggerOp& op : triggerOps) {
        if (op.trigName.empty()) op.trigName = triggerName;
        if (std::find(cbNames.begin(), cbNames.end(), op.trigName) == cbNames.end())
            cbNames.push_back(op.trigName);
    }
}

PLI_INT32 start_of_sim(t_cb_data* data) {
    parseArgs();
    TestVpiHandle it = vpi_iterate(vpiModule, NULL);
    TEST_CHECK_NZ(it);
    modDump(it, 0, false);
    if (!atName.empty()) {
        vpiHandle hndl = vpi_handle_by_name(const_cast<PLI_BYTE8*>(atName.c_str()), NULL);
        TEST_CHECK_NZ(hndl);
        if (hndl) registerCb(cbValueChange, &at_change, hndl, NULL);
        if (dumpValues) registerCb(cbEndOfSimulation, &end_of_sim, NULL, NULL);
    }
    if (!clockName.empty()) registerCb(cbAfterDelay, &clock_toggle, NULL, NULL, clockHalf);
    if (dumpValues || !cbNames.empty()) registerCb(cbReadOnlySynch, &read_only_synch, NULL, NULL);
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
