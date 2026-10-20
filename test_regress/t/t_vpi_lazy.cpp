// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "TestCheck.h"
#include "TestVpi.h"
#include "vpi_user.h"

#ifdef T_VPI_LAZY_SAVABLE
#include "verilated_save.h"
#include VM_PREFIX_INCLUDE
extern VM_PREFIX* testVpiTopp;
#endif

#include <algorithm>
#include <cstdint>
#include <cstdio>
#include <functional>
#include <string>
#include <utility>
#include <vector>

int errors = 0;

namespace {

vpiHandle find(const std::string& name) {
    vpiHandle handle = vpi_handle_by_name(const_cast<PLI_BYTE8*>(name.c_str()), nullptr);
    TEST_CHECK_NZ_LABEL(name, handle);
    return handle;
}

uint32_t get(vpiHandle handle) {
    s_vpi_value value{};
    value.format = vpiIntVal;
    vpi_get_value(handle, &value);
    return static_cast<uint32_t>(value.value.integer);
}
uint32_t get(const std::string& name) { return get(find(name)); }

void put(vpiHandle handle, uint32_t v, PLI_INT32 flags = vpiNoDelay) {
    s_vpi_value value{};
    value.format = vpiIntVal;
    value.value.integer = static_cast<PLI_INT32>(v);
    vpi_put_value(handle, &value, nullptr, flags);
}
void put(const std::string& name, uint32_t v, PLI_INT32 flags = vpiNoDelay) {
    put(find(name), v, flags);
}

// A top-level input
void in(const char* port, uint32_t v) { put(std::string{"TOP."} + port, v); }

void check(const std::string& label, uint32_t got, uint32_t exp) {
    TEST_CHECK_EQ_LABEL(label, got, exp);
}

void accept(const std::string& name, uint32_t v, PLI_INT32 flags = vpiNoDelay) {
    put(name, v, flags);
    TEST_CHECK_ERROR(false);
    if (flags == vpiNoDelay) check(name, get(name), v);
}

// The test is a sequence of steps, each run at the start of its own time step, so between
// evals; the eval after each one consumes its puts
std::vector<std::function<void()>> s_steps;
size_t s_stepNo = 0;
void step(std::function<void()> fn) { s_steps.push_back(std::move(fn)); }

PLI_INT32 runStep(p_cb_data);
void scheduleStep() {
    static s_vpi_time time{vpiSimTime, 0, 1, 0};
    s_cb_data cb{};
    cb.reason = cbAfterDelay;
    cb.cb_rtn = runStep;
    cb.time = &time;
    vpi_release_handle(vpi_register_cb(&cb));
}
PLI_INT32 runStep(p_cb_data) {
    s_steps[s_stepNo++]();
    if (s_stepNo < s_steps.size()) {
        scheduleStep();
    } else if (!errors) {
        std::printf("*-* All Finished *-*\n");
    }
    return 0;
}

#ifdef T_VPI_LAZY_SAVABLE
const char* const s_savePath = VL_STRINGIFY(TEST_OBJ_DIR) "/saved.vltsv";

void saveModel() {
    VerilatedSave os;
    os.open(s_savePath);
    os << *testVpiTopp;
}

void restoreModel() {
    VerilatedRestore os;
    os.open(s_savePath);
    os >> *testVpiTopp;
}

bool plusArg(const std::string& arg) {
    s_vpi_vlog_info info{};
    vpi_get_vlog_info(&info);
    for (int i = 0; i < info.argc; ++i)
        if (info.argv[i] == arg) return true;
    return false;
}

// Saved between a put and the eval consuming it: restored, into this model or a fresh one, the
// put's readers read as before it until that eval
void checkRestored() {
    check("lz_save.k_q restored", get("lz_save.k_q"), 0x40);
    check("lz_save.ch1 restored", get("lz_save.ch1"), 0x28);
    check("lz_save.al1 restored", get("lz_save.al1"), 0x21);
}

void script() {
    if (plusArg("+restore")) {
        step([] {
            restoreModel();
            checkRestored();
        });
        step([] { check("lz_save.ch1", get("lz_save.ch1"), 0x47); });
        return;
    }
    step([] { in("clk", 1); });
    step([] { in("clk", 0); });
    step([] {
        accept("lz_save.k_q", 0x40);
        check("lz_save.ch1 before eval", get("lz_save.ch1"), 0x28);
        check("lz_save.al1 before eval", get("lz_save.al1"), 0x21);
        // Traced as a put
        accept("lz_save.u_tr.keep", 0x10);
        saveModel();
    });
    step([] {
        check("lz_save.ch1", get("lz_save.ch1"), 0x47);
        check("lz_save.al1", get("lz_save.al1"), 0x40);
        restoreModel();
        checkRestored();
    });
    step([] { check("lz_save.ch1", get("lz_save.ch1"), 0x47); });
}

PLI_INT32 startOfSimulation(p_cb_data) {
    // For the design's $dumpvars
    Verilated::traceEverOn(true);
    in("clk", 0);
    put("lz_save.d", 0x21);
    script();
    scheduleStep();
    return 0;
}

}  // namespace

#else
void putStr(const std::string& name, PLI_INT32 format, const char* str) {
    s_vpi_value value{};
    value.format = format;
    value.value.str = const_cast<PLI_BYTE8*>(str);
    vpi_put_value(find(name), &value, nullptr, vpiNoDelay);
}

std::string getStr(vpiHandle handle, PLI_INT32 format) {
    s_vpi_value value{};
    value.format = format;
    vpi_get_value(handle, &value);
    s_vpi_error_info info{};
    if (vpi_chk_error(&info)) return "?";
    if (format == vpiRealVal) return std::to_string(value.value.real);
    return value.value.str;
}

// The combinational refusal's text is printed in full once, then only the name it reports
void reject(const std::string& name, uint32_t v, PLI_INT32 flags = vpiNoDelay) {
    static const std::string s_combMsg
        = "vpi_put_value was used on signal combinationally driven under --vpi-lazy, use a "
          "public_flat_rw attribute to write ";
    static bool s_combPrinted = false;
    const uint32_t before = get(name);
    put(name, v, flags);
    s_vpi_error_info info{};
    TEST_CHECK_NZ_LABEL(name.c_str(), vpi_chk_error(&info));
    const std::string msg = info.message ? info.message : "";
    if (msg.rfind(s_combMsg, 0) == 0 && s_combPrinted) {
        std::printf("reject %s\n", msg.substr(s_combMsg.size()).c_str());
    } else {
        s_combPrinted |= msg.rfind(s_combMsg, 0) == 0;
        std::printf("vpi_chk_error: %s\n", msg.c_str());
    }
    check(name, get(name), before);
}

// A put into a masked signal writes the other bits and keeps the masked ones, silently
void merge(const std::string& name, uint32_t v, uint32_t combMask) {
    const uint32_t before = get(name);
    put(name, v);
    TEST_CHECK_ERROR(false);
    check(name, get(name), (v & ~combMask) | (before & combMask));
}

void putArray(const std::string& name, int index, const PLI_INT32* valsp, int num,
              bool expectError) {
    s_vpi_arrayvalue value{};
    value.format = vpiIntVal;
    value.value.integers = const_cast<PLI_INT32*>(valsp);
    PLI_INT32 indexes[1] = {index};
    vpi_put_value_array(find(name), &value, indexes, num);
    TEST_CHECK_ERROR(expectError);
}

// Flip each bit in turn, restoring any taken put: 'W' where a put changes it, 'r' where not
std::string writableBits(vpiHandle handle) {
    const int size = vpi_get(vpiSize, handle);
    if (size <= 0 || size > 32) return "?";
    std::string bits;
    for (int bit = size - 1; bit >= 0; --bit) {
        const uint32_t before = get(handle);
        put(handle, before ^ (1U << bit));
        s_vpi_error_info info{};
        const bool refused = vpi_chk_error(&info) || get(handle) == before;
        if (!refused) put(handle, before);
        bits += refused ? 'r' : 'W';
    }
    if (bits.find('r') == std::string::npos) return "W";
    if (bits.find('W') == std::string::npos) return "r";
    return bits;
}

std::string valueStr(vpiHandle handle) {
    switch (vpi_get(vpiType, handle)) {
    case vpiRealVar: return getStr(handle, vpiRealVal);
    case vpiStringVar: return '"' + getStr(handle, vpiStringVal) + '"';
    default: return getStr(handle, vpiHexStrVal);
    }
}

// Every row, as a handle, in hierarchy order
void walk(vpiHandle scopep, const std::function<void(vpiHandle)>& fn) {
    for (const PLI_INT32 type : {vpiReg, vpiNet}) {
        TestVpiHandle iterp = vpi_iterate(type, scopep);
        if (!iterp) continue;
        while (vpiHandle handle = vpi_scan(iterp)) fn(handle);
        iterp.freed();
    }
    for (const PLI_INT32 type : {vpiModule, vpiInterface}) {
        TestVpiHandle iterp = vpi_iterate(type, scopep);
        if (!iterp) continue;
        while (vpiHandle subp = vpi_scan(iterp)) walk(subp, fn);
        iterp.freed();
    }
}

std::string fullName(vpiHandle handle) { return vpi_get_str(vpiFullName, handle); }

// Before the first eval a variable reads its reset value, all ones under
// +verilator+rand+reset+1, whether stored or rebuilt on read; the golden lists the others
void printResetValues() {
    walk(nullptr, [](vpiHandle handle) {
        const PLI_INT32 type = vpi_get(vpiType, handle);
        if (type == vpiParameter || type == vpiRealVar || type == vpiStringVar) return;
        // Whether a constant is folded into its net before the first eval depends on -O
        if (fullName(handle) == "t.cst_w") return;
        const std::string bin = getStr(handle, vpiBinStrVal);
        if (bin != "?" && bin.find_first_not_of('1') != std::string::npos)
            std::printf("reset %s %s\n", fullName(handle).c_str(), bin.c_str());
    });
}

// The whole VPI-visible set, each row's value and writability
void dumpRows() {
    std::vector<std::string> lines;
    walk(nullptr, [&lines](vpiHandle handle) {
        const std::string name = fullName(handle);
        // A compiler temporary has no RTL name; force controls are public by V3Force
        const bool forceCtl = name.find("__VforceEn") != std::string::npos
                              || name.find("__VforceVal") != std::string::npos;
        if (!forceCtl && name.find("__") != std::string::npos) {
            std::printf("%%Error: compiler temporary is VPI-visible: %s\n", name.c_str());
            ++errors;
        }
        lines.push_back(name + " " + valueStr(handle) + " " + writableBits(handle));
    });
    std::sort(lines.begin(), lines.end());
    for (const std::string& line : lines) std::printf("%s\n", line.c_str());
}

struct ValueCb final {
    std::string name;
    vpiHandle cb;
    int count;
    uint32_t value;
};
std::vector<ValueCb> s_valueCbs;

PLI_INT32 valueCb(p_cb_data cbp) {
    ValueCb* const vcp = reinterpret_cast<ValueCb*>(cbp->user_data);
    ++vcp->count;
    vcp->value = static_cast<uint32_t>(cbp->value->value.integer);
    return 0;
}

void armValueCbs(std::initializer_list<const char*> names) {
    for (const char* name : names) s_valueCbs.push_back({name, nullptr, 0, 0});
    static s_vpi_time time{vpiSuppressTime, 0, 0, 0};
    static s_vpi_value value{vpiIntVal, {0}};
    for (ValueCb& vc : s_valueCbs) {
        s_cb_data cb{};
        cb.reason = cbValueChange;
        cb.cb_rtn = valueCb;
        cb.obj = find(vc.name);
        cb.time = &time;
        cb.value = &value;
        cb.user_data = reinterpret_cast<PLI_BYTE8*>(&vc);
        vc.cb = vpi_register_cb(&cb);
        TEST_CHECK_NZ_LABEL(vc.name, vc.cb);
    }
}

void reportValueCbs() {
    for (ValueCb& vc : s_valueCbs) {
        std::printf("cbValueChange %s fired %d 0x%02x\n", vc.name.c_str(), vc.count, vc.value);
        vpi_remove_cb(vc.cb);
    }
    s_valueCbs.clear();
}

// Values held across steps
uint32_t s_mix, s_dWas, s_ohHeld, s_st, s_g0, s_driven;
std::vector<uint32_t> s_held;
std::string s_strComb;
int s_probes = 0;

// The encoder drives all of level 0 and one bit per segment of each level above
constexpr uint32_t ohMask = 0x15f;
uint32_t ohDriven(uint32_t d) {
    const uint32_t i = d & 0xf;
    return i | (i & 3 ? 1U : 0U) << 4 | (i & 0xc ? 1U : 0U) << 6 | (i ? 1U : 0U) << 8;
}

void script() {
    // After the first eval, which fired each callback once for its settle
    step([] {
        reportValueCbs();
        in("rst", 0);
        in("rst_n", 1);
        in("set_n", 1);
        in("ld", 0);
        in("clk", 1);
    });
    step([] { in("clk", 0); });
    step([] { in("clk", 1); });
    step([] { in("clk", 0); });
    step([] {
        // Before either instance's own row refreshes it, so a refresh of the wrong one shows
        for (const char* inst : {"0", "1"}) {
            const std::string fy = std::string{"t.fy"} + inst;
            check("t.fyx" + std::string{inst} + "_c", get("t.fyx" + std::string{inst} + "_c"),
                  0xff & ((get(fy + ".r") + 1) ^ 0x55));
        }
        // Each cone reads storage only a compiler temporary holds
        check("t.px_o", get("t.px_o"), 0xff & ~(0x21 ^ 0x40));
        check("t.u_px.i", get("t.u_px.i"), 0x21 ^ 0x40);
        check("t.nest_c", get("t.nest_c"), (0x21 + 3) ^ (0x40 + 3));
        check("t.tw weak", get("t.tw"), 0x40);
        check("t.tw_r weak", get("t.tw_r"), 0x40);
        in("en", 1);
    });
    step([] {
        check("t.tw_r strong", get("t.tw_r"), 0x21);
        in("en", 0);
    });
    step([] {
        for (const char* name :
             {"t.ff_q", "t.arn_q", "t.arp_q", "t.as_q", "t.al_q", "t.lat_q", "t.ilat_q",
              "t.undr_mem[2]", "t.init_r", "t.ini_r", "t.in_a", "t.frw_c", "t.frc_al", "t.u_ff.q",
              "t.bus.q", "t.pf", "t.intf_inst.sig", "t.spl_l", "t.imp_l"}) {
            accept(name, 0x5a);
        }
        // Each instance as the RTL drives it, beside a comb-driven instance of the same variable
        for (const char* name : {"t.ia.q", "t.cf0.p", "t.cu.p", "t.mc2.m"}) accept(name, 0x5a);
        s_mix = get("t.u_mix.m");
        accept("t.u_mix.m", (s_mix & 1) | 0xa4);
        in("d", 0x33);
    });
    step([] {
        // A flop holds the put until its next edge
        check("t.ff_q held", get("t.ff_q"), 0x5a);
        check("t.lat_q held", get("t.lat_q"), 0x5a);
        check("t.ib.q follows", get("t.ib.q"), 0x5a);
        in("clk", 1);
    });
    step([] { in("clk", 0); });
    step([] {
        check("t.ff_q edge", get("t.ff_q"), 0x33);
        // The put is in the storage the logic reads
        check("t.n_ff", get("t.n_ff"), 0x5a);
        check("t.n_mix", get("t.n_mix"), (s_mix & 1) | 0xa4);
        check("t.n_if", get("t.n_if"), 0x5a);
        check("t.n_in", get("t.n_in"), 0xa5);
        check("t.n_cons", get("t.n_cons"), 0x5a);
        check("t.n_ia", get("t.n_ia"), 0x5a);
        check("t.n_cf0", get("t.n_cf0"), 0x5a);
        check("t.n_cu", get("t.n_cu"), 0x5a);
        check("t.n_mc2", get("t.n_mc2"), 0x5a);
        check("t.ia.q edge", get("t.ia.q"), 0x33);
        check("t.ib.q edge", get("t.ib.q"), 0x33);

        for (const char* name :
             {"t.asg_w",     "t.ac_c",     "t.star_c",  "t.out_c",   "t.sub_o",  "t.u_sub.o",
              "t.fc_c",      "t.gclk",     "t.vidx[0]", "t.cst_w",   "t.loop_c", "t.while_c",
              "t.w_ff",      "t.w_mix",    "t.u_in.i",  "t.c1_c",    "t.cg_c",   "t.pon_c",
              "t.pand_c",    "t.px_o",     "t.u_px.i",  "t.u_px.o",  "t.tw",     "t.tw_r",
              "t.out_q",     "t.out_m",    "t.ib.q",    "t.cf1.p",   "t.ch2",    "t.sgn_c",
              "t.cat_c",     "t.self_c",   "t.part_c",  "t.ctv_c",   "t.cts_c",  "t.hl_c",
              "t.us_c.a",    "t.mem_c[0]", "t.mixf_w",  "t.ovl_w",   "t.al1",    "t.al2",
              "t.pass_o",    "t.fmid_c",   "t.sib_b",   "t.sib_c",   "t.wd_w",   "t.u_wdrv.o",
              "t.rdpin",     "t.ivec",     "t.cy0.din", "t.cy1.din", "t.cy0.cy", "t.tmp_o",
              "t.u_tmp.cpy", "t.ifd.a",    "t.alc_x",   "t.plv_c"}) {
            reject(name, get(name) ^ 0x5b);
        }
        {
            vpiHandle const mdp = vpi_handle_by_index(vpi_handle_by_index(find("t.mdp_c"), 0), 0);
            TEST_CHECK_NZ_LABEL("t.mdp_c[0][0]", mdp);
            const uint32_t before = get(mdp);
            put(mdp, before ^ 0x5b);
            TEST_CHECK_ERROR(true);
            check("t.mdp_c[0][0]", get(mdp), before);
        }
        // A refused put into one instance leaves the other's value as its own driver made it
        check("t.cy1.cy", get("t.cy1.cy"), get("t.k_q") ^ 0xa5);
        // Each alias row reports its own metadata, not its canonical's, and reads the canonical
        for (const char* name : {"t.al_sw", "t.al_nw", "t.al1", "t.sib_bt", "t.ch1"}) {
            TEST_CHECK_EQ_LABEL(name, vpi_get(vpiSize, find(name)), 8);
        }
        TEST_CHECK_EQ_LABEL("t.al_sw", vpi_get(vpiSigned, find("t.al_sw")), 1);
        TEST_CHECK_EQ_LABEL("t.sgn_c", vpi_get(vpiSigned, find("t.sgn_c")), 1);
        TEST_CHECK_EQ_LABEL("t.sib_bt", vpi_get(vpiType, find("t.sib_bt")), vpiBitVar);
        TEST_CHECK_EQ_LABEL("t.ch1", vpi_get(vpiType, find("t.ch1")), vpiReg);
        TEST_CHECK_EQ_LABEL("t.al1", vpi_get(vpiSigned, find("t.al1")), 0);
        TEST_CHECK_EQ_LABEL("t.al_sw", get(vpi_handle(vpiLeftRange, find("t.al_sw"))), 8);
        TEST_CHECK_EQ_LABEL("t.al_sw", get(vpi_handle(vpiRightRange, find("t.al_sw"))), 1);
        TEST_CHECK_EQ_LABEL("t.pk_al", vpi_get(vpiSize, find("t.pk_al")), 16);
        for (const char* name : {"t.al_sw", "t.al_nw"}) check(name, get(name), get("t.k_q"));
        check("t.sib_bt", get("t.sib_bt"), get("t.ch1"));
        check("t.pk_al", get("t.pk_al"), get("t.pk_c"));
        check("t.us_c.b", get("t.us_c.b"), 0xff & ~get("t.us_c.a"));
        // Only the bits no comb driver writes take a put
        accept("t.nopre_c", get("t.nopre_c") ^ 0xa0);
        merge("t.nopre_c", get("t.nopre_c") ^ 0x1, 0x0f);
        merge("t.nopre_c", get("t.nopre_c") ^ 0xff, 0x0f);
        accept("t.pla_l", get("t.pla_l") ^ 0x0f);
        accept("t.plb_l", get("t.plb_l") ^ 0x0f);
        merge("t.plb_l", get("t.plb_l") ^ 0xf0, 0xf0);
        accept("t.plc_l", get("t.plc_l") ^ 0x0c);
        merge("t.plc_l", get("t.plc_l") ^ 0x03, 0x03);
        merge("t.plc_l", get("t.plc_l") ^ 0xff, 0x03);
        accept("t.plm_l[0]", get("t.plm_l[0]") ^ 0xff);
        merge("t.plm_l[1]", get("t.plm_l[1]") ^ 0xff, 0xff);
        merge("t.ple_l[1]", get("t.ple_l[1]") ^ 0xff, 0x0f);
        merge("t.ple_l[1]", get("t.ple_l[1]") ^ 0x0f, 0x0f);
        merge("t.plu_l[0]", get("t.plu_l[0]") ^ 0xff, 0xf0);
        merge("t.plu_l[1]", get("t.plu_l[1]") ^ 0xff, 0x0f);
        // Undriven bits no read reaches hold a put; the driven ones stay the encoder's
        s_dWas = get("TOP.d");
        check("t.oh.v", get("t.oh.v") & ohMask, ohDriven(s_dWas));
        merge("t.oh.v", get("t.oh.v") ^ 0x1, ohMask);
        merge("t.oh.v", get("t.oh.v") ^ 0xfff, ohMask);
        s_ohHeld = get("t.oh.v") & ~ohMask;
        in("d", 0x08);
    });
    step([] {
        check("t.oh.v held", get("t.oh.v"), s_ohHeld | ohDriven(0x08));
        check("t.oh_a", get("t.oh_a"), 3);
        in("d", s_dWas);
    });
    step([] {
        check("t.oh.v restored", get("t.oh.v"), s_ohHeld | ohDriven(s_dWas));
        // A variable read of the undriven bits sees the put
        merge("t.dli", get("t.dli") ^ 0xff00ff00, 0x00ff00ff);
        in("sel", 3);
    });
    step([] {
        check("t.dli_o", get("t.dli_o"), get("t.dli") >> 24);
        in("sel", 1);
    });
    step([] {
        reject("t.ac_c", 0, vpiInertialDelay);
        reject("t.ac_c", 0, vpiForceFlag);
        // public_flat_rw takes a put on a comb-driven net until the next eval
        for (const char* name : {"t.u_na.z", "t.u_na.w"}) accept(name, 0x5a);
        reject("t.u_na.q", get("t.u_na.q") ^ 0x5b);
        // A put may change only the bits no comb driver writes
        const uint32_t st = get("t.st");
        accept("t.st", (st & 1) | (0x05 << 1));
        merge("t.st", get("t.st") ^ 1, 0x01);
        // An inertial put is merged when it lands, after this step's eval
        s_st = get("t.st");
        accept("t.st", s_st ^ 0xff, vpiInertialDelay);
    });
    step([] {
        check("t.st.cnt inertial", get("t.st.cnt"), (s_st >> 1) ^ 0x7f);
        accept("t.st.cnt", 0x09, vpiInertialDelay);
    });
    step([] {
        check("t.st.cnt inertial", get("t.st.cnt"), 0x09);
        check("t.st.busy", get("t.st.busy"), 1);
        // A packed member takes its parent's mask
        accept("t.st.cnt", get("t.st.cnt") ^ 0x55);
        merge("t.st.busy", get("t.st.busy") ^ 1, 0x1);
        // A mixed-mask signal is not forceable, so force/release are refused as-is
        reject("t.st", get("t.st") ^ (1 << 1), vpiForceFlag);
        reject("t.st", get("t.st") ^ (1 << 1), vpiReleaseFlag);
        {
            // A non-canonical inertial-delay format falls through to the ordinary put
            const uint32_t before = get("t.st");
            s_vpi_value value{};
            value.format = vpiTimeVal;
            vpi_put_value(find("t.st"), &value, nullptr, vpiInertialDelay);
            TEST_CHECK_ERROR(true);
            // Nor can a masked put be made in a format no signal takes
            vpi_put_value(find("t.st"), &value, nullptr, vpiNoDelay);
            TEST_CHECK_ERROR(true);
            check("t.st bad format", get("t.st"), before);
            putStr("t.st", vpiDecStrVal, "zz");
            TEST_CHECK_ERROR(true);
            check("t.st bad decimal", get("t.st"), before);
        }
        const uint32_t vec = get("t.vec");
        accept("t.vec", (vec & 1) | 0xa4);
        merge("t.vec", get("t.vec") ^ 1, 0x01);
        merge("t.u_mix.m", get("t.u_mix.m") ^ 1, 0x01);
        accept("t.pmem[0]", 0x5a);
        accept("t.pmem[2]", 0x5b);
        merge("t.pmem[1]", get("t.pmem[1]") ^ 0x5a, 0xff);
        merge("t.pmem[3]", get("t.pmem[3]") ^ 0x5a, 0xff);
        // Instances of one variable, each masked by its own comb drivers
        for (const auto& pr : {std::make_pair("t.cp.p", 0x0fU), std::make_pair("t.mc0.m", 0x0fU),
                               std::make_pair("t.mc1.m", 0xf0U)}) {
            accept(pr.first, get(pr.first) ^ (0xffU & ~pr.second));
            merge(pr.first, get(pr.first) ^ pr.second, pr.second);
            merge(pr.first, get(pr.first) ^ 0xff, pr.second);
        }
        const PLI_INT32 one[1] = {0x6c};
        putArray("t.pmem", 0, one, 1, false);
        check("t.pmem[0] array", get("t.pmem[0]"), 0x6c);
        // Wraps from [3] to [0]
        const uint32_t pmem3 = get("t.pmem[3]");
        const PLI_INT32 wrap[2] = {static_cast<PLI_INT32>(pmem3 ^ 0xff), 0x4e};
        putArray("t.pmem", 3, wrap, 2, false);
        check("t.pmem[0] array wrapped", get("t.pmem[0]"), 0x4e);
        check("t.pmem[3] array wrapped", get("t.pmem[3]"), pmem3);
        const uint32_t pmem1 = get("t.pmem[1]");
        const PLI_INT32 two[2] = {0x7d, static_cast<PLI_INT32>(pmem1 ^ 0xff)};
        putArray("t.pmem", 0, two, 2, false);
        check("t.pmem[0] array merged", get("t.pmem[0]"), 0x7d);
        check("t.pmem[1] array merged", get("t.pmem[1]"), pmem1);
        const PLI_INT32 masked[1] = {static_cast<PLI_INT32>(pmem1 ^ 0xff)};
        putArray("t.pmem", 1, masked, 1, false);
        check("t.pmem[1] array kept", get("t.pmem[1]"), pmem1);
        putArray("t.vidx", 0, one, 1, true);
        // A retained memory's array put reaches a cone reading it only at the next eval
        s_g0 = get("t.gmem[0]");
        const PLI_INT32 flipped[1] = {static_cast<PLI_INT32>(s_g0 ^ 0xff)};
        putArray("t.gmem", 0, flipped, 1, false);
        check("t.gmem_r before eval", get("t.gmem_r"), s_g0);
    });
    step([] {
        check("t.gmem_r after eval", get("t.gmem_r"), s_g0 ^ 0xff);
        const uint32_t d = get("TOP.d");
        const uint32_t inA = get("TOP.in_a");
        const uint32_t sel = get("TOP.sel");
        check("t.vax", (get("t.vax") >> sel) & 1, get("TOP.en"));
        check("t.ct_c", get("t.ct_c"), d);
        check("t.uw_c", get("t.uw_c"), sel & 1 ? d : inA);
        check("t.uv_c", get("t.uv_c"), (d & 0xf) ^ inA);
        check("t.mc_x", get("t.mc_x"), (((d + 3) & 0xf) << 4) | (d & 0xf));
        accept("t.m4[1][1]", get("t.m4[1][1]") ^ 0xff);
        merge("t.m4[0][0]", get("t.m4[0][0]") ^ 0xff, 0x0f);
        // A refused put into a retained comb signal leaves the flop sampling it its driven value
        s_driven = get("t.ret_c");
        reject("t.ret_c", s_driven ^ 0x5b);
        in("clk", 1);
    });
    step([] {
        check("t.ret_q", get("t.ret_q"), s_driven);
        in("clk", 0);
    });
    step([] {
        check("t.ret_c edge", get("t.ret_c"), get("t.k_q") ^ 0x5a);
        // An unparsable decimal put writes nothing
        const uint32_t before = get("t.ff_q");
        putStr("t.ff_q", vpiDecStrVal, "A123");
        TEST_CHECK_ERROR(true);
        check("t.ff_q bad decimal", get("t.ff_q"), before);
        in("d", 0x3c);
        in("clk", 1);
    });
    step([] { in("clk", 0); });
    step([] {
        // A packed member reads through its reconstructed parent and takes its write policy
        check("t.cts_c.hi", get("t.cts_c.hi"), 0xc);
        reject("t.cts_c.hi", get("t.cts_c.hi") ^ 0x5);
        accept("t.st.cnt", get("t.st.cnt") ^ 0x2a);
        // Read mid-eval at each rising edge
        s_probes = 0;
        put("t.prb_s", 0x12);
        in("clk", 1);
    });
    step([] {
        check("probes", s_probes, 1);
        in("clk", 0);
    });
    step([] {
        // A put into a stored source, string and real alike, reaches its readers at the next
        // eval; until then they read as before it
        s_held = {get("t.u_po.s_comb"), get("t.u_mi.p0.xali"), get("t.fyx0_c"),
                  get("t.u_po.f_comb"), get("t.u_cc.frc_c"),   get("t.u_cc.orphan_c")};
        s_strComb = getStr(find("t.u_po.str_comb"), vpiStringVal);
        accept("t.u_po.s", 0x22);
        accept("t.u_mi.p0.uc.cflop", 0x3c);
        accept("t.fy0.r", 0x10);
        accept("t.u_cc.orphan", 0x2a);
        putStr("t.u_po.str", vpiStringVal, "longer_than_any_short_string_buffer");
        TEST_CHECK_ERROR(false);
        putStr("t.u_po.str", vpiStringVal, "longer_than_any_short_string_buffer");
        TEST_CHECK_ERROR(false);
        {
            s_vpi_value value{};
            value.format = vpiRealVal;
            value.value.real = 4.0;
            vpi_put_value(find("t.u_po.r"), &value, nullptr, vpiNoDelay);
            TEST_CHECK_ERROR(false);
        }
        accept("t.u_po.f", 0x55, vpiForceFlag);
        accept("t.u_cc.frc", 0x55, vpiForceFlag);
        check("t.u_po.f forced", get("t.u_po.f"), 0x55);
        check("t.u_cc.frc forced", get("t.u_cc.frc"), 0x55);
        const std::vector<uint32_t> now
            = {get("t.u_po.s_comb"), get("t.u_mi.p0.xali"), get("t.fyx0_c"),
               get("t.u_po.f_comb"), get("t.u_cc.frc_c"),   get("t.u_cc.orphan_c")};
        for (size_t i = 0; i < now.size(); ++i) check("held before eval", now[i], s_held[i]);
        TEST_CHECK_EQ(getStr(find("t.u_po.str_comb"), vpiStringVal), s_strComb);
        // Each instance keeps its own
        accept("t.u_mi.if1.s", 0x2a);
        s_held = {get("t.u_mi.if0.b"), get("t.u_mi.if1.b"), get("t.u_mi.p1.uc.cflop")};
    });
    step([] {
        check("t.u_po.s_comb", get("t.u_po.s_comb"), 0x22 ^ 0x5a);
        check("t.u_mi.p0.xali", get("t.u_mi.p0.xali"), 0x3c);
        check("t.u_mi.p1.uc.cflop", get("t.u_mi.p1.uc.cflop"), s_held[2]);
        check("t.fyx0_c", get("t.fyx0_c"), (0x11 ^ 0x55));
        check("t.u_cc.orphan_c", get("t.u_cc.orphan_c"), 0x2a ^ 0x0f);
        check("t.u_po.f_comb", get("t.u_po.f_comb"), 0x55 ^ 0x0f);
        check("t.u_cc.frc_c", get("t.u_cc.frc_c"), 0x55 ^ 0x7f);
        TEST_CHECK_EQ(getStr(find("t.u_po.str_comb"), vpiStringVal),
                      std::string{"longer_than_any_short_string_buffer!"});
        TEST_CHECK_EQ(getStr(find("t.u_po.r_comb"), vpiRealVal), std::to_string(8.0));
        // Released, a flop holds until its next edge, a net follows its driver
        accept("t.u_po.f", 0, vpiReleaseFlag);
        accept("t.u_cc.frc", 0, vpiReleaseFlag);
        check("t.u_po.f released", get("t.u_po.f"), 0x55);
        // A top input read through $root
        in("pre_in", 0x5c);
        in("clk", 1);
    });
    step([] {
        check("t.u_po.f_comb", get("t.u_po.f_comb"), ((0x22 + 1) ^ 0x0f));
        check("t.u_cc.frc", get("t.u_cc.frc"), (get("t.u_cc.keep_frc") + 0x11) & 0x7f);
        check("t.u_mi.observe2", get("t.u_mi.observe2"), s_held[0] ^ s_held[1] ^ 0x2a);
        check("t.u_cc.pre_ic", get("t.u_cc.pre_ic"), 0x5c);
        // Set mid-eval by initial blocks, which read them back
        check("t.u_po.mid_seen", get("t.u_po.mid_seen"), 0x5b);
        check("t.u_po.mc_a", get("t.u_po.mc_a"), 0x01);
        check("t.u_po.mc_b", get("t.u_po.mc_b"), 0x04);
        // A parameter is read-only
        reject("t.u_cb.INTF_QTY", 5);
        // An element of a rebuilt memory
        check("t.u_cc.mem[2]", get(vpi_handle_by_index(find("t.u_cc.mem"), 2)),
              (get("TOP.d") + 2) & 0xff);
        // A member of a rebuilt memory's element
        check("t.hla_c[1].lo", get("t.hla_c[1].lo"), ~get("TOP.d") & 0xf);
        reject("t.hla_c[1].lo", get("t.hla_c[1].lo") ^ 0x5);
        in("clk", 0);
    });
    step([] {
        // Latches -O2 never opens hold what is put, so read alike under any -O
        merge("t.plc_l", 0xa5, 0x03);
        accept("t.plm_l[0]", 0xa5);
        dumpRows();
    });
}

PLI_INT32 startOfSimulation(p_cb_data) {
    printResetValues();
    in("clk", 0);
    in("rst", 1);
    in("rst_n", 0);
    in("set_n", 0);
    in("ld", 1);
    in("en", 0);
    in("never", 0);
    in("sel", 1);
    in("d", 0x21);
    in("in_a", 0x40);
    // Each fires once, for the first eval's settle
    armValueCbs({"t.ch1", "t.fmid_c", "t.sib_b", "t.al_sw", "t.cy0.din", "t.cy0.cy", "t.cy1.cy",
                 "t.ifd.din", "t.ifd.a", "t.ff_q", "t.hl_c.hi", "t.hl_c.lo", "t.hl_c",
                 "t.u_sub.i"});
    script();
    scheduleStep();
    return 0;
}

}  // namespace

// An impure 1, which a cone can't be rebuilt over
extern "C" int dpiOne() { return 1; }

// Called from an initial block: each read is from the same eval, after its input moved
extern "C" void midEvalRead(int src) {
    const uint32_t got = get("t.mid_c");
    std::printf("mid-eval t.mid_c 0x%02x\n", got);
    check("t.mid_c mid-eval", got, (static_cast<uint32_t>(src) + 1) & 0xff);
}

// Called at each rising edge: the cone reads its source as the eval sees it
extern "C" void midEvalProbe() {
    ++s_probes;
    check("t.prb_c mid-eval", get("t.prb_c"), get("t.prb_s") ^ 0x3c);
}

// Called from an initial block: the eval itself consumes the put
extern "C" void midEvalPut(const char* name, int v) { put(name, static_cast<uint32_t>(v)); }

#endif

void startup() {
    s_cb_data cb{};
    cb.reason = cbStartOfSimulation;
    cb.cb_rtn = startOfSimulation;
    vpi_release_handle(vpi_register_cb(&cb));
}

void (*vlog_startup_routines[])() = {startup, nullptr};
