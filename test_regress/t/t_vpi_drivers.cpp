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

#ifdef VERILATOR
#include "verilated.h"
#include "verilated_vpi.h"
#endif

#include "TestCheck.h"
#include "TestSimulator.h"
#include "TestVpi.h"
#include "svdpi.h"
#include "vpi_user.h"

#include <algorithm>
#include <cstdint>
#include <cstdio>
#include <functional>
#include <initializer_list>
#include <string>
#include <utility>
#include <vector>

int errors = 0;
extern "C" int t_xq();

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
    // Others reject a null time even for a zero-delay inertial put
    s_vpi_time time{vpiSimTime, 0, 0, 0};
    vpi_put_value(handle, &value, &time, flags);
}
void put(const std::string& name, uint32_t v, PLI_INT32 flags = vpiNoDelay) {
    put(find(name), v, flags);
}

// A top-level port, which Verilator alone roots at TOP
std::string port(const char* name) {
    return std::string{TestSimulator::is_verilator() ? "TOP." : "t."} + name;
}
void in(const char* name, uint32_t v) { put(port(name), v); }

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
        return 0;
    }
    if (!errors) std::printf("*-* All Finished *-*\n");
    vpi_control(vpiFinish, 0);
    return 0;
}

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

using Words = std::vector<uint32_t>;

Words getVec(const std::string& name) {
    const vpiHandle handle = find(name);
    s_vpi_value value{};
    value.format = vpiVectorVal;
    vpi_get_value(handle, &value);
    Words words;
    for (int i = 0; i < (vpi_get(vpiSize, handle) + 31) / 32; ++i) {
        TEST_CHECK_EQ_LABEL(name, value.value.vector[i].bval, 0);
        words.push_back(value.value.vector[i].aval);
    }
    return words;
}

void putVec(const std::string& name, const Words& words) {
    std::vector<s_vpi_vecval> vec;
    for (const uint32_t word : words) vec.push_back({word, 0});
    s_vpi_value value{};
    value.format = vpiVectorVal;
    value.value.vector = vec.data();
    s_vpi_time time{vpiSimTime, 0, 0, 0};
    vpi_put_value(find(name), &value, &time, vpiNoDelay);
    TEST_CHECK_ERROR(false);
}

void checkVec(const std::string& label, const Words& got, const Words& exp) {
    TEST_CHECK_EQ_LABEL(label, got.size(), exp.size());
    for (size_t i = 0; i < std::min(got.size(), exp.size()); ++i)
        check(label + " word " + std::to_string(i), got[i], exp[i]);
}

// A concatenation of {value, width} parts, most significant first, as in the RTL
Words cat(std::initializer_list<std::pair<uint32_t, int>> parts) {
    int width = 0;
    for (const auto& part : parts) width += part.second;
    Words words((width + 31) / 32, 0);
    int lsb = width;
    for (const auto& part : parts) {
        lsb -= part.second;
        for (int bit = 0; bit < part.second; ++bit)
            if (part.first >> bit & 1) words[(lsb + bit) / 32] |= 1U << ((lsb + bit) % 32);
    }
    return words;
}

void putVecFlipped(const std::string& name) {
    const int size = vpi_get(vpiSize, find(name));
    Words flipped = getVec(name);
    for (uint32_t& word : flipped) word = ~word;
    if (size % 32) flipped.back() &= (1U << (size % 32)) - 1;
    putVec(name, flipped);
    checkVec(name, getVec(name), flipped);
}

void putArray(const std::string& name, int index, const PLI_INT32* valsp, int num) {
    s_vpi_arrayvalue value{};
    value.format = vpiIntVal;
    value.value.integers = const_cast<PLI_INT32*>(valsp);
    PLI_INT32 indexes[1] = {index};
    vpi_put_value_array(find(name), &value, indexes, num);
    TEST_CHECK_ERROR(false);
}

// Every module-level signal row, as a handle, in hierarchy order. A forced signal's force
// controls and a static function's locals are VPI-visible, but are not module signals.
void walk(vpiHandle scopep, const std::function<void(vpiHandle)>& fn) {
    for (const PLI_INT32 type : {vpiReg, vpiNet}) {
        TestVpiHandle iterp = vpi_iterate(type, scopep);
        if (!iterp) continue;
        while (vpiHandle handle = vpi_scan(iterp)) {
            const std::string name = vpi_get_str(vpiFullName, handle);
            if (name.find("__Vforce") != std::string::npos) continue;
            if (name.find("__Vstatic__") != std::string::npos) continue;
            fn(handle);
        }
        iterp.freed();
    }
    for (const PLI_INT32 type : {vpiModule, vpiInterface}) {
        TestVpiHandle iterp = vpi_iterate(type, scopep);
        if (!iterp) continue;
        while (vpiHandle subp = vpi_scan(iterp)) walk(subp, fn);
        iterp.freed();
    }
}

// A compiler temporary has no RTL name, so must not be VPI-visible
void checkNoTemporaries() {
    walk(nullptr, [](vpiHandle handle) {
        const std::string name = vpi_get_str(vpiFullName, handle);
        TEST_CHECK_EQ_LABEL(name, name.find("__"), std::string::npos);
    });
}

struct ValueCb final {
    std::string name;
    vpiHandle cb;
    int count;
};
std::vector<ValueCb> s_valueCbs;

PLI_INT32 valueCb(p_cb_data cbp) {
    ValueCb* const vcp = reinterpret_cast<ValueCb*>(cbp->user_data);
    ++vcp->count;
    return 0;
}

void armValueCbs(std::initializer_list<const char*> names) {
    for (const char* name : names) s_valueCbs.push_back({name, nullptr, 0});
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

void checkValueCbs() {
    for (ValueCb& vc : s_valueCbs) {
        TEST_CHECK_EQ_LABEL(vc.name, vc.count <= 1, true);
        vpi_remove_cb(vc.cb);
    }
    s_valueCbs.clear();
}

// Values held across steps
uint32_t s_mix, s_dWas, s_ohHeld, s_st, s_g0, s_driven;
std::vector<uint32_t> s_held;
std::string s_strComb;

// The encoder drives all of level 0 and one bit per segment of each level above
constexpr uint32_t ohMask = 0x15f;
uint32_t ohDriven(uint32_t d) {
    const uint32_t i = d & 0xf;
    return i | (i & 3 ? 1U : 0U) << 4 | (i & 0xc ? 1U : 0U) << 6 | (i ? 1U : 0U) << 8;
}

// --binary's main, unlike other simulators, lands an inertial put only when asked
void landInertial() {
#ifdef VERILATOR
    VerilatedVpi::doInertialPuts();
#endif
}

void script() {
    // After the first eval, which fired each callback at most once for its settle
    step([] {
        checkValueCbs();
        in("rst", 0);
        in("rst_n", 1);
        in("clk", 1);
    });
    step([] { in("clk", 0); });
    step([] { in("clk", 1); });
    step([] { in("clk", 0); });
    step([] {
        // Each reads its own instance's flop, read before the flop's own row
        for (const char* inst : {"0", "1"}) {
            const std::string fy = std::string{"t.fy"} + inst;
            check("t.fyx" + std::string{inst} + "_c", get("t.fyx" + std::string{inst} + "_c"),
                  0xff & ((get(fy + ".r") + 1) ^ 0x55));
        }
        // Comb logic over a port expression and over a function's temporaries
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
        // Wide values read whole across word boundaries
        const uint32_t d = 0x21;
        const uint32_t ina = 0x40;
        const uint32_t x = d ^ ina;
        checkVec("t.w33_c", getVec("t.w33_c"), cat({{d & 1, 1}, {x, 8}, {x, 8}, {x, 8}, {x, 8}}));
        checkVec(
            "t.w65_c", getVec("t.w65_c"),
            cat({{d, 8}, {x, 8}, {x, 8}, {x, 8}, {d & 1, 1}, {x, 8}, {x, 8}, {x, 8}, {x, 8}}));
        checkVec("t.w95_c", getVec("t.w95_c"),
                 cat({{x & 0x3f, 6},
                      {x, 8},
                      {x, 8},
                      {x, 8},
                      {~d & 0xff, 8},
                      {~x & 0xff, 8},
                      {~x & 0xff, 8},
                      {~x & 0xff, 8},
                      {~d & 1, 1},
                      {~x & 0xff, 8},
                      {~x & 0xff, 8},
                      {~x & 0xff, 8},
                      {~x & 0xff, 8}}));
        const Words wm33 = cat(
            {{static_cast<uint32_t>(__builtin_parity(d)), 1}, {d, 8}, {d, 8}, {d, 8}, {d, 8}});
        const Words wm65 = cat({{d, 8},
                                {d, 8},
                                {d, 8},
                                {d & 0x1f, 5},
                                {ina, 8},
                                {d & 0xf, 4},
                                {ina, 8},
                                {ina, 8},
                                {ina, 8}});
        const Words wm95 = cat({{ina, 8},
                                {ina, 8},
                                {ina, 8},
                                {d & 7, 3},
                                {ina, 8},
                                {d & 0xf, 4},
                                {d, 8},
                                {d, 8},
                                {d, 8},
                                {d, 8},
                                {d, 8},
                                {d, 8},
                                {d, 8}});
        checkVec("t.wm33", getVec("t.wm33"), wm33);
        checkVec("t.wm65", getVec("t.wm65"), wm65);
        checkVec("t.wm95", getVec("t.wm95"), wm95);
        for (const char* name : {"t.wm33", "t.wm65", "t.wm95"}) putVecFlipped(name);
    });
    step([] {
        for (const char* name : {"t.ff_q", "t.arn_q", "t.lat_q", "t.in_a", "t.frc_al", "t.u_ff.q",
                                 "t.bus.q", "t.spl_l"}) {
            accept(name, 0x5a);
        }
        // Each instance as the RTL drives it, beside a comb-driven instance of the same variable
        for (const char* name : {"t.ia.q", "t.mc2.m"}) accept(name, 0x5a);
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
        // The logic reads the put
        check("t.n_ff", get("t.n_ff"), 0x5a);
        check("t.n_mix", get("t.n_mix"), (s_mix & 1) | 0xa4);
        check("t.n_if", get("t.n_if"), 0x5a);
        check("t.n_ia", get("t.n_ia"), 0x5a);
        check("t.n_mc2", get("t.n_mc2"), 0x5a);
        check("t.ia.q edge", get("t.ia.q"), 0x33);
        check("t.ib.q edge", get("t.ib.q"), 0x33);
        // Each alias reports its own metadata, not its source's, and reads its source
        for (const char* name : {"t.al_sw", "t.sib_bt", "t.ch1"}) {
            TEST_CHECK_EQ_LABEL(name, vpi_get(vpiSize, find(name)), 8);
        }
        TEST_CHECK_EQ_LABEL("t.al_sw", vpi_get(vpiSigned, find("t.al_sw")), 1);
        TEST_CHECK_EQ_LABEL("t.sib_bt", vpi_get(vpiType, find("t.sib_bt")), vpiBitVar);
        TEST_CHECK_EQ_LABEL("t.ch1", vpi_get(vpiType, find("t.ch1")), vpiReg);
        TEST_CHECK_EQ_LABEL("t.al_sw", get(vpi_handle(vpiLeftRange, find("t.al_sw"))), 8);
        TEST_CHECK_EQ_LABEL("t.al_sw", get(vpi_handle(vpiRightRange, find("t.al_sw"))), 1);
        check("t.al_sw", get("t.al_sw"), get("t.k_q"));
        check("t.sib_bt", get("t.sib_bt"), get("t.ch1"));
        // Undriven bits no read reaches hold a put
        s_dWas = get(port("d"));
        check("t.oh.v", get("t.oh.v") & ohMask, ohDriven(s_dWas));
        accept("t.oh.v", get("t.oh.v") ^ (0xfff & ~ohMask));
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
        // public_flat_rw takes a put on a comb-driven net until the next eval
        accept("t.u_na.z", 0x5a);
        // Questa reads a put into a driven net back as its driver at once
        if (TestSimulator::is_verilator()) accept("t.u_na.w", 0x5a);
        const uint32_t st = get("t.st");
        accept("t.st", (st & 1) | (0x05 << 1));
        // An inertial put lands after this step's eval
        s_st = get("t.st");
        accept("t.st", s_st ^ 0xff, vpiInertialDelay);
    });
    step([] {
        landInertial();
        check("t.st.cnt inertial", get("t.st.cnt"), (s_st >> 1) ^ 0x7f);
        accept("t.st.cnt", 0x09, vpiInertialDelay);
    });
    step([] {
        landInertial();
        check("t.st.cnt inertial", get("t.st.cnt"), 0x09);
        accept("t.st.cnt", get("t.st.cnt") ^ 0x55);
        {
            // An inertial put in a format that cannot be delayed falls through to the
            // ordinary put
            const uint32_t before = get("t.st");
            s_vpi_value value{};
            value.format = vpiTimeVal;
            vpi_put_value(find("t.st"), &value, nullptr, vpiInertialDelay);
            TEST_CHECK_ERROR(true);
            // Nor can a put be made in a format no signal takes
            vpi_put_value(find("t.st"), &value, nullptr, vpiNoDelay);
            TEST_CHECK_ERROR(true);
            check("t.st bad format", get("t.st"), before);
            putStr("t.st", vpiDecStrVal, "zz");
            TEST_CHECK_ERROR(true);
            check("t.st bad decimal", get("t.st"), before);
        }
        accept("t.pmem[0]", 0x5a);
        accept("t.pmem[2]", 0x5b);
        // Instances of one variable, each driven in part by its own comb logic
        for (const auto& pr : {std::make_pair("t.cp.p", 0x0fU), std::make_pair("t.mc0.m", 0x0fU),
                               std::make_pair("t.mc1.m", 0xf0U)}) {
            accept(pr.first, get(pr.first) ^ (0xffU & ~pr.second));
        }
        // Not every simulator implements vpi_put_value_array; Questa 2025.1 does not
        if (!TestSimulator::is_verilator()) return;
        const PLI_INT32 one[1] = {0x6c};
        putArray("t.pmem", 0, one, 1);
        check("t.pmem[0] array", get("t.pmem[0]"), 0x6c);
        // Wraps from [3] to [0]
        const uint32_t pmem3 = get("t.pmem[3]");
        const PLI_INT32 wrap[2] = {static_cast<PLI_INT32>(pmem3 ^ 0xff), 0x4e};
        putArray("t.pmem", 3, wrap, 2);
        check("t.pmem[3] array wrapped", get("t.pmem[3]"), pmem3 ^ 0xff);
        check("t.pmem[0] array wrapped", get("t.pmem[0]"), 0x4e);
        // An array put into a memory reaches its comb readers only at the next eval
        s_g0 = get("t.gmem[0]");
        const PLI_INT32 flipped[1] = {static_cast<PLI_INT32>(s_g0 ^ 0xff)};
        putArray("t.gmem", 0, flipped, 1);
        check("t.gmem_r before eval", get("t.gmem_r"), s_g0);
    });
    step([] {
        if (TestSimulator::is_verilator())
            check("t.gmem_r after eval", get("t.gmem_r"), s_g0 ^ 0xff);
        const uint32_t d = get(port("d"));
        check("t.ct_c", get("t.ct_c"), d);
        check("t.mc_x", get("t.mc_x"), (((d + 3) & 0xf) << 4) | (d & 0xf));
        // A flop samples comb logic over an impure call
        s_driven = get("t.ret_c");
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
        // A packed member reads as its parent
        check("t.hl_c.hi", get("t.hl_c.hi"), 0x3);
        accept("t.st.cnt", get("t.st.cnt") ^ 0x2a);
        in("clk", 1);
    });
    step([] { in("clk", 0); });
    step([] {
        // A put into a stored source, string and real alike, reaches its readers at the next
        // eval; until then they read as before it
        s_held = {get("t.u_po.s_comb"), get("t.u_mi.p0.xali"), get("t.fyx0_c"),
                  get("t.u_po.f_comb"), get("t.orphan_c")};
        s_strComb = getStr(find("t.u_po.str_comb"), vpiStringVal);
        accept("t.u_po.s", 0x22);
        accept("t.u_mi.p0.uc.cflop", 0x3c);
        accept("t.fy0.r", 0x10);
        accept("t.orphan", 0x2a);
        // Elsewhere still X, as t.u_po.s was never put before
        if (TestSimulator::is_verilator())
            check("t.u_po.xq_c", get("t.u_po.xq_c"), (get("t.u_po.xq") + 1) & 0xff);
        accept("t.u_po.xq", 0x33);
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
        check("t.u_po.f forced", get("t.u_po.f"), 0x55);
        const std::vector<uint32_t> now
            = {get("t.u_po.s_comb"), get("t.u_mi.p0.xali"), get("t.fyx0_c"), get("t.u_po.f_comb"),
               get("t.orphan_c")};
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
        check("t.orphan_c", get("t.orphan_c"), 0x2a ^ 0x0f);
        check("t.u_po.xq_c", get("t.u_po.xq_c"), 0x34);
        svSetScope(svGetScopeFromName("t.u_po"));
        check("t_xq", static_cast<uint32_t>(t_xq()), 0x33);
        check("t.u_po.f_comb", get("t.u_po.f_comb"), 0x55 ^ 0x0f);
        TEST_CHECK_EQ(getStr(find("t.u_po.str_comb"), vpiStringVal),
                      std::string{"longer_than_any_short_string_buffer!"});
        TEST_CHECK_EQ(getStr(find("t.u_po.r_comb"), vpiRealVal), std::to_string(8.0));
        // Released, a flop holds until its next edge
        accept("t.u_po.f", 0, vpiReleaseFlag);
        check("t.u_po.f released", get("t.u_po.f"), 0x55);
        in("clk", 1);
    });
    step([] {
        check("t.u_po.f_comb", get("t.u_po.f_comb"), ((0x22 + 1) ^ 0x0f));
        // Questa reads it as if the put into t.u_mi.if1.s were not made
        if (TestSimulator::is_verilator())
            check("t.u_mi.observe2", get("t.u_mi.observe2"), s_held[0] ^ s_held[1] ^ 0x2a);
        // Set mid-eval by an initial block, which reads it back
        check("t.u_po.mc_a", get("t.u_po.mc_a"), 0x01);
        check("t.u_po.mc_b", get("t.u_po.mc_b"), 0x04);
        // A parameter is read-only
        {
            const uint32_t before = get("t.INTF_QTY");
            put("t.INTF_QTY", 5);
            s_vpi_error_info info{};
            TEST_CHECK_NZ_LABEL("t.INTF_QTY put", vpi_chk_error(&info));
            check("t.INTF_QTY", get("t.INTF_QTY"), before);
        }
        // An element of a comb-driven memory
        const uint32_t d = get(port("d"));
        const uint32_t m1 = ((d >> 4) | ((((d >> 4) ^ get(port("in_a"))) & 0xf) << 4)) & 0xff;
        check("t.mem_chain[2]", get(vpi_handle_by_index(find("t.mem_chain"), 2)), (m1 + 1) & 0xff);
        // A member of a comb-driven memory's element
        check("t.hla_c[1].lo", get("t.hla_c[1].lo"), ~d & 0xf);
        // A member of an unpacked struct holding a put
        const uint32_t fusA = get("t.fus.a");
        accept("t.fus.b", 0xa5);
        check("t.fus.a", get("t.fus.a"), fusA);
        in("clk", 0);
    });
    step([] { checkNoTemporaries(); });
}

PLI_INT32 startOfSimulation(p_cb_data) {
    in("clk", 0);
    in("rst", 1);
    in("rst_n", 0);
    in("en", 0);
    in("never", 0);
    in("sel", 1);
    in("d", 0x21);
    in("in_a", 0x40);
    // Each fires at most once, for the first eval's settle
    armValueCbs({"t.ch1", "t.fmid_c", "t.sib_b", "t.al_sw", "t.ff_q", "t.hl_c.hi", "t.hl_c.lo",
                 "t.hl_c", "t.u_px.i"});
    script();
    scheduleStep();
    return 0;
}
}  // namespace

// An impure 1
extern "C" int dpiOne() { return 1; }

// Called mid-eval: the read sees the stores made before the call
extern "C" void midEvalPeek(const char* name, int want, int mask) {
    check(name, get(name) & static_cast<uint32_t>(mask), static_cast<uint32_t>(want));
}

// Called from an initial block: the eval itself consumes the put
extern "C" void midEvalPut(const char* name, int v) { put(name, static_cast<uint32_t>(v)); }

void startup() {
#ifdef VERILATOR
    Verilated::fatalOnVpiError(false);
#endif
    s_cb_data cb{};
    cb.reason = cbStartOfSimulation;
    cb.cb_rtn = startOfSimulation;
    vpi_release_handle(vpi_register_cb(&cb));
}

void (*vlog_startup_routines[])() = {startup, nullptr};
