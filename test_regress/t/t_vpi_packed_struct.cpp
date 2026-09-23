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
#endif

#include "vpi_user.h"

#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <iostream>
#include <string>
#include <vector>

// These require the above. Comment prevents clang-format moving them
#include "TestCheck.h"
#include "TestSimulator.h"
#include "TestVpi.h"

int errors = 0;

//======================================================================
// Helpers

static vpiHandle handle(const char* namep) {
    vpiHandle vh = VPI_HANDLE(namep);
    if (!vh) {
        std::cout << "%Error: no handle for " << namep << std::endl;
        ++errors;
    }
    return vh;
}

static vpiHandle relHandle(const char* namep, vpiHandle scope) {
    return vpi_handle_by_name(const_cast<PLI_BYTE8*>(namep), scope);
}

// Verilator also resolves a name relative to a struct handle, IEEE 1800-2023 38.21 only
// defines a scope as the reference object, so other simulators look up the full name
static vpiHandle memberHandle(const char* relp, vpiHandle parent, const char* fullp) {
    if (!TestSimulator::is_verilator()) return handle(fullp);
    vpiHandle vh = relHandle(relp, parent);
    TEST_CHECK_NZ(vh);
    return vh;
}

// Questa does not index a packed array of structs as IEEE 1800-2023 38.19 requires, so other
// simulators look up the full name
static vpiHandle elementHandle(vpiHandle arrh, PLI_INT32 index, const char* fullp) {
    if (!TestSimulator::is_verilator()) return handle(fullp);
    vpiHandle vh = vpi_handle_by_index(arrh, index);
    TEST_CHECK_NZ(vh);
    return vh;
}

// IEEE 1800-2023 37.17 requires a member's vpiName without its struct prefix, Questa includes
// it, e.g. "s.hi"
static std::string memberName(vpiHandle vh) {
    const std::string name = vpi_get_str(vpiName, vh);
    if (TestSimulator::is_verilator()) return name;
    return name.substr(name.rfind('.') + 1);
}

static PLI_INT32 getInt(vpiHandle vh) {
    s_vpi_value v;
    v.format = vpiIntVal;
    vpi_get_value(vh, &v);
    return v.value.integer;
}

static std::string getStr(vpiHandle vh, PLI_INT32 format) {
    s_vpi_value v;
    v.format = format;
    vpi_get_value(vh, &v);
    return v.value.str;
}

static std::vector<PLI_UINT32> getVec(vpiHandle vh) {
    s_vpi_value v;
    v.format = vpiVectorVal;
    vpi_get_value(vh, &v);
    const int words = (vpi_get(vpiSize, vh) + 31) / 32;
    std::vector<PLI_UINT32> out;
    for (int i = 0; i < words; ++i) out.push_back(v.value.vector[i].aval);
    return out;
}

static void putInt(vpiHandle vh, PLI_INT32 val) {
    s_vpi_value v;
    v.format = vpiIntVal;
    v.value.integer = val;
    vpi_put_value(vh, &v, nullptr, vpiNoDelay);
}

static void putHex(vpiHandle vh, const char* strp) {
    s_vpi_value v;
    v.format = vpiHexStrVal;
    v.value.str = const_cast<PLI_BYTE8*>(strp);
    vpi_put_value(vh, &v, nullptr, vpiNoDelay);
}

static void putVec(vpiHandle vh, const std::vector<PLI_UINT32>& words) {
    std::vector<s_vpi_vecval> vec;
    for (const PLI_UINT32 word : words) vec.push_back({word, 0});
    s_vpi_value v;
    v.format = vpiVectorVal;
    v.value.vector = vec.data();
    vpi_put_value(vh, &v, nullptr, vpiNoDelay);
}

static PLI_INT32 rangeBound(PLI_INT32 which, vpiHandle vh) {
    TestVpiHandle bound = vpi_handle(which, vh);
    TEST_CHECK_NZ(bound);
    return bound ? getInt(bound) : -1;
}

static std::vector<std::string> memberNames(vpiHandle vh) {
    std::vector<std::string> names;
    TestVpiHandle iter = vpi_iterate(vpiMember, vh);
    TEST_CHECK_NZ(iter);
    if (!iter) return names;
    while (TestVpiHandle memberh = vpi_scan(iter)) { names.emplace_back(memberName(memberh)); }
    iter.freed();  // IEEE 37.2.2 vpi_scan at end does a vpi_release_handle
    return names;
}

//======================================================================
// Static checks, done once before simulation starts

static void checkHandles() {
    TestVpiHandle sh = handle("s");
    TestVpiHandle hih = handle("s.hi");
    TEST_CHECK_EQ(memberName(hih), "hi");
    TEST_CHECK_CSTR(vpi_get_str(vpiFullName, hih), "t.s.hi");
    // Relative to the struct handle
    TestVpiHandle hi2h = memberHandle("hi", sh, "s.hi");
    // Deep dotted names, through a nested struct and a union
    TestVpiHandle deeph = handle("n.inner.lo");
    TEST_CHECK_CSTR(vpi_get_str(vpiFullName, deeph), "t.n.inner.lo");
    TestVpiHandle uhih = handle("u.s.hi");
    TEST_CHECK_CSTR(vpi_get_str(vpiFullName, uhih), "t.u.s.hi");
    // Packed array of packed structs
    TestVpiHandle ahih = handle("arr[2].hi");
    TEST_CHECK_CSTR(vpi_get_str(vpiFullName, ahih), "t.arr[2].hi");
    // Unpacked array of packed structs
    TestVpiHandle uahih = handle("uarr[1].hi");
    TEST_CHECK_CSTR(vpi_get_str(vpiFullName, uahih), "t.uarr[1].hi");
    // Missing members
    TestVpiHandle nope1 = VPI_HANDLE("s.nope");
    TEST_CHECK_Z(nope1);
    TestVpiHandle nope2 = VPI_HANDLE("s.hi.nope");
    TEST_CHECK_Z(nope2);
}

static void checkProperties() {
    TestVpiHandle sh = handle("s");
    TEST_CHECK_EQ(vpi_get(vpiType, sh), vpiStructVar);
    TEST_CHECK_EQ(vpi_get(vpiPacked, sh), 1);
    TEST_CHECK_EQ(vpi_get(vpiSize, sh), 12);
    // Not defined on struct vars by IEEE 1800-2023 37.17, Verilator provides the packed range
    if (TestSimulator::is_verilator()) {
        TEST_CHECK_EQ(rangeBound(vpiLeftRange, sh), 11);
        TEST_CHECK_EQ(rangeBound(vpiRightRange, sh), 0);
    }
    TEST_CHECK_EQ(vpi_get(vpiSigned, sh), 0);

    TestVpiHandle hih = handle("s.hi");
    TEST_CHECK_EQ(vpi_get(vpiType, hih), vpiLogicVar);
    TEST_CHECK_EQ(vpi_get(vpiSize, hih), 4);
    TEST_CHECK_EQ(rangeBound(vpiLeftRange, hih), 3);
    TEST_CHECK_EQ(rangeBound(vpiRightRange, hih), 0);
    TEST_CHECK_EQ(vpi_get(vpiSigned, hih), 0);

    TestVpiHandle eh = handle("s.e");
    TEST_CHECK_EQ(vpi_get(vpiSize, eh), 2);

    TestVpiHandle loh = handle("s.lo");
    TEST_CHECK_EQ(vpi_get(vpiSize, loh), 6);
    TEST_CHECK_EQ(vpi_get(vpiSigned, loh), 1);

    TestVpiHandle uh = handle("u");
    TEST_CHECK_EQ(vpi_get(vpiType, uh), vpiUnionVar);
    TEST_CHECK_EQ(vpi_get(vpiPacked, uh), 1);
    TEST_CHECK_EQ(vpi_get(vpiSize, uh), 12);
    TestVpiHandle ush = handle("u.s");
    TEST_CHECK_EQ(vpi_get(vpiType, ush), vpiStructVar);

    TestVpiHandle innerh = handle("n.inner");
    TEST_CHECK_EQ(vpi_get(vpiType, innerh), vpiStructVar);
    TEST_CHECK_EQ(vpi_get(vpiSize, innerh), 12);
    TestVpiHandle pah = handle("n.pa");
    TEST_CHECK_EQ(vpi_get(vpiType, pah), vpiLogicVar);
    TEST_CHECK_EQ(vpi_get(vpiSize, pah), 8);
    TEST_CHECK_EQ(rangeBound(vpiLeftRange, pah), 3);
    TEST_CHECK_EQ(rangeBound(vpiRightRange, pah), 0);

    TestVpiHandle wh = handle("w");
    TEST_CHECK_EQ(vpi_get(vpiSize, wh), 100);
    TestVpiHandle wideh = handle("w.wide");
    TEST_CHECK_EQ(vpi_get(vpiSize, wideh), 40);
    TEST_CHECK_EQ(rangeBound(vpiLeftRange, wideh), 39);

    // A packed array of structs is not itself a struct, an element is. IEEE 1800-2023 37.18
    // requires vpiPackedArrayVar, Verilator does not yet support it
    TestVpiHandle arrh = handle("arr");
    TEST_CHECK_EQ(vpi_get(vpiType, arrh),
                  TestSimulator::is_verilator() ? vpiReg : vpiPackedArrayVar);
    TestVpiHandle arr2h = elementHandle(arrh, 2, "arr[2]");
    TEST_CHECK_EQ(vpi_get(vpiType, arr2h), vpiStructVar);
    TEST_CHECK_EQ(vpi_get(vpiSize, arr2h), 12);

    TestVpiHandle uarrh = handle("uarr");
    TEST_CHECK_EQ(vpi_get(vpiType, uarrh), vpiRegArray);
    TestVpiHandle uarr1h = vpi_handle_by_index(uarrh, 1);
    TEST_CHECK_NZ(uarr1h);
    TEST_CHECK_EQ(vpi_get(vpiType, uarr1h), vpiStructVar);

    // vpiPacked is only supported on struct/union variables. IEEE 1800-2023 38.6 does not
    // define the result elsewhere, Verilator flags an error
    if (!TestSimulator::is_verilator()) return;
    TestVpiHandle pvech = handle("pvec");
    TEST_CHECK_EQ(vpi_get(vpiPacked, pvech), vpiUndefined);
    TEST_CHECK_ERROR(1);
    TestVpiHandle modh = relHandle("t", nullptr);
    TEST_CHECK_NZ(modh);
    TEST_CHECK_EQ(vpi_get(vpiPacked, modh), vpiUndefined);
    TEST_CHECK_ERROR(1);
}

static void checkIteration() {
    using Names = std::vector<std::string>;
    TestVpiHandle sh = handle("s");
    TEST_CHECK_EQ(memberNames(sh) == (Names{"hi", "e", "lo"}), true);
    TestVpiHandle nh = handle("n");
    TEST_CHECK_EQ(memberNames(nh) == (Names{"tag", "inner", "pa"}), true);
    TestVpiHandle innerh = handle("n.inner");
    TEST_CHECK_EQ(memberNames(innerh) == (Names{"hi", "e", "lo"}), true);
    TestVpiHandle wh = handle("w");
    TEST_CHECK_EQ(memberNames(wh) == (Names{"top", "wide", "mid", "b8", "low"}), true);
    TestVpiHandle uh = handle("u");
    TEST_CHECK_EQ(memberNames(uh).size(), 2);

    // Members of an indexed element carry the index in their full name
    TestVpiHandle arrh = handle("arr");
    TestVpiHandle arr2h = elementHandle(arrh, 2, "arr[2]");
    TestVpiHandle iter = vpi_iterate(vpiMember, arr2h);
    TEST_CHECK_NZ(iter);
    if (iter) {
        TestVpiHandle firsth = vpi_scan(iter);
        TEST_CHECK_CSTR(vpi_get_str(vpiFullName, firsth), "t.arr[2].hi");
        iter.release();
    }

    // Not selecting a whole struct, IEEE 1800-2023 37.26 only defines vpiMember on struct/union
    // variables. Questa instead iterates the members of every element of a packed array
    if (TestSimulator::is_verilator()) {
        TestVpiHandle arrIter = vpi_iterate(vpiMember, arrh);
        TEST_CHECK_Z(arrIter);
    }
    TestVpiHandle hih = handle("s.hi");
    TestVpiHandle hiIter = vpi_iterate(vpiMember, hih);
    TEST_CHECK_Z(hiIter);
}

static void checkStruct() {
    TestVpiHandle sh = handle("s");
    TestVpiHandle hih = handle("s.hi");
    TestVpiHandle eh = handle("s.e");
    TestVpiHandle loh = handle("s.lo");

    putInt(sh, 0x5a5);
    TEST_CHECK_HEX_EQ(getInt(hih), 0x5);
    TEST_CHECK_HEX_EQ(getInt(eh), 0x2);
    TEST_CHECK_HEX_EQ(getInt(loh), 0x25);
    TEST_CHECK_EQ(getStr(eh, vpiBinStrVal), "10");
    TEST_CHECK_EQ(getStr(loh, vpiHexStrVal), "25");

    // Writing a member leaves its siblings alone
    putInt(eh, 0x1);
    TEST_CHECK_HEX_EQ(getInt(sh), 0x565);
    putHex(hih, "c");
    TEST_CHECK_EQ(getStr(sh, vpiHexStrVal), "c65");
    TEST_CHECK_EQ(getStr(sh, vpiBinStrVal), "110001100101");
}

static void checkUnion() {
    TestVpiHandle uh = handle("u");
    TestVpiHandle rawh = handle("u.raw");
    putInt(rawh, 0xabc);
    TestVpiHandle hih = handle("u.s.hi");
    TestVpiHandle eh = handle("u.s.e");
    TestVpiHandle loh = handle("u.s.lo");
    TEST_CHECK_HEX_EQ(getInt(hih), 0xa);
    TEST_CHECK_HEX_EQ(getInt(eh), 0x2);
    TEST_CHECK_HEX_EQ(getInt(loh), 0x3c);
    putInt(loh, 0x1);
    TEST_CHECK_HEX_EQ(getInt(uh), 0xa81);
    TEST_CHECK_HEX_EQ(getInt(rawh), 0xa81);
}

static void checkNested() {
    TestVpiHandle nh = handle("n");
    TestVpiHandle innerh = memberHandle("inner", nh, "n.inner");
    TestVpiHandle loh = memberHandle("lo", innerh, "n.inner.lo");
    putInt(loh, 0x3f);
    TEST_CHECK_HEX_EQ(getInt(nh), 0x3f00);
    TestVpiHandle tagh = handle("n.tag");
    putInt(tagh, 0x9);
    TEST_CHECK_HEX_EQ(getInt(nh), 0x903f00);
    TEST_CHECK_EQ(getStr(innerh, vpiHexStrVal), "03f");

    // Packed array member, and indexing into it
    TestVpiHandle pah = handle("n.pa");
    putHex(pah, "a5");
    TEST_CHECK_HEX_EQ(getInt(nh), 0x903fa5);
    TestVpiHandle pa1h = vpi_handle_by_index(pah, 1);
    TEST_CHECK_NZ(pa1h);
    TEST_CHECK_HEX_EQ(getInt(pa1h), 0x1);
    TestVpiHandle pa3h = vpi_handle_by_index(pah, 3);
    TEST_CHECK_HEX_EQ(getInt(pa3h), 0x2);
    TestVpiHandle pa0h = vpi_handle_by_index(pah, 0);
    putInt(pa0h, 0x2);
    TEST_CHECK_HEX_EQ(getInt(nh), 0x903fa6);
    TEST_CHECK_EQ(getStr(pa0h, vpiBinStrVal), "10");
}

static void checkWide() {
    TestVpiHandle wh = handle("w");
    TestVpiHandle toph = handle("w.top");
    TestVpiHandle wideh = handle("w.wide");
    TestVpiHandle midh = handle("w.mid");
    TestVpiHandle b8h = handle("w.b8");
    TestVpiHandle lowh = handle("w.low");

    // Straddles the 32-bit word boundary
    putHex(midh, "abcde");
    TEST_CHECK_EQ(getVec(wh) == (std::vector<PLI_UINT32>{0xe0000000, 0x0000abcd, 0, 0}), true);
    TEST_CHECK_HEX_EQ(getInt(midh), 0xabcde);
    // Spans three words
    putVec(wideh, {0x89abcdef, 0x67});
    TEST_CHECK_EQ(getVec(wh) == (std::vector<PLI_UINT32>{0xe0000000, 0xcdefabcd, 0x006789ab, 0}),
                  true);
    TEST_CHECK_EQ(getVec(wideh) == (std::vector<PLI_UINT32>{0x89abcdef, 0x67}), true);
    TEST_CHECK_EQ(getStr(wideh, vpiHexStrVal), "6789abcdef");
    putInt(b8h, 0xff);
    putInt(toph, 0xfff);
    TEST_CHECK_EQ(getVec(wh) == (std::vector<PLI_UINT32>{0xeff00000, 0xcdefabcd, 0xff6789ab, 0xf}),
                  true);
    TEST_CHECK_EQ(getStr(midh, vpiHexStrVal), "abcde");
    TEST_CHECK_HEX_EQ(getInt(lowh), 0);
}

static void checkArrays() {
    TestVpiHandle arrh = handle("arr");
    TestVpiHandle hih = handle("arr[2].hi");
    putInt(hih, 0xc);
    TEST_CHECK_EQ(getVec(arrh) == (std::vector<PLI_UINT32>{0, 0xc}), true);
    // Index then member, relative to the element handle
    TestVpiHandle arr1h = elementHandle(arrh, 1, "arr[1]");
    TestVpiHandle loh = memberHandle("lo", arr1h, "arr[1].lo");
    putInt(loh, 0x2a);
    TEST_CHECK_EQ(getVec(arrh) == (std::vector<PLI_UINT32>{0x2a000, 0xc}), true);
    TestVpiHandle arr3hih = handle("arr[3].hi");
    TEST_CHECK_HEX_EQ(getInt(arr3hih), 0);
    TEST_CHECK_HEX_EQ(getInt(hih), 0xc);

    TestVpiHandle uarrh = handle("uarr");
    TestVpiHandle ueh = handle("uarr[1].e");
    putInt(ueh, 0x3);
    TestVpiHandle uarr0h = vpi_handle_by_index(uarrh, 0);
    TestVpiHandle uarr1h = vpi_handle_by_index(uarrh, 1);
    TEST_CHECK_HEX_EQ(getInt(uarr0h), 0);
    TEST_CHECK_HEX_EQ(getInt(uarr1h), 0x0c0);
}

static void checkForceable() {
    // Only Verilator needs the forceable metacomment
    if (!TestSimulator::is_verilator()) return;
    // Unsupported, must error rather than bypass the force control signals
    TestVpiHandle hih = VPI_HANDLE("fs.hi");
    TEST_CHECK_Z(hih);
    TEST_CHECK_ERROR(1);
    TestVpiHandle fsh = handle("fs");
    TestVpiHandle iter = vpi_iterate(vpiMember, fsh);
    TEST_CHECK_Z(iter);
    TEST_CHECK_ERROR(1);
}

//======================================================================
// Value change callbacks on members fire on their own change only

struct CbInfo final {
    explicit CbInfo(const char* namep)
        : m_namep{namep} {}
    const char* m_namep;
    int m_count = 0;
    PLI_INT32 m_lastValue = -1;
    TestVpiHandle m_cbh;
};

// The last is not a struct member, but a multi-bit select that must behave the same
static CbInfo s_cbs[]
    = {CbInfo{"s.hi"}, CbInfo{"w.wide"}, CbInfo{"w.mid"}, CbInfo{"arr[2].e"}, CbInfo{"pvec[3]"}};

static int valueCb(p_cb_data cb_data) {
    CbInfo* const infop = reinterpret_cast<CbInfo*>(cb_data->user_data);
    ++infop->m_count;
    infop->m_lastValue = cb_data->value->value.integer;
    TEST_VERBOSE_PRINTF("- cbValueChange %s = 0x%x\n", infop->m_namep, infop->m_lastValue);
    return 0;
}

static void registerCbs() {
    for (CbInfo& info : s_cbs) {
        TestVpiHandle vh = handle(info.m_namep);
        s_vpi_time t;
        t.type = vpiSuppressTime;
        s_vpi_value v;
        v.format = vpiIntVal;
        t_cb_data cb_data;
        bzero(&cb_data, sizeof(cb_data));
        cb_data.reason = cbValueChange;
        cb_data.cb_rtn = valueCb;
        cb_data.obj = vh;
        cb_data.time = &t;
        cb_data.value = &v;
        cb_data.user_data = reinterpret_cast<PLI_BYTE8*>(&info);
        info.m_cbh = vpi_register_cb(&cb_data);
        TEST_CHECK_NZ(info.m_cbh);
        if (!info.m_cbh) _test_check_error();
    }
}

static void checkCbs() {
    // See t_vpi_packed_struct.v: each watched member changes once, among sibling changes
    TEST_CHECK_EQ(s_cbs[0].m_count, 1);
    TEST_CHECK_HEX_EQ(s_cbs[0].m_lastValue, 0x9);
    TEST_CHECK_EQ(s_cbs[1].m_count, 1);
    TEST_CHECK_HEX_EQ(s_cbs[1].m_lastValue, 0);
    TEST_CHECK_EQ(s_cbs[2].m_count, 1);
    TEST_CHECK_HEX_EQ(s_cbs[2].m_lastValue, 0x1);
    TEST_CHECK_EQ(s_cbs[3].m_count, 1);
    TEST_CHECK_HEX_EQ(s_cbs[3].m_lastValue, 0x1);
    TEST_CHECK_EQ(s_cbs[4].m_count, 1);
    TEST_CHECK_HEX_EQ(s_cbs[4].m_lastValue, 0x2);
    for (CbInfo& info : s_cbs) {
        vpi_remove_cb(info.m_cbh);
        info.m_cbh.freed();
    }
}

//======================================================================
// Entry points, called from t_vpi_packed_struct.v

extern "C" int mon_check() {
#ifdef VERILATOR
    Verilated::fatalOnVpiError(false);  // checkForceable expects errors
#endif
    checkHandles();
    checkProperties();
    checkIteration();
    checkStruct();
    checkUnion();
    checkNested();
    checkWide();
    checkArrays();
    checkForceable();
    registerCbs();
    return errors;
}

extern "C" int mon_check_cbs() {
    checkCbs();
    return errors;
}

#ifdef IS_VPI
static int mon_check_vpi(PLI_BYTE8*) {
    TestVpiHandle href = vpi_handle(vpiSysTfCall, 0);
    s_vpi_value vpi_value;
    vpi_value.format = vpiIntVal;
    vpi_value.value.integer = mon_check();
    vpi_put_value(href, &vpi_value, NULL, vpiNoDelay);
    return 0;
}

static int mon_check_cbs_vpi(PLI_BYTE8*) {
    TestVpiHandle href = vpi_handle(vpiSysTfCall, 0);
    s_vpi_value vpi_value;
    vpi_value.format = vpiIntVal;
    vpi_value.value.integer = mon_check_cbs();
    vpi_put_value(href, &vpi_value, NULL, vpiNoDelay);
    return 0;
}

static s_vpi_systf_data vpi_systf_data[]
    = {{vpiSysFunc, vpiIntFunc, (PLI_BYTE8*)"$mon_check", mon_check_vpi, 0, 0, 0},
       {vpiSysFunc, vpiIntFunc, (PLI_BYTE8*)"$mon_check_cbs", mon_check_cbs_vpi, 0, 0, 0},
       {0, 0, 0, 0, 0, 0, 0}};

// cver entry
extern "C" void vpi_compat_bootstrap(void) {
    for (p_vpi_systf_data systfp = vpi_systf_data; systfp->type; ++systfp) {
        vpi_register_systf(systfp);
    }
}

// icarus entry
void (*vlog_startup_routines[])() = {vpi_compat_bootstrap, 0};
#endif
