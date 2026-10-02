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

#include <cstdio>
#include <string>

int errors = 0;

namespace {

const char* const s_dynNames[] = {"q", "da", "aa", "c", "carr", "mb", "sem", "ev", "st.q"};

vpiHandle byName(const std::string& name) {
    return vpi_handle_by_name(const_cast<PLI_BYTE8*>(("t." + name).c_str()), nullptr);
}

bool isPackedVector(vpiHandle handle) {
    switch (vpi_get(vpiType, handle)) {
    case vpiReg:
    case vpiNet:
    case vpiBitVar:
    case vpiRegBit:
    case vpiNetBit: return true;
    default: return false;
    }
}

// Errors are allowed; only the SV-side integrity checks judge the outcome
void pokeAndPeek(vpiHandle handle) {
    PLI_BYTE8 str[] = "ffffffffffffffffffffffffffffffffffffffff";
    s_vpi_vecval vec[8] = {};
    for (const PLI_INT32 format :
         {vpiIntVal, vpiVectorVal, vpiStringVal, vpiBinStrVal, vpiHexStrVal}) {
        s_vpi_value v{};
        v.format = format;
        v.value.integer = -1;
        if (format == vpiVectorVal) v.value.vector = vec;
        if (format != vpiIntVal && format != vpiVectorVal) v.value.str = str;
        vpi_put_value(handle, &v, nullptr, vpiNoDelay);
        vpi_chk_error(nullptr);
        v = {};
        v.format = format;
        vpi_get_value(handle, &v);
        vpi_chk_error(nullptr);
    }
}

PLI_INT32 afterDelayCb(s_cb_data*) {
    for (const char* const name : s_dynNames) {
        TestVpiHandle handle = byName(name);
        vpi_chk_error(nullptr);
        if (!handle) continue;
        TEST_CHECK_EQ_LABEL(name, isPackedVector(handle), false);
        pokeAndPeek(handle);
    }
    TestVpiHandle st = byName("st");
    vpi_chk_error(nullptr);
    if (st) pokeAndPeek(st);
    for (const char* const name : {"str", "lg", "st.a"}) {
        TestVpiHandle handle = byName(name);
        TEST_CHECK_NZ_LABEL(name, handle);
    }
    if (errors) vpi_control(vpiStop, 1);
    return 0;
}

PLI_INT32 startOfSimCb(s_cb_data*) {
    s_vpi_time time = {vpiSimTime, 0, 5, 0};
    s_cb_data cb_data{};
    cb_data.reason = cbAfterDelay;
    cb_data.cb_rtn = afterDelayCb;
    cb_data.time = &time;
    TestVpiHandle handle = vpi_register_cb(&cb_data);
    TEST_CHECK_NZ(handle);
    return 0;
}

void bootstrap() {
    s_cb_data cb_data{};
    cb_data.reason = cbStartOfSimulation;
    cb_data.cb_rtn = startOfSimCb;
    TestVpiHandle handle = vpi_register_cb(&cb_data);
    TEST_CHECK_NZ(handle);
}

}  // namespace

void (*vlog_startup_routines[])() = {bootstrap, 0};
