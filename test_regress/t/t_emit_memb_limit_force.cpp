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

#include "verilated.h"

#include "TestCheck.h"
#include "TestVpi.h"
#include "vpi_user.h"

namespace {

int errors = 0;

PLI_INT32 getValue(vpiHandle handle) {
    s_vpi_value value{};
    value.format = vpiIntVal;
    vpi_get_value(handle, &value);
    return value.value.integer;
}

void putValue(vpiHandle handle, PLI_INT32 val, PLI_INT32 flags) {
    s_vpi_value value{};
    value.format = vpiIntVal;
    value.value.integer = val;
    vpi_put_value(handle, &value, nullptr, flags);
}

PLI_INT32 start_of_sim(t_cb_data*) {
    TestVpiHandle xv = vpi_handle_by_name(const_cast<PLI_BYTE8*>("t.x.v"), nullptr);
    TEST_CHECK_NZ(xv);
    if (errors) {
        vpi_control(vpiStop);
        return 0;
    }
    putValue(xv, 0x21, vpiNoDelay);
    TEST_CHECK_EQ(getValue(xv), 0x21);
    if (errors) vpi_control(vpiStop);
    return 0;
}

void vpi_compat_bootstrap() {
    s_cb_data cb_data{};
    cb_data.reason = cbStartOfSimulation;
    cb_data.cb_rtn = &start_of_sim;
    TestVpiHandle callback_h = vpi_register_cb(&cb_data);
}

}  // namespace

void (*vlog_startup_routines[])() = {vpi_compat_bootstrap, 0};
