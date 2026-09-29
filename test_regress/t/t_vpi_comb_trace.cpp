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
#include "vpi_user.h"

#include <cstdio>
#include <string>

int errors = 0;

namespace {

vpiHandle findHandle(const char* const name) {
    if (vpiHandle handle = vpi_handle_by_name(const_cast<PLI_BYTE8*>(name), nullptr))
        return handle;
    const std::string rooted = std::string{"top."} + name;
    return vpi_handle_by_name(const_cast<PLI_BYTE8*>(rooted.c_str()), nullptr);
}

int readInt(vpiHandle handle) {
    s_vpi_value value{};
    value.format = vpiIntVal;
    vpi_get_value(handle, &value);
    return value.value.integer;
}

void checkComb() {
    const vpiHandle keeph = findHandle("t.keep");
    const vpiHandle cmbh = findHandle("t.cmb");
    const vpiHandle alias1h = findHandle("t.alias1");
    TEST_CHECK_NZ_LABEL("t.keep", keeph);
    TEST_CHECK_NZ_LABEL("t.cmb", cmbh);
    TEST_CHECK_NZ_LABEL("t.alias1", alias1h);
    if (errors) return;

    TEST_CHECK_EQ_LABEL("t.keep", readInt(keeph), 0x2d);
    TEST_CHECK_EQ_LABEL("t.cmb", readInt(cmbh), 0x2e);
    TEST_CHECK_EQ_LABEL("t.alias1", readInt(alias1h), 0x2d);
}

PLI_INT32 readOnlySynchCb(s_cb_data*) {
    checkComb();
    return 0;
}

PLI_INT32 endOfSimCb(s_cb_data*) {
    if (!errors) std::printf("*-* All Finished *-*\n");
    return 0;
}

PLI_INT32 startOfSimCb(s_cb_data*) {
    s_vpi_time time = {vpiSimTime, 0, 0, 0};
    s_cb_data cb_data{};
    cb_data.reason = cbReadOnlySynch;
    cb_data.cb_rtn = readOnlySynchCb;
    cb_data.time = &time;
    const vpiHandle handle = vpi_register_cb(&cb_data);
    TEST_CHECK_NZ_LABEL("cbReadOnlySynch", handle);
    return 0;
}

void bootstrap() {
    s_cb_data cb_data{};
    cb_data.reason = cbStartOfSimulation;
    cb_data.cb_rtn = startOfSimCb;
    vpi_register_cb(&cb_data);

    cb_data.reason = cbEndOfSimulation;
    cb_data.cb_rtn = endOfSimCb;
    vpi_register_cb(&cb_data);
}

}  // namespace

void (*vlog_startup_routines[])() = {bootstrap, 0};
