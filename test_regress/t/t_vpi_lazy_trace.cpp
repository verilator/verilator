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

#include <string>

namespace {

int errors = 0;

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

PLI_INT32 checkTrace(PLI_BYTE8*) {
    const vpiHandle keeph = findHandle("t.keep");
    const vpiHandle cmbh = findHandle("t.cmb");
    const vpiHandle alias1h = findHandle("t.alias1");
    TEST_CHECK_NZ_LABEL("t.keep", keeph);
    TEST_CHECK_NZ_LABEL("t.cmb", cmbh);
    TEST_CHECK_NZ_LABEL("t.alias1", alias1h);
    if (errors) return 1;

    const int keep = readInt(keeph);
    const int cmb = readInt(cmbh);
    const int alias1 = readInt(alias1h);
    TEST_CHECK_EQ_LABEL("t.keep", keep, 0x2d);
    TEST_CHECK_EQ_LABEL("t.cmb", cmb, 0x2e);
    TEST_CHECK_EQ_LABEL("t.alias1", alias1, 0x2d);
    return errors ? 1 : 0;
}

PLI_INT32 checkTraceVpi(PLI_BYTE8*) {
    s_vpi_value value{};
    value.format = vpiIntVal;
    value.value.integer = checkTrace(nullptr);
    vpi_put_value(vpi_handle(vpiSysTfCall, nullptr), &value, nullptr, vpiNoDelay);
    return 0;
}

}  // namespace

extern "C" int vpi_lazy_trace_check() { return checkTrace(nullptr); }

static s_vpi_systf_data vpiSystfData[]
    = {{vpiSysFunc, vpiIntFunc, const_cast<PLI_BYTE8*>("$vpi_lazy_trace_check"), checkTraceVpi, 0,
        0, 0},
       {0, 0, 0, 0, 0, 0, 0}};

void vpi_compat_bootstrap() {
    for (p_vpi_systf_data systfp = &vpiSystfData[0]; systfp->type; ++systfp) {
        vpi_register_systf(systfp);
    }
}

void (*vlog_startup_routines[])() = {vpi_compat_bootstrap, 0};
