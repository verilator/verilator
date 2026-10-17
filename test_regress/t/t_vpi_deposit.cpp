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

#include "TestVpi.h"
#include "vpi_user.h"

extern "C" void vpi_deposit(const char* path, int value) {
    TestVpiHandle const handle = vpi_handle_by_name(const_cast<PLI_BYTE8*>(path), nullptr);
    if (!handle) return;
    s_vpi_value vpiValue{};
    vpiValue.format = vpiIntVal;
    vpiValue.value.integer = value;
    vpi_put_value(handle, &vpiValue, nullptr, vpiNoDelay);
}

extern "C" void vpi_force(const char* path, int value) {
    TestVpiHandle const handle = vpi_handle_by_name(const_cast<PLI_BYTE8*>(path), nullptr);
    if (!handle) return;
    s_vpi_value vpiValue{};
    vpiValue.format = vpiIntVal;
    vpiValue.value.integer = value;
    vpi_put_value(handle, &vpiValue, nullptr, vpiForceFlag);
}
