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
#include "verilated_vpi.h"

#include "svdpi.h"

#include VM_PREFIX_INCLUDE

#include <cstdio>
#include <cstring>
#include <memory>

// These require the above. Comment prevents clang-format moving them
#include "TestSimulator.h"
#include "TestVpi.h"

extern "C" int dpic_check_scope() {
    const char* const namep = svGetNameFromScope(svGetScope());
    if (std::strcmp(namep, "top.t.u_sub") == 0) return 0;
    printf("%%Error: DPI scope name %s\n", namep);
    return 1;
}

static int checkValue(const char* namep, int expected) {
    TestVpiHandle handle = vpi_handle_by_name(const_cast<PLI_BYTE8*>(namep), nullptr);
    CHECK_RESULT_NZ(handle);
    s_vpi_value value;
    value.format = vpiIntVal;
    vpi_get_value(handle, &value);
    CHECK_RESULT(value.value.integer, expected);
    return 0;
}

static int checkNames() {
    // The same names as in the non-hierarchical build, without the top module of the library
    if (const int line = checkValue("top.t.u_sub.count", 1)) return line;
    if (const int line = checkValue("top.t.u_sub.u_leaf.last", 2)) return line;
    TestVpiHandle handle
        = vpi_handle_by_name(const_cast<PLI_BYTE8*>("top.t.u_sub.sub.count"), nullptr);
    CHECK_RESULT_Z(handle);
    // The instance is named after itself, not after its module
    TestVpiHandle scope = vpi_handle_by_name(const_cast<PLI_BYTE8*>("top.t.u_sub"), nullptr);
    CHECK_RESULT_NZ(scope);
    CHECK_RESULT_CSTR(vpi_get_str(vpiName, scope), "u_sub");
    return 0;
}

int main(int argc, char** argv) {
    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};
    contextp->commandArgs(argc, argv);
    contextp->fatalOnVpiError(0);
    const std::unique_ptr<VM_PREFIX> topp{new VM_PREFIX{contextp.get(), "top"}};
    topp->eval();
    if (checkNames()) return 1;
    topp->final();
    printf("*-* All Finished *-*\n");
    return 0;
}
