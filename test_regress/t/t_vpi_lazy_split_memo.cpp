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

#include VM_PREFIX_INCLUDE
#include "vpi_user.h"

#include <cstdio>
#include <memory>

namespace {

int errors = 0;

vpiHandle mustFind(const char* name) {
    vpiHandle handle = vpi_handle_by_name((PLI_BYTE8*)name, nullptr);
    if (!handle) {
        std::printf("%%Error: failed to find %s\n", name);
        ++errors;
    }
    return handle;
}

int readInt(vpiHandle handle) {
    s_vpi_value value{};
    value.format = vpiIntVal;
    vpi_get_value(handle, &value);
    return value.value.integer;
}

void checkInt(const char* name, vpiHandle handle, int expected) {
    const int got = readInt(handle);
    if (got != expected) {
        std::printf("%%Error: %s expected %0d, got %0d\n", name, expected, got);
        ++errors;
    }
}

}  // namespace

int main(int argc, char** argv) {
    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};
    contextp->commandArgs(argc, argv);

    const std::unique_ptr<VM_PREFIX> topp{new VM_PREFIX{contextp.get(), ""}};

    topp->clk = 0;
    topp->a = 0x12;
    topp->b = 0x34;
    topp->eval();

    vpiHandle m1h = mustFind("t.m1");
    vpiHandle m4h = mustFind("t.m4");
    if (errors) return 10;

    const auto expect = [](int a, int b) {
        const int m1 = (a ^ 0x5a) & 0xff;
        const int m2 = (m1 + b) & 0xff;
        const int m3 = (m2 ^ 0x3c) & 0xff;
        return (m3 + 0x11) & 0xff;
    };

    // Two reads in one epoch: the second is served from the memo
    checkInt("t.m4 (first read)", m4h, expect(0x12, 0x34));
    checkInt("t.m4 (memoised read)", m4h, expect(0x12, 0x34));
    checkInt("t.m1", m1h, (0x12 ^ 0x5a) & 0xff);

    // A new epoch must recompute
    topp->a = 0x77;
    topp->b = 0x03;
    topp->eval();
    checkInt("t.m4 (after eval)", m4h, expect(0x77, 0x03));
    checkInt("t.m4 (memoised after eval)", m4h, expect(0x77, 0x03));

    topp->clk = 1;
    topp->eval();
    checkInt("t.m4 (after edge)", m4h, expect(0x77, 0x03));

    topp->final();
    if (errors) {
        std::printf("%%Error: %0d failures\n", errors);
        return 1;
    }
    std::printf("*-* All Finished *-*\n");
    return 0;
}
