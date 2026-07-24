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

#include "Vt_vpi_lazy_public_rw_multiinst.h"
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

    const std::unique_ptr<Vt_vpi_lazy_public_rw_multiinst> topp{
        new Vt_vpi_lazy_public_rw_multiinst{contextp.get(), ""}};

    const auto cycle = [&]() {
        topp->clk = 0;
        topp->eval();
        topp->clk = 1;
        topp->eval();
        VerilatedVpi::callValueCbs();
    };

    topp->rst = 1;
    topp->clk = 0;
    topp->eval();
    cycle();
    topp->rst = 0;

    vpiHandle ctrh = mustFind("t.ctr");
    vpiHandle aVal = mustFind("t.if_a.val");
    vpiHandle bVal = mustFind("t.if_b.val");
    vpiHandle cVal = mustFind("t.if_c.val");
    vpiHandle aDer = mustFind("t.if_a.derived");
    vpiHandle bDer = mustFind("t.if_b.derived");
    vpiHandle cDer = mustFind("t.if_c.derived");
    if (errors) return 10;

    // Each instance must reconstruct/retain to ITS OWN driver, not a value
    // shared from the first instance (the multi-instance miscompile).
    for (int i = 0; i < 4; ++i) {
        cycle();
        const int ctr = readInt(ctrh);
        checkInt("t.if_a.val", aVal, (ctr + 0x1) & 0x7f);
        checkInt("t.if_b.val", bVal, (ctr ^ 0x2a) & 0x7f);
        checkInt("t.if_c.val", cVal, 0x55);
        checkInt("t.if_a.derived", aDer, (((ctr + 0x1) & 0x7f) + 0x1) & 0x7f);
        checkInt("t.if_b.derived", bDer, (((ctr ^ 0x2a) & 0x7f) + 0x1) & 0x7f);
        checkInt("t.if_c.derived", cDer, 0x56);
    }

    topp->final();
    if (errors) {
        std::printf("%%Error: %0d failures\n", errors);
        return 1;
    }
    std::printf("*-* All Finished *-*\n");
    return 0;
}
