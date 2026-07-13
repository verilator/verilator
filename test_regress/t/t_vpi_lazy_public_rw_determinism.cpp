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
// Byte-identical runs (comparison in .py)
//*************************************************************************

#include "verilated.h"
#include "verilated_vpi.h"

#include "Vt_vpi_lazy_public_rw_determinism.h"
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

}  // namespace

int main(int argc, char** argv) {
    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};
    contextp->commandArgs(argc, argv);

    const std::unique_ptr<Vt_vpi_lazy_public_rw_determinism> topp{
        new Vt_vpi_lazy_public_rw_determinism{contextp.get(), ""}};

    topp->clk = 0;
    topp->rst = 1;
    topp->eval();

    // Sanity check
    mustFind("t.keep");
    mustFind("t.cyc_a");
    mustFind("t.cyc_b");
    mustFind("t.ali_a");
    mustFind("t.self_loop");
    mustFind("t.cyc_down");
    mustFind("t.cmb3");
    mustFind("t.cf_ifelse");
    mustFind("t.ps_comb");
    mustFind("t.alias2");
    mustFind("t.u0.s2");
    mustFind("t.u1.s2");
    if (errors) return 10;

    for (int i = 0; i < 8; ++i) {
        topp->clk = 0;
        topp->eval();
        topp->rst = (i == 0) ? 1 : 0;
        topp->clk = 1;
        topp->eval();
    }

    topp->final();
    if (errors) {
        std::printf("%%Error: %0d failures\n", errors);
        return 1;
    }
    std::printf("*-* All Finished *-*\n");
    return 0;
}
