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

#include "Vt_vpi_lazy_public_rw_chandle.h"
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

    const std::unique_ptr<Vt_vpi_lazy_public_rw_chandle> topp{
        new Vt_vpi_lazy_public_rw_chandle{contextp.get(), ""}};

    const auto cycle = [&]() {
        topp->clk = 0;
        topp->eval();
        topp->clk = 1;
        topp->eval();
    };

    topp->rst = 1;
    topp->clk = 0;
    topp->eval();
    cycle();
    topp->rst = 0;
    for (int i = 0; i < 4; ++i) cycle();

    // Verify chandle survives as VPI entry.
    vpiHandle handleh = mustFind("t.handle");
    if (errors) return 10;

    // Opaque round-trip check (existence matters, not value).
    Verilated::fatalOnVpiError(false);
    s_vpi_value rd{};
    rd.format = vpiIntVal;
    vpi_get_value(handleh, &rd);
    s_vpi_value wr{};
    wr.format = vpiIntVal;
    wr.value.integer = 0x1;
    vpi_put_value(handleh, &wr, nullptr, vpiNoDelay);
    Verilated::fatalOnVpiError(true);

    topp->final();
    if (errors) {
        std::printf("%%Error: %0d failures\n", errors);
        return 1;
    }
    std::printf("*-* All Finished *-*\n");
    return 0;
}
