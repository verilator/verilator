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

#include "Vt_vpi_lazy_public_rw_cycle.h"
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

    const std::unique_ptr<Vt_vpi_lazy_public_rw_cycle> topp{
        new Vt_vpi_lazy_public_rw_cycle{contextp.get(), ""}};

    topp->clk = 0;
    topp->eval();

    vpiHandle cycA = mustFind("t.cyc_a");
    vpiHandle cycB = mustFind("t.cyc_b");
    mustFind("t.ali_a");
    mustFind("t.ali_b");
    vpiHandle selfLoop = mustFind("t.self_loop");
    vpiHandle dHnd = mustFind("t.d");
    vpiHandle cycDown = mustFind("t.cyc_down");
    vpiHandle cycDown2 = mustFind("t.cyc_down2");
    vpiHandle boundary = mustFind("t.boundary");
    if (errors) return 10;

    const auto cycle = [&]() {
        topp->clk = 0;
        topp->eval();
        topp->clk = 1;
        topp->eval();
    };

    // Cycle property: cyc_a ^ cyc_b == d == boundary+1 (mod 128).
    for (int i = 0; i < 4; ++i) {
        cycle();
        const int b = readInt(boundary) & 0x7f;
        const int dval = (b + 1) & 0x7f;
        const int axb = (readInt(cycA) ^ readInt(cycB)) & 0x7f;
        if (axb != dval) {
            std::printf("%%Error: cyc_a^cyc_b (%0d) != d (%0d)\n", axb, dval);
            ++errors;
        }
        checkInt("t.d", dHnd, dval);
        checkInt("t.cyc_down", cycDown, dval);
        checkInt("t.cyc_down2", cycDown2, (dval + b) & 0x7f);
    }

    // Reconstructed signal read-only.
    Verilated::fatalOnVpiError(false);
    s_vpi_value wr{};
    wr.format = vpiIntVal;
    wr.value.integer = 0x3;
    if (vpi_put_value(cycDown, &wr, nullptr, vpiNoDelay)) {
        std::printf("%%Error: vpi_put_value on reconstructed t.cyc_down unexpectedly succeeded\n");
        ++errors;
    }
    if (!vpi_chk_error(nullptr)) {
        std::printf("%%Error: expected a VPI error from writing reconstructed t.cyc_down\n");
        ++errors;
    }
    Verilated::fatalOnVpiError(true);

    wr.value.integer = 0x2a;
    if (!vpi_put_value(cycA, &wr, nullptr, vpiNoDelay)) {
        std::printf("%%Error: failed to write retained cycle member t.cyc_a\n");
        ++errors;
    }
    checkInt("t.cyc_a (after put)", cycA, 0x2a);

    wr.value.integer = 0x15;
    if (!vpi_put_value(selfLoop, &wr, nullptr, vpiNoDelay)) {
        std::printf("%%Error: failed to write retained self-loop t.self_loop\n");
        ++errors;
    }
    checkInt("t.self_loop (after put)", selfLoop, 0x15);

    topp->final();
    if (errors) {
        std::printf("%%Error: %0d failures\n", errors);
        return 1;
    }
    std::printf("*-* All Finished *-*\n");
    return 0;
}
