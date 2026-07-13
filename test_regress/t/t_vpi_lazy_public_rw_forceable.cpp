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

#include "Vt_vpi_lazy_public_rw_forceable.h"
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

    const std::unique_ptr<Vt_vpi_lazy_public_rw_forceable> topp{
        new Vt_vpi_lazy_public_rw_forceable{contextp.get(), ""}};

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

    vpiHandle keeph = mustFind("t.keep");
    vpiHandle frch = mustFind("t.frc");
    if (errors) return 10;

    int keep = 0;
    const auto frcOf = [](int k) { return (k + 0x11) & 0x7f; };

    for (int i = 0; i < 3; ++i) {
        cycle();
        keep = (keep + 0x3) & 0x7f;
        checkInt("t.keep", keeph, keep);
        checkInt("t.frc", frch, frcOf(keep));
    }

    // Force t.frc to a fixed value; the underlying comb driver keeps running,
    // but the forced value must win until released.
    s_vpi_value wr{};
    wr.format = vpiIntVal;
    wr.value.integer = 0x55;
    if (!vpi_put_value(frch, &wr, nullptr, vpiForceFlag)) {
        std::printf("%%Error: failed to force forceable signal t.frc\n");
        ++errors;
    }
    checkInt("t.frc (forced, pre-eval)", frch, 0x55);

    for (int i = 0; i < 2; ++i) {
        cycle();
        keep = (keep + 0x3) & 0x7f;
        checkInt("t.keep (while forced)", keeph, keep);
        checkInt("t.frc (while forced)", frch, 0x55);
    }

    if (!vpi_put_value(frch, &wr, nullptr, vpiReleaseFlag)) {
        std::printf("%%Error: failed to release forceable signal t.frc\n");
        ++errors;
    }
    cycle();
    keep = (keep + 0x3) & 0x7f;
    checkInt("t.keep (after release)", keeph, keep);
    checkInt("t.frc (after release)", frch, frcOf(keep));

    topp->final();
    if (errors) {
        std::printf("%%Error: %0d failures\n", errors);
        return 1;
    }
    std::printf("*-* All Finished *-*\n");
    return 0;
}
