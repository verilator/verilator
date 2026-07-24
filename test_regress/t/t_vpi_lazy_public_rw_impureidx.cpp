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

#include "Vt_vpi_lazy_public_rw_impureidx.h"
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

}  // namespace

int main(int argc, char** argv) {
    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};
    contextp->commandArgs(argc, argv);

    const std::unique_ptr<Vt_vpi_lazy_public_rw_impureidx> topp{
        new Vt_vpi_lazy_public_rw_impureidx{contextp.get(), ""}};

    topp->data = 0x5;
    topp->eval();

    // Both signals retained with real storage.
    vpiHandle vecHnd = mustFind("t.vec");
    vpiHandle obsHnd = mustFind("t.obs");
    if (errors) return 10;

    // Cross-check: obs is alias of vec, should have same value.
    const int vecVal = readInt(vecHnd);
    const int obsVal = readInt(obsHnd);
    if (vecVal != obsVal) {
        std::printf("%%Error: t.vec (%0d) != t.obs (%0d)\n", vecVal, obsVal);
        ++errors;
    }

    // Test VPI write to retained signal.
    s_vpi_value wr{};
    wr.format = vpiIntVal;
    wr.value.integer = 0x5a;
    if (!vpi_put_value(vecHnd, &wr, nullptr, vpiNoDelay)) {
        std::printf("%%Error: failed to write retained t.vec\n");
        ++errors;
    }
    const int got = readInt(vecHnd);
    if (got != 0x5a) {
        std::printf("%%Error: t.vec expected %0d, got %0d\n", 0x5a, got);
        ++errors;
    }

    topp->final();
    if (errors) {
        std::printf("%%Error: %0d failures\n", errors);
        return 1;
    }
    std::printf("*-* All Finished *-*\n");
    return 0;
}
