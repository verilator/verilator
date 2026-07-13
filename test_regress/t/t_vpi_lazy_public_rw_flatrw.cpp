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

#include "Vt_vpi_lazy_public_rw_flatrw.h"
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

void checkInt(const char* name, vpiHandle handle, int expected) {
    s_vpi_value value{};
    value.format = vpiIntVal;
    vpi_get_value(handle, &value);
    if (value.value.integer != expected) {
        std::printf("%%Error: %s expected %0d, got %0d\n", name, expected, value.value.integer);
        ++errors;
    }
}

}  // namespace

int main(int argc, char** argv) {
    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};
    contextp->commandArgs(argc, argv);

    const std::unique_ptr<Vt_vpi_lazy_public_rw_flatrw> topp{
        new Vt_vpi_lazy_public_rw_flatrw{contextp.get(), ""}};

    const int a = 0x30;
    topp->a = a;
    topp->eval();

    vpiHandle pinnedH = mustFind("t.pinned_rw");
    vpiHandle lazyH = mustFind("t.lazy_ro");
    if (errors) return 10;

    checkInt("t.pinned_rw", pinnedH, (a ^ 0x5) & 0xff);
    checkInt("t.lazy_ro", lazyH, (a + 1) & 0xff);

    // Test write to public_flat_rw signal.
    s_vpi_value wr{};
    wr.format = vpiIntVal;
    wr.value.integer = 0x99;
    if (!vpi_put_value(pinnedH, &wr, nullptr, vpiNoDelay)) {
        std::printf("%%Error: vpi_put_value on public_flat_rw t.pinned_rw failed\n");
        ++errors;
    }
    checkInt("t.pinned_rw (after put)", pinnedH, 0x99);

    // Reconstructed is read-only.
    Verilated::fatalOnVpiError(false);
    if (vpi_put_value(lazyH, &wr, nullptr, vpiNoDelay)) {
        std::printf("%%Error: vpi_put_value on reconstructed t.lazy_ro unexpectedly succeeded\n");
        ++errors;
    }
    Verilated::fatalOnVpiError(true);
    checkInt("t.lazy_ro (after rejected put)", lazyH, (a + 1) & 0xff);

    topp->final();
    if (errors) {
        std::printf("%%Error: %0d failures\n", errors);
        return 1;
    }
    std::printf("*-* All Finished *-*\n");
    return 0;
}
