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

#include "Vt_vpi_lazy_public_rw_contretain.h"
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

    const std::unique_ptr<Vt_vpi_lazy_public_rw_contretain> topp{
        new Vt_vpi_lazy_public_rw_contretain{contextp.get(), ""}};

    topp->idx = 2;
    topp->nib = 0xb;
    topp->eval();

    // Both signals retained with real storage.
    vpiHandle baseh = mustFind("t.base");
    vpiHandle rndh = mustFind("t.rnd");
    if (errors) return 10;

    {
        const int got = readInt(baseh);
        const int nibble = (got >> 2) & 0xf;
        if (nibble != 0xb) {
            std::printf("%%Error: t.base[idx+:4] expected %0d, got %0d\n", 0xb, nibble);
            ++errors;
        }
    }

    // Test VPI write to retained signals.
    s_vpi_value wr{};
    wr.format = vpiIntVal;
    wr.value.integer = 0x1234abcd;
    if (!vpi_put_value(rndh, &wr, nullptr, vpiNoDelay)) {
        std::printf("%%Error: failed to write retained t.rnd\n");
        ++errors;
    }
    checkInt("t.rnd (after put)", rndh, 0x1234abcd);

    wr.value.integer = 0x5a;
    if (!vpi_put_value(baseh, &wr, nullptr, vpiNoDelay)) {
        std::printf("%%Error: failed to write retained t.base\n");
        ++errors;
    }
    checkInt("t.base (after put)", baseh, 0x5a);

    // Eval overwrites written value with new partial-write logic.
    topp->idx = 1;
    topp->nib = 0x3;
    topp->eval();
    {
        const int got = readInt(baseh);
        const int nibble = (got >> 1) & 0xf;
        if (nibble != 0x3) {
            std::printf("%%Error: t.base[idx+:4] after eval expected %0d, got %0d\n", 0x3, nibble);
            ++errors;
        }
    }

    topp->final();
    if (errors) {
        std::printf("%%Error: %0d failures\n", errors);
        return 1;
    }
    std::printf("*-* All Finished *-*\n");
    return 0;
}
