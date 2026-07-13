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

#include "Vt_vpi_lazy_public_rw_floor.h"
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

    const std::unique_ptr<Vt_vpi_lazy_public_rw_floor> topp{
        new Vt_vpi_lazy_public_rw_floor{contextp.get(), ""}};

    topp->a = 5;
    topp->eval();

    // Reconstructed (read-only) vs floor-retained (read-write).
    vpiHandle reconh = mustFind("t.recon");
    vpiHandle orphanh = mustFind("t.orphan");
    if (errors) return 10;

    checkInt("t.recon", reconh, 6);

    // Test write to reconstructed (should fail).
    Verilated::fatalOnVpiError(false);
    s_vpi_value wr{};
    wr.format = vpiIntVal;
    wr.value.integer = 0x11;
    vpiHandle putRet = vpi_put_value(reconh, &wr, nullptr, vpiNoDelay);
    if (putRet) {
        std::printf("%%Error: vpi_put_value on reconstructed t.recon unexpectedly succeeded\n");
        ++errors;
    }
    if (!vpi_chk_error(nullptr)) {
        std::printf("%%Error: expected a VPI error from writing reconstructed t.recon\n");
        ++errors;
    }
    Verilated::fatalOnVpiError(true);

    // Test write to floor-retained (should succeed).
    wr.value.integer = 0x2a;
    if (!vpi_put_value(orphanh, &wr, nullptr, vpiNoDelay)) {
        std::printf("%%Error: failed to write floor-retained t.orphan\n");
        ++errors;
    }
    checkInt("t.orphan (after put)", orphanh, 0x2a);
    topp->eval();
    checkInt("t.orphan (after eval)", orphanh, 0x2a);

    topp->final();
    if (errors) {
        std::printf("%%Error: %0d failures\n", errors);
        return 1;
    }
    std::printf("*-* All Finished *-*\n");
    return 0;
}
