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

#include "Vt_vpi_lazy_public_rw_creset.h"
#include "vpi_user.h"

#include <cstdint>
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

// Low 32 bits of the (64-bit) vector value.
unsigned readVecLow32(vpiHandle handle) {
    s_vpi_value value{};
    value.format = vpiVectorVal;
    vpi_get_value(handle, &value);
    return static_cast<unsigned>(value.value.vector[0].aval);
}

void checkVecLow32(const char* name, vpiHandle handle, unsigned expected) {
    const unsigned got = readVecLow32(handle);
    if (got != expected) {
        std::printf("%%Error: %s expected %0x, got %0x\n", name, expected, got);
        ++errors;
    }
}

}  // namespace

int main(int argc, char** argv) {
    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};
    contextp->commandArgs(argc, argv);

    const std::unique_ptr<Vt_vpi_lazy_public_rw_creset> topp{
        new Vt_vpi_lazy_public_rw_creset{contextp.get(), ""}};

    topp->d = 0x0011223344556677ULL;
    topp->eval();
    const std::uint64_t expectedSwapped = 0x7766554433221100ULL;
    if (topp->o != expectedSwapped) {
        std::printf("%%Error: t.o expected %llx, got %llx\n",
                    static_cast<unsigned long long>(expectedSwapped),
                    static_cast<unsigned long long>(topp->o));
        ++errors;
    }

    // Retained signal inside interface instance.
    vpiHandle swappedh = mustFind("t.intf.swapped");
    if (errors) return 10;

    // Read value matches design output.
    checkVecLow32("t.intf.swapped", swappedh, static_cast<unsigned>(expectedSwapped));

    // Test VPI write.
    s_vpi_vecval vec[2];
    vec[0].aval = 0xdeadbeef;
    vec[0].bval = 0;
    vec[1].aval = 0x1;
    vec[1].bval = 0;
    s_vpi_value wr{};
    wr.format = vpiVectorVal;
    wr.value.vector = vec;
    if (!vpi_put_value(swappedh, &wr, nullptr, vpiNoDelay)) {
        std::printf("%%Error: failed to write retained t.intf.swapped\n");
        ++errors;
    }
    checkVecLow32("t.intf.swapped (after put)", swappedh, 0xdeadbeef);

    // Eval overwrites written value.
    topp->eval();
    checkVecLow32("t.intf.swapped (after eval)", swappedh, static_cast<unsigned>(expectedSwapped));

    topp->final();
    if (errors) {
        std::printf("%%Error: %0d failures\n", errors);
        return 1;
    }
    std::printf("*-* All Finished *-*\n");
    return 0;
}
