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

#include "Vt_vpi_lazy_public_rw_stream.h"
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

uint32_t readU32(vpiHandle handle) {
    s_vpi_value value{};
    value.format = vpiIntVal;
    vpi_get_value(handle, &value);
    return static_cast<uint32_t>(value.value.integer);
}

void checkHex(const char* name, vpiHandle handle, uint32_t expected) {
    const uint32_t got = readU32(handle);
    if (got != expected) {
        std::printf("%%Error: %s expected %08x, got %08x\n", name, expected, got);
        ++errors;
    }
}

// Streaming semantics: per SV LRM.

uint32_t bitrev(uint32_t v, int bits) {
    uint32_t r = 0;
    for (int i = 0; i < bits; ++i) { r |= ((v >> i) & 1u) << (bits - 1 - i); }
    return r;
}

uint32_t packStreamGG(uint32_t a, uint32_t b, uint32_t c) { return (a << 16) | (b << 8) | c; }
uint32_t packStreamLL(uint32_t a, uint32_t b, uint32_t c) {
    return bitrev(packStreamGG(a, b, c), 24);
}
uint32_t packStreamLB(uint32_t a, uint32_t b, uint32_t c) { return (c << 16) | (b << 8) | a; }
uint32_t packStreamArrGG(uint32_t a0, uint32_t a1, uint32_t a2, uint32_t a3) {
    return (a0 << 24) | (a1 << 16) | (a2 << 8) | a3;
}

}  // namespace

int main(int argc, char** argv) {
    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};
    contextp->commandArgs(argc, argv);

    const std::unique_ptr<Vt_vpi_lazy_public_rw_stream> topp{
        new Vt_vpi_lazy_public_rw_stream{contextp.get(), ""}};

    vpiHandle flatGg = mustFind("t.flat_gg");
    vpiHandle flatLl = mustFind("t.flat_ll");
    vpiHandle flatLb = mustFind("t.flat_lb");
    vpiHandle flatArrGg = mustFind("t.flat_arr_gg");
    if (errors) return 10;

    const auto cycle = [&]() {
        topp->clk = 0;
        topp->eval();
        topp->clk = 1;
        topp->eval();
        VerilatedVpi::callValueCbs();
    };

    // Test vectors with all-ones/high-bit bytes to expose ordering bugs.
    struct Vec {
        uint32_t in0, in1, in2, in3;
    };
    const Vec vecs[] = {
        {0x11, 0x22, 0xF0, 0x55},
        {0xDE, 0xAD, 0xBE, 0xEF},
        {0xFF, 0x00, 0x80, 0x01},
    };

    for (const Vec& v : vecs) {
        topp->in0 = v.in0;
        topp->in1 = v.in1;
        topp->in2 = v.in2;
        topp->in3 = v.in3;
        cycle();

        const uint32_t a = v.in0, b = v.in1, c = v.in2;
        checkHex("t.flat_gg", flatGg, packStreamGG(a, b, c));
        checkHex("t.flat_ll", flatLl, packStreamLL(a, b, c));
        checkHex("t.flat_lb", flatLb, packStreamLB(a, b, c));
        checkHex("t.flat_arr_gg", flatArrGg, packStreamArrGG(v.in0, v.in1, v.in2, v.in3));

        // Cached: no eval between reads.
        checkHex("t.flat_gg (cached)", flatGg, packStreamGG(a, b, c));
        checkHex("t.flat_arr_gg (cached)", flatArrGg, packStreamArrGG(v.in0, v.in1, v.in2, v.in3));
    }

    // Reconstructed read-only.
    Verilated::fatalOnVpiError(false);
    {
        s_vpi_value wr{};
        wr.format = vpiIntVal;
        wr.value.integer = 0x123456;
        vpiHandle putRet = vpi_put_value(flatGg, &wr, nullptr, vpiNoDelay);
        if (putRet) {
            std::printf(
                "%%Error: vpi_put_value on reconstructed t.flat_gg unexpectedly succeeded\n");
            ++errors;
        }
        if (!vpi_chk_error(nullptr)) {
            std::printf("%%Error: expected a VPI error from writing reconstructed t.flat_gg\n");
            ++errors;
        }
    }
    Verilated::fatalOnVpiError(true);
    checkHex("t.flat_gg (after failed put)", flatGg, packStreamGG(0xFF, 0x00, 0x80));

    topp->final();
    if (errors) {
        std::printf("%%Error: %0d failures\n", errors);
        return 1;
    }
    std::printf("*-* All Finished *-*\n");
    return 0;
}
