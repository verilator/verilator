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

#include VM_PREFIX_INCLUDE
#include "vpi_user.h"

#include <cinttypes>
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

void putInt(vpiHandle handle, int v) {
    s_vpi_value wr{};
    wr.format = vpiIntVal;
    wr.value.integer = v;
    if (!vpi_put_value(handle, &wr, nullptr, vpiNoDelay)) {
        std::printf("%%Error: vpi_put_value failed\n");
        ++errors;
    }
}

int m8(int v) { return v & 0xff; }
int ifaceA(int din) { return m8(din + 0x11); }
int ifaceB(int din) { return m8(ifaceA(din) ^ 0x5a); }
int subS1(int din) { return m8(din + 0x07); }
int subS2(int din) { return m8(subS1(din) + m8(din << 1)); }

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

    const std::unique_ptr<VM_PREFIX> topp{new VM_PREFIX{contextp.get(), ""}};

    topp->base = 0;
    topp->in0 = topp->in1 = topp->in2 = topp->in3 = 0;
    topp->idx = 0;
    topp->nib = 0;
    topp->d = 0;
    topp->clk = 0;
    topp->eval();

    const auto cycle = [&]() {
        topp->clk = 0;
        topp->eval();
        topp->clk = 1;
        topp->eval();
        VerilatedVpi::callValueCbs();
    };

    // multi: multi-instance dedup
    {
        vpiHandle if0a = mustFind("t.if0.a");
        vpiHandle if0b = mustFind("t.if0.b");
        vpiHandle if1a = mustFind("t.if1.a");
        vpiHandle if1b = mustFind("t.if1.b");
        vpiHandle u0s1 = mustFind("t.u0.s1");
        vpiHandle u0s2 = mustFind("t.u0.s2");
        vpiHandle u1s1 = mustFind("t.u1.s1");
        vpiHandle u1s2 = mustFind("t.u1.s2");
        if (errors) return 10;

        for (const int base : {0x00, 0x13, 0x40, 0xa5, 0xff}) {
            topp->base = base;
            cycle();
            const int if0din = m8(base);
            const int if1din = m8(base + 0x20);
            const int u0din = m8(base);
            const int u1din = m8(base + 0x30);
            checkInt("t.if0.a", if0a, ifaceA(if0din));
            checkInt("t.if0.b", if0b, ifaceB(if0din));
            checkInt("t.if1.a", if1a, ifaceA(if1din));
            checkInt("t.if1.b", if1b, ifaceB(if1din));
            checkInt("t.u0.s1", u0s1, subS1(u0din));
            checkInt("t.u0.s2", u0s2, subS2(u0din));
            checkInt("t.u1.s1", u1s1, subS1(u1din));
            checkInt("t.u1.s2", u1s2, subS2(u1din));
            if (readInt(if0a) == readInt(if1a)) {
                std::printf("%%Error: if0.a and if1.a share storage (both %0d)\n", readInt(if0a));
                ++errors;
            }
            if (readInt(u0s2) == readInt(u1s2)) {
                std::printf("%%Error: u0.s2 and u1.s2 share storage (both %0d)\n", readInt(u0s2));
                ++errors;
            }
        }

        topp->base = 0x30;
        cycle();
        putInt(if0a, 0x77);
        checkInt("t.if0.a (deposit)", if0a, 0x77);
        checkInt("t.if1.a (unaffected)", if1a, ifaceA(m8(0x30 + 0x20)));
        topp->eval();
        checkInt("t.if0.a (after eval)", if0a, ifaceA(m8(0x30)));
        checkInt("t.if1.a (after eval)", if1a, ifaceA(m8(0x30 + 0x20)));
    }

    // stream: streaming semantics per SV LRM
    {
        vpiHandle flatGg = mustFind("t.flat_gg");
        vpiHandle flatLl = mustFind("t.flat_ll");
        vpiHandle flatLb = mustFind("t.flat_lb");
        vpiHandle flatArrGg = mustFind("t.flat_arr_gg");
        if (errors) return 10;

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
            checkVecLow32("t.flat_gg", flatGg, packStreamGG(a, b, c));
            checkVecLow32("t.flat_ll", flatLl, packStreamLL(a, b, c));
            checkVecLow32("t.flat_lb", flatLb, packStreamLB(a, b, c));
            checkVecLow32("t.flat_arr_gg", flatArrGg, packStreamArrGG(v.in0, v.in1, v.in2, v.in3));
            checkVecLow32("t.flat_gg (cached)", flatGg, packStreamGG(a, b, c));
            checkVecLow32("t.flat_arr_gg (cached)", flatArrGg,
                          packStreamArrGG(v.in0, v.in1, v.in2, v.in3));
        }

        s_vpi_value wr{};
        wr.format = vpiIntVal;
        wr.value.integer = 0x123456;
        if (!vpi_put_value(flatGg, &wr, nullptr, vpiNoDelay)) {
            std::printf("%%Error: vpi_put_value on reconstructed t.flat_gg failed\n");
            ++errors;
        }
        checkVecLow32("t.flat_gg (deposit)", flatGg, 0x123456);
        topp->eval();
        checkVecLow32("t.flat_gg (after eval)", flatGg, packStreamGG(0xFF, 0x00, 0x80));
    }

    // cycle: comb cycles and cyclic aliases retained
    {
        vpiHandle cycA = mustFind("t.cyc_a");
        vpiHandle cycB = mustFind("t.cyc_b");
        mustFind("t.ali_a");
        mustFind("t.ali_b");
        vpiHandle selfLoop = mustFind("t.self_loop");
        vpiHandle dHnd = mustFind("t.cyc_d");
        vpiHandle cycDown = mustFind("t.cyc_down");
        vpiHandle cycDown2 = mustFind("t.cyc_down2");
        vpiHandle boundary = mustFind("t.cyc_boundary");
        if (errors) return 10;

        for (int i = 0; i < 4; ++i) {
            cycle();
            const int b = readInt(boundary) & 0x7f;
            const int dval = (b + 1) & 0x7f;
            const int axb = (readInt(cycA) ^ readInt(cycB)) & 0x7f;
            if (axb != dval) {
                std::printf("%%Error: cyc_a^cyc_b (%0d) != cyc_d (%0d)\n", axb, dval);
                ++errors;
            }
            checkInt("t.cyc_d", dHnd, dval);
            checkInt("t.cyc_down", cycDown, dval);
            checkInt("t.cyc_down2", cycDown2, (dval + b) & 0x7f);
        }

        const int cycDownWas = readInt(cycDown);
        putInt(cycDown, 0x3);
        checkInt("t.cyc_down (deposit)", cycDown, 0x3);
        topp->eval();
        checkInt("t.cyc_down (after eval)", cycDown, cycDownWas);

        putInt(cycA, 0x2a);
        checkInt("t.cyc_a (after put)", cycA, 0x2a);

        putInt(selfLoop, 0x15);
        checkInt("t.self_loop (after put)", selfLoop, 0x15);
    }

    // aliascycle: a deposit into either side propagates to the other and holds, the pair
    // being a pure alias ring with no other driver
    {
        vpiHandle alcX = mustFind("t.alc_x");
        vpiHandle alcY = mustFind("t.alc_y");
        if (errors) return 10;

        putInt(alcX, 0x2a);
        checkInt("t.alc_x (deposit)", alcX, 0x2a);
        topp->eval();
        checkInt("t.alc_x (after eval)", alcX, 0x2a);
        checkInt("t.alc_y (after eval)", alcY, 0x2a);
    }

    // creset: cross-scope write inside interface retained
    {
        topp->d = 0x0011223344556677ULL;
        topp->eval();
        const std::uint64_t expectedSwapped = 0x7766554433221100ULL;
        if (topp->o != expectedSwapped) {
            std::printf("%%Error: t.o expected %" PRIx64 ", got %" PRIx64 "\n", expectedSwapped,
                        topp->o);
            ++errors;
        }

        vpiHandle swappedh = mustFind("t.intf.swapped");
        if (errors) return 10;
        checkVecLow32("t.intf.swapped", swappedh, static_cast<unsigned>(expectedSwapped));

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
        topp->eval();
        checkVecLow32("t.intf.swapped (after eval)", swappedh,
                      static_cast<unsigned>(expectedSwapped));
    }

    // contretain: impure/RNG/time drivers retained
    {
        topp->idx = 0x5;
        topp->nib = 0xa;
        topp->eval();

        vpiHandle vecHnd = mustFind("t.crbase");
        vpiHandle rndH = mustFind("t.rnd");
        if (errors) return 10;

        putInt(rndH, 0);  // Read-write proof only; the value is impure
        putInt(vecHnd, 0x5a);
        checkInt("t.crbase (after put)", vecHnd, 0x5a);
    }

    // chainorder: co_tap shares co_deep's shadow across a retained chain link. Read the
    // downstream cone first, so only its own operand refresh can freshen that shadow.
    {
        vpiHandle coUse = mustFind("t.co_use");
        vpiHandle coTap = mustFind("t.co_tap");
        vpiHandle coDeep = mustFind("t.co_deep");
        if (errors) return 10;

        for (const int base : {0x00, 0x21, 0x7e, 0xc3}) {
            topp->base = base;
            topp->eval();
            const int deep = m8(base + 0x1f) ^ 0x3c;
            checkInt("t.co_use", coUse, deep ^ 0xa5);
            checkInt("t.co_tap", coTap, deep);
            checkInt("t.co_deep", coDeep, deep);
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
