// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: RepCut compatibility regression
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026-2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "verilated.h"

#include "Vt_repcut_values.h"

#if VM_TRACE
#include "verilated_vcd_c.h"
#endif
#if VM_VPI
#include "verilated_vpi.h"
#endif

#include <cstdlib>
#include <iostream>
#include <string>

using Wide = unsigned __int128;
using SignedWide = __int128;

static Wide getWide(const VlWide<3>& value) {
    return Wide{value[0]} | (Wide{value[1]} << 32) | (Wide{value[2]} << 64);
}
static void setWide(VlWide<3>& value, Wide bits) {
    for (unsigned i = 0; i < 3; ++i) value[i] = bits >> (32 * i);
}
static SignedWide signedValue(Wide value, unsigned width) {
    return (value & (Wide{1} << (width - 1)))
               ? static_cast<SignedWide>(value) - (SignedWide{1} << width)
               : static_cast<SignedWide>(value);
}
static void check(Wide actual, Wide expected, const char* name, unsigned step) {
    if (actual != expected) {
        std::cerr << name << " mismatch at " << step << '\n';
        std::exit(1);
    }
}
int main(int argc, char** argv) {
    VerilatedContext context;
    context.commandArgs(argc, argv);
    context.threads(REPCUT_TEST_THREADS);
    context.randReset(0);
#if VM_TRACE
    context.traceEverOn(true);
#endif
    Vt_repcut_values model{&context};
#if VM_TRACE
    VerilatedVcdC trace;
    model.trace(&trace, 99);
    if (argc != 2) return 1;
    trace.open(argv[1]);
#endif
    model.seed = 0x3210;
    model.clk = 0;
    uint32_t rng = 0x193aca;
    const auto randomWord = [&]() {
        rng ^= rng << 13;
        rng ^= rng >> 17;
        rng ^= rng << 5;
        return rng;
    };
    const Wide mask = (Wide{1} << 95) - 1;
    unsigned previous = 0;
    unsigned written[3] = {};
    unsigned chain[16] = {};
    Wide previousWide = 0;
    Wide grouped[8] = {};
    unsigned enq = 0, deq = 0, full = 0;
    const unsigned rom[4] = {0x1234, 0x7654, 0x1357, 0};
    const unsigned initialized[4] = {0x3210, 0x3210 ^ 0x5a5a, 0x3217, 0};
    for (unsigned step = 0; step < 2048; ++step) {
        model.a = randomWord() & 0x7fffffff;
        model.b = step % 11 ? randomWord() & 0x7fffffff : 0;
        Wide a = Wide{randomWord()} | (Wide{randomWord()} << 32)
                 | (Wide{randomWord() & 0x7fffffff} << 64);
        Wide b = Wide{randomWord()} | (Wide{randomWord()} << 32)
                 | (Wide{randomWord() & 0x7fffffff} << 64);
        if (step % 7 == 0) b = randomWord();
        if (step % 11 == 0) b = 0;
        // Exercise signed minimum / -1 without overflowing the host oracle.
        if (step % 17 == 0) {
            a = Wide{1} << 94;
            b = mask;
        }
        setWide(model.wide_a, a);
        setWide(model.wide_b, b);
        model.addr = (step / 2) % 4;
        model.packed_in = randomWord() & 0x7fff;
        model.clk = step & 1;
        model.reset = step < 4 || (step % 23 == 0);
        model.enqueue = randomWord() & 1;
        model.dequeue = randomWord() & 1;
#if VM_VPI
        if (model.clk && !model.reset && step % 31 == 7) {
            // A held register may have been changed externally since its last
            // active write. Publishing a stale candidate must not undo this.
            grouped[0] = a;
            model.enqueue = a & 1;
            model.dequeue = 0;
            const vpiHandle handle
                = vpi_handle_by_name(const_cast<char*>("TOP.t.grouped0"), nullptr);
            if (!handle) return 1;
            s_vpi_vecval words[3]{};
            for (unsigned n = 0; n < 3; ++n) words[n].aval = a >> (32 * n);
            s_vpi_value value{};
            value.format = vpiVectorVal;
            value.value.vector = words;
            vpi_put_value(handle, &value, nullptr, vpiNoDelay);
            vpi_release_handle(handle);
        }
#endif
        model.eval();
        const SignedWide sa = signedValue(a, 95), sb = signedValue(b, 95);
        const SignedWide x = signedValue(model.a, 31), y = signedValue(model.b, 31);
        check(model.quotient, model.b ? model.a / model.b : 0, "divide", step);
        check(model.remainder, model.b ? model.a % model.b : 0, "remainder", step);
        check(model.signed_quotient, Wide(y ? x / y : 0) & 0x7fffffff, "signed divide", step);
        check(model.signed_remainder, Wide(y ? x % y : 0) & 0x7fffffff, "signed remainder", step);
        check(getWide(model.wide_quotient), b ? a / b : 0, "wide divide", step);
        check(getWide(model.wide_remainder), b ? a % b : 0, "wide remainder", step);
        check(getWide(model.wide_signed_quotient), Wide(sb ? sa / sb : 0) & mask,
              "wide signed divide", step);
        check(getWide(model.wide_signed_remainder), Wide(sb ? sa % sb : 0) & mask,
              "wide signed remainder", step);
        check(model.rom_out, rom[model.addr], "constant ROM", step);
        check(model.init_out, initialized[model.addr], "initialized ROM", step);
        check(model.initial_scalar, 0x3210 ^ 0x7b7b, "initialized scalar", step);
        check(model.offset_out, model.addr ? rom[3 - model.addr] : 0, "nonzero ROM", step);
        check(model.ascending_out, rom[model.addr], "ascending ROM", step);
        const unsigned packed = ((model.packed_in & 31) << 10) | ((model.packed_in >> 5) & 1023);
        check(model.packed_out, packed, "packed aggregate", step);
        if (model.clk) previous = packed ^ initialized[model.addr];
        check(model.registered_out, previous, "registered aggregate", step);
        if (model.clk && model.addr < 3) {
            if (model.enqueue) written[model.addr] = model.packed_in;
            if (model.dequeue) written[model.addr] = model.packed_in ^ 0x2a55;
        }
        check(model.written0, written[0], "memory write 0", step);
        check(model.written1, written[1], "memory write 1", step);
        check(model.written2, written[2], "memory write 2", step);
        if (model.clk) {
            if (model.reset)
                previousWide = 0;
            else if (model.enqueue)
                previousWide = model.dequeue ? a / (b | 1) : a ^ b;
        }
        check(getWide(model.registered_wide), previousWide, "guarded wide register", step);
        if (model.clk) {
            const bool first = model.enqueue ^ (grouped[0] & 1);
            const bool second = model.dequeue & (grouped[1] & 1);
            const Wide firstOld = grouped[0];
            for (unsigned n = 0; n < 8; ++n) {
                const Wide nextOld = n == 7 ? firstOld : grouped[n + 1];
                if (model.reset) {
                    grouped[n] = n;
                } else {
                    if (first) grouped[n] = ((nextOld ^ a) + n + 1) & mask;
                    if (second) grouped[n] = b ^ (n + 11);
                }
            }
        }
        const VlWide<3>* const actualGroups[]
            = {&model.grouped0, &model.grouped1, &model.grouped2, &model.grouped3,
               &model.grouped4, &model.grouped5, &model.grouped6, &model.grouped7};
        for (unsigned n = 0; n < 8; ++n)
            check(getWide(*actualGroups[n]), grouped[n], "grouped wide register", step);
        if (model.clk) {
            if (model.reset)
                enq = deq = full = 0;
            else {
                if (model.enqueue) enq = (enq + 1) % 3;
                if (model.dequeue) deq = (deq + 1) % 3;
                if (model.enqueue != model.dequeue) full = model.enqueue;
            }
        }
        check(model.table_out, (enq << 3) | (deq << 1) | full, "clocked table", step);
        unsigned link = (model.a ^ model.b) + 1;
        unsigned accumulated = 0;
        for (unsigned n = 0; n < 16; ++n) {
            if (n) link = (link << 1) ^ (link + model.a + n);
            link &= 0x7fffffff;
#if VM_VPI
            const std::string name = "TOP.t.chain[" + std::to_string(n) + "].link_value";
            const vpiHandle handle = vpi_handle_by_name(const_cast<char*>(name.c_str()), nullptr);
            if (!handle) {
                std::cerr << "Missing public chain value: " << name << '\n';
                return 1;
            }
            s_vpi_value value{};
            value.format = vpiIntVal;
            vpi_get_value(handle, &value);
            check(value.value.integer, link, "public combinational chain", step);
            vpi_release_handle(handle);
#endif
            if (model.clk) {
                chain[n] = model.reset ? 0 : (link ^ (chain[n] + model.b)) & 0x7fffffff;
            }
            accumulated ^= chain[n];
        }
        check(model.chain_out, accumulated, "partitioned combinational chain", step);
#if VM_TRACE
        trace.dump(step);
#endif
        model.seed ^= 0x1234;  // Initialization must not repeat during eval().
    }
    model.final();
#if VM_TRACE
    trace.close();
#endif
    std::cout << "*-* All Finished *-*\n";
}
