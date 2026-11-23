// DESCRIPTION: Verilator: Concurrent RepCut independent behavioral oracle
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026-2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0
#include "verilated.h"

#include "Vt_repcut_concurrent.h"

#include <array>
#include <cstdio>
#include <cstdlib>
#include <memory>

using Wide = std::array<uint32_t, 3>;
static Wide advance(const Wide& x, uint32_t data, uint32_t upper) {
    return {(x[0] << 1 | x[2] >> 30) ^ data, (x[1] << 1 | x[0] >> 31) ^ data,
            ((x[2] << 1 | x[1] >> 31) ^ upper) & 0x7fffffffU};
}
static void check(uint64_t got, uint64_t expected, unsigned step, const char* label) {
    if (got != expected) {
        std::fprintf(stderr, "step %u %s: got %" PRIx64 " expected %" PRIx64 "\n", step, label,
                     got, expected);
        std::abort();
    }
}
int main(int argc, char** argv) {
    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};
    contextp->commandArgs(argc, argv);
    const std::unique_ptr<Vt_repcut_concurrent> modelp{new Vt_repcut_concurrent{contextp.get()}};
    auto& m = *modelp;
    std::array<Wide, 4> a{}, b{}, memory{};
    uint32_t ca = 0, cb = 0, left = 0, right = 0, predicate = 0, guarded = 0;
    uint64_t negative = 0;
    unsigned olda = 0, oldb = 0, oldc = 0;
    uint32_t random = 0x135792abU;
    uint64_t digest = 0;
    for (unsigned step = 0; step < 10000; ++step) {
        random ^= random << 13;
        random ^= random >> 17;
        random ^= random << 5;
        m.clk_a = (step / 2) & 1;
        m.clk_b = (step / 3) & 1;
        m.clk_c = (step / 5) & 1;
        m.reset = step < 32 || step % 997 < 20;
        m.enable = (random & 7) != 0;
        m.data = random;
        m.address = (random >> 17) & 3;
        const uint32_t oldca = ca, oldcb = cb;
        if (m.clk_a && !olda) {
            for (unsigned i = 0; i < 4; ++i) {
                if (m.reset)
                    a[i] = {i + 1, 0, 0};
                else if (m.enable)
                    a[i] = advance(a[i], random, random + i);
            }
#ifndef ISOLATED
            const uint32_t oldleft = left, oldright = right, oldpred = predicate;
            ca = m.reset ? 1 : oldcb + random;
            left = m.reset ? 3 : oldright + random;
            right = m.reset ? 7 : oldleft ^ random;
            predicate = m.reset ? 0 : random;
            if (m.reset)
                guarded = 11;
            else if (oldpred & 1)
                guarded += random;
#endif
        }
        if (m.clk_b && !oldb) {
            for (unsigned i = 0; i < 4; ++i) {
                if (m.reset)
                    b[i] = {i + 9, 0, 0};
                else if (m.enable)
                    b[i] = advance(b[i], random, random - i);
            }
#ifndef ISOLATED
            cb = m.reset ? 2 : oldca ^ random;
#endif
            if (m.reset) {
                for (unsigned i = 0; i < 4; ++i) memory[i] = {i, 0, 0};
            } else if (m.enable) {
                memory[m.address] = {random, random & 1 ? ~random : random, random & 0x7fffffffU};
            }
        }
        if (!m.clk_c && oldc) {
            if (m.reset)
                negative = 5;
            else if (m.enable)
                negative = (negative + random) & 0x1ffffffffULL;
        }
        olda = m.clk_a;
        oldb = m.clk_b;
        oldc = m.clk_c;
        m.eval();
        check(m.cross_a, ca, step, "cross_a");
        check(m.cross_b, cb, step, "cross_b");
        check(m.left_state, left, step, "left");
        check(m.right_state, right, step, "right");
        check(m.predicate, predicate, step, "predicate");
        check(m.guarded, guarded, step, "guarded");
        check(m.negative, negative, step, "negative");
        for (unsigned i = 0; i < 4; ++i) {
            for (unsigned w = 0; w < 3; ++w) {
                const unsigned bit = i * 95 + w * 32;
                const unsigned index = bit / 32, shift = bit % 32;
                const uint64_t mask = w == 2 ? 0x7fffffffU : 0xffffffffU;
                const uint64_t aw
                    = m.banks_a[index] | (index < 11 ? uint64_t{m.banks_a[index + 1]} << 32 : 0);
                const uint64_t bw
                    = m.banks_b[index] | (index < 11 ? uint64_t{m.banks_b[index + 1]} << 32 : 0);
                check((aw >> shift) & mask, a[i][w], step, "bank_a");
                check((bw >> shift) & mask, b[i][w], step, "bank_b");
            }
        }
        for (unsigned w = 0; w < 3; ++w)
            check(m.memory_out[w], memory[m.address][w], step, "memory");
        std::array<uint32_t, 6> mixed{};
        for (unsigned bit = 0; bit < 190; ++bit) {
            const unsigned source = bit % 95;
            const Wide& value = bit < 95 ? a[0] : b[0];
            mixed[bit / 32] |= ((value[source / 32] >> (source % 32)) & 1U) << (bit % 32);
        }
        for (unsigned w = 0; w < 6; ++w) check(m.mixed[w], mixed[w], step, "mixed");
        digest = digest * 0x100000001b3ULL ^ ca ^ cb ^ m.banks_a[0] ^ m.memory_out[1];
        contextp->timeInc(1);
    }
    m.final();
    std::printf("digest %" PRIx64 "\n*-* All Finished *-*\n", digest);
}
