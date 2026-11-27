// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: RepCut partial memory write reference model
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026-2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//*************************************************************************

#include "verilated.h"

#include "Vt_repcut_memory.h"

#include <array>
#include <iostream>

using Word = std::array<IData, 3>;

static QData low(const Word& value) { return (QData{value[1]} << 32) | value[0]; }

static void slice(Word& value, unsigned width, unsigned offset, unsigned bits, QData data) {
    for (unsigned bit = 0; bit < bits && offset + bit < width; ++bit) {
        const unsigned position = offset + bit;
        const IData mask = IData{1} << (position % 32);
        value[position / 32]
            = (value[position / 32] & ~mask) | (data & (QData{1} << bit) ? mask : 0);
    }
}

int main(int argc, char** argv) {
    VerilatedContext context;
    context.commandArgs(argc, argv);
    context.threads(REPCUT_TEST_THREADS);
    context.randReset(0);
    Vt_repcut_memory model{&context};
    std::array<Word, 8> wide{}, small{}, longs{};
    Word cross{};
    Word retained{};
#if REPCUT_PUBLICATION_WORDS
    std::array<std::array<IData, REPCUT_PUBLICATION_WORDS>, 2> publication{}, publicationOld{};
#endif
    IData random = 137;
    for (unsigned cycle = 0; cycle < 4096; ++cycle) {
        model.clk = model.clk_b = 0;
        model.enables = cycle % 17 == 0 ? 0 : cycle % 64;
        model.address = (cycle / 64) % 8;
        model.other = cycle % 3 == 0 ? model.address : (cycle / 8) % 8;
        model.offset = (cycle / 5) % 128;
        Word data;
        for (unsigned w = 0; w < 3; ++w) {
            random = random * 1664525U + 1013904223U;
            data[w] = model.data[w] = random & (w == 2 ? 0x7fffffffU : 0xffffffffU);
        }
        model.eval();
        const unsigned a = model.address;
        const unsigned b = model.other;
        const bool av = a >= 1 && a <= 3;
        const bool bv = b >= 1 && b <= 3;
        const Word oldwide = av ? wide[a] : Word{};
        const Word oldsmall = av ? small[a] : Word{};
        const Word oldlong = a <= 4 ? longs[a] : Word{};
#ifdef REPCUT_SINGLE_CLOCK
        const bool otherEdge = true;
#else
        const bool otherEdge = cycle % 2 == 0;
#endif
        if (otherEdge) {
            cross = oldwide;
            retained = oldwide;
#ifndef REPCUT_SINGLE_CLOCK
            retained[0] ^= model.address;
#endif
        }
#if REPCUT_PUBLICATION_WORDS
        if (otherEdge) publicationOld = publication;
        for (unsigned bank = 0; bank < publication.size(); ++bank) {
            IData carry = 0;
            for (unsigned word = 0; word < publication[bank].size(); ++word) {
                const IData old = publication[bank][word];
                publication[bank][word]
                    = (old << 1) ^ carry ^ data[0] ^ (word == 0 ? bank + 1 : 0);
                carry = old >> 31;
            }
        }
#endif
        if (av) {
            if (model.enables & 1) wide[a] = data;
            if (model.enables & 2) slice(wide[a], 95, 7, 33, low(data));
            if ((model.enables & 4) && (model.offset <= 78 || model.offset >= 95))
                slice(wide[a], 95, model.offset, 17, low(data));
        }
        if (bv && (model.enables & 8)) slice(wide[b], 95, 31, 33, low(oldwide) ^ low(data));
        if (av) {
            if (model.enables & 16) slice(wide[a], 95, 94, 1, low(data) >> 3);
            if (model.enables & 32) {
                for (unsigned w = 0; w < 3; ++w) wide[a][w] = ~data[w];
                wide[a][2] &= 0x7fffffffU;
            }
            if (model.enables & 1) slice(small[a], 15, 0, 15, low(data));
            if (model.enables & 2) slice(small[a], 15, model.offset & 15, 7, low(data));
        }
        if (bv && (model.enables & 4)) slice(small[b], 15, 3, 7, low(oldsmall) ^ (low(data) >> 7));
        if (a <= 4) {
            if (model.enables & 1) slice(longs[a], 63, 0, 63, low(data));
            if (model.enables & 2) slice(longs[a], 63, 21, 17, low(data));
        }
        if (b <= 4 && (model.enables & 4))
            slice(longs[b], 63, 0, 1, low(oldlong) ^ (low(data) >> 4));
        model.clk = 1;
        model.clk_b = otherEdge;
        model.eval();
        for (unsigned repeat = 0; repeat < 3; ++repeat) {
#if REPCUT_PUBLICATION_WORDS
            for (unsigned bank = 0; bank < publication.size(); ++bank) {
                for (unsigned word = 0; word < publication[bank].size(); ++word) {
                    const unsigned index = bank * REPCUT_PUBLICATION_WORDS + word;
                    if (model.publication[index] != publication[bank][word]
                        || model.publication_old[index] != publicationOld[bank][word]) {
                        std::cerr << "Publication mismatch at cycle " << cycle << '\n';
                        return 3;
                    }
                }
            }
#endif
            for (unsigned w = 0; w < 3; ++w) {
                const IData mask = w == 2 ? 0x7fffffffU : 0xffffffffU;
                if ((model.wide_out[w] & mask) != (av ? wide[a][w] : 0)
                    || (model.wide_old[w] & mask) != oldwide[w]
                    || (model.cross_old[w] & mask) != cross[w]
                    || (model.retained_old[w] & mask) != retained[w]) {
                    std::cerr << "Wide memory mismatch at cycle " << cycle << " word " << w
                              << " out " << std::hex << model.wide_out[w] << "/"
                              << (av ? wide[a][w] : 0) << " old " << model.wide_old[w] << "/"
                              << oldwide[w] << " cross " << model.cross_old[w] << "/" << cross[w]
                              << '\n';
                    return 1;
                }
            }
            if ((model.small_out & 0x7fffU) != (av ? low(small[a]) : 0)
                || (model.small_old & 0x7fffU) != low(oldsmall)
                || (model.long_out & 0x7fffffffffffffffULL) != (a <= 4 ? low(longs[a]) : 0)
                || (model.long_old & 0x7fffffffffffffffULL) != low(oldlong)) {
                std::cerr << "Memory mismatch at cycle " << cycle << '\n';
                return 2;
            }
            model.eval();
        }
    }
    model.final();
    std::cout << "*-* All Finished *-*\n";
}
