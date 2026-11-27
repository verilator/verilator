// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Native decoder cache lifetime regression
//
// Code available from: https://verilator.org
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026-2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//*************************************************************************

#include "verilated.h"

#include "Vt_repcut_decoder_state.h"
#ifdef DECODER_SAVE
#include "verilated_save.h"
#endif

#include <array>
#include <cstdlib>
#include <iostream>
#include <memory>

int main(int argc, char** argv) {
    std::array<VerilatedContext, 2> contexts;
    std::array<std::unique_ptr<Vt_repcut_decoder_state>, 2> models;
    uint32_t expected[2][3][4] = {};
    for (unsigned id = 0; id < 2; ++id) {
        contexts[id].commandArgs(argc, argv);
        contexts[id].threads(REPCUT_TEST_THREADS);
        contexts[id].randReset(2);
        models[id].reset(new Vt_repcut_decoder_state{&contexts[id]});
    }
    // Interleaved instances expose accidentally shared caches. Every index is
    // repeated, revisited after wraparound, and exercised under disabled guards.
    for (unsigned step = 0; step < 1024; ++step) {
        for (unsigned id = 0; id < 2; ++id) {
            Vt_repcut_decoder_state& model = *models[id];
            VerilatedContext& context = contexts[id];
            model.a = (step / 2 + id * 37) & 127;
            model.b = 127 - model.a;
            model.reset = step == 0 || step == 601;
            model.en_a = step % 5 != 0;
            model.en_b = step % 7 != 0;
            for (unsigned word = 0; word < 4; ++word)
                model.mask[word] = 0x9e3779b9U * (step + 1 + word * 13 + id * 19);
            uint32_t da[4] = {}, db[4] = {};
            for (unsigned bit = 0; bit < 128; ++bit) {
                const unsigned reverse = 127 - bit;
                da[bit / 32] |= ((model.a == bit) ^ ((model.mask[bit / 32] >> (bit % 32)) & 1))
                                << (bit % 32);
                db[bit / 32]
                    |= ((model.b != bit) ^ ((model.mask[reverse / 32] >> (reverse % 32)) & 1))
                       << (bit % 32);
            }
            for (unsigned word = 0; word < 4; ++word) {
                if (model.reset) {
                    for (auto& output : expected[id]) output[word] = 0;
                } else {
                    if (model.en_a) expected[id][0][word] = da[word];
                    if (model.en_b) expected[id][1][word] = db[word];
                    if (model.en_a && model.en_b) expected[id][2][word] = da[word] ^ db[word];
                }
            }
            model.clk = 0;
            context.timeInc(1);
            model.eval();
            model.clk = 1;
            context.timeInc(1);
            model.eval();
            model.eval();  // Repeated evaluation must not advance cache state incorrectly.
#ifdef DECODER_SAVE
            if (step == 257 && id == 0) {
                if (argc != 2) std::abort();
                VerilatedSave save;
                save.open(argv[1]);
                save << &context << model;
                save.close();
                for (unsigned tick = 0; tick < 40; ++tick) {
                    model.clk = tick & 1;
                    model.a = (tick * 7) & 127;
                    model.b = (tick * 11) & 127;
                    context.timeInc(1);
                    model.eval();
                }
                VerilatedRestore restore;
                restore.open(argv[1]);
                restore >> &context >> model;
                restore.close();
            }
#endif
            for (unsigned word = 0; word < 4; ++word) {
                if (model.qa[word] != expected[id][0][word]
                    || model.qb[word] != expected[id][1][word]
                    || model.qc[word] != expected[id][2][word]) {
                    std::cerr << "Decoder mismatch: instance " << id << " step " << step << '\n';
                    return 1;
                }
            }
        }
    }
    for (const auto& model : models) model->final();
    std::cout << "*-* All Finished *-*\n";
}
