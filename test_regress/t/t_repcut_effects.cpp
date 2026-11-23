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
#if VM_COVERAGE
#include "verilated_cov.h"
#endif

#include "Vt_repcut_effects.h"
#include "repcut_effect_pending.h"

#include <cstdlib>
#include <iostream>
#include <string>

int main(int argc, char** argv) {
    VerilatedContext context;
    context.commandArgs(argc, argv);
    context.threads(2);
    context.randReset(0);
    context.fatalOnError(false);
    Vt_repcut_effects model{&context};
    model.fd = 0x80000001;
    unsigned previous = 0;
    uint64_t previousTime = 0;
    const auto step = [&]() {
        uint32_t chain = model.data ^ 0x4719235U;
        for (unsigned i = 0; i < 16; ++i) {
            chain = ((chain << 1) ^ (chain + model.data + i)) & 0x7fffffffU;
        }
#ifdef REPCUT_EFFECT_MULTI
        if (!model.clk && model.enable && context.time()) {
            std::cout << "EXPECT N " << chain << ' ' << previous << '\n';
        }
#endif
        if (model.clk && model.enable) {
            std::cout << "EXPECT A " << model.data << ' ' << previous << '\n';
            if (model.data & 1) std::cout << "EXPECT B " << ((previous + 1) & 0x7fff) << '\n';
            std::cout << "EXPECT F " << previous << '\n';
            if (chain & 4) std::cout << "EXPECT C " << chain << '\n';
#ifdef REPCUT_EFFECT_FALLBACK
            uint32_t local = 0;
            for (unsigned i = 0; i < 8; ++i) local ^= chain / (model.data | (1U << i) | 1U);
            std::cout << "EXPECT L " << local << '\n';
#endif
        }
        context.timeInc(1);
        model.eval();
        if (!checkEffectPending(model)) std::exit(8);
        if (model.clk) previousTime = context.time();
        if (model.edge_time != previousTime) std::exit(6);
        if (model.clk) previous = model.data;
        if (model.q != previous || model.result != (previous ^ model.data)) std::exit(1);
    };
    for (unsigned i = 0; i < 128; ++i) {
        model.clk = i & 1;
        model.enable = (i % 5) < 2;
        model.data = (i * 193 + 11) & 0x7fff;
        step();
        if (context.gotError() || context.gotFinish()) return 2;
    }
    model.enable = 0;
    model.clk = 0;
    step();
    if (argc > 1 && std::string{argv[1]} == "+finish") {
        model.done = 1;
        model.clk = 1;
        step();
        if (!context.gotFinish() || context.gotError()) return 3;
    } else {
        model.bad = 1;
        context.assertOn(false);
        model.clk = 1;
        step();
        if (context.gotError()) return 4;
        model.clk = 0;
        step();
        context.assertOn(true);
        model.clk = 1;
        step();
        if (!context.gotError() || !context.gotFinish()) return 5;
    }
    model.final();
#if VM_COVERAGE
    if (argc != 3) return 7;
    context.coveragep()->write(argv[2]);
#endif
    std::cout << "*-* All Finished *-*\n";
}
