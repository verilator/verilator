// -*- mode: C++; c-file-style: "cc-mode" -*-
// DESCRIPTION: Verilator: RepCut clocked DPI capture ordering oracle
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026-2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

#include "verilated.h"

#include "Vt_repcut_dpi_capture.h"
#include "Vt_repcut_dpi_capture__Dpi.h"

#include <cstdlib>
#include <iostream>
#include <thread>

static QData expected[3] = {};
static unsigned calls[3] = {};
static std::thread::id caller;

static void check(bool condition) {
    if (!condition) std::abort();
}

extern "C" void repcut_observe(unsigned lane, unsigned long long value) {
    check(std::this_thread::get_id() == caller && lane < 3);
    if (value != expected[lane]) {
        std::cerr << "Stale DPI capture: lane " << lane << " expected " << expected[lane]
                  << " observed " << value << '\n';
        std::abort();
    }
    ++calls[lane];
}

int main(int argc, char** argv) {
    VerilatedContext context;
    context.commandArgs(argc, argv);
    context.threads(REPCUT_TEST_THREADS);
    context.randReset(0);
    caller = std::this_thread::get_id();
    Vt_repcut_dpi_capture model{&context};
    model.clk = 0;
    model.reset = 1;
    model.enable = 0;
    model.delta = 0;
    model.clk_b = 0;
    model.gate = 0;
    model.async_reset = 0;
    bool previousClock = false;
    bool previousGenerated = false;
    bool previousReset = false;
    QData cross = 0;
    unsigned asyncCalls = 0;
    const auto eval = [&]() {
        const bool generated = model.clk_b && model.gate;
        const bool triggered
            = (generated && !previousGenerated) || (model.async_reset && !previousReset);
        const QData next = model.async_reset ? 0
                                             : (expected[2] + model.delta + expected[0] + 3)
                                                   & 0x7fffffffffffffffULL;
        if (previousClock && !model.clk_b) cross = expected[2];
        model.eval();
        if (triggered) {
            expected[2] = next;
            ++asyncCalls;
        }
        check(model.async_q == expected[2] && model.cross_q == cross && calls[2] == asyncCalls);
        previousClock = model.clk_b;
        previousGenerated = generated;
        previousReset = model.async_reset;
    };
    eval();
    check(calls[0] == 0 && calls[1] == 0 && calls[2] == 0);
    unsigned negativeCalls = 0;
    for (unsigned step = 0; step < 257; ++step) {
        model.reset = step % 47 == 0;
        model.enable = step % 3 != 0;
        model.delta = (QData{step} << 51) ^ (QData{step + 7} * 0x193acaU);
        model.clk_b = step % 3 != 0;
        model.gate = step % 5 != 0;
        model.async_reset = step % 23 == 7;
        model.clk = 1;
        eval();
        expected[0] = model.reset ? 0 : expected[0] + 1;
        check(model.q == expected[0] && model.neg_q == expected[1]);
        check(calls[0] == step + 1 && calls[1] == negativeCalls);
        // Changing a guard without a clock edge must not invoke a callback.
        model.enable = !model.enable;
        eval();
        check(calls[0] == step + 1 && calls[1] == negativeCalls);
        // Exercise generated edges, reset-only edges and simultaneous domains.
        model.clk_b = step % 7 < 4;
        model.gate = !model.gate;
        model.async_reset = step % 19 == 3;
        model.clk = 0;
        eval();
        if (model.enable) ++negativeCalls;
        expected[1] = model.reset ? 0 : (expected[1] + model.delta + 1) & 0x7fffffffffffffffULL;
        check(model.q == expected[0] && model.neg_q == expected[1]);
        check(calls[0] == step + 1 && calls[1] == negativeCalls);
    }
    check(asyncCalls > 100);
    model.final();
    std::cout << "*-* All Finished *-*\n";
}
