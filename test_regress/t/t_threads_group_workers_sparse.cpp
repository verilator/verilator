// -*- mode: C++; c-file-style: "cc-mode" -*-
// DESCRIPTION: Verilator: Verify that a pinned group runs on the pool worker.
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Michael Bedford Taylor
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

#include "verilated.h"

#include "Vt_threads_group_workers_sparse.h"

#include <cstdio>
#include <thread>

static std::thread::id caller;
static unsigned onCaller = 0;
static unsigned onPool = 0;

extern "C" void record_worker() {
    if (std::this_thread::get_id() == caller) {
        ++onCaller;
    } else {
        ++onPool;
    }
}

int main(int argc, char** argv) {
    caller = std::this_thread::get_id();
    VerilatedContext context;
    context.commandArgs(argc, argv);
    context.threads(2);
    Vt_threads_group_workers_sparse model{&context};
    for (unsigned cycle = 0; cycle < 20; ++cycle) {
        model.clk = 0;
        model.eval();
        model.clk = 1;
        model.eval();
    }
    model.final();
    if (onCaller != 0 || onPool != 20) {
        std::printf("Unexpected placement: caller=%u pool=%u\n", onCaller, onPool);
        return 1;
    }
    std::puts("*-* All Finished *-*");
    return 0;
}
