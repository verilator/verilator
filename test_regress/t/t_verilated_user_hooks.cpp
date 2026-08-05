// -*- mode: C++; c-file-style: "cc-mode" -*-
// DESCRIPTION: Verilator: User replaced vl_finish/vl_stop/vl_fatal/vl_warn test
//*************************************************************************
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include VM_PREFIX_INCLUDE

#include <memory>

// This requires the above. Comment prevents clang-format moving it
#include "TestCheck.h"

int errors = 0;

int finishCalls = 0;
int stopCalls = 0;
int fatalCalls = 0;
int warnCalls = 0;

// An embedder replaces these four and keeps control of the process
void vl_finish(const char* filename, int linenum, const char* hier) { ++finishCalls; }

void vl_stop(const char* filename, int linenum, const char* hier) {
    ++stopCalls;
    if (Verilated::threadContextp()->fatalOnError())
        vl_fatal(filename, linenum, hier, "Verilog $stop");
}

void vl_fatal(const char* filename, int linenum, const char* hier, const char* msg) {
    ++fatalCalls;
}

void vl_warn(const char* filename, int linenum, const char* hier, const char* msg) { ++warnCalls; }

static void tick(VM_PREFIX* topp, int step) {
    topp->step = step;
    topp->clk = 0;
    topp->eval();
    topp->clk = 1;
    topp->eval();
}

int main(int argc, char** argv) {
    VerilatedContext context;
    Verilated::threadContextp(&context);
    context.commandArgs(argc, argv);
    std::unique_ptr<VM_PREFIX> topp{new VM_PREFIX{&context}};

    tick(topp.get(), 1);
    TEST_CHECK_EQ(warnCalls, 1);

    tick(topp.get(), 2);
    TEST_CHECK_EQ(stopCalls, 1);
    TEST_CHECK_EQ(fatalCalls, 1);
    TEST_CHECK_EQ(context.errorCount(), 1);

    tick(topp.get(), 3);
    TEST_CHECK_EQ(stopCalls, 2);
    TEST_CHECK_EQ(fatalCalls, 2);
    TEST_CHECK_EQ(context.errorCount(), 2);

    tick(topp.get(), 4);
    TEST_CHECK_EQ(finishCalls, 1);

    TEST_CHECK_EQ(warnCalls, 1);
    topp->final();
    return errors ? 10 : 0;
}
