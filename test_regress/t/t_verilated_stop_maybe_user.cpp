// -*- mode: C++; c-file-style: "cc-mode" -*-
// DESCRIPTION: Verilator: Custom stop-maybe hook pending termination test
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

// Workaround to include verilated_imp.h, needed to drive the eval message queue
#define VERILATOR_VERILATED_CPP_
#include "verilated_imp.h"

#include <memory>

// These require the above. Comment prevents clang-format moving them
#include "TestCheck.h"

int errors = 0;

int stopMaybeCalls = 0;

// Non-terminating vl_stop_maybe override; ignores every maybe-stop
void vl_stop_maybe(const char* filename, int linenum, const char* hier, bool maybe) {
    ++stopMaybeCalls;
    TEST_CHECK_EQ(Verilated::threadContextp()->finishPending(), !maybe);
}

int main(int argc, char** argv) {
    VerilatedContext context;
    Verilated::threadContextp(&context);
    context.commandArgs(argc, argv);
    std::unique_ptr<VM_PREFIX> topp{new VM_PREFIX{&context}};

    // An ignored worker maybe-stop must not gate same-slot assertion work.
    VerilatedEvalMsgQueue evalMsgQ;
    Verilated::mtaskId(1);
    VL_STOP_MT(__FILE__, __LINE__, "TOP.t", true);
    TEST_CHECK_EQ(stopMaybeCalls, 0);
    TEST_CHECK_EQ(context.finishPending(), false);
    Verilated::endOfThreadMTask(&evalMsgQ);
    Verilated::endOfEval(&evalMsgQ);
    TEST_CHECK_EQ(stopMaybeCalls, 1);
    TEST_CHECK_EQ(context.finishPending(), false);

    // A definite stop request holds pending until its handler runs.
    Verilated::mtaskId(1);
    VL_STOP_MT(__FILE__, __LINE__, "TOP.t", false);
    TEST_CHECK_EQ(stopMaybeCalls, 1);
    TEST_CHECK_EQ(context.finishPending(), true);
    Verilated::endOfThreadMTask(&evalMsgQ);
    Verilated::endOfEval(&evalMsgQ);
    TEST_CHECK_EQ(stopMaybeCalls, 2);
    TEST_CHECK_EQ(context.finishPending(), false);

    topp->final();
    return errors ? 10 : 0;
}
