// -*- mode: C++; c-file-style: "cc-mode" -*-
// DESCRIPTION: Verilator: VerilatedContext pending termination state test
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

int stopCalls = 0;
int fatalCalls = 0;

// Non-exiting overrides so a request can be observed after it ran
void vl_stop(const char* filename, int linenum, const char* hier) {
    ++stopCalls;
    TEST_CHECK_EQ(Verilated::threadContextp()->finishPending(), true);
}

void vl_fatal(const char* filename, int linenum, const char* hier, const char* msg) {
    ++fatalCalls;
    TEST_CHECK_EQ(Verilated::threadContextp()->finishPending(), true);
}

int main(int argc, char** argv) {
    VerilatedContext context;
    Verilated::threadContextp(&context);
    context.commandArgs(argc, argv);
    std::unique_ptr<VM_PREFIX> topp{new VM_PREFIX{&context}};

    // A maybe-stop under the error limit is ignored and marks nothing pending
    context.errorLimit(3);
    context.errorCount(0);
    VL_STOP_MT(__FILE__, __LINE__, "TOP.t");
    TEST_CHECK_EQ(context.errorCount(), 1);
    TEST_CHECK_EQ(stopCalls, 0);
    TEST_CHECK_EQ(context.finishPending(), false);
    VL_STOP_MT(__FILE__, __LINE__, "TOP.t");
    TEST_CHECK_EQ(context.errorCount(), 2);
    TEST_CHECK_EQ(stopCalls, 0);
    TEST_CHECK_EQ(context.finishPending(), false);

    // Reaching the limit stops, and a definite stop always stops
    VL_STOP_MT(__FILE__, __LINE__, "TOP.t");
    TEST_CHECK_EQ(context.errorCount(), 3);
    TEST_CHECK_EQ(stopCalls, 1);
    context.errorCount(0);
    VL_STOP_MT(__FILE__, __LINE__, "TOP.t", false);
    TEST_CHECK_EQ(context.errorCount(), 1);
    TEST_CHECK_EQ(stopCalls, 2);

    // A worker-queued stop is pending from the moment it is posted
    context.errorCount(0);
    context.time(10);
    {
        VerilatedEvalMsgQueue evalMsgQ;
        Verilated::mtaskId(1);
        VL_STOP_MT(__FILE__, __LINE__, "TOP.t", false);
        TEST_CHECK_EQ(stopCalls, 2);
        TEST_CHECK_EQ(context.finishPending(), true);
        TEST_CHECK_EQ(context.finishPendingTime(), 10);
        context.time(20);
        Verilated::endOfThreadMTask(&evalMsgQ);
        TEST_CHECK_EQ(stopCalls, 2);
        TEST_CHECK_EQ(context.finishPending(), true);
        TEST_CHECK_EQ(context.finishPendingTime(), 10);
        Verilated::endOfEval(&evalMsgQ);
        TEST_CHECK_EQ(stopCalls, 3);
        TEST_CHECK_EQ(context.finishPending(), false);
        TEST_CHECK_EQ(context.finishPendingTime(), 20);
    }

    // An ignored worker-queued maybe-stop must not gate same-slot work
    context.errorLimit(3);
    context.errorCount(0);
    {
        VerilatedEvalMsgQueue evalMsgQ;
        Verilated::mtaskId(1);
        VL_STOP_MT(__FILE__, __LINE__, "TOP.t");
        TEST_CHECK_EQ(context.errorCount(), 1);
        TEST_CHECK_EQ(context.finishPending(), false);
        Verilated::endOfThreadMTask(&evalMsgQ);
        Verilated::endOfEval(&evalMsgQ);
        TEST_CHECK_EQ(stopCalls, 3);
        TEST_CHECK_EQ(context.finishPending(), false);
    }

    // A worker-queued fatal stays pending until end-of-eval runs its handler
    context.time(30);
    {
        VerilatedEvalMsgQueue evalMsgQ;
        Verilated::mtaskId(1);
        VL_FATAL_MT(__FILE__, __LINE__, "TOP.t", "queued fatal");
        TEST_CHECK_EQ(fatalCalls, 0);
        TEST_CHECK_EQ(context.finishPending(), true);
        TEST_CHECK_EQ(context.finishPendingTime(), 30);
        Verilated::endOfThreadMTask(&evalMsgQ);
        Verilated::endOfEval(&evalMsgQ);
        TEST_CHECK_EQ(fatalCalls, 1);
        TEST_CHECK_EQ(context.finishPending(), false);
    }

    // The first pending request owns the timestamp until all requests drain
    context.time(40);
    context.finishPendingInc();
    context.time(50);
    context.finishPendingInc();
    TEST_CHECK_EQ(context.finishPendingTime(), 40);
    context.finishPendingDec();
    TEST_CHECK_EQ(context.finishPending(), true);
    TEST_CHECK_EQ(context.finishPendingTime(), 40);
    context.finishPendingDec();
    TEST_CHECK_EQ(context.finishPending(), false);
    TEST_CHECK_EQ(context.finishPendingTime(), 50);

    // A latched termination keeps its timestamp; clearing it releases both
    context.time(60);
    context.finishPendingInc();
    context.gotFinish(true);
    context.finishPendingDec();
    TEST_CHECK_EQ(context.finishPending(), true);
    TEST_CHECK_EQ(context.finishPendingTime(), 60);
    context.time(70);
    context.gotFinish(false);
    TEST_CHECK_EQ(context.finishPending(), false);
    TEST_CHECK_EQ(context.finishPendingTime(), 70);

    topp->final();
    return errors ? 10 : 0;
}
