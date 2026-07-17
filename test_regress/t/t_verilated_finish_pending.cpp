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

int fatalCalls = 0;

// Non-exiting vl_fatal override
void vl_fatal(const char* filename, int linenum, const char* hier, const char* msg) {
    ++fatalCalls;
    TEST_CHECK_EQ(Verilated::threadContextp()->finishPending(), true);
}

int main(int argc, char** argv) {
    VerilatedContext context;
    Verilated::threadContextp(&context);
    context.commandArgs(argc, argv);
    std::unique_ptr<VM_PREFIX> topp{new VM_PREFIX{&context}};

    // An ignored maybe-stop reserves its error count without pending termination.
    context.errorLimit(3);
    context.errorCount(0);
    vl_stop_maybe(__FILE__, __LINE__, "TOP.t", true);
    TEST_CHECK_EQ(context.errorCount(), 1);
    TEST_CHECK_EQ(context.finishPending(), false);
    vl_stop_maybe(__FILE__, __LINE__, "TOP.t", true);
    TEST_CHECK_EQ(context.errorCount(), 2);
    TEST_CHECK_EQ(context.finishPending(), false);

    bool firstIgnored = true;
    TEST_CHECK_EQ(context.errorCountIncMaybeStop(true, firstIgnored), true);
    TEST_CHECK_EQ(firstIgnored, false);
    TEST_CHECK_EQ(context.errorCount(), 3);
    context.errorCount(0);
    TEST_CHECK_EQ(context.errorCountIncMaybeStop(false, firstIgnored), true);
    TEST_CHECK_EQ(firstIgnored, false);
    TEST_CHECK_EQ(context.errorCount(), 1);

    // The first pending request owns the timestamp until all requests drain.
    context.gotFinish(false);
    context.time(10);
    context.finishPendingInc();
    context.time(20);
    context.finishPendingInc();
    TEST_CHECK_EQ(context.finishPending(), true);
    TEST_CHECK_EQ(context.finishPendingTime(), 10);
    context.finishPendingDec();
    TEST_CHECK_EQ(context.finishPending(), true);
    TEST_CHECK_EQ(context.finishPendingTime(), 10);
    context.finishPendingDec();
    TEST_CHECK_EQ(context.finishPending(), false);
    TEST_CHECK_EQ(context.finishPendingTime(), 20);

    // Clearing gotFinish invalidates a stale timestamp for context reuse.
    context.time(30);
    context.finishPendingInc();
    context.gotFinish(true);
    context.finishPendingDec();
    TEST_CHECK_EQ(context.finishPending(), true);
    TEST_CHECK_EQ(context.finishPendingTime(), 30);
    context.time(40);
    context.gotFinish(false);
    TEST_CHECK_EQ(context.finishPending(), false);
    TEST_CHECK_EQ(context.finishPendingTime(), 40);

    // A posted fatal request holds finishPending until its handler returns.
    context.time(50);
    VL_FATAL_MT(__FILE__, __LINE__, "TOP.t", "test fatal");
    TEST_CHECK_EQ(fatalCalls, 1);
    TEST_CHECK_EQ(context.finishPending(), false);

    // A worker-queued fatal stays pending until end-of-eval runs its handler.
    context.time(60);
    {
        VerilatedEvalMsgQueue evalMsgQ;
        Verilated::mtaskId(1);
        VL_FATAL_MT(__FILE__, __LINE__, "TOP.t", "queued fatal");
        TEST_CHECK_EQ(fatalCalls, 1);
        TEST_CHECK_EQ(context.finishPending(), true);
        TEST_CHECK_EQ(context.finishPendingTime(), 60);
        Verilated::endOfThreadMTask(&evalMsgQ);
        TEST_CHECK_EQ(fatalCalls, 1);
        TEST_CHECK_EQ(context.finishPending(), true);
        Verilated::endOfEval(&evalMsgQ);
        TEST_CHECK_EQ(fatalCalls, 2);
        TEST_CHECK_EQ(context.finishPending(), false);
    }

    // Clearing gotFinish keeps the timestamp while a request is still pending.
    context.time(70);
    context.finishPendingInc();
    context.gotFinish(false);
    context.time(80);
    TEST_CHECK_EQ(context.finishPending(), true);
    TEST_CHECK_EQ(context.finishPendingTime(), 70);
    context.finishPendingDec();
    TEST_CHECK_EQ(context.finishPending(), false);
    TEST_CHECK_EQ(context.finishPendingTime(), 80);

    topp->final();
    return errors ? 10 : 0;
}
