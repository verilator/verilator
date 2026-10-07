// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "verilated_cov.h"

// Allow access to the eval message queue to test deferred fatal messages.
#define VERILATOR_VERILATED_CPP_
#include "verilated_imp.h"

int main(int argc, char** argv) {
    VerilatedContext context;
    context.commandArgs(argc, argv);
    // A nonzero task ID defers fatal messages until end-of-eval, as in a worker task.
    Verilated::mtaskId(context.commandArgsPlusMatch("defer")[0] ? 1 : 0);
    const char* const keyp = context.commandArgsPlusMatch("key=");
    if (keyp[0]) {
        // Re-entering insertion requires the fatal path to release the coverage mutex and
        // discard its pending item before running callbacks. zero() also checks the mutex.
        Verilated::addExitCb(
            [](void* datap) {
                VerilatedCovContext* const covp = static_cast<VerilatedCovContext*>(datap);
                static uint32_t count = 0;
                VL_COVER_INSERT(covp, "top", &count, "comment", "exit callback");
                covp->zero();
                VL_PRINTF("Coverage exit callback completed\n");
            },
            context.coveragep());
        uint32_t count = 0;
        VL_COVER_INSERT(context.coveragep(), "top", &count, keyp + 5, "value");
    } else {
        // Opening a directory as a file fails without relying on permissions or name limits.
        context.coverageFilename(".");
        // The callback retries the failing write, so error reporting must release the coverage
        // mutex before invoking it. Both failures must be reported without hanging.
        Verilated::addExitCb(
            [](void* datap) { static_cast<VerilatedCovContext*>(datap)->write(); },
            context.coveragep());
        context.coveragep()->write();
    }

    VerilatedEvalMsgQueue evalMsgQ;
    Verilated::endOfThreadMTask(&evalMsgQ);
    Verilated::endOfEval(&evalMsgQ);
    return 0;
}
