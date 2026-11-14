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

// Access the eval message queue to exercise immediate and deferred fatal callbacks.
#define VERILATOR_VERILATED_CPP_
#include "verilated_imp.h"

int main(int argc, char** argv) {
    VerilatedContext context;
    const std::string mode = argc > 1 ? argv[1] : "normal";
    if (mode == "normal") {
        // Appending before commandArgs(), replacing, and clearing must all set loaded state.
        const char* first[] = {"", "+first"};
        context.commandArgsAdd(2, first);
        assert(std::strcmp(context.commandArgsPlusMatch("first"), "+first") == 0);
        const char* second[] = {"test", "+second"};
        context.commandArgs(2, second);
        assert(!context.commandArgsPlusMatch("first")[0]);
        assert(std::strcmp(context.commandArgsPlusMatch("second"), "+second") == 0);
        context.commandArgsAdd(2, first);
        assert(std::strcmp(context.commandArgsPlusMatch("first"), "+first") == 0);
        assert(std::strcmp(context.commandArgsPlusMatch("second"), "+second") == 0);
        context.commandArgs(0, second);
        assert(!context.commandArgsPlusMatch("second")[0]);
        VL_PRINTF("*-* All Finished *-*\n");
        return 0;
    }

    Verilated::mtaskId(argc > 2 ? 1 : 0);
    Verilated::addExitCb(
        [](void* datap) {
            VerilatedContext* const contextp = static_cast<VerilatedContext*>(datap);
            VL_PRINTF("Arguments in exit callback: '%s'\n",
                      contextp->commandArgsPlusMatch("after"));
        },
        &context);
    if (mode == "missing") {
        // Mark the missing arguments as reported before callbacks query them again.
        context.commandArgsPlusMatch("after");
    } else {
        // The callback must see arguments after the failing option, with either API.
        const char* args[] = {"test", "+verilator+seed+bad", "+after"};
        if (mode == "add") {
            context.commandArgsAdd(3, args);
        } else {
            context.commandArgs(3, args);
        }
    }
    VerilatedEvalMsgQueue queue;
    Verilated::endOfThreadMTask(&queue);
    Verilated::endOfEval(&queue);
    return 0;
}
