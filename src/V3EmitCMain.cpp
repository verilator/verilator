// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Emit C++ for tree
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2026 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3EmitCMain.h"

#include "V3EmitC.h"
#include "V3EmitCBase.h"

#include <map>

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################

class EmitCMain final : EmitCBaseVisitorConst {
    // METHODS

    // VISITORS
    // This visitor doesn't really iterate, but exist to appease base class
    void visit(AstNode* nodep) override { iterateChildrenConst(nodep); }  // LCOV_EXCL_LINE

public:
    // CONSTRUCTORS
    EmitCMain() { emitInt(); }

private:
    // MAIN METHOD
    void emitInt() {
        // Not defining main_time/vl_time_stamp, so
        v3Global.opt.addCFlags("-DVL_TIME_CONTEXT");  // On MSVC++ anyways

        // Optional main top name argument, with empty string replacement
        string topName = v3Global.opt.mainTopName();
        if (topName == "-") topName = "";

        openNewOutputSourceFile(EmitCUtil::topClassName() + "__main", false, false,
                                "main() simulation loop, created with --main");
        puts("\n");

        // Heavily commented output, as users are likely to look at or copy this code

        puts("#include \"verilated.h\"\n");
        puts("#include \"" + EmitCUtil::topClassName() + ".h\"\n");
        if (v3Global.opt.debugRuntimeTimeout()) {
            puts("\n");
            puts("#include <csignal>\n");
        }

        puts("\n//======================\n\n");

        if (v3Global.opt.debugRuntimeTimeout()) {
            puts("void alarmHandler(int signum) {\n");
            puts("    VL_FATAL_MT(\"\", 0, \"\", \"Alarm signal received,"s
                 + " '--debug-runtime-timeout "s
                 + std::to_string(v3Global.opt.debugRuntimeTimeout()) + "' exceeded\\n\");\n");
            puts("}\n");
            puts("\n");
        }

        puts("int main(int argc, char** argv, char**) {\n");
        puts("// Setup context, defaults, and parse command line\n");
        puts("Verilated::debug(0);\n");
        puts("const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};\n");
        if (v3Global.opt.trace()) puts("contextp->traceEverOn(true);\n");
        puts("contextp->threads(" + std::to_string(v3Global.opt.threads()) + ");\n");
        puts("contextp->commandArgs(argc, argv);\n");
        puts("\n");

        if (v3Global.opt.debugRuntimeTimeout()) {
            puts("signal(SIGALRM, alarmHandler);\n");
            puts("alarm("s + std::to_string(v3Global.opt.debugRuntimeTimeout()) + ");\n");
            puts("\n");
        }

        puts("// Construct the Verilated model, from Vtop.h generated from Verilating\n");
        puts("const std::unique_ptr<" + EmitCUtil::topClassName() + "> topp{new "
             + EmitCUtil::topClassName() + "{contextp.get(), \"" + topName + "\"}};\n");
        puts("\n");

        puts("// Simulate until $finish\n");
        puts("while (VL_LIKELY(!contextp->gotFinish())) {\n");
        puts(/**/ "// Evaluate model\n");
        puts(/**/ "topp->eval();\n");
        puts(/**/ "// Advance time\n");
        if (v3Global.rootp()->delaySchedulerp() || v3Global.opt.timing()) {
            puts("if (!topp->eventsPending()) break;\n");
        }
        if (v3Global.rootp()->delaySchedulerp()) {
            puts("contextp->time(topp->nextTimeSlot());\n");
        } else {
            puts("contextp->timeInc(1);\n");
        }

        puts("}\n");
        puts("\n");

        puts("if (VL_LIKELY(!contextp->gotFinish())) {\n");
        puts(/**/ "VL_DEBUG_IF(VL_PRINTF(\"+ Exiting without $finish; no events left\\n\"););\n");
        puts("}\n");
        puts("\n");

        puts("// Execute 'final' processes\n");
        puts("topp->final();\n");
        puts("\n");

        if (v3Global.opt.coverage()) {
            puts("// Write coverage data (since Verilated with --coverage)\n");
            puts("contextp->coveragep()->write();\n");
            puts("\n");
        }

        puts("// Print statistical summary report\n");
        puts("contextp->statsPrintSummary();\n");
        puts("\n");

        puts("return 0;\n");
        puts("}\n");

        closeOutputFile();
    }
};

//######################################################################
// EmitC class functions

void V3EmitCMain::emit() {
    UINFO(2, __FUNCTION__ << ":");
    { EmitCMain visitor; }
}
