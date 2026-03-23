// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Emit C++ for tree
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2003-2026 Wilson Snyder
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
        if (v3Global.opt.vpi()) puts("#include \"verilated_vpi.h\"\n");
        puts("#include \"" + EmitCUtil::topClassName() + ".h\"\n");
        if (v3Global.opt.debugRuntimeTimeout()) {
            puts("\n");
            puts("#include <csignal>\n");
        }
        puts("\n");

        if (v3Global.opt.vpi()) {
            puts("// User VPI code adds to this array to get startup main() callbacks\n");
            puts("extern \"C\" void (*vlog_startup_routines[])() VL_ATTR_WEAK;\n");
            puts("\n");
        }

        puts("//======================\n\n");

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

        if (v3Global.opt.vpi()) {
            puts("// Hook VPI startup routines and invoke callback\n");
            puts("if (vlog_startup_routines) {\n");
            puts(/**/ "for (auto routinep = &vlog_startup_routines[0]; *routinep; routinep++)"
                      " (*routinep)();\n");
            puts("}\n");
            puts("VerilatedVpi::callCbs(cbStartOfSimulation);\n");
            puts("\n");
        }

        puts("// Simulate until $finish\n");
        puts("while (VL_LIKELY(!contextp->gotFinish())) {\n");
        if (v3Global.opt.vpi()) {
            puts(/**/ "// VPI callbacks\n");
            puts(/**/ "VerilatedVpi::callTimedCbs();\n");
            puts(/**/ "VerilatedVpi::callCbs(cbNextSimTime);\n");  // Before next event queue
            puts(/**/ "VerilatedVpi::callCbs(cbAtStartOfSimTime);\n");  // Before time queue
        }
        puts(/**/ "// Evaluate model\n");
        puts(/**/ "topp->eval();\n");
        if (v3Global.opt.vpi()) {
            puts(/**/ "// VPI callbacks\n");
            puts(/**/ "VerilatedVpi::callValueCbs();\n");
            puts(/**/ "VerilatedVpi::callCbs(cbAtEndOfSimTime);\n");  // After nonblocking events
            puts(/**/ "VerilatedVpi::callCbs(cbReadWriteSynch);\n");  // After a specified time
            puts(/**/ "VerilatedVpi::callCbs(cbReadOnlySynch);\n");  // After cbReadWriteSynch
        }
        puts(/**/ "// Advance time\n");
        if (v3Global.rootp()->delaySchedulerp() || v3Global.opt.timing()) {
            puts("if (!topp->eventsPending()) break;\n");
        }
        const std::string nextSlot = v3Global.rootp()->delaySchedulerp() ? "topp->nextTimeSlot()"
                                                                         : "contextp->time() + 1";
        if (v3Global.opt.vpi()) {
            puts("contextp->time(std::min("s + nextSlot + ", VerilatedVpi::cbNextDeadline()));\n");
        } else {
            puts("contextp->time("s + nextSlot + ");\n");
        }

        puts("}\n");
        puts("\n");

        puts("if (VL_LIKELY(!contextp->gotFinish())) {\n");
        puts(/**/ "VL_DEBUG_IF(VL_PRINTF(\"+ Exiting without $finish; no events left\\n\"););\n");
        puts("}\n");
        puts("\n");

        puts("// Execute 'final' processes\n");
        puts("topp->final();\n");
        if (v3Global.opt.vpi()) puts("VerilatedVpi::callCbs(cbEndOfSimulation);\n");
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
