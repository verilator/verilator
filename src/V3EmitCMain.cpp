// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Emit C++ for tree
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2024 by Wilson Snyder. This program is free software; you
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
        const string filename = v3Global.opt.makeDir() + "/" + topClassName() + "__main.cpp";
        newCFile(filename, false /*slow*/, true /*source*/);
        V3OutCFile cf{filename};
        m_ofp = &cf;

        // Not defining main_time/vl_time_stamp, so
        v3Global.opt.addCFlags("-DVL_TIME_CONTEXT");  // On MSVC++ anyways

        // Optional main top name argument, with empty string replacement
        string topArg;
        string topName = v3Global.opt.mainTopName();
        if (!topName.empty()) {
            if (topName == "-") topName = "";
            topArg = ", \"" + topName + "\"";
        }

        // Heavily commented output, as users are likely to look at or copy this code
        ofp()->putsHeader();
        puts("// DESCRIPTION: main() calling loop, created with Verilator --main\n");
        puts("\n");

        puts("#include \"verilated.h\"\n");
        puts("#include \"" + topClassName() + ".h\"\n");

        puts("\n//======================\n\n");

        puts("int main(int argc, char** argv, char**) {\n");
        puts("// Setup context, defaults, and parse command line\n");
        puts("Verilated::debug(0);\n");
        puts("const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};\n");
        if (v3Global.opt.trace()) puts("contextp->traceEverOn(true);\n");
        puts("contextp->commandArgs(argc, argv);\n");
        puts("\n");

        puts("// Construct the Verilated model, from Vtop.h generated from Verilating\n");
        puts("const std::unique_ptr<" + topClassName() + "> topp{new " + topClassName()
             + "{contextp.get()" + topArg + "}};\n");
        puts("\n");

        puts("// Simulate until $finish\n");
        puts("while (!contextp->gotFinish()) {\n");
        puts(/**/ "// Evaluate model\n");
        puts(/**/ "topp->eval();\n");
        puts(/**/ "// Advance time\n");
        if (v3Global.rootp()->delaySchedulerp()) {
            puts("if (!topp->eventsPending()) break;\n");
            puts("contextp->time(topp->nextTimeSlot());\n");
        } else {
            puts("contextp->timeInc(1);\n");
        }

        puts("}\n");
        puts("\n");

        puts("if (!contextp->gotFinish()) {\n");
        puts(/**/ "VL_DEBUG_IF(VL_PRINTF(\"+ Exiting without $finish; no events left\\n\"););\n");
        puts("}\n");
        puts("\n");

        puts("// Final model cleanup\n");
        puts("topp->final();\n");
        puts("return 0;\n");
        puts("}\n");

        m_ofp = nullptr;
    }
};

//######################################################################
// EmitC class functions

void V3EmitCMain::emit() {
    UINFO(2, __FUNCTION__ << ": " << endl);
    { EmitCMain visitor; }
}
