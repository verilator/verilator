// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Emit C++ for tree
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2020 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3Global.h"
#include "V3EmitC.h"
#include "V3EmitCBase.h"
#include "V3EmitCMain.h"

#include <map>

//######################################################################

class EmitCMain final : EmitCBaseVisitor {
    // METHODS

    // VISITORS
    // This visitor doesn't really iterate, but exist to appease base class
    virtual void visit(AstNode* nodep) override { iterateChildren(nodep); }  // LCOV_EXCL_LINE

public:
    // CONSTRUCTORS
    explicit EmitCMain(AstNetlist*) { emitInt(); }

private:
    // MAIN METHOD
    void emitInt() {
        string filename = v3Global.opt.makeDir() + "/" + topClassName() + "__main.cpp";
        newCFile(filename, false /*slow*/, true /*source*/);
        V3OutCFile cf(filename);
        m_ofp = &cf;

        // Heavly commented output, as users are likely to look at or copy this code
        ofp()->putsHeader();
        puts("// DESCRIPTION: main() calling loop, created with Verilator --main\n");
        puts("\n");

        puts("#include \"verilated.h\"\n");
        puts("#include \"" + topClassName() + ".h\"\n");

        puts("\n//======================\n\n");

        puts(topClassName() + "* topp;\n");
        puts("\n");
        puts("// Requires -DVL_TIME_STAMP64\n");
        v3Global.opt.addCFlags("-DVL_TIME_STAMP64");
        puts("vluint64_t main_time = 0;\n");
        puts("vluint64_t vl_time_stamp64() { return main_time; }\n");
        puts("\n");

        puts("int main(int argc, char** argv, char**) {\n");
        puts("// Setup defaults and parse command line\n");
        puts("Verilated::debug(0);\n");
        puts("Verilated::commandArgs(argc, argv);\n");
        puts("// Construct the Verilated model, from Vtop.h generated from Verilating\n");
        puts("topp = new " + topClassName() + "(\"top\");\n");
        puts("// Evaluate initials\n");
        puts("topp->eval();  // Evaluate\n");

        puts("// Simulate until $finish\n");
        puts("while (!Verilated::gotFinish()) {\n");
        puts(/**/ "// Evaluate model\n");
        puts(/**/ "topp->eval();\n");
        puts(/**/ "// Advance time\n");
        puts(/**/ "++main_time;\n");
        puts("}\n");
        puts("\n");

        puts("if (!Verilated::gotFinish()) {\n");
        puts(/**/ "VL_DEBUG_IF(VL_PRINTF(\"+ Exiting without $finish; no events left\\n\"););\n");
        puts("}\n");
        puts("\n");

        puts("// Final model cleanup\n");
        puts("topp->final();\n");
        puts("VL_DO_DANGLING(delete topp, topp);\n");
        puts("exit(0);\n");
        puts("}\n");
    }
};

//######################################################################
// EmitC class functions

void V3EmitCMain::emit() {
    UINFO(2, __FUNCTION__ << ": " << endl);
    EmitCMain(v3Global.rootp());
}
