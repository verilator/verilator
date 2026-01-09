// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// Code available from: https://verilator.org
//
// Copyright 2003-2026 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
// DESCRIPTION: Verilator: Emit C++ for precompiled header include
//

#include "V3PchAstMT.h"

#include "V3EmitC.h"
#include "V3EmitCBase.h"
#include "V3File.h"

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// Precompiled header emitter

class EmitCPch final : public EmitCBaseVisitorConst {
public:
    // METHODS

    void emitPch() {
        openNewOutputHeaderFile(EmitCUtil::pchClassName(), "Precompiled header");
        puts("//\n");
        puts("// Internal details; most user sources do not need this header,\n");
        puts("// unless using verilator public meta comments.\n");
        puts("// Suggest use " + EmitCUtil::topClassName() + ".h instead.\n");

        ofp()->putsGuard();

        puts("\n");
        puts("// GCC and Clang only will precompile headers (PCH) for the first header.\n");
        puts("// So, make sure this is the one and only PCH.\n");
        puts("// If multiple module's includes are needed, use individual includes.\n");
        puts("#ifdef VL_PCH_INCLUDED\n");
        puts("# error \"Including multiple precompiled header files\"\n");
        puts("#endif\n");
        puts("#define VL_PCH_INCLUDED\n");

        puts("\n");
        puts("\n#include \"verilated.h\"\n");
        if (v3Global.dpi()) puts("#include \"verilated_dpi.h\"\n");

        puts("\n");
        puts("#include \"" + EmitCUtil::symClassName() + ".h\"\n");
        puts("#include \"" + EmitCUtil::topClassName() + ".h\"\n");

        puts("\n// Additional include files added using '--compiler-include'\n");
        for (const string& filename : v3Global.opt.compilerIncludes()) {
            puts("#include \"" + filename + "\"\n");
        }

        ofp()->putsEndGuard();

        closeOutputFile();
    }

    // VISITOR
    void visit(AstNode* nodep) override { nodep->v3fatalSrc("Unused"); }

public:
    explicit EmitCPch() { emitPch(); }
};

//######################################################################
// EmitC static functions

void V3EmitC::emitcPch() {
    UINFO(2, __FUNCTION__ << ":");
    EmitCPch{};
}
