// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// Code available from: https://verilator.org
//
// Copyright 2003-2024 by Wilson Snyder. This program is free software; you
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

class EmitCPch final : EmitCBase {
public:
    // METHODS

    void emitPch() {
        // Generate the makefile
        V3OutCFile of{v3Global.opt.makeDir() + "/" + pchClassName() + ".h"};
        of.putsHeader();
        of.puts("// DESCRIPTION: Verilator output: Precompiled header\n");
        of.puts("//\n");
        of.puts("// Internal details; most user sources do not need this header,\n");
        of.puts("// unless using verilator public meta comments.\n");
        of.puts("// Suggest use " + topClassName() + ".h instead.\n");
        of.puts("\n");

        of.putsGuard();

        of.puts("\n");
        of.puts("// GCC and Clang only will precompile headers (PCH) for the first header.\n");
        of.puts("// So, make sure this is the one and only PCH.\n");
        of.puts("// If multiple module's includes are needed, use individual includes.\n");
        of.puts("#ifdef VL_PCH_INCLUDED\n");
        of.puts("# error \"Including multiple precompiled header files\"\n");
        of.puts("#endif\n");
        of.puts("#define VL_PCH_INCLUDED\n");

        of.puts("\n");
        of.puts("\n#include \"verilated.h\"\n");
        if (v3Global.dpi()) of.puts("#include \"verilated_dpi.h\"\n");

        of.puts("\n");
        of.puts("#include \"" + symClassName() + ".h\"\n");
        of.puts("#include \"" + topClassName() + ".h\"\n");

        of.putsEndGuard();
    }

public:
    explicit EmitCPch() { emitPch(); }
};

//######################################################################
// EmitC static functions

void V3EmitC::emitcPch() {
    UINFO(2, __FUNCTION__ << ": " << endl);
    EmitCPch{};
}
