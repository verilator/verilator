// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Emit structural (primitive-netlist) Verilog
//
// A direct in-memory port of the System-Verilog-suite structural
// decompiler flow (sv_parse -> sv_transform -> sv_tran_struct -> sv_gen /
// sv_gen_xilinx_rtl).  Runs at the --json-only point of the pipeline and
// walks the elaborated AST once, streaming one structural module to the
// output file at a time, so no JSON tree is ever materialised on disk or
// re-parsed by a downstream tool.
//
//*************************************************************************
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#ifndef VERILATOR_V3EMITSTRUCT_H_
#define VERILATOR_V3EMITSTRUCT_H_

#include "config_build.h"
#include "verilatedos.h"

#include <string>

class AstNodeModule;

//============================================================================

class V3EmitStruct final {
public:
    // Emit the whole netlist as structural Verilog to filename
    static void emit(const std::string& filename) VL_MT_DISABLED;
    // The same text, in memory (for the in-process mapper)
    static std::string emitString() VL_MT_DISABLED;
    // --struct-only-blackbox names match the module's original (pre-parameter
    // specialisation) name as well as its specialised name
    static bool isBlackbox(const AstNodeModule* modp) VL_MT_DISABLED;
    // The name an instance of modp should carry in the output
    static std::string cellTypeName(const AstNodeModule* modp) VL_MT_DISABLED;
};

#endif  // Guard
