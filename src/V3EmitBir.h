// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Emit the System-Verilog-suite Behavioral IR
//
// A C++ port of the suite's verilator_to_behavioral.ml front end that
// walks Verilator's elaborated AST directly (at the --json-only cut point)
// and streams the BIR as JSON, instead of dumping the whole tree to a
// .tree.json for the OCaml side to rebuild.  Loaded on the suite side by
// bir_json_load.ml (frontend name "verilator-bir").
//
//*************************************************************************
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#ifndef VERILATOR_V3EMITBIR_H_
#define VERILATOR_V3EMITBIR_H_

#include "config_build.h"
#include "verilatedos.h"

#include <string>

//============================================================================

class V3EmitBir final {
public:
    static void emit(const std::string& filename) VL_MT_DISABLED;
};

#endif  // Guard
