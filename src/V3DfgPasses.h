// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Passes over DfgGraph
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2025 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#ifndef VERILATOR_V3DFGPASSES_H_
#define VERILATOR_V3DFGPASSES_H_

#include "config_build.h"
#include "verilatedos.h"

#include "V3DfgContext.h"

class AstModule;
class DfgGraph;

namespace V3DfgPasses {
//===========================================================================
// Top level entry points
//===========================================================================

// Construct a DfGGraph representing the combinational logic in the given AstModule. The logic
// that is represented by the graph is removed from the given AstModule. Returns the
// constructed DfgGraph.
DfgGraph* astToDfg(AstModule&, V3DfgContext&) VL_MT_DISABLED;

// Same as above, but for the entire netlist, after V3Scope
DfgGraph* astToDfg(AstNetlist&, V3DfgContext&) VL_MT_DISABLED;

// Attempt to make the given cyclic graph into an acyclic, or "less cyclic"
// equivalent. If the returned pointer is null, then no improvement was
// possible on the input graph. Otherwise the returned graph is an improvement
// on the input graph, with at least some cycles eliminated. The returned
// graph is always independent of the original. If an imporoved graph is
// returned, then the returned 'bool' flag indicated if the returned graph is
// acyclic (flag 'true'), or still cyclic (flag 'false').
std::pair<std::unique_ptr<DfgGraph>, bool>  //
breakCycles(const DfgGraph&, V3DfgContext&) VL_MT_DISABLED;

// Optimize the given DfgGraph
void optimize(DfgGraph&, V3DfgContext&) VL_MT_DISABLED;

// Convert DfgGraph back into Ast, and insert converted graph back into the Ast.
void dfgToAst(DfgGraph&, V3DfgContext&) VL_MT_DISABLED;

//===========================================================================
// Intermediate/internal operations
//===========================================================================

// Construct binary to oneHot decoders
void binToOneHot(DfgGraph&, V3DfgBinToOneHotContext&) VL_MT_DISABLED;
// Common subexpression elimination
void cse(DfgGraph&, V3DfgCseContext&) VL_MT_DISABLED;
// Inline fully driven variables
void inlineVars(DfgGraph&) VL_MT_DISABLED;
// Peephole optimizations
void peephole(DfgGraph&, V3DfgPeepholeContext&) VL_MT_DISABLED;
// Regularize graph. This must be run before converting back to Ast.
void regularize(DfgGraph&, V3DfgRegularizeContext&) VL_MT_DISABLED;
// Remove unused nodes
void removeUnused(DfgGraph&) VL_MT_DISABLED;
// Eliminate (remove or replace) redundant variables. Also removes resulting unused logic.
void eliminateVars(DfgGraph&, V3DfgEliminateVarsContext&) VL_MT_DISABLED;

}  // namespace V3DfgPasses

#endif
