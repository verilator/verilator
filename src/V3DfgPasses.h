// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Passes over DfgGraph
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
std::unique_ptr<DfgGraph> astToDfg(AstModule&, V3DfgContext&) VL_MT_DISABLED;

// Same as above, but for the entire netlist, after V3Scope
std::unique_ptr<DfgGraph> astToDfg(AstNetlist&, V3DfgContext&) VL_MT_DISABLED;

// Synthesize DfgLogic vertices into primitive operations.
// Removes all DfgLogic (even those that were not synthesized).
void synthesize(DfgGraph&, V3DfgContext&) VL_MT_DISABLED;

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
// Populates the given DfgUserMap for all vertext to:
// - 0, if the vertex is not part of a non-trivial strongly connected component
//   and is not part of a self-loop. That is: the Vertex is not part of any cycle.
// - N, if the vertex is part of a non-trivial strongly conneced component or self-loop N.
//   That is: each set of vertices that are reachable from each other will have the same
//   non-zero value assigned.
// Returns the number of non-trivial SCCs (distinct cycles)
uint32_t colorStronglyConnectedComponents(const DfgGraph&, DfgUserMap<uint64_t>&) VL_MT_DISABLED;
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
// Check all types are consistent. This will not return if there is a type error.
void typeCheck(const DfgGraph&) VL_MT_DISABLED;

}  // namespace V3DfgPasses

#endif
