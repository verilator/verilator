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

#include "V3DfgPatternStats.h"
#include "V3DfgPeephole.h"

class AstModule;
class DfgGraph;

//===========================================================================
// Various context objects hold data that need to persist across invocations
// of a DFG pass.

class V3DfgBinToOneHotContext final {
    const std::string m_label;  // Label to apply to stats

public:
    VDouble0 m_decodersCreated;  // Number of bianry to one-hot decoders created
    explicit V3DfgBinToOneHotContext(const std::string& label)
        : m_label{label} {}
    ~V3DfgBinToOneHotContext() VL_MT_DISABLED;
};

class V3DfgBreakCyclesContext final {
    const std::string m_label;  // Label to apply to stats

public:
    VDouble0 m_nFixed;  // Number of graphs that became acyclic
    VDouble0 m_nImproved;  // Number of graphs that were imporoved but still cyclic
    VDouble0 m_nUnchanged;  // Number of graphs that were left unchanged
    VDouble0 m_nTrivial;  // Number of graphs that were not changed
    VDouble0 m_nImprovements;  // Number of changes made to graphs
    explicit V3DfgBreakCyclesContext(const std::string& label)
        : m_label{label} {}
    ~V3DfgBreakCyclesContext() VL_MT_DISABLED;
};

class V3DfgCseContext final {
    const std::string m_label;  // Label to apply to stats

public:
    VDouble0 m_eliminated;  // Number of common sub-expressions eliminated
    explicit V3DfgCseContext(const std::string& label)
        : m_label{label} {}
    ~V3DfgCseContext() VL_MT_DISABLED;
};

class V3DfgRegularizeContext final {
    const std::string m_label;  // Label to apply to stats

public:
    VDouble0 m_temporariesIntroduced;  // Number of temporaries introduced

    explicit V3DfgRegularizeContext(const std::string& label)
        : m_label{label} {}
    ~V3DfgRegularizeContext() VL_MT_DISABLED;
};

class V3DfgEliminateVarsContext final {
    const std::string m_label;  // Label to apply to stats

public:
    VDouble0 m_varsReplaced;  // Number of variables replaced
    VDouble0 m_varsRemoved;  // Number of variables removed

    explicit V3DfgEliminateVarsContext(const std::string& label)
        : m_label{label} {}
    ~V3DfgEliminateVarsContext() VL_MT_DISABLED;
};

class V3DfgOptimizationContext final {
    const std::string m_label;  // Label to add to stats, etc.
    const std::string m_prefix;  // Prefix to add to file dumps (derived from label)

public:
    VDouble0 m_modules;  // Number of modules optimized
    VDouble0 m_coalescedAssignments;  // Number of partial assignments coalesced
    VDouble0 m_inputEquations;  // Number of input combinational equations
    VDouble0 m_representable;  // Number of combinational equations representable
    VDouble0 m_nonRepDType;  // Equations non-representable due to data type
    VDouble0 m_nonRepImpure;  // Equations non-representable due to impure node
    VDouble0 m_nonRepTiming;  // Equations non-representable due to timing control
    VDouble0 m_nonRepLhs;  // Equations non-representable due to lhs
    VDouble0 m_nonRepNode;  // Equations non-representable due to node type
    VDouble0 m_nonRepUnknown;  // Equations non-representable due to unknown node
    VDouble0 m_nonRepVarRef;  // Equations non-representable due to variable reference
    VDouble0 m_nonRepWidth;  // Equations non-representable due to width mismatch
    VDouble0 m_resultEquations;  // Number of result combinational equations

    V3DfgBinToOneHotContext m_binToOneHotContext{m_label};
    V3DfgBreakCyclesContext m_breakCyclesContext{m_label};
    V3DfgCseContext m_cseContext0{m_label + " 1st"};
    V3DfgCseContext m_cseContext1{m_label + " 2nd"};
    V3DfgPeepholeContext m_peepholeContext{m_label};
    V3DfgRegularizeContext m_regularizeContext{m_label};
    V3DfgEliminateVarsContext m_eliminateVarsContext{m_label};

    V3DfgPatternStats m_patternStats;

    explicit V3DfgOptimizationContext(const std::string& label) VL_MT_DISABLED;
    ~V3DfgOptimizationContext() VL_MT_DISABLED;

    const std::string& prefix() const { return m_prefix; }
};

namespace V3DfgPasses {
//===========================================================================
// Top level entry points
//===========================================================================

// Construct a DfGGraph representing the combinational logic in the given AstModule. The logic
// that is represented by the graph is removed from the given AstModule. Returns the
// constructed DfgGraph.
DfgGraph* astToDfg(AstModule&, V3DfgOptimizationContext&) VL_MT_DISABLED;

// Same as above, but for the entire netlist, after V3Scope
DfgGraph* astToDfg(AstNetlist&, V3DfgOptimizationContext&) VL_MT_DISABLED;

// Attempt to make the given cyclic graph into an acyclic, or "less cyclic"
// equivalent. If the returned pointer is null, then no improvement was
// possible on the input graph. Otherwise the returned graph is an improvement
// on the input graph, with at least some cycles eliminated. The returned
// graph is always independent of the original. If an imporoved graph is
// returned, then the returned 'bool' flag indicated if the returned graph is
// acyclic (flag 'true'), or still cyclic (flag 'false').
std::pair<std::unique_ptr<DfgGraph>, bool> breakCycles(const DfgGraph&,
                                                       V3DfgOptimizationContext&) VL_MT_DISABLED;

// Optimize the given DfgGraph
void optimize(DfgGraph&, V3DfgOptimizationContext&) VL_MT_DISABLED;

// Convert DfgGraph back into Ast, and insert converted graph back into the Ast.
void dfgToAst(DfgGraph&, V3DfgOptimizationContext&) VL_MT_DISABLED;

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
