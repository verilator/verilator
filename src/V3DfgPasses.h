// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Passes over DfgGraph
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2022 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#ifndef VERILATOR_V3DFGPASSES_H_
#define VERILATOR_V3DFGPASSES_H_

#include "config_build.h"

#include "V3DfgPeephole.h"

class AstModule;
class DfgGraph;

//===========================================================================
// Various context objects hold data that need to persist across invocations
// of a DFG pass.

class V3DfgCseContext final {
    const std::string m_label;  // Label to apply to stats

public:
    VDouble0 m_eliminated;  // Number of common sub-expressions eliminated
    explicit V3DfgCseContext(const std::string& label)
        : m_label{label} {}
    ~V3DfgCseContext();
};

class DfgRemoveVarsContext final {
    const std::string m_label;  // Label to apply to stats

public:
    VDouble0 m_removed;  // Number of redundant variables removed
    explicit DfgRemoveVarsContext(const std::string& label)
        : m_label{label} {}
    ~DfgRemoveVarsContext();
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
    VDouble0 m_intermediateVars;  // Number of intermediate variables introduced
    VDouble0 m_replacedVars;  // Number of variables replaced
    VDouble0 m_resultEquations;  // Number of result combinational equations

    V3DfgCseContext m_cseContext0{m_label + " 1st"};
    V3DfgCseContext m_cseContext1{m_label + " 2nd"};
    V3DfgPeepholeContext m_peepholeContext{m_label};
    DfgRemoveVarsContext m_removeVarsContext{m_label};
    explicit V3DfgOptimizationContext(const std::string& label);
    ~V3DfgOptimizationContext();

    const std::string& prefix() const { return m_prefix; }
};

namespace V3DfgPasses {
//===========================================================================
// Top level entry points
//===========================================================================

// Construct a DfGGraph representing the combinational logic in the given AstModule. The logic
// that is represented by the graph is removed from the given AstModule. Returns the
// constructed DfgGraph.
DfgGraph* astToDfg(AstModule&, V3DfgOptimizationContext&);

// Optimize the given DfgGraph
void optimize(DfgGraph&, V3DfgOptimizationContext&);

// Convert DfgGraph back into Ast, and insert converted graph back into its parent module.
// Returns the parent module.
AstModule* dfgToAst(DfgGraph&, V3DfgOptimizationContext&);

//===========================================================================
// Intermediate/internal operations
//===========================================================================

// Common subexpression elimination
void cse(DfgGraph&, V3DfgCseContext&);
// Inline fully driven variables
void inlineVars(DfgGraph&);
// Peephole optimizations
void peephole(DfgGraph&, V3DfgPeepholeContext&);
// Remove redundant variables
void removeVars(DfgGraph&, DfgRemoveVarsContext&);
// Remove unused nodes
void removeUnused(DfgGraph&);
}  // namespace V3DfgPasses

#endif
