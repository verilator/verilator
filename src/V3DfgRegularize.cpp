// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Convert DfgGraph to AstModule
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
//
// - Ensures intermediate values (other than simple memory references or
//   constants) with multiple uses are assigned to variables
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Dfg.h"
#include "V3DfgPasses.h"

VL_DEFINE_DEBUG_FUNCTIONS;

class DfgRegularize final {
    DfgGraph& m_dfg;  // The graph being processed
    V3DfgRegularizeContext& m_ctx;  // The optimization context for stats

    // Prefix of temporary variable names
    size_t m_nTmps = 0;  // Number of temporaries added to this graph - for variable names only

    // Insert intermediate variables for vertices with multiple sinks (or use an existing one)
    DfgRegularize(DfgGraph& dfg, V3DfgRegularizeContext& ctx)
        : m_dfg{dfg}
        , m_ctx{ctx} {

        // Scope cache for below
        const bool scoped = !dfg.modulep();
        DfgVertex::ScopeCache scopeCache;

        // Ensure intermediate values used multiple times are written to variables
        for (DfgVertex& vtx : m_dfg.opVertices()) {
            const bool needsIntermediateVariable = [&]() {
                // Splice vertices represent partial assignments, so they need a variable
                // iff and only if they have a non-variable sink.
                if (vtx.is<DfgVertexSplice>()) {
                    const bool hasNonVarSink
                        = vtx.findSink<DfgVertex>([](const DfgVertex& snk) {  //
                              return !snk.is<DfgVertexVar>() && !snk.is<DfgVertexSplice>();
                          });
                    return hasNonVarSink;
                }
                // Operations without multiple sinks need no variables
                if (!vtx.hasMultipleSinks()) return false;
                // Array selects need no variables, they are just memory references
                if (vtx.is<DfgArraySel>()) return false;
                // Otherwise needs an intermediate variable
                return true;
            }();

            if (!needsIntermediateVariable) continue;

            // This is an op that requires a result variable. Ensure it is
            // assigned to one, and redirect other sinks read that variable.
            if (DfgVertexVar* const varp = vtx.getResultVar()) {
                varp->sourceEdge<0>()->unlinkSource();
                vtx.replaceWith(varp);
                varp->srcp(&vtx);
            } else {
                // Need to create an intermediate variable
                const std::string name = m_dfg.makeUniqueName("Regularize", m_nTmps);
                FileLine* const flp = vtx.fileline();
                AstScope* const scopep = scoped ? vtx.scopep(scopeCache) : nullptr;
                DfgVertexVar* const newp = m_dfg.makeNewVar(flp, name, vtx.dtypep(), scopep);
                ++m_nTmps;
                ++m_ctx.m_temporariesIntroduced;
                // Replace vertex with the variable and add back driver
                vtx.replaceWith(newp);
                newp->srcp(&vtx);
            }
        }
    }

public:
    static void apply(DfgGraph& dfg, V3DfgRegularizeContext& ctx) { DfgRegularize{dfg, ctx}; }
};

void V3DfgPasses::regularize(DfgGraph& dfg, V3DfgRegularizeContext& ctx) {
    DfgRegularize::apply(dfg, ctx);
}
