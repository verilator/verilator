// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Convert DfgGraph to AstModule
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2024 by Wilson Snyder. This program is free software; you
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

std::string V3DfgRegularizeContext::tmpNamePrefix(DfgGraph& dfg) {
    V3Hash hash{dfg.modulep()->name()};
    hash += m_label;
    std::string name = hash.toString();
    const uint32_t sequenceNumber = m_multiplicity[name]++;
    name += '_' + std::to_string(sequenceNumber);
    return name;
}

class DfgRegularize final {
    DfgGraph& m_dfg;  // The graph being processed
    V3DfgRegularizeContext& m_ctx;  // The optimization context for stats

    // Prefix of temporary variable names
    const std::string m_tmpNamePrefix = "__VdfgRegularize_" + m_ctx.tmpNamePrefix(m_dfg) + '_';
    size_t m_nTmps = 0;  // Number of temporaries added to this graph - for variable names only

    // Return canonical variable that can be used to hold the value of this vertex
    DfgVarPacked* getCanonicalVariable(DfgVertex& vtx) {
        // First gather all existing variables fully written by this vertex. Ignore SystemC
        // variables, those cannot act as canonical variables, as they cannot participate in
        // expressions or be assigned rvalues.
        std::vector<DfgVarPacked*> varVtxps;
        vtx.forEachSink([&](DfgVertex& sink) {
            if (DfgVarPacked* const varVtxp = sink.cast<DfgVarPacked>()) {
                if (varVtxp->isDrivenFullyByDfg() && !varVtxp->varp()->isSc()) {
                    varVtxps.push_back(varVtxp);
                }
            }
        });

        if (!varVtxps.empty()) {
            // There is at least one usable, existing variable. Pick the first one in source
            // order for deterministic results.
            std::stable_sort(varVtxps.begin(), varVtxps.end(),
                             [](const DfgVarPacked* ap, const DfgVarPacked* bp) {
                                 // Prefer those variables that must be kept anyway
                                 const bool keepA = ap->keep() || ap->hasDfgRefs();
                                 const bool keepB = bp->keep() || bp->hasDfgRefs();
                                 if (keepA != keepB) return keepA;
                                 // Prefer those that already have module references, so we don't
                                 // have to support recursive substitutions.
                                 if (ap->hasModRefs() != bp->hasModRefs()) return ap->hasModRefs();
                                 // Otherwise source order
                                 const FileLine& aFl = *(ap->fileline());
                                 const FileLine& bFl = *(bp->fileline());
                                 if (const int cmp = aFl.operatorCompare(bFl)) return cmp < 0;
                                 // Fall back on names if all else fails
                                 return ap->varp()->name() < bp->varp()->name();
                             });
            return varVtxps.front();
        }

        // We need to introduce a temporary
        ++m_ctx.m_temporariesIntroduced;

        // Add temporary AstVar to containing module
        FileLine* const flp = vtx.fileline();
        const std::string name = m_tmpNamePrefix + std::to_string(m_nTmps++);
        AstVar* const varp = new AstVar{flp, VVarType::MODULETEMP, name, vtx.dtypep()};
        m_dfg.modulep()->addStmtsp(varp);

        // Create and return a variable vertex for the temporary
        return new DfgVarPacked{m_dfg, varp};
    }

    // Insert intermediate variables for vertices with multiple sinks (or use an existing one)
    DfgRegularize(DfgGraph& dfg, V3DfgRegularizeContext& ctx)
        : m_dfg{dfg}
        , m_ctx{ctx} {

        // Ensure intermediate values used multiple times are written to variables
        for (DfgVertex& vtx : m_dfg.opVertices()) {
            const bool needsIntermediateVariable = [&]() {
                // Anything that drives an SC variable needs an intermediate,
                // as we can only assign simple variables to SC variables at runtime.
                const bool hasScSink = vtx.findSink<DfgVertexVar>([](const DfgVertexVar& var) {  //
                    return var.varp()->isSc();
                });
                if (hasScSink) return true;
                // Operations without multiple sinks need no variables
                if (!vtx.hasMultipleSinks()) return false;
                // Array selects need no variables, they are just memory references
                if (vtx.is<DfgArraySel>()) return false;
                // Otherwise needs an intermediate variable
                return true;
            }();

            if (!needsIntermediateVariable) continue;

            // This is an op which has multiple sinks. Ensure it is assigned to a variable.
            DfgVarPacked* const varp = getCanonicalVariable(vtx);
            if (varp->arity()) {
                // Existing variable
                FileLine* const flp = varp->driverFileLine(0);
                varp->sourceEdge(0)->unlinkSource();
                varp->resetSources();
                vtx.replaceWith(varp);
                varp->addDriver(flp, 0, &vtx);
            } else {
                // Temporary variable
                vtx.replaceWith(varp);
                varp->addDriver(vtx.fileline(), 0, &vtx);
            }
        }
    }

public:
    static void apply(DfgGraph& dfg, V3DfgRegularizeContext& ctx) { DfgRegularize{dfg, ctx}; }
};

void V3DfgPasses::regularize(DfgGraph& dfg, V3DfgRegularizeContext& ctx) {
    DfgRegularize::apply(dfg, ctx);
}
