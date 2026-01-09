// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Convert DfgGraph to AstModule
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
    // STATE
    DfgGraph& m_dfg;  // The graph being processed
    V3DfgRegularizeContext& m_ctx;  // The optimization context for stats
    size_t m_nTmps = 0;  // Number of temporaries added to this graph - for variable names only
    VNDeleter m_deleter;  // Deletes replacement nodes at the end

    // METHODS

    // For all operation vetices, if they drive multiple variables, pick
    // a "canonical" one and uninline the logic through that variable.
    void uninlineVariables() {
        // Const vertices we can just emit as drivers to multiple sinks
        // directly. Variable vertices, would have been inlined if equivalent,
        // so no need to process them here, they are where they must be.
        for (DfgVertex& vtx : m_dfg.opVertices()) {
            // Don't process LValue operations
            if (vtx.is<DfgVertexSplice>()) continue;
            if (vtx.is<DfgUnitArray>()) continue;

            // The prefered result variable is the canonical one if exists
            DfgVertexVar* const varp = vtx.getResultVar();
            if (!varp) continue;

            // Relink all other sinks reading this vertex to read 'varp'
            varp->srcp(nullptr);
            vtx.replaceWith(varp);
            varp->srcp(&vtx);
        }
    }

    std::unordered_set<const DfgVertexVar*> gatherCyclicVariables() {
        DfgUserMap<uint64_t> vtx2Scc = m_dfg.makeUserMap<uint64_t>();
        V3DfgPasses::colorStronglyConnectedComponents(m_dfg, vtx2Scc);
        std::unordered_set<const DfgVertexVar*> circularVariables;
        for (const DfgVertexVar& vtx : m_dfg.varVertices()) {
            if (vtx2Scc[vtx]) circularVariables.emplace(&vtx);
        }
        return circularVariables;
    }

    bool isUnused(const DfgVertex& vtx) {
        if (vtx.hasSinks()) return false;
        if (const DfgVertexVar* const varp = vtx.cast<DfgVertexVar>()) {
            // There is only one Dfg when running this pass
            UASSERT_OBJ(!varp->hasDfgRefs(), varp, "Should not have refs in other DfgGraph");
            if (varp->hasModRefs()) return false;
            if (varp->hasExtRefs()) return false;
        }
        return true;
    }

    // Given a variable and its driver, return true iff the variable can be
    // replaced with its driver. Record replacement to be applied in the Ast
    // in user2p of the replaced variable.
    bool replaceable(DfgVertexVar* varp, DfgVertex* srcp) {
        // The given variable has no external references, and is read in the module

        // Make sure we are not trying to double replace something
        AstNode* const nodep = varp->nodep();
        UASSERT_OBJ(!nodep->user2p(), nodep, "Replacement already exists");

        // If it is driven from another variable, it can be replaced by that variable.
        if (const DfgVarPacked* const drvp = srcp->cast<DfgVarPacked>()) {
            // Record replacement
            nodep->user2p(drvp->nodep());
            // The replacement will be read in the module, mark as such so it doesn't get removed.
            drvp->setHasModRdRefs();
            drvp->varp()->propagateAttrFrom(varp->varp());
            return true;
        }

        // Expressions can only be inlined after V3Scope, as some passes assume variables.
        if (m_dfg.modulep()) return false;

        // If it is driven from a constant, it can be replaced by that constant.
        if (const DfgConst* const constp = srcp->cast<DfgConst>()) {
            // Need to create the AstConst
            AstConst* const newp = new AstConst{constp->fileline(), constp->num()};
            m_deleter.pushDeletep(newp);
            // Record replacement
            nodep->user2p(newp);
            return true;
        }

        // Don't replace
        return false;
    }

    template <bool T_Scoped>
    static void applyReplacement(AstVarRef* refp) {
        AstNode* const tgtp = T_Scoped ? static_cast<AstNode*>(refp->varScopep())
                                       : static_cast<AstNode*>(refp->varp());
        AstNode* replacementp = tgtp;
        while (AstNode* const altp = replacementp->user2p()) replacementp = altp;
        if (replacementp == tgtp) return;
        UASSERT_OBJ(refp->access().isReadOnly(), refp, "Replacing write AstVarRef");
        // If it's an inlined expression, repalce the VarRef entirely
        if (AstNodeExpr* const newp = VN_CAST(replacementp, NodeExpr)) {
            refp->replaceWith(newp->cloneTreePure(false));
            VL_DO_DANGLING(refp->deleteTree(), refp);
            return;
        }
        // Otherwise just re-point the VarRef to the new variable
        if VL_CONSTEXPR_CXX17 (T_Scoped) {
            AstVarScope* const newp = VN_AS(replacementp, VarScope);
            refp->varScopep(newp);
            refp->varp(newp->varp());
        } else {
            AstVar* const newp = VN_AS(replacementp, Var);
            refp->varp(newp);
        }
    }

    void eliminateVars() {
        // Although we could eliminate some circular variables, doing so would
        // make UNOPTFLAT traces fairly usesless, so we will not do so.
        const std::unordered_set<const DfgVertexVar*> circularVariables = gatherCyclicVariables();

        // Worklist based algoritm
        DfgWorklist workList{m_dfg};

        // Add all variables and all vertices with no sinks to the worklist
        m_dfg.forEachVertex([&](DfgVertex& vtx) {
            if (vtx.is<DfgVertexVar>() || !vtx.hasSinks()) workList.push_front(vtx);
        });

        // AstVar::user2p() : AstVar*/AstNodeExpr* -> The replacement variable/expression
        // AstVarScope::user2p() : AstVarScope*/AstNodeExpr* -> The replacement variable/expression
        const VNUser2InUse user2InUse;

        // Remove vertex, enqueue it's sources
        const auto removeVertex = [&](DfgVertex& vtx) {
            // Add sources of removed vertex to work list
            vtx.foreachSource([&](DfgVertex& src) {
                workList.push_front(src);
                return false;
            });
            // Delete corresponsing Ast variable at the end
            if (const DfgVertexVar* const varp = vtx.cast<DfgVertexVar>()) {
                m_ctx.m_deleteps.push_back(varp->nodep());
            }
            // Remove the unused vertex
            vtx.unlinkDelete(m_dfg);
        };

        // Used to check if we need to apply variable replacements
        const VDouble0 usedVarsReplacedBefore = m_ctx.m_usedVarsReplaced;

        // Process the work list
        workList.foreach([&](DfgVertex& vtx) {
            // Remove unused vertices
            if (isUnused(vtx)) {
                ++m_ctx.m_unusedRemoved;
                removeVertex(vtx);
                return;
            }

            // Consider eliminating variables
            DfgVertexVar* const varp = vtx.cast<DfgVertexVar>();
            if (!varp) return;

            // If it has no driver (in this Dfg), there is nothing further we can optimize
            DfgVertex* const srcp = varp->srcp();
            if (!srcp) return;

            // If it has multiple sinks, it can't be eliminated - would increase logic size
            if (varp->hasMultipleSinks()) return;
            // Can't eliminate if referenced external to the module - can't replace those refs
            if (varp->hasExtRefs()) return;
            // Can't eliminate if written in the module - the write needs to go somewhere, and
            // we need to observe the write in this graph if the variable has sinks
            if (varp->hasModWrRefs()) return;
            // There is only one Dfg when running this pass
            UASSERT_OBJ(!varp->hasDfgRefs(), varp, "Should not have refs in other DfgGraph");

            // At this point, the variable is used, driven only in this Dfg,
            // it has exactly 0 or 1 sinks in this Dfg, and might be read in
            // the host module, but no other references exist.

            // Do not eliminate circular variables - need to preserve UNOPTFLAT traces
            if (circularVariables.count(varp)) return;

            // If it is not read in the module, it can be inlined into the
            // Dfg unless partially driven (the partial driver network
            // can't be fed into arbitrary logic. TODO: we should peeophole
            // these away entirely).
            if (!varp->hasModRdRefs()) {
                UASSERT_OBJ(varp->hasSinks(), varp, "Shouldn't have made it here without sinks");
                // Don't inline if partially driven
                if (varp->defaultp()) return;
                if (srcp->is<DfgVertexSplice>()) return;
                if (srcp->is<DfgUnitArray>()) return;
                // Inline this variable into its single sink
                ++m_ctx.m_usedVarsInlined;
                varp->replaceWith(varp->srcp());
                removeVertex(*varp);
                return;
            }

            // The varable is read in the module. We might still be able to replace it.
            if (replaceable(varp, srcp)) {
                // Replace this variable with its driver
                ++m_ctx.m_usedVarsReplaced;
                // Inline it if it has a sink
                if (varp->hasSinks()) varp->replaceWith(srcp);
                // Delete the repalced variabel
                removeVertex(*varp);
            }
        });

        // Job done if no replacements need to be applied
        if (m_ctx.m_usedVarsReplaced == usedVarsReplacedBefore) return;

        // Apply variable replacements
        if (AstModule* const modp = m_dfg.modulep()) {
            modp->foreach([](AstVarRef* refp) { applyReplacement<false>(refp); });
        } else {
            v3Global.rootp()->foreach([](AstVarRef* refp) { applyReplacement<true>(refp); });
        }
    }

    void insertTemporaries() {
        // Insert a temporary variable for all vertices that have multiple non-variable sinks

        // Scope cache for below
        const bool scoped = !m_dfg.modulep();
        DfgVertex::ScopeCache scopeCache;

        // Ensure intermediate values used multiple times are written to variables
        for (DfgVertex& vtx : m_dfg.opVertices()) {
            // LValue vertices feed into variables eventually and need not temporaries
            if (vtx.is<DfgVertexSplice>()) continue;
            if (vtx.is<DfgUnitArray>()) continue;

            // If this Vertex was driving a variable, 'unlinline' would have
            // made that the single sink, so if there are multiple sinks
            // remaining, they must be non-variables. So nothing to do if:
            if (!vtx.hasMultipleSinks()) continue;

            // 'uninline' would have made the result var cannonical, so there shouldn't be one
            UASSERT_OBJ(!vtx.getResultVar(), &vtx, "Failed to uninline variable");

            // Do not add a temporary if it's cheaper to re-compute than to
            // load it from memory. This also increases available parallelism.
            if (vtx.isCheaperThanLoad()) {
                ++m_ctx.m_temporariesOmitted;
                continue;
            }

            // Need to create an intermediate variable
            const std::string name = m_dfg.makeUniqueName("Regularize", m_nTmps);
            FileLine* const flp = vtx.fileline();
            AstScope* const scopep = scoped ? vtx.scopep(scopeCache) : nullptr;
            DfgVertexVar* const newp = m_dfg.makeNewVar(flp, name, vtx.dtype(), scopep);
            ++m_nTmps;
            ++m_ctx.m_temporariesIntroduced;
            // Replace vertex with the variable, make it drive the variable
            vtx.replaceWith(newp);
            newp->srcp(&vtx);
        }
    }

    // Insert intermediate variables for vertices with multiple sinks (or use an existing one)
    DfgRegularize(DfgGraph& dfg, V3DfgRegularizeContext& ctx)
        : m_dfg{dfg}
        , m_ctx{ctx} {

        uninlineVariables();
        if (dumpDfgLevel() >= 9) dfg.dumpDotFilePrefixed(ctx.prefix() + "regularize-uninlined");

        eliminateVars();
        if (dumpDfgLevel() >= 9) dfg.dumpDotFilePrefixed(ctx.prefix() + "regularize-eliminate");

        insertTemporaries();
        if (dumpDfgLevel() >= 9) dfg.dumpDotFilePrefixed(ctx.prefix() + "regularize-inserttmp");
    }

public:
    static void apply(DfgGraph& dfg, V3DfgRegularizeContext& ctx) { DfgRegularize{dfg, ctx}; }
};

void V3DfgPasses::regularize(DfgGraph& dfg, V3DfgRegularizeContext& ctx) {
    DfgRegularize::apply(dfg, ctx);
}
