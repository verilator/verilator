// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Convert DfgGraph to AstModule
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2003-2026 Wilson Snyder
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
        // Variable vertices, would have been inlined if equivalent,
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

        // Const vertices driving an Ast reference can only be inlined in scoped
        // mode as some algorithms assume VarRefs in certain places.
        if (m_dfg.modulep()) {
            for (DfgConst& vtx : m_dfg.constVertices()) {
                const bool drivesAstRef = vtx.foreachSink([](const DfgVertex& dst) {  //
                    return dst.is<DfgAstRd>();
                });
                if (!drivesAstRef) continue;

                // The prefered result variable is the canonical one if exists
                DfgVertexVar* const varp = vtx.getResultVar();
                if (!varp) continue;

                // Relink all other sinks reading this vertex to read 'varp'
                varp->srcp(nullptr);
                vtx.replaceWith(varp);
                varp->srcp(&vtx);
            }
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

    static bool isUnused(const DfgVertex& vtx) {
        if (vtx.hasSinks()) return false;
        if (const DfgVertexVar* const varp = vtx.cast<DfgVertexVar>()) {
            // There is only one Dfg when running this pass
            UASSERT_OBJ(!varp->hasDfgRefs(), varp, "Should not have refs in other DfgGraph");
            if (varp->hasModWrRefs()) return false;
            if (varp->hasExtRefs()) return false;
        }
        return true;
    }

    // Predicate to determine if a temporary should be inserted or if a variable
    // should be preserved. The given vertices are either the same, or aVtxp is
    // the sole driver of bVtx, or aVtxp is cheaper to recompute and might have
    // multiple sinks. In either case, bVtx can be used to check sinks, and aVtx
    // can be used to check the operation.
    bool needsTemporary(DfgVertex& aVtx, DfgVertex& bVtx) {
        UASSERT_OBJ(&aVtx == &bVtx || aVtx.isCheaperThanLoad() || aVtx.singleSink() == &bVtx,
                    &aVtx, "Mismatched vertices");
        UASSERT_OBJ(!aVtx.is<DfgVertexVar>(), &aVtx, "Should be an operation vertex");

        if (bVtx.hasMultipleSinks()) {
            // We are not inlining expressions prior to the final scoped run
            if (m_dfg.modulep()) return true;

            // Add a temporary if it's cheaper to store and load from memory than recompute
            if (!aVtx.isCheaperThanLoad()) return true;

            // Not adding temporary
            return false;
        }

        DfgVertex& sink = *bVtx.singleSink();

        // No need to add a temporary if the single sink is a variable already
        if (sink.is<DfgVertexVar>()) return false;

        // Do not inline expressions prior to the final scoped run, or if they are in a loop
        if (const DfgAstRd* const astRdp = sink.cast<DfgAstRd>()) {
            return m_dfg.modulep() || astRdp->inLoop();
        }

        // Make sure roots of wide concatenation trees are written to variables,
        // this enables V3FuncOpt to split them which can be a big speed gain
        // without expanding them.
        if (aVtx.is<DfgConcat>()) {
            if (sink.is<DfgConcat>()) return false;  // Not root of tree
            return VL_WORDS_I(static_cast<int>(aVtx.width())) > v3Global.opt.expandLimit();
        }

        // No need for a temporary otherwise
        return false;
    }

    void eliminateVars() {
        // Although we could eliminate some circular variables, doing so would
        // make UNOPTFLAT traces fairly usesless, so we will not do so.
        const std::unordered_set<const DfgVertexVar*> circularVariables = gatherCyclicVariables();

        // Worklist based algoritm
        DfgWorklist workList{m_dfg};

        // Add all variables and all vertices with no sinks to the worklist
        m_dfg.forEachVertex([&](DfgVertex& vtx) {
            if (vtx.is<DfgVertexAst>()) return;
            if (vtx.is<DfgVertexVar>() || !vtx.hasSinks()) workList.push_front(vtx);
        });

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

            // Can't eliminate if referenced external to the module - can't replace those refs
            if (varp->hasExtRefs()) return;
            // Can't eliminate if written in the module - the write needs to go somewhere, and
            // we need to observe the write in this graph if the variable has sinks
            if (varp->hasModWrRefs()) return;
            // There is only one Dfg when running this pass
            UASSERT_OBJ(!varp->hasDfgRefs(), varp, "Should not have refs in other DfgGraph");

            // Do not eliminate circular variables - need to preserve UNOPTFLAT traces
            if (circularVariables.count(varp)) return;

            // Do not inline if partially driven (the partial driver network can't be fed into
            // arbitrary logic. TODO: we should peeophole these away entirely)
            if (varp->defaultp()) return;
            if (srcp->is<DfgVertexSplice>()) return;
            if (srcp->is<DfgUnitArray>()) return;

            // Do not eliminate variables that are driven from a vertex that needs a temporary
            if (!srcp->is<DfgVertexVar>() && needsTemporary(*srcp, *varp)) return;

            // Inline this variable into its single sink
            ++m_ctx.m_usedVarsInlined;
            varp->replaceWith(varp->srcp());
            removeVertex(*varp);
            return;
        });
    }

    void insertTemporaries() {
        // Insert a temporary variable for all vertices that have multiple non-variable sinks

        // Scope cache for below
        const bool scoped = !m_dfg.modulep();
        DfgVertex::ScopeCache scopeCache;

        // Ensure intermediate values used multiple times are written to variables
        for (DfgVertex& vtx : m_dfg.opVertices()) {
            // LValue vertices feed into variables eventually and need no temporaries
            if (vtx.is<DfgVertexSplice>()) continue;
            if (vtx.is<DfgUnitArray>()) continue;

            if (!needsTemporary(vtx, vtx)) continue;

            // Need to create an intermediate variable
            ++m_ctx.m_temporariesIntroduced;
            const std::string name = m_dfg.makeUniqueName("Regularize", m_nTmps);
            FileLine* const flp = vtx.fileline();
            AstScope* const scopep = scoped ? vtx.scopep(scopeCache) : nullptr;
            DfgVertexVar* const newp = m_dfg.makeNewVar(flp, name, vtx.dtype(), scopep);
            ++m_nTmps;
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
