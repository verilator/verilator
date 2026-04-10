// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Dataflow based optimization of combinational logic
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
// High level entry points from Ast world to the DFG optimizer.
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3DfgOptimizer.h"

#include "V3Const.h"
#include "V3Dfg.h"
#include "V3DfgPasses.h"
#include "V3Error.h"

#include <vector>

VL_DEFINE_DEBUG_FUNCTIONS;

class DataflowOptimize final {
    // NODE STATE
    // AstVar::user1, AstVarScope::user1 -> int, used as a bit-field
    // - bit0: Read via AstVarXRef (hierarchical reference)
    // - bit1: Written via AstVarXRef (hierarchical reference)
    // - bit2: Read by logic in same module/netlist not represented in DFG
    // - bit3: Written by logic in same module/netlist not represented in DFG
    // - bit4: Has READWRITE references
    // - bit31-5: Reference count, how many DfgVertexVar represent this variable
    //
    // AstNode::user2/user3/user4 can be used by various DFG algorithms
    const VNUser1InUse m_user1InUse;

    // STATE
    V3DfgContext m_ctx;  // The context holding values that need to persist across multiple graphs

    void endOfStage(const std::string& name) {
        if (VL_UNLIKELY(v3Global.opt.stats())) V3Stats::statsStage("dfg-" + name);
    }

    void endOfStage(const std::string& name, const DfgGraph& dfg,
                    const std::vector<std::unique_ptr<DfgGraph>>& componentps) {
        // Dump the graphs for debugging
        if (VL_UNLIKELY(dumpDfgLevel() >= 5)) {
            if (dfg.size() > 0) dfg.dumpDotFilePrefixed(name);
            for (const std::unique_ptr<DfgGraph>& componentp : componentps) {
                if (componentp->size() > 0) componentp->dumpDotFilePrefixed(name);
            }
        }
        // Type check the graphs
        if (VL_UNLIKELY(v3Global.opt.debugCheck())) {
            V3DfgPasses::typeCheck(dfg);
            for (const std::unique_ptr<DfgGraph>& componentp : componentps) {
                V3DfgPasses::typeCheck(*componentp);
            }
        }
        // Dump stage stats
        endOfStage(name);
    }

    // Mark variables with external references
    void markExternallyReferencedVariables(AstNetlist* netlistp) {
        netlistp->foreach([](AstNode* nodep) {
            // Check variable flags
            if (AstVarScope* const vscp = VN_CAST(nodep, VarScope)) {
                const AstVar* const varp = vscp->varp();
                // Force and trace have already been processed
                const bool hasExtRd = varp->isPrimaryIO() || varp->isSigUserRdPublic();
                const bool hasExtWr
                    = (varp->isPrimaryIO() && varp->isNonOutput()) || varp->isSigUserRWPublic();
                if (hasExtRd) DfgVertexVar::setHasExtRdRefs(vscp);
                if (hasExtWr) DfgVertexVar::setHasExtWrRefs(vscp);
                return;
            }
            // Check references
            if (const AstVarRef* const refp = VN_CAST(nodep, VarRef)) {
                if (refp->access().isRW()) DfgVertexVar::setHasRWRefs(refp->varScopep());
                UASSERT_OBJ(!refp->classOrPackagep(), refp, "V3Scope should have removed");
                return;
            }
            UASSERT_OBJ(!VN_IS(nodep, VarXRef), nodep, "V3Scope should have removed");
            // Check cell ports
            if (const AstCell* const cellp = VN_CAST(nodep, Cell)) {
                // Why does this not hold?
                UASSERT_OBJ(true || !cellp->pinsp(), cellp, "Pins should have been lowered");
                return;
            }
        });
    }

    void optimize(DfgGraph& dfg) {
        // Remove unobservable variabels and logic that drives only such variables
        V3DfgPasses::removeUnobservable(dfg, m_ctx);
        endOfStage("removeUnobservable", dfg, {});

        // Synthesize DfgLogic vertices
        V3DfgPasses::synthesize(dfg, m_ctx);
        endOfStage("synthesize", dfg, {});

        // Extract the cyclic sub-graphs. We do this because a lot of the optimizations assume a
        // DAG, and large, mostly acyclic graphs could not be optimized due to the presence of
        // small cycles.
        std::vector<std::unique_ptr<DfgGraph>> cyclicComps = dfg.extractCyclicComponents("cyclic");
        endOfStage("extractCyclic", dfg, cyclicComps);

        // Attempt to convert cyclic components into acyclic ones
        std::vector<std::unique_ptr<DfgGraph>> madeAcyclicComponents;
        if (v3Global.opt.fDfgBreakCycles()) {
            for (auto it = cyclicComps.begin(); it != cyclicComps.end();) {
                auto result = V3DfgPasses::breakCycles(**it, m_ctx);
                if (!result.first) {
                    // No improvement, moving on.
                    ++it;
                } else if (!result.second) {
                    // Improved, but still cyclic. Replace the original cyclic component.
                    *it = std::move(result.first);
                    ++it;
                } else {
                    // Result became acyclic. Move to madeAcyclicComponents, delete original.
                    madeAcyclicComponents.emplace_back(std::move(result.first));
                    it = cyclicComps.erase(it);
                }
            }
        }
        // Merge those that were made acyclic back to the graph, this enables optimizing more
        dfg.mergeGraphs(std::move(madeAcyclicComponents));
        endOfStage("breakCycles", dfg, cyclicComps);

        // Split the acyclic DFG into [weakly] connected components
        std::vector<std::unique_ptr<DfgGraph>> acyclicComps = dfg.splitIntoComponents("acyclic");
        UASSERT(dfg.size() == 0, "DfgGraph should have become empty");
        endOfStage("splitAcyclic", dfg, acyclicComps);

        // Optimize each acyclic component
        for (auto& cp : acyclicComps) V3DfgPasses::inlineVars(*cp);
        endOfStage("inlineVars", dfg, acyclicComps);
        for (auto& cp : acyclicComps) V3DfgPasses::cse(*cp, m_ctx.m_cseContext0);
        endOfStage("cse0", dfg, acyclicComps);
        for (auto& cp : acyclicComps) V3DfgPasses::binToOneHot(*cp, m_ctx.m_binToOneHotContext);
        endOfStage("binToOneHot", dfg, acyclicComps);
        for (auto& cp : acyclicComps) V3DfgPasses::peephole(*cp, m_ctx.m_peepholeContext);
        endOfStage("peephole", dfg, acyclicComps);
        // Accumulate patterns for reporting
        if (v3Global.opt.stats()) {
            V3DfgPasses::dumpPatterns(acyclicComps);
            endOfStage("patterns");
        }
        for (auto& cp : acyclicComps) V3DfgPasses::pushDownSels(*cp, m_ctx.m_pushDownSelsContext);
        endOfStage("pushDownSels", dfg, acyclicComps);
        for (auto& cp : acyclicComps) V3DfgPasses::cse(*cp, m_ctx.m_cseContext1);
        endOfStage("cse1", dfg, acyclicComps);

        // Merge everything back under the main DFG
        dfg.mergeGraphs(std::move(acyclicComps));
        dfg.mergeGraphs(std::move(cyclicComps));
        endOfStage("optimized", dfg, {});

        // Regularize the graph after merging it all back together so all
        // references are known and we only need to iterate the Ast once
        // to replace redundant variables.
        V3DfgPasses::regularize(dfg, m_ctx.m_regularizeContext);
        endOfStage("regularize", dfg, {});
    }

    void removeNeverActives(AstNetlist* netlistp) {
        std::vector<AstActive*> neverActiveps;
        netlistp->foreach([&](AstActive* activep) {
            AstSenTree* const senTreep = activep->sentreep();
            if (!senTreep) return;
            const AstNode* const nodep = V3Const::constifyEdit(senTreep);
            UASSERT_OBJ(nodep == senTreep, nodep, "Should not have been repalced");
            if (senTreep->sensesp()->isNever()) {
                UASSERT_OBJ(!senTreep->sensesp()->nextp(), nodep,
                            "Never senitem should be alone, else the never should be eliminated.");
                neverActiveps.emplace_back(activep);
            }
        });
        for (AstActive* const activep : neverActiveps) {
            VL_DO_DANGLING(activep->unlinkFrBack()->deleteTree(), activep);
        }
    }

    DataflowOptimize(AstNetlist* netlistp) {
        // Mark interfaces that might be referenced by a virtual interface
        if (v3Global.hasVirtIfaces()) {
            netlistp->typeTablep()->foreach([](const AstIfaceRefDType* nodep) {
                if (!nodep->isVirtual()) return;
                nodep->ifaceViaCellp()->setHasVirtualRef();
            });
        }
        // Mark variables with external references
        markExternallyReferencedVariables(netlistp);
        // Dump stage stats
        endOfStage("init");
        // Post V3Scope application. Run on whole netlist.
        UINFO(4, "Applying DFG optimization to entire netlist");
        // Build the DFG of the entire netlist
        const std::unique_ptr<DfgGraph> dfgp = V3DfgPasses::astToDfg(*netlistp, m_ctx);
        endOfStage("astToDfg", *dfgp, {});
        // Actually process the graph
        optimize(*dfgp);
        // Convert back to Ast
        V3DfgPasses::dfgToAst(*dfgp, m_ctx);
        endOfStage("dfgToAst", *dfgp, {});
        // Some sentrees might have become constant, remove them
        removeNeverActives(netlistp);
        // Reset interned types so the corresponding Ast types can be garbage collected
        DfgDataType::reset();
        // Dump stage stats
        endOfStage("fini");
    }

public:
    static void apply(AstNetlist* netlistp) { DataflowOptimize{netlistp}; }
};

void V3DfgOptimizer::optimize(AstNetlist* netlistp) {
    UINFO(2, __FUNCTION__ << ":");
    DataflowOptimize::apply(netlistp);
    V3Global::dumpCheckGlobalTree("dfg-optimize", 0, dumpTreeEitherLevel() >= 3);
}
