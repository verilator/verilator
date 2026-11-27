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

#include "V3Dfg.h"
#include "V3DfgPasses.h"
#include "V3Error.h"
#include "V3Stats.h"

#include <vector>

VL_DEFINE_DEBUG_FUNCTIONS;

class DataflowOptimize final {
    // NODE STATE
    // AstVar::user1 -> int, used as a bit-field
    // - bit0: Read via AstMemberRef (virtual interface)
    // - bit1: Written via AstMemberRef (virtual interface)
    // AstVarScope::user1 -> int, used as a bit-field
    // - bit0: Read via AstVarXRef (hierarchical reference)
    // - bit1: Written via AstVarXRef (hierarchical reference)
    // - bit2: Read by logic in same module/netlist not represented in DFG
    // - bit3: Written by logic in same module/netlist not represented in DFG
    // - bit4: Has READWRITE references
    // - bit5: Has DfgPrev instance
    // - bit31-6: Reference count, how many DfgVertexVar represent this variable
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
        std::vector<AstVarScope*> ifaceVscps;  // Variables in interfaces
        netlistp->foreach([&](AstNode* nodep) {
            // Check variable flags
            if (AstVarScope* const vscp = VN_CAST(nodep, VarScope)) {
                const AstVar* const varp = vscp->varp();
                // Force has already been processed
                const bool hasExtRd =  //
                    varp->isPrimaryIO()  // Top level port - readable
                    || varp->isSigUserRdPublic()  // Readable by user
                    || varp->constPoolEntry()  // Held in V3ConstPool lookup cache, keep
                    ;
                const bool hasExtWr =  //
                    (varp->isPrimaryIO() && varp->isNonOutput())  // Top level port - writable
                    || varp->isSigUserRWPublic()  // Writable by user
                    || varp->keepPort()  // Kept port of a non-inlined module
                    ;
                if (hasExtRd) DfgVertexVar::setHasExtRdRefs(vscp);
                if (hasExtWr) DfgVertexVar::setHasExtWrRefs(vscp);
                if (VN_IS(vscp->scopep()->modp(), Iface)) ifaceVscps.push_back(vscp);
                return;
            }
            // Check member references. The referenced instance is not known statically.
            if (const AstMemberRef* const refp = VN_CAST(nodep, MemberRef)) {
                AstVar* const varp = refp->varp();
                if (refp->access().isReadOrRW()) varp->user1(varp->user1() | 0x01);
                if (refp->access().isWriteOrRW()) varp->user1(varp->user1() | 0x02);
                return;
            }
            // Variables read by descriptors are read externally
            if (const AstRtmdVar* const sigp = VN_CAST(nodep, RtmdVar)) {
                if (sigp->refp()) DfgVertexVar::setHasExtRdRefs(sigp->vscp());
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
        // Mark all instances of variables read through a member reference.
        // Written vars are rejected by V3Dfg::isSupported.
        for (AstVarScope* const vscp : ifaceVscps) {
            if (vscp->varp()->user1() & 0x01) DfgVertexVar::setHasExtRdRefs(vscp);
        }
    }

    void optimize(DfgGraph& dfg) {
        // Remove unobservable variabels and logic that drives only such variables
        V3DfgPasses::removeUnobservable(dfg, m_ctx);
        endOfStage("removeUnobservable", dfg, {});

        // Synthesize DfgLogic vertices
        V3DfgPasses::synthesize(dfg, m_ctx);
        endOfStage("synthesize", dfg, {});

        // Extract the cyclic sub-graphs, so breakCycles can operate on small graphs,
        // make all of them acyclic, then merge them back to the main graph
        {
            std::vector<std::unique_ptr<DfgGraph>> comps = dfg.extractCyclicComponents("cyclic");
            for (const auto& cp : comps) V3DfgPasses::breakCycles(*cp, m_ctx);
            dfg.mergeGraphs(std::move(comps));
            endOfStage("breakCycles", dfg, {});
        }

        // Split the now entirely acyclic DFG into [weakly] connected components
        std::vector<std::unique_ptr<DfgGraph>> comps = dfg.splitIntoComponents("acyclic");
        UASSERT(dfg.size() == 0, "DfgGraph should have become empty");
        endOfStage("splitAcyclic", dfg, comps);

        // Main pass pipeline - optimize each acyclic component
        {
            for (auto& cp : comps) V3DfgPasses::removeSelects(*cp, m_ctx.m_removeSelectsContext);
            endOfStage("removeSelects", dfg, comps);
            for (const auto& cp : comps) V3DfgPasses::inlineVars(*cp);
            endOfStage("inlineVars", dfg, comps);
            for (auto& cp : comps) V3DfgPasses::cse(*cp, m_ctx.m_cseContext0);
            endOfStage("cse0", dfg, comps);
            for (auto& cp : comps) V3DfgPasses::binToOneHot(*cp, m_ctx.m_binToOneHotContext);
            endOfStage("binToOneHot", dfg, comps);
            for (auto& cp : comps) V3DfgPasses::peephole(*cp, m_ctx.m_peepholeContext);
            endOfStage("peephole", dfg, comps);

            // Accumulate patterns for reporting
            if (v3Global.opt.dumpDfgPatterns()) V3DfgPasses::dumpPatterns(comps);

            for (auto& cp : comps) V3DfgPasses::pushDownSels(*cp, m_ctx.m_pushDownSelsContext);
            endOfStage("pushDownSels", dfg, comps);
            for (auto& cp : comps) V3DfgPasses::cse(*cp, m_ctx.m_cseContext1);
            endOfStage("cse1", dfg, comps);
        }

        // Merge everything back under the main graph
        dfg.mergeGraphs(std::move(comps));
        endOfStage("optimized", dfg, {});

        // Regularize the graph after merging it all back together so all
        // references are known and we only need to iterate the Ast once
        // to replace redundant variables.
        V3DfgPasses::regularize(dfg, m_ctx.m_regularizeContext);
        endOfStage("regularize", dfg, {});
    }

    explicit DataflowOptimize(AstNetlist* netlistp) {
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

static void limitBlockExpressions(DfgGraph& dfg, size_t limit) {
    const std::vector<DfgVertex*> order = V3DfgPasses::topologicalOrder(dfg);
    DfgUserMap<size_t> sizes = dfg.makeUserMap<size_t>();
    DfgVertex::ScopeCache scopeCache;
    size_t count = 0;
    for (DfgVertex* const vtxp : order) {
        sizes[vtxp] = 1;
        if (vtxp->is<DfgVertexVar>() || vtxp->is<DfgConst>()) continue;
        vtxp->foreachSource([&](const DfgVertex& source) {
            sizes[vtxp] += sizes.at(source);
            return false;
        });
        if (sizes[vtxp] <= limit) continue;
        // Bound expression trees after optimization, without splitting guards.
        ++count;
        DfgVertexVar* const varp = dfg.makeNewVar(vtxp->fileline(), "ScopedSplit", vtxp->dtype(),
                                                  vtxp->scopep(scopeCache));
        vtxp->replaceWith(varp);
        varp->srcp(vtxp);
        sizes[varp] = 1;
    }
    V3Stats::addStatSum("DFG scoped, bounded expressions", count);
}

bool V3DfgOptimizer::optimizeBlock(AstScope& scope, std::vector<AstNodeStmt*>& statements,
                                   const std::set<AstVarScope*>& liveOuts,
                                   const std::set<AstVarScope*>& availableInputs,
                                   size_t expressionLimit, V3DfgContext& ctx) {
    if (statements.empty()) return true;
    const VNUser1InUse user1InUse;
    std::unique_ptr<DfgGraph> dfgp
        = V3DfgPasses::astBlockToDfg(scope, statements, liveOuts, availableInputs, ctx);
    if (!dfgp) {
        DfgDataType::reset();
        V3Stats::addStatSum("DFG scoped, unsupported blocks", 1);
        return false;
    }
    const size_t before = dfgp->size();
    std::set<AstVarScope*> locals;
    for (const DfgVertexVar& var : dfgp->varVertices()) {
        if (var.srcp() && !var.hasExtRefs()) locals.insert(var.vscp());
    }
    V3DfgPasses::typeCheck(*dfgp);
    V3DfgPasses::inlineVars(*dfgp);
    V3DfgPasses::cse(*dfgp, ctx.m_cseContext0);
    V3DfgPasses::peephole(*dfgp, ctx.m_peepholeContext);
    V3DfgPasses::pushDownSels(*dfgp, ctx.m_pushDownSelsContext);
    V3DfgPasses::cse(*dfgp, ctx.m_cseContext1);
    V3DfgPasses::regularize(*dfgp, ctx.m_regularizeContext);
    const size_t localCount = locals.size();
    for (const DfgVertexVar& var : dfgp->varVertices()) locals.erase(var.vscp());
    V3Stats::addStatSum("DFG scoped, local definitions", localCount);
    V3Stats::addStatSum("DFG scoped, locals removed", locals.size());
    limitBlockExpressions(*dfgp, expressionLimit);
    for (const DfgVertexVar& var : dfgp->varVertices()) {
        if (var.hasExtRefs()) continue;  // Existing bindings keep their attributes.
        var.vscp()->varp()->isInternal(true);
        var.vscp()->varp()->noReset(true);
        var.vscp()->varp()->trace(false);
    }
    std::vector<AstNodeStmt*> result = V3DfgPasses::dfgToBlock(*dfgp, ctx);
    V3Stats::addStatSum("DFG scoped, blocks", 1);
    V3Stats::addStatSum("DFG scoped, input vertices", before);
    V3Stats::addStatSum("DFG scoped, output vertices", dfgp->size());
    VNDeleter deleter;
    for (AstNodeStmt* const stmtp : statements) deleter.pushDeletep(stmtp);
    statements = std::move(result);
    dfgp.reset();
    DfgDataType::reset();
    return true;
}
