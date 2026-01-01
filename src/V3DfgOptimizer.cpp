// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Dataflow based optimization of combinational logic
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
// High level entry points from Ast world to the DFG optimizer.
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3DfgOptimizer.h"

#include "V3AstUserAllocator.h"
#include "V3Dfg.h"
#include "V3DfgPasses.h"
#include "V3Graph.h"
#include "V3UniqueNames.h"

#include <vector>

VL_DEFINE_DEBUG_FUNCTIONS;

// Extract more combinational logic equations from procedures for better optimization opportunities
class DataflowExtractVisitor final : public VNVisitor {
    // NODE STATE
    // AstVar::user3            -> bool: Flag indicating variable is subject of force or release
    // statement AstVar::user4  -> bool: Flag indicating variable is combinationally driven
    // AstNodeModule::user4     -> Extraction candidates (via m_extractionCandidates)
    const VNUser3InUse m_user3InUse;
    const VNUser4InUse m_user4InUse;

    // Expressions considered for extraction as separate assignment to gain more opportunities for
    // optimization, together with the list of variables they read.
    using Candidates = std::vector<std::pair<AstNodeExpr*, std::vector<const AstVar*>>>;

    // Expressions considered for extraction. All the candidates are pure expressions.
    AstUser4Allocator<AstNodeModule, Candidates> m_extractionCandidates;

    // STATE
    AstNodeModule* m_modp = nullptr;  // The module being visited
    Candidates* m_candidatesp = nullptr;
    bool m_impure = false;  // True if the visited tree has a side effect
    bool m_inForceReleaseLhs = false;  // Iterating LHS of force/release
    // List of AstVar nodes read by the visited tree. 'vector' rather than 'set' as duplicates are
    // somewhat unlikely and we can handle them later.
    std::vector<const AstVar*> m_readVars;

    // METHODS

    // Node considered for extraction as a combinational equation. Trace variable usage/purity.
    void iterateExtractionCandidate(AstNode* nodep) {
        UASSERT_OBJ(!VN_IS(nodep->backp(), NodeExpr), nodep,
                    "Should not try to extract nested expressions (only root expressions)");

        // Simple VarRefs should not be extracted, as they only yield trivial assignments.
        // Similarly, don't extract anything if no candidate map is set up (for non-modules).
        // We still need to visit them though, to mark hierarchical references.
        if (VN_IS(nodep, NodeVarRef) || !m_candidatesp) {
            iterate(nodep);
            return;
        }

        // Don't extract plain constants
        if (VN_IS(nodep, Const)) return;

        // Candidates can't nest, so no need for VL_RESTORER, just initialize iteration state
        m_impure = false;
        m_readVars.clear();

        // Trace variable usage
        iterate(nodep);

        // We only extract pure expressions
        if (m_impure) return;

        // Do not extract expressions without any variable references
        if (m_readVars.empty()) return;

        // Add to candidate list
        m_candidatesp->emplace_back(VN_AS(nodep, NodeExpr), std::move(m_readVars));
    }

    // VISIT methods

    void visit(AstNetlist* nodep) override {
        // Analyze the whole design
        iterateChildrenConst(nodep);

        // Replace candidate expressions only reading combinationally driven signals with variables
        V3UniqueNames names{"__VdfgExtracted"};
        for (AstNodeModule* modp = nodep->modulesp(); modp;
             modp = VN_AS(modp->nextp(), NodeModule)) {
            // Only extract from proper modules
            if (!VN_IS(modp, Module)) continue;

            for (const auto& pair : m_extractionCandidates(modp)) {
                AstNodeExpr* const cnodep = pair.first;

                // Do not extract expressions without any variable references
                if (pair.second.empty()) continue;

                // Check if all variables read by this expression are driven combinationally,
                // and move on if not. Also don't extract it if one of the variables is subject
                // to a force/release, as releasing nets must have immediate effect, but adding
                // extra combinational logic can change semantics (see t_force_release_net*).
                {
                    bool hasBadVar = false;
                    for (const AstVar* const readVarp : pair.second) {
                        // variable is target of force/release or not combinationally driven
                        if (readVarp->user3() || !readVarp->user4()) {
                            hasBadVar = true;
                            break;
                        }
                    }
                    if (hasBadVar) continue;
                }

                // Create temporary variable
                FileLine* const flp = cnodep->fileline();
                const string name = names.get(cnodep);
                AstVar* const varp = new AstVar{flp, VVarType::MODULETEMP, name, cnodep->dtypep()};
                varp->trace(false);
                modp->addStmtsp(varp);

                // Replace expression with temporary variable
                cnodep->replaceWith(new AstVarRef{flp, varp, VAccess::READ});

                // Add assignment driving temporary variable
                AstAssignW* const ap
                    = new AstAssignW{flp, new AstVarRef{flp, varp, VAccess::WRITE}, cnodep};
                modp->addStmtsp(new AstAlways{ap});
            }
        }
    }

    void visit(AstNodeModule* nodep) override {
        VL_RESTORER(m_modp);
        m_modp = nodep;
        iterateChildrenConst(nodep);
    }

    void visit(AstAlways* nodep) override {
        VL_RESTORER(m_candidatesp);
        // Only extract from combinational logic under proper modules
        const bool isComb = !nodep->sentreep()
                            && (nodep->keyword() == VAlwaysKwd::ALWAYS
                                || nodep->keyword() == VAlwaysKwd::ALWAYS_COMB
                                || nodep->keyword() == VAlwaysKwd::ALWAYS_LATCH);
        m_candidatesp
            = isComb && VN_IS(m_modp, Module) ? &m_extractionCandidates(m_modp) : nullptr;
        iterateChildrenConst(nodep);
    }

    void visit(AstAssignW* nodep) override {
        // Mark LHS variable as combinationally driven
        if (const AstVarRef* const vrefp = VN_CAST(nodep->lhsp(), VarRef)) {
            vrefp->varp()->user4(true);
        }
        //
        iterateChildrenConst(nodep);
    }

    void visit(AstAssign* nodep) override {
        iterateExtractionCandidate(nodep->rhsp());
        iterate(nodep->lhsp());
    }

    void visit(AstAssignDly* nodep) override {
        iterateExtractionCandidate(nodep->rhsp());
        iterate(nodep->lhsp());
    }

    void visit(AstIf* nodep) override {
        iterateExtractionCandidate(nodep->condp());
        iterateAndNextConstNull(nodep->thensp());
        iterateAndNextConstNull(nodep->elsesp());
    }

    void visit(AstAssignForce* nodep) override {
        VL_RESTORER(m_inForceReleaseLhs);
        iterate(nodep->rhsp());
        UASSERT_OBJ(!m_inForceReleaseLhs, nodep, "Should not nest");
        m_inForceReleaseLhs = true;
        iterate(nodep->lhsp());
    }

    void visit(AstRelease* nodep) override {
        VL_RESTORER(m_inForceReleaseLhs);
        UASSERT_OBJ(!m_inForceReleaseLhs, nodep, "Should not nest");
        m_inForceReleaseLhs = true;
        iterate(nodep->lhsp());
    }

    void visit(AstNodeExpr* nodep) override { iterateChildrenConst(nodep); }

    void visit(AstNodeVarRef* nodep) override {
        if (nodep->access().isWriteOrRW()) {
            // If it writes a variable, mark as impure
            m_impure = true;
            // Mark target of force/release
            if (m_inForceReleaseLhs) nodep->varp()->user3(true);
        } else {
            // Otherwise, add read reference
            m_readVars.push_back(nodep->varp());
        }
    }

    void visit(AstNode* nodep) override {
        // Conservatively assume unhandled nodes are impure. This covers all AstNodeFTaskRef
        // as AstNodeFTaskRef are sadly not AstNodeExpr.
        m_impure = true;
        // Still need to gather all references/force/release, etc.
        iterateChildrenConst(nodep);
    }

    // CONSTRUCTOR
    explicit DataflowExtractVisitor(AstNetlist* netlistp) { iterate(netlistp); }

public:
    static void apply(AstNetlist* netlistp) { DataflowExtractVisitor{netlistp}; }
};

void V3DfgOptimizer::extract(AstNetlist* netlistp) {
    UINFO(2, __FUNCTION__ << ":");
    // Extract more optimization candidates
    DataflowExtractVisitor::apply(netlistp);
    V3Global::dumpCheckGlobalTree("dfg-extract", 0, dumpTreeEitherLevel() >= 3);
}

class DataflowOptimize final {
    // NODE STATE
    // AstVar::user1, AstVarScope::user1 -> int, used as a bit-field
    // - bit0: Read via AstVarXRef (hierarchical reference)
    // - bit1: Written via AstVarXRef (hierarchical reference)
    // - bit2: Read by logic in same module/netlist not represented in DFG
    // - bit3: Written by logic in same module/netlist not represented in DFG
    // - bit31-4: Reference count, how many DfgVertexVar represent this variable
    //
    // AstNode::user2/user3/user4 can be used by various DFG algorithms
    const VNUser1InUse m_user1InUse;

    // STATE
    V3DfgContext m_ctx;  // The context holding values that need to persist across multiple graphs

    static void markExternallyReferencedVariables(AstNetlist* netlistp, bool scoped) {
        netlistp->foreach([scoped](AstNode* nodep) {
            // Check variable flags
            if (scoped) {
                if (AstVarScope* const vscp = VN_CAST(nodep, VarScope)) {
                    const AstVar* const varp = vscp->varp();
                    // Force and trace have already been processed
                    const bool hasExtRd = varp->isPrimaryIO() || varp->isSigUserRdPublic();
                    const bool hasExtWr = varp->isPrimaryIO() || varp->isSigUserRWPublic();
                    if (hasExtRd) DfgVertexVar::setHasExtRdRefs(vscp);
                    if (hasExtWr) DfgVertexVar::setHasExtWrRefs(vscp);
                    return;
                }
                // TODO: remove once Actives can tolerate NEVER SenItems
                if (AstSenItem* senItemp = VN_CAST(nodep, SenItem)) {
                    senItemp->foreach([](const AstVarRef* refp) {
                        DfgVertexVar::setHasExtRdRefs(refp->varScopep());
                    });
                }
            } else {
                if (AstVar* const varp = VN_CAST(nodep, Var)) {
                    const bool hasExtRd = varp->isPrimaryIO() || varp->isSigUserRdPublic()  //
                                          || varp->isForced() || varp->isTrace();
                    const bool hasExtWr = varp->isPrimaryIO() || varp->isSigUserRWPublic()  //
                                          || varp->isForced();
                    if (hasExtRd) DfgVertexVar::setHasExtRdRefs(varp);
                    if (hasExtWr) DfgVertexVar::setHasExtWrRefs(varp);
                    return;
                }
            }
            // Check hierarchical references
            if (const AstVarXRef* const xrefp = VN_CAST(nodep, VarXRef)) {
                AstVar* const tgtp = xrefp->varp();
                if (!tgtp) return;
                if (xrefp->access().isReadOrRW()) DfgVertexVar::setHasExtRdRefs(tgtp);
                if (xrefp->access().isWriteOrRW()) DfgVertexVar::setHasExtWrRefs(tgtp);
                return;
            }
            // Check cell ports
            if (const AstCell* const cellp = VN_CAST(nodep, Cell)) {
                for (const AstPin *pinp = cellp->pinsp(), *nextp; pinp; pinp = nextp) {
                    nextp = VN_AS(pinp->nextp(), Pin);
                    AstVar* const tgtp = pinp->modVarp();
                    if (!tgtp) return;
                    const VDirection dir = tgtp->direction();
                    // hasExtRd/hasExtWr from perspective of Pin
                    const bool hasExtRd = dir == VDirection::OUTPUT || dir.isInoutOrRef();
                    const bool hasExtWr = dir == VDirection::INPUT || dir.isInoutOrRef();
                    if (hasExtRd) DfgVertexVar::setHasExtRdRefs(tgtp);
                    if (hasExtWr) DfgVertexVar::setHasExtWrRefs(tgtp);
                }
                return;
            }
        });
    }

    void optimize(DfgGraph& dfg) {
        // Dump the initial graph for debugging
        if (dumpDfgLevel() >= 8) dfg.dumpDotFilePrefixed(m_ctx.prefix() + "dfg-in");

        // Synthesize DfgLogic vertices
        V3DfgPasses::synthesize(dfg, m_ctx);
        if (dumpDfgLevel() >= 8) dfg.dumpDotFilePrefixed(m_ctx.prefix() + "synth");

        // Extract the cyclic sub-graphs. We do this because a lot of the optimizations assume a
        // DAG, and large, mostly acyclic graphs could not be optimized due to the presence of
        // small cycles.
        std::vector<std::unique_ptr<DfgGraph>> cyclicComponents
            = dfg.extractCyclicComponents("cyclic");

        // Attempt to convert cyclic components into acyclic ones
        std::vector<std::unique_ptr<DfgGraph>> madeAcyclicComponents;
        if (v3Global.opt.fDfgBreakCycles()) {
            for (auto it = cyclicComponents.begin(); it != cyclicComponents.end();) {
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
                    it = cyclicComponents.erase(it);
                }
            }
        }
        // Merge those that were made acyclic back to the graph, this enables optimizing more
        dfg.mergeGraphs(std::move(madeAcyclicComponents));

        // Split the acyclic DFG into [weakly] connected components
        std::vector<std::unique_ptr<DfgGraph>> acyclicComponents
            = dfg.splitIntoComponents("acyclic");

        // Quick sanity check
        UASSERT(dfg.size() == 0, "DfgGraph should have become empty");

        // Optimize each acyclic component
        for (const std::unique_ptr<DfgGraph>& component : acyclicComponents) {
            V3DfgPasses::optimize(*component, m_ctx);
        }

        // Merge everything back under the main DFG
        dfg.mergeGraphs(std::move(acyclicComponents));
        dfg.mergeGraphs(std::move(cyclicComponents));
        if (dumpDfgLevel() >= 8) dfg.dumpDotFilePrefixed(m_ctx.prefix() + "optimized");

        // Regularize the graph after merging it all back together so all
        // references are known and we only need to iterate the Ast once
        // to replace redundant variables.
        V3DfgPasses::regularize(dfg, m_ctx.m_regularizeContext);

        // Dump the final graph for debugging
        if (dumpDfgLevel() >= 8) dfg.dumpDotFilePrefixed(m_ctx.prefix() + "dfg-out");
    }

    DataflowOptimize(AstNetlist* netlistp, const string& label)
        : m_ctx{label} {

        // Mark interfaces that might be referenced by a virtual interface
        if (v3Global.hasVirtIfaces()) {
            netlistp->typeTablep()->foreach([](const AstIfaceRefDType* nodep) {
                if (!nodep->isVirtual()) return;
                nodep->ifaceViaCellp()->setHasVirtualRef();
            });
        }

        // Running after V3Scope
        const bool scoped = netlistp->topScopep();

        // Mark variables with external references
        markExternallyReferencedVariables(netlistp, scoped);

        if (!scoped) {
            // Pre V3Scope application. Run on each module separately.
            for (AstNode* nodep = netlistp->modulesp(); nodep; nodep = nodep->nextp()) {
                // Only optimize proper modules
                AstModule* const modp = VN_CAST(nodep, Module);
                if (!modp) continue;
                // Pre V3Scope application. Run on module.
                UINFO(4, "Applying DFG optimization to module '" << modp->name() << "'");
                ++m_ctx.m_modules;
                // Build the DFG of this module or netlist
                const std::unique_ptr<DfgGraph> dfgp = V3DfgPasses::astToDfg(*modp, m_ctx);
                // Actually process the graph
                optimize(*dfgp);
                // Convert back to Ast
                V3DfgPasses::dfgToAst(*dfgp, m_ctx);
            }
        } else {
            // Post V3Scope application. Run on whole netlist.
            UINFO(4, "Applying DFG optimization to entire netlist");
            // Build the DFG of the entire netlist
            const std::unique_ptr<DfgGraph> dfgp = V3DfgPasses::astToDfg(*netlistp, m_ctx);
            // Actually process the graph
            optimize(*dfgp);
            // Convert back to Ast
            V3DfgPasses::dfgToAst(*dfgp, m_ctx);
        }

        // Reset interned types so the corresponding Ast types can be garbage collected
        DfgDataType::reset();
    }

public:
    static void apply(AstNetlist* netlistp, const string& label) {
        DataflowOptimize{netlistp, label};
    }
};

void V3DfgOptimizer::optimize(AstNetlist* netlistp, const string& label) {
    UINFO(2, __FUNCTION__ << ":");
    DataflowOptimize::apply(netlistp, label);
    V3Global::dumpCheckGlobalTree("dfg-optimize", 0, dumpTreeEitherLevel() >= 3);
}
