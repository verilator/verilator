// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Dataflow based optimization of combinational logic
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
//
// High level entry points from Ast world to the DFG optimizer.
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3DfgOptimizer.h"

#include "V3Ast.h"
#include "V3AstUserAllocator.h"
#include "V3Dfg.h"
#include "V3DfgPasses.h"
#include "V3Error.h"
#include "V3Global.h"
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
    using Candidates = std::vector<std::pair<AstNodeMath*, std::vector<const AstVar*>>>;

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
        UASSERT_OBJ(!VN_IS(nodep->backp(), NodeMath), nodep,
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
        m_candidatesp->emplace_back(VN_AS(nodep, NodeMath), std::move(m_readVars));
    }

    // VISIT methods

    void visit(AstNetlist* nodep) override {
        // Analyse the whole design
        iterateChildrenConst(nodep);

        // Replace candidate expressions only reading combinationally driven signals with variables
        V3UniqueNames names{"__VdfgExtracted"};
        for (AstNodeModule* modp = nodep->modulesp(); modp;
             modp = VN_AS(modp->nextp(), NodeModule)) {
            // Only extract from proper modules
            if (!VN_IS(modp, Module)) continue;

            for (const auto& pair : m_extractionCandidates(modp)) {
                AstNodeMath* const nodep = pair.first;

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
                FileLine* const flp = nodep->fileline();
                const string name = names.get(nodep);
                AstVar* const varp = new AstVar{flp, VVarType::MODULETEMP, name, nodep->dtypep()};
                varp->trace(false);
                modp->addStmtsp(varp);

                // Replace expression with temporary variable
                nodep->replaceWith(new AstVarRef{flp, varp, VAccess::READ});

                // Add assignment driving temporary variable
                modp->addStmtsp(
                    new AstAssignW{flp, new AstVarRef{flp, varp, VAccess::WRITE}, nodep});
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
        const bool isComb = !nodep->sensesp()
                            && (nodep->keyword() == VAlwaysKwd::ALWAYS
                                || nodep->keyword() == VAlwaysKwd::ALWAYS_COMB
                                || nodep->keyword() == VAlwaysKwd::ALWAYS_LATCH);
        m_candidatesp
            = isComb && VN_IS(m_modp, Module) ? &m_extractionCandidates(m_modp) : nullptr;
        iterateChildrenConst(nodep);
    }

    void visit(AstAssignW* nodep) override {
        // Mark LHS variable as combinationally driven
        if (AstVarRef* const vrefp = VN_CAST(nodep->lhsp(), VarRef)) vrefp->varp()->user4(true);
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
        iterate(nodep->rhsp());
        UASSERT_OBJ(!m_inForceReleaseLhs, nodep, "Should not nest");
        m_inForceReleaseLhs = true;
        iterate(nodep->lhsp());
        m_inForceReleaseLhs = false;
    }

    void visit(AstRelease* nodep) override {
        UASSERT_OBJ(!m_inForceReleaseLhs, nodep, "Should not nest");
        m_inForceReleaseLhs = true;
        iterate(nodep->lhsp());
        m_inForceReleaseLhs = false;
    }

    void visit(AstNodeMath* nodep) override { iterateChildrenConst(nodep); }

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
        // as AstNodeFTaskRef are sadly not AstNodeMath.
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
    UINFO(2, __FUNCTION__ << ": " << endl);
    // Extract more optimization candidates
    DataflowExtractVisitor::apply(netlistp);
    V3Global::dumpCheckGlobalTree("dfg-extract", 0, dumpTree() >= 3);
}

void V3DfgOptimizer::optimize(AstNetlist* netlistp, const string& label) {
    UINFO(2, __FUNCTION__ << ": " << endl);

    // NODE STATE
    // AstVar::user1        -> Used by V3DfgPasses::astToDfg
    // AstVar::user2        -> bool: Flag indicating referenced by AstVarXRef
    const VNUser2InUse user2InUse;

    // Mark cross-referenced variables
    netlistp->foreach([](const AstVarXRef* xrefp) { xrefp->varp()->user2(true); });

    V3DfgOptimizationContext ctx{label};

    // Run the optimization phase
    for (AstNode* nodep = netlistp->modulesp(); nodep; nodep = nodep->nextp()) {
        // Only optimize proper modules
        AstModule* const modp = VN_CAST(nodep, Module);
        if (!modp) continue;

        UINFO(4, "Applying DFG optimization to module '" << modp->name() << "'" << endl);
        ++ctx.m_modules;

        // Build the DFG of this module
        const std::unique_ptr<DfgGraph> dfg{V3DfgPasses::astToDfg(*modp, ctx)};
        if (dumpDfg() >= 8) dfg->dumpDotFilePrefixed(ctx.prefix() + "whole-input");

        // Extract the cyclic sub-graphs. We do this because a lot of the optimizations assume a
        // DAG, and large, mostly acyclic graphs could not be optimized due to the presence of
        // small cycles.
        const std::vector<std::unique_ptr<DfgGraph>>& cyclicComponents
            = dfg->extractCyclicComponents("cyclic");

        // Split the remaining acyclic DFG into [weakly] connected components
        const std::vector<std::unique_ptr<DfgGraph>>& acyclicComponents
            = dfg->splitIntoComponents("acyclic");

        // Quick sanity check
        UASSERT_OBJ(dfg->size() == 0, nodep, "DfgGraph should have become empty");

        // For each cyclic component
        for (auto& component : cyclicComponents) {
            if (dumpDfg() >= 7) component->dumpDotFilePrefixed(ctx.prefix() + "source");
            // TODO: Apply optimizations safe for cyclic graphs
            // Add back under the main DFG (we will convert everything back in one go)
            dfg->addGraph(*component);
        }

        // For each acyclic component
        for (auto& component : acyclicComponents) {
            if (dumpDfg() >= 7) component->dumpDotFilePrefixed(ctx.prefix() + "source");
            // Optimize the component
            V3DfgPasses::optimize(*component, ctx);
            // Add back under the main DFG (we will convert everything back in one go)
            dfg->addGraph(*component);
        }

        // Convert back to Ast
        if (dumpDfg() >= 8) dfg->dumpDotFilePrefixed(ctx.prefix() + "whole-optimized");
        AstModule* const resultModp = V3DfgPasses::dfgToAst(*dfg, ctx);
        UASSERT_OBJ(resultModp == modp, modp, "Should be the same module");
    }
    V3Global::dumpCheckGlobalTree("dfg-optimize", 0, dumpTree() >= 3);
}
