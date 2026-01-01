// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: CFG liveness analysis
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
// Classical data flow analysis computing live variables input to a CFG
// https://en.wikipedia.org/wiki/Live-variable_analysis
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3Ast.h"
#include "V3Cfg.h"

#include <limits>
#include <memory>
#include <unordered_map>

VL_DEFINE_DEBUG_FUNCTIONS;

template <bool T_Scoped>
class CfgLiveVariables final : VNVisitorConst {
    // TYPES
    using Variable = std::conditional_t<T_Scoped, AstVarScope, AstVar>;

    // State associted with each basic block
    struct BlockState final {
        // Variables used in block, before a complete assignment in the same block
        std::unordered_set<Variable*> m_gen;
        // Variables that are assigned a complete value in the basic block
        std::unordered_set<Variable*> m_kill;
        std::unordered_set<Variable*> m_liveIn;  // Variables live on entry to the block
        std::unordered_set<Variable*> m_liveOut;  // Variables live on exit from the block
        bool m_isOnWorkList = false;  // Block is on work list
        bool m_wasProcessed = false;  // Already processed at least once
    };

    // STATE
    const CfgGraph& m_cfg;  // The CFG beign analysed
    // State for each block
    CfgBlockMap<BlockState> m_blockState{m_cfg.makeBlockMap<BlockState>()};
    BlockState* m_currp = nullptr;  // State of current block being analysed
    bool m_abort = false;  // Abort analysis - unhandled construct

    // METHODS
    static Variable* getTarget(const AstNodeVarRef* refp) {
        // TODO: remove the useless reinterpret_casts when C++17 'if constexpr' actually works
        if VL_CONSTEXPR_CXX17 (T_Scoped) {
            return reinterpret_cast<Variable*>(refp->varScopep());
        } else {
            return reinterpret_cast<Variable*>(refp->varp());
        }
    }

    // This is to match DFG, but can be extended independently - eventually should handle all
    static bool isSupportedPackedDType(const AstNodeDType* dtypep) {
        dtypep = dtypep->skipRefp();
        if (const AstBasicDType* const typep = VN_CAST(dtypep, BasicDType)) {
            return typep->keyword().isIntNumeric();
        }
        if (const AstPackArrayDType* const typep = VN_CAST(dtypep, PackArrayDType)) {
            return isSupportedPackedDType(typep->subDTypep());
        }
        if (const AstNodeUOrStructDType* const typep = VN_CAST(dtypep, NodeUOrStructDType)) {
            return typep->packed();
        }
        return false;
    }

    // Check and return if variable is incompatible
    bool incompatible(Variable* varp) {
        if (!isSupportedPackedDType(varp->dtypep())) return true;
        const AstVar* astVarp = nullptr;
        // TODO: remove the useless reinterpret_casts when C++17 'if constexpr' actually works
        if VL_CONSTEXPR_CXX17 (T_Scoped) {
            astVarp = reinterpret_cast<AstVarScope*>(varp)->varp();
        } else {
            astVarp = reinterpret_cast<AstVar*>(varp);
        }
        if (astVarp->ignoreSchedWrite()) return true;
        return false;
    }

    void updateGen(AstNode* nodep) {
        UASSERT_OBJ(!m_abort, nodep, "Doing useless work");
        m_abort = nodep->exists([&](const AstNodeVarRef* refp) {
            // Cross reference is ambiguous
            if (VN_IS(refp, VarXRef)) return true;
            // Only care about reads
            if (refp->access().isWriteOnly()) return false;
            // Grab referenced variable
            Variable* const tgtp = getTarget(refp);
            // Bail if not a compatible type
            if (incompatible(tgtp)) return true;
            // Add to gen set, if not killed - assume whole variable read
            if (m_currp->m_kill.count(tgtp)) return false;
            m_currp->m_gen.emplace(tgtp);
            return false;
        });
    }

    void updateKill(AstNode* nodep) {
        UASSERT_OBJ(!m_abort, nodep, "Doing useless work");
        m_abort = nodep->exists([&](const AstNodeVarRef* refp) {
            // Cross reference is ambiguous
            if (VN_IS(refp, VarXRef)) return true;
            // Only care about writes
            if (refp->access().isReadOnly()) return false;
            // Grab referenced variable
            Variable* const tgtp = getTarget(refp);
            // Bail if not a compatible type
            if (incompatible(tgtp)) return true;
            // If whole written, add to kill set
            if (refp->nextp()) return false;
            if (VN_IS(refp->abovep(), Sel)) return false;
            m_currp->m_kill.emplace(tgtp);
            return false;
        });
    }

    void single(AstNode* nodep) {
        // Assume all reads hapen before any writes
        if (m_abort) return;
        updateGen(nodep);
        if (m_abort) return;
        updateKill(nodep);
    }

    // Apply transfer function of block, return true if changed
    bool transfer(const CfgBlock& bb) {
        BlockState& state = m_blockState[bb];

        // liveIn = gen union (liveOut - kill)
        std::unordered_set<Variable*> liveIn = state.m_gen;
        for (Variable* const varp : state.m_liveOut) {
            if (state.m_kill.count(varp)) continue;
            liveIn.insert(varp);
        }
        if (liveIn == state.m_liveIn) return false;
        std::swap(liveIn, state.m_liveIn);
        return true;
    }

    // VISIT
    void visit(AstNode* nodep) override {  //
        UASSERT_OBJ(!m_abort, nodep, "Repeat traversal after abort");
        m_abort = true;
        UINFO(9, "Unhandled AstNode type " << nodep->typeName());
    }

    void visit(AstAssign* nodep) override { single(nodep); }
    void visit(AstAssignW* nodep) override { single(nodep); }
    void visit(AstDisplay* nodep) override { single(nodep); }
    void visit(AstFinish* nodep) override { single(nodep); }
    void visit(AstFinishFork* nodep) override { single(nodep); }
    void visit(AstStmtExpr* nodep) override { single(nodep); }
    void visit(AstStop* nodep) override { single(nodep); }

    // Only the condition check belongs to the terminated basic block
    void visit(AstIf* nodep) override { single(nodep->condp()); }
    void visit(AstLoopTest* nodep) override { single(nodep->condp()); }

    // CONSTRUCTOR
    explicit CfgLiveVariables(const CfgGraph& cfg)
        : m_cfg{cfg} {
        // For each basic block, compute the gen and kill set via visit
        for (const V3GraphVertex& vtx : cfg.vertices()) {
            const CfgBlock& bb = static_cast<const CfgBlock&>(vtx);
            if (m_abort) return;
            VL_RESTORER(m_currp);
            m_currp = &m_blockState[bb];
            for (AstNode* const stmtp : bb.stmtps()) iterateConst(stmtp);
        }
        if (m_abort) return;

        // Perform the flow analysis
        std::deque<const CfgBlock*> workList;
        const auto enqueue = [&](const CfgBlock& bb) {
            BlockState& state = m_blockState[bb];
            if (state.m_isOnWorkList) return;
            state.m_isOnWorkList = true;
            workList.emplace_back(&bb);
        };

        enqueue(cfg.exit());

        while (!workList.empty()) {
            const CfgBlock* const currp = workList.front();
            workList.pop_front();
            BlockState& state = m_blockState[*currp];
            state.m_isOnWorkList = false;

            // Compute meet (liveOut = union liveIn of successors)
            currp->forEachSuccessor([&](const CfgBlock& bb) {
                auto& liveIn = m_blockState[bb].m_liveIn;
                state.m_liveOut.insert(liveIn.begin(), liveIn.end());
            });

            // Apply transfer function of block
            const bool changed = transfer(*currp);
            // Enqueue predecessors
            if (changed || !state.m_wasProcessed) currp->forEachPredecessor(enqueue);
            // Mark as done with first visit
            state.m_wasProcessed = true;
        }
    }

public:
    static std::unique_ptr<std::vector<Variable*>> apply(const CfgGraph& cfg) {
        CfgLiveVariables analysis{cfg};
        // If failed, return nullptr
        if (analysis.m_abort) return nullptr;
        // Gather variables live in to the entry blockstd::unique_ptr<std::vector<Variable*>>
        const std::unordered_set<Variable*>& lin = analysis.m_blockState[cfg.enter()].m_liveIn;
        std::vector<Variable*>* const resultp = new std::vector<Variable*>{lin.begin(), lin.end()};
        // Sort for stability
        std::stable_sort(resultp->begin(), resultp->end(), [](Variable* ap, Variable* bp) {  //
            return ap->name() < bp->name();
        });
        return std::unique_ptr<std::vector<Variable*>>{resultp};
    }
};

std::unique_ptr<std::vector<AstVar*>> V3Cfg::liveVars(const CfgGraph& cfg) {
    return CfgLiveVariables</* T_Scoped: */ false>::apply(cfg);
}

std::unique_ptr<std::vector<AstVarScope*>> V3Cfg::liveVarScopes(const CfgGraph& cfg) {
    return CfgLiveVariables</* T_Scoped: */ true>::apply(cfg);
}
