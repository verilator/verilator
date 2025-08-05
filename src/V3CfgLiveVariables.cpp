// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: CFG liveness analysis
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
// Classical data flow analysis computing live variables input to a CFG
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

    struct BlockState final {
        std::unordered_set<Variable*> m_gen;
        std::unordered_set<Variable*> m_kill;
        std::unordered_set<Variable*> m_liveIn;
        std::unordered_set<Variable*> m_liveOut;
        bool m_isOnWorkList = false;
        bool m_wasProcessed = false;  // Already processed at least once
    };

    // STATE
    const ControlFlowGraph& m_cfg;  // The CFG beign analysed
    BasicBlockMap<BlockState> m_blockState{m_cfg};  // State for each block
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

    static AstVar* getAstVar(Variable* varp) {
        // TODO: remove the useless reinterpret_casts when C++17 'if constexpr' actually works
        if VL_CONSTEXPR_CXX17 (T_Scoped) {
            return reinterpret_cast<AstVarScope*>(varp)->varp();
        } else {
            return reinterpret_cast<AstVar*>(varp);
        }
    }

    // This is to match DFG, but can be extended independently
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
        AstVar* const astVarp = getAstVar(varp);
        if (astVarp->ignoreSchedWrite()) return true;
        return false;
    }

    void updateGen(AstNode* nodep) {
        nodep->foreach([&](AstNodeVarRef* refp) {
            // Cross reference is ambiguous
            if (VN_IS(refp, VarXRef)) {
                m_abort = true;
                return;
            }
            // Only care about reads
            if (refp->access().isWriteOnly()) return;
            // Grab referenced variable
            Variable* const tgtp = getTarget(refp);
            // Bail if not a compatible type
            if (incompatible(tgtp)) {
                m_abort = true;
                return;
            }
            // Add to gen set, if not killed - assume whole variable read
            if (m_currp->m_kill.count(tgtp)) return;
            m_currp->m_gen.emplace(tgtp);
        });
    }

    void updateKill(AstNode* nodep) {
        nodep->foreach([&](AstNodeVarRef* refp) {
            // Cross reference is ambiguous
            if (VN_IS(refp, VarXRef)) {
                m_abort = true;
                return;
            }
            // Only care about writes
            if (refp->access().isReadOnly()) return;
            // Grab referenced variable
            Variable* const tgtp = getTarget(refp);
            // Bail if not a compatible type
            if (incompatible(tgtp)) {
                m_abort = true;
                return;
            }
            // If whole written, add to kill set
            if (refp->nextp()) return;
            if (VN_IS(refp->abovep(), Sel)) return;
            m_currp->m_kill.emplace(tgtp);
        });
    }

    void single(AstNode* nodep) {
        if (m_abort) return;
        // Assume all reads hapen before any writes
        updateGen(nodep);
        updateKill(nodep);
    }

    // Apply transfer function of block, return true if changed
    bool transfer(const BasicBlock& bb) {
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
    void visit(AstDisplay* nodep) override { single(nodep); }
    void visit(AstFinish* nodep) override { single(nodep); }
    void visit(AstStmtExpr* nodep) override { single(nodep); }
    void visit(AstStop* nodep) override { single(nodep); }

    // Only the condition check belongs to the terminated basic block
    void visit(AstIf* nodep) override { single(nodep->condp()); }
    void visit(AstWhile* nodep) override { single(nodep->condp()); }

    // CONSTRUCTOR
    CfgLiveVariables(const ControlFlowGraph& cfg)
        : m_cfg{cfg} {
        // For each basic block, compute the gen and kill set via visit
        cfg.foreach([&](const BasicBlock& bb) {
            VL_RESTORER(m_currp);
            m_currp = &m_blockState[bb];
            for (AstNode* const stmtp : bb.stmtps()) iterateConst(stmtp);
            if (m_abort) return;
        });

        // Perform the flow analysis
        std::deque<const BasicBlock*> workList;
        const auto enqueue = [&](const BasicBlock& bb) {
            BlockState& state = m_blockState[bb];
            if (state.m_isOnWorkList) return;
            state.m_isOnWorkList = true;
            workList.emplace_back(&bb);
        };

        enqueue(cfg.exit());

        while (!workList.empty()) {
            const BasicBlock* const currp = workList.front();
            workList.pop_front();
            BlockState& state = m_blockState[*currp];
            state.m_isOnWorkList = false;

            // Compute meet (liveOut = union liveIn of successors)
            currp->forEachSuccessor([&](const BasicBlock& bb) {
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
    static std::unique_ptr<std::vector<Variable*>> apply(const ControlFlowGraph& cfg) {
        CfgLiveVariables analysis{cfg};
        // If failed, return nullptr
        if (analysis.m_abort) return nullptr;
        // Gather variables live in to the entry block
        const auto& enterLiveIn = analysis.m_blockState[cfg.enter()].m_liveIn;
        std::unique_ptr<std::vector<Variable*>> resultp{new std::vector<Variable*>{}};
        resultp->reserve(enterLiveIn.size());
        for (const auto& pair : enterLiveIn) resultp->emplace_back(pair);
        // Sort for stability
        std::stable_sort(resultp->begin(), resultp->end(),
                         [](Variable* ap, Variable* bp) { return ap->name() < bp->name(); });
        return resultp;
    }
};

std::unique_ptr<std::vector<AstVar*>> V3Cfg::liveVars(const ControlFlowGraph& cfg) {
    return CfgLiveVariables</* T_Scoped: */ false>::apply(cfg);
}

std::unique_ptr<std::vector<AstVarScope*>> V3Cfg::liveVarScopes(const ControlFlowGraph& cfg) {
    return CfgLiveVariables</* T_Scoped: */ true>::apply(cfg);
}
