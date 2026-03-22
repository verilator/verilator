// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Static initializer ordering
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
//
// V3Sched::scheduleStatic performs a dependency-oriented reordering of
// static initializers.
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Graph.h"
#include "V3GraphStream.h"
#include "V3Sched.h"

VL_DEFINE_DEBUG_FUNCTIONS;

namespace {

struct StaticLogic final {
    AstScope* m_scopep = nullptr;
    AstNode* m_nodep = nullptr;

    StaticLogic() = default;
    StaticLogic(AstScope* const scopep, AstNode* const nodep)
        : m_scopep{scopep}
        , m_nodep{nodep} {}
};

struct StaticLogicSummary final {
    std::unordered_set<AstVarScope*> m_reads;
    std::unordered_set<AstVarScope*> m_writes;
};

using ScopeVarMap = std::unordered_map<AstVar*, AstVarScope*>;

AstCFunc* createScopeSubFunc(AstCFunc* topFuncp, AstScope* scopep, const string& suffix) {
    const string subName{topFuncp->name() + "__" + scopep->nameDotless() + suffix};
    AstCFunc* const subFuncp = new AstCFunc{scopep->fileline(), subName, scopep};
    subFuncp->isLoose(true);
    subFuncp->isConst(false);
    subFuncp->declPrivate(true);
    subFuncp->slow(topFuncp->slow());
    scopep->addBlocksp(subFuncp);
    topFuncp->addStmtsp(V3Sched::util::callVoidFunc(subFuncp));
    return subFuncp;
}

const FileLine* fileLineOf(const StaticLogic& logic) {
    return logic.m_nodep ? logic.m_nodep->fileline() : nullptr;
}

bool fileLineLess(const StaticLogic& lhs, const StaticLogic& rhs) {
    const FileLine* const lhsFlp = fileLineOf(lhs);
    const FileLine* const rhsFlp = fileLineOf(rhs);
    if (!lhsFlp || !rhsFlp) return lhsFlp < rhsFlp;
    return lhsFlp->operatorCompare(*rhsFlp) < 0;
}

AstCFunc* staticSubFuncCallee(AstNodeStmt* stmtp) {
    if (AstStmtExpr* const sexprp = VN_CAST(stmtp, StmtExpr)) {
        if (AstCCall* const ccallp = VN_CAST(sexprp->exprp(), CCall)) return ccallp->funcp();
    }
    return nullptr;
}

// Collect reorderable static logic and dependencies induced by variable accesses.
class StaticLogicCollector final : public VNVisitorConst {
    std::vector<StaticLogic> m_logics;
    std::vector<StaticLogicSummary> m_summaries;
    std::vector<std::unordered_map<size_t, int>> m_depSucc;
    bool m_collectSubFuncs = false;
    AstScope* m_subScopep = nullptr;
    const ScopeVarMap* m_varMap = nullptr;
    StaticLogicSummary* m_summaryp = nullptr;
    std::unordered_set<AstCFunc*> m_calledFuncs;

    void collectStmt(AstScope* scopep, AstNodeStmt* stmtp) {
        stmtp->unlinkFrBack();
        m_logics.emplace_back(scopep, stmtp);
        m_summaries.emplace_back();
        m_summaryp = &m_summaries.back();
        m_calledFuncs.clear();
        iterateConst(stmtp);
        m_summaryp = nullptr;
    }

    void collectSubFunc(AstCFunc* subFuncp) {
        AstScope* const scopep = subFuncp->scopep();
        m_collectSubFuncs = true;
        m_subScopep = scopep;
        ScopeVarMap varMap;
        for (AstVarScope* vscp = scopep->varsp(); vscp; vscp = VN_AS(vscp->nextp(), VarScope)) {
            varMap.emplace(vscp->varp(), vscp);
        }
        m_varMap = &varMap;
        iterateConst(subFuncp);
        m_varMap = nullptr;
        m_subScopep = nullptr;
        m_collectSubFuncs = false;
    }

    void visitCallee(AstCFunc* funcp) {
        if (!m_calledFuncs.insert(funcp).second) return;
        iterateConst(funcp);
    }

    void visit(AstNodeStmt* nodep) override {
        if (m_summaryp) return iterateChildrenConst(nodep);
        if (m_collectSubFuncs) {
            collectStmt(m_subScopep, nodep);
            return;
        }
        iterateChildrenConst(nodep);
    }

    void visit(AstCCall* nodep) override {
        if (!m_summaryp) return;
        visitCallee(nodep->funcp());
        iterateChildrenConst(nodep);
    }
    void visit(AstCMethodCall* nodep) override {
        if (!m_summaryp) return;
        visitCallee(nodep->funcp());
        iterateChildrenConst(nodep);
    }
    void visit(AstCNew* nodep) override {
        if (!m_summaryp) return;
        visitCallee(nodep->funcp());
        iterateChildrenConst(nodep);
    }

    void visit(AstScope* nodep) override {
        if (!m_collectSubFuncs) iterateChildrenConst(nodep);
    }

    void visit(AstCFunc* nodep) override { iterateChildrenConst(nodep); }

    void visit(AstNodeVarRef* nodep) override {
        if (!m_summaryp) return;
        AstVarScope* const vscp = nodep->varScopep();
        if (!vscp) return;
        if (nodep->access().isReadOrRW()) m_summaryp->m_reads.insert(vscp);
        if (nodep->access().isWriteOrRW()
            && (!nodep->varp()->ignoreSchedWrite() || nodep->varp()->isConst())) {
            m_summaryp->m_writes.insert(vscp);
        }
    }
    void visit(AstVar* nodep) override {
        if (!m_summaryp || !m_varMap) return;
        if (nodep->valuep()) {
            const auto it = m_varMap->find(nodep);
            if (it != m_varMap->end()) { m_summaryp->m_writes.insert(it->second); }
        }
        iterateChildrenConst(nodep);
    }
    void visit(AstNode* nodep) override { iterateChildrenConst(nodep); }

    void buildDependencies(AstCFunc* funcp) {
        const size_t n = m_logics.size();
        UASSERT_OBJ(m_summaries.size() == n, funcp, "Static summaries out of sync with logic");
        m_depSucc.resize(n);
        std::unordered_map<AstVarScope*, std::vector<size_t>> scopeWriters;
        scopeWriters.reserve(n * 4);
        for (size_t i = 0; i < n; ++i) {
            for (AstVarScope* const vscp : m_summaries[i].m_writes)
                scopeWriters[vscp].push_back(i);
        }
        for (size_t readerIdx = 0; readerIdx < n; ++readerIdx) {
            for (AstVarScope* const vscp : m_summaries[readerIdx].m_reads) {
                const auto it = scopeWriters.find(vscp);
                if (it == scopeWriters.end()) continue;
                const int depWeight = (it->second.size() == 1) ? 2 : 1;
                for (const size_t writerIdx : it->second) {
                    if (writerIdx == readerIdx) continue;
                    auto& succ = m_depSucc[writerIdx];
                    const auto emplaced = succ.emplace(readerIdx, depWeight);
                    if (!emplaced.second && depWeight > emplaced.first->second) {
                        emplaced.first->second = depWeight;
                    }
                }
            }
        }
    }

public:
    explicit StaticLogicCollector(AstCFunc* const evalStaticp) {
        AstScope* const evalScopep = evalStaticp->scopep();
        UASSERT_OBJ(evalScopep, evalStaticp, "_eval_static must have a scope");
        // Split _eval_static into schedulable logic:
        //  - direct statements become top-scope logic
        //  - wrapper calls contribute their callee statements as logic in callee scope
        for (AstNode *nodep = evalStaticp->stmtsp(), *nextp; nodep; nodep = nextp) {
            nextp = nodep->nextp();
            if (AstNodeStmt* const stmtp = VN_CAST(nodep, NodeStmt)) {
                if (AstCFunc* const calleep = staticSubFuncCallee(stmtp)) {
                    collectSubFunc(calleep);
                } else {
                    collectStmt(evalScopep, stmtp);
                }
            }
        }
        buildDependencies(evalStaticp);
    }
    const std::vector<StaticLogic>& logics() const { return m_logics; }
    const std::vector<std::unordered_map<size_t, int>>& depSucc() const { return m_depSucc; }
};

class StaticLogicVertex final : public V3GraphVertex {
    size_t m_idx = 0;
    const StaticLogic* m_logicp = nullptr;

public:
    StaticLogicVertex(V3Graph* graphp, size_t idx, const StaticLogic* logicp)
        : V3GraphVertex{graphp}
        , m_idx{idx}
        , m_logicp{logicp} {}
    size_t idx() const { return m_idx; }
    const StaticLogic* logicp() const { return m_logicp; }
};

struct StaticLogicSeqLess final {
    bool operator()(const V3GraphVertex* a, const V3GraphVertex* b) const {
        const auto* const avtxp = static_cast<const StaticLogicVertex*>(a);
        const auto* const bvtxp = static_cast<const StaticLogicVertex*>(b);
        if (fileLineLess(*avtxp->logicp(), *bvtxp->logicp())) return true;
        if (fileLineLess(*bvtxp->logicp(), *avtxp->logicp())) return false;
        return avtxp->idx() < bvtxp->idx();
    }
};

void orderStaticEval(AstCFunc* funcp) {
    const VNUser1InUse user1InUse;  // AstCFunc -> bool: old static subfunc seen
    StaticLogicCollector collector{funcp};
    const std::vector<StaticLogic>& logics = collector.logics();

    if (logics.empty()) return;

    // Remove old wrapper calls/subfuncs before emitting reordered wrappers.
    for (AstNode *nodep = funcp->stmtsp(), *nextp; nodep; nodep = nextp) {
        nextp = nodep->nextp();
        AstNodeStmt* const stmtp = VN_CAST(nodep, NodeStmt);
        if (!stmtp) continue;
        AstCFunc* const subFuncp = staticSubFuncCallee(stmtp);
        if (!subFuncp) continue;
        if (subFuncp->backp()) {
            subFuncp->unlinkFrBack();
            VL_DO_DANGLING(subFuncp->deleteTree(), subFuncp);
        }
        stmtp->unlinkFrBack();
        VL_DO_DANGLING(stmtp->deleteTree(), stmtp);
    }

    const size_t n = logics.size();
    const std::vector<std::unordered_map<size_t, int>>& depSucc = collector.depSucc();
    UASSERT_OBJ(depSucc.size() == n, funcp, "Static dependencies out of sync with logic");

    V3Graph depGraph;
    std::vector<StaticLogicVertex*> logicVtxps;
    logicVtxps.reserve(n);
    for (size_t i = 0; i < n; ++i) {
        logicVtxps.push_back(new StaticLogicVertex{&depGraph, i, &logics[i]});
    }
    for (size_t from = 0; from < n; ++from) {
        for (const auto& dep : depSucc[from]) {
            new V3GraphEdge{&depGraph, logicVtxps[from], logicVtxps[dep.first], dep.second,
                            V3GraphEdge::CUTABLE};
        }
    }
    // Break dependency cycles conservatively, then drop cut edges so stream order
    // reflects only preserved dependencies.
    depGraph.acyclic(&V3GraphEdge::followAlwaysTrue);
    for (V3GraphVertex& vtx : depGraph.vertices()) {
        for (V3GraphEdge* const edgep : vtx.outEdges().unlinkable()) {
            if (edgep->weight() != 0) continue;
            VL_DO_DANGLING(edgep->unlinkDelete(), edgep);
        }
    }

    // Emit reordered logic, grouping contiguous logic by scope into subfuncs.
    GraphStream<StaticLogicSeqLess> depOrder{&depGraph, GraphWay::FORWARD, StaticLogicSeqLess{}};
    size_t subFuncNum = 0;
    AstScope* currentScopep = nullptr;
    AstCFunc* currentSubFuncp = nullptr;
    size_t orderedCount = 0;
    while (const V3GraphVertex* const vxp = depOrder.nextp()) {
        ++orderedCount;
        const size_t idx = static_cast<const StaticLogicVertex*>(vxp)->idx();
        const StaticLogic& logic = logics[idx];
        if (logic.m_scopep != currentScopep) {
            if (currentSubFuncp) V3Sched::util::splitCheck(currentSubFuncp);
            currentScopep = logic.m_scopep;
            currentSubFuncp
                = createScopeSubFunc(funcp, currentScopep, "__Vstatic" + cvtToStr(subFuncNum++));
        }
        currentSubFuncp->addStmtsp(logic.m_nodep);
    }
    UASSERT_OBJ(orderedCount == n, funcp, "Static ordering dropped vertices");
    if (currentSubFuncp) V3Sched::util::splitCheck(currentSubFuncp);
}  // namespace

}  //namespace

void V3Sched::scheduleStatic(AstCFunc* const evalStaticp) { orderStaticEval(evalStaticp); }
