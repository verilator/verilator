// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Post-schedule static initializer ordering
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

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3SchedStatic.h"

#include "V3Graph.h"
#include "V3GraphStream.h"
#include "V3Sched.h"

VL_DEFINE_DEBUG_FUNCTIONS;

namespace {

struct StaticUnit final {
    AstScope* m_scopep = nullptr;
    AstNode* m_nodep = nullptr;
    size_t m_seq = 0;
};

struct StaticUnitSummary final {
    std::unordered_set<AstVarScope*> m_reads;
    std::unordered_set<AstVarScope*> m_writes;
};

using ScopeVarMap = std::unordered_map<AstVar*, AstVarScope*>;
using ScopeVarListMap = std::unordered_map<AstVar*, std::vector<AstVarScope*>>;

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

const FileLine* fileLineOf(const StaticUnit& unit) {
    return unit.m_nodep ? unit.m_nodep->fileline() : nullptr;
}

bool fileLineLess(const StaticUnit& lhs, const StaticUnit& rhs) {
    const FileLine* const lhsFlp = fileLineOf(lhs);
    const FileLine* const rhsFlp = fileLineOf(rhs);
    if (!lhsFlp || !rhsFlp) return lhsFlp < rhsFlp;
    if (lhsFlp->filenameno() != rhsFlp->filenameno()) {
        return lhsFlp->filenameno() < rhsFlp->filenameno();
    }
    if (lhsFlp->lineno() != rhsFlp->lineno()) return lhsFlp->lineno() < rhsFlp->lineno();
    return lhsFlp->firstColumn() < rhsFlp->firstColumn();
}

class StaticDepCollector final : public VNVisitorConst {
    const ScopeVarListMap& m_allVarMap;
    const ScopeVarMap& m_varMap;
    StaticUnitSummary& m_summary;

    AstVarScope* resolveVarScope(const AstNodeVarRef* refp) const {
        if (AstVarScope* const vscp = refp->varScopep()) return vscp;
        const auto it = m_allVarMap.find(refp->varp());
        if (it != m_allVarMap.end() && it->second.size() == 1) return it->second.front();
        return nullptr;
    }

    void visit(AstNodeVarRef* nodep) override {
        AstVarScope* const vscp = resolveVarScope(nodep);
        if (!vscp) return;
        if (nodep->access().isReadOrRW()) m_summary.m_reads.insert(vscp);
        if (nodep->access().isWriteOrRW()
            && (!nodep->varp()->ignoreSchedWrite() || nodep->varp()->isConst())) {
            m_summary.m_writes.insert(vscp);
        }
    }
    void visit(AstVar* nodep) override {
        if (nodep->valuep()) {
            const auto it = m_varMap.find(nodep);
            if (it != m_varMap.end()) m_summary.m_writes.insert(it->second);
        }
        iterateChildrenConst(nodep);
    }
    void visit(AstNode* nodep) override { iterateChildrenConst(nodep); }

public:
    StaticDepCollector(AstNode* nodep, const ScopeVarListMap& allVarMap, const ScopeVarMap& varMap,
                       StaticUnitSummary& summary)
        : m_allVarMap{allVarMap}
        , m_varMap{varMap}
        , m_summary{summary} {
        iterateConst(nodep);
    }
};

class StaticUnitVertex final : public V3GraphVertex {
    size_t m_idx = 0;
    size_t m_seq = 0;

public:
    StaticUnitVertex(V3Graph* graphp, size_t idx, size_t seq)
        : V3GraphVertex{graphp}
        , m_idx{idx}
        , m_seq{seq} {}
    size_t idx() const { return m_idx; }
    size_t seq() const { return m_seq; }
};

struct StaticUnitSeqLess final {
    bool operator()(const V3GraphVertex* a, const V3GraphVertex* b) const {
        return static_cast<const StaticUnitVertex*>(a)->seq()
               < static_cast<const StaticUnitVertex*>(b)->seq();
    }
};

AstCFunc* findTopEvalStatic(AstNetlist* netlistp) {
    AstTopScope* const topScopep = netlistp->topScopep();
    if (!topScopep) return nullptr;
    AstScope* const scopep = topScopep->scopep();
    if (!scopep) return nullptr;
    for (AstNode* blockp = scopep->blocksp(); blockp; blockp = blockp->nextp()) {
        if (AstCFunc* const funcp = VN_CAST(blockp, CFunc)) {
            if (funcp->name() == "_eval_static") return funcp;
        }
    }
    return nullptr;
}

AstCCall* ccallFromStmt(AstNodeStmt* stmtp) {
    if (AstStmtExpr* const sexprp = VN_CAST(stmtp, StmtExpr)) {
        return VN_CAST(sexprp->exprp(), CCall);
    }
    return nullptr;
}

void orderStaticEval(AstCFunc* funcp, const ScopeVarListMap& allVarMap) {
    std::vector<AstNodeStmt*> callStmts;
    std::vector<AstCFunc*> oldSubFuncs;
    std::unordered_set<AstCFunc*> seenSubFuncs;
    const string expectedPrefix = funcp->name() + "__";

    for (AstNode* stmtp = funcp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
        AstNodeStmt* const nodep = VN_AS(stmtp, NodeStmt);
        AstCCall* const ccallp = ccallFromStmt(nodep);
        if (!ccallp || !ccallp->funcp()) return;
        AstCFunc* const calleep = ccallp->funcp();
        if (calleep->name().compare(0, expectedPrefix.size(), expectedPrefix) != 0) return;
        if (!calleep->scopep()) return;
        callStmts.push_back(nodep);
        if (seenSubFuncs.insert(calleep).second) oldSubFuncs.push_back(calleep);
    }
    if (callStmts.empty()) return;
    const auto cleanupOld = [&]() {
        for (AstNodeStmt* const stmtp : callStmts) {
            stmtp->unlinkFrBack();
            VL_DO_DANGLING(stmtp->deleteTree(), stmtp);
        }
        for (AstCFunc* const subFuncp : oldSubFuncs) {
            if (!subFuncp->backp()) continue;
            subFuncp->unlinkFrBack();
            VL_DO_DANGLING(subFuncp->deleteTree(), subFuncp);
        }
    };

    std::vector<StaticUnit> units;
    std::vector<StaticUnitSummary> summaries;
    units.reserve(callStmts.size() * 2);
    summaries.reserve(callStmts.size() * 2);

    for (AstCFunc* const subFuncp : oldSubFuncs) {
        AstScope* const scopep = subFuncp->scopep();
        if (!scopep) continue;
        ScopeVarMap varMap;
        for (AstVarScope* vscp = scopep->varsp(); vscp; vscp = VN_AS(vscp->nextp(), VarScope)) {
            varMap.emplace(vscp->varp(), vscp);
        }
        for (AstNode *stmtp = subFuncp->stmtsp(), *nextp; stmtp; stmtp = nextp) {
            nextp = stmtp->nextp();
            stmtp->unlinkFrBack();
            units.emplace_back();
            summaries.emplace_back();
            StaticUnit& unit = units.back();
            unit.m_scopep = scopep;
            unit.m_nodep = stmtp;
            StaticDepCollector{stmtp, allVarMap, varMap, summaries.back()};
        }
    }

    if (units.empty()) return;

    std::vector<size_t> seqOrder(units.size());
    for (size_t i = 0; i < units.size(); ++i) seqOrder[i] = i;
    std::stable_sort(seqOrder.begin(), seqOrder.end(),
                     [&](size_t lhs, size_t rhs) { return fileLineLess(units[lhs], units[rhs]); });
    for (size_t seq = 0; seq < seqOrder.size(); ++seq) units[seqOrder[seq]].m_seq = seq;

    const size_t n = units.size();
    UASSERT_OBJ(summaries.size() == n, funcp, "Static summaries out of sync with units");

    // Keep dependency extraction minimal and deterministic:
    // direct read/write analysis plus source-order tie breaking.

    if (n == 1) {
        AstCFunc* const subFuncp = createScopeSubFunc(funcp, units[0].m_scopep, "__Vstatic0");
        subFuncp->addStmtsp(units[0].m_nodep);
        V3Sched::util::splitCheck(subFuncp);
        cleanupOld();
        return;
    }

    std::vector<std::unordered_set<size_t>> depSucc(n);

    std::unordered_map<AstVarScope*, std::vector<size_t>> writers;
    writers.reserve(n * 4);
    for (size_t i = 0; i < n; ++i) {
        for (AstVarScope* const vscp : summaries[i].m_writes) writers[vscp].push_back(i);
    }

    for (size_t readerIdx = 0; readerIdx < n; ++readerIdx) {
        for (AstVarScope* const vscp : summaries[readerIdx].m_reads) {
            const auto it = writers.find(vscp);
            if (it == writers.end()) continue;
            for (const size_t writerIdx : it->second) {
                if (writerIdx == readerIdx) continue;
                depSucc[writerIdx].insert(readerIdx);
            }
        }
    }

    V3Graph depGraph;
    std::vector<StaticUnitVertex*> unitVtxps;
    unitVtxps.reserve(n);
    for (size_t i = 0; i < n; ++i) {
        unitVtxps.push_back(new StaticUnitVertex{&depGraph, i, units[i].m_seq});
    }
    for (size_t from = 0; from < n; ++from) {
        for (const size_t to : depSucc[from]) {
            new V3GraphEdge{&depGraph, unitVtxps[from], unitVtxps[to], 1, V3GraphEdge::CUTABLE};
        }
    }
    depGraph.acyclic(&V3GraphEdge::followAlwaysTrue);
    for (V3GraphVertex& vtx : depGraph.vertices()) {
        for (V3GraphEdge* const edgep : vtx.outEdges().unlinkable()) {
            if (edgep->weight() != 0) continue;
            VL_DO_DANGLING(edgep->unlinkDelete(), edgep);
        }
    }

    std::vector<size_t> ordered;
    ordered.reserve(n);
    GraphStream<StaticUnitSeqLess> depOrder{&depGraph, GraphWay::FORWARD, StaticUnitSeqLess{}};
    while (const V3GraphVertex* const vxp = depOrder.nextp()) {
        ordered.push_back(static_cast<const StaticUnitVertex*>(vxp)->idx());
    }
    UASSERT_OBJ(ordered.size() == n, funcp, "Static ordering dropped vertices");

    size_t subFuncNum = 0;
    AstScope* currentScopep = nullptr;
    AstCFunc* currentSubFuncp = nullptr;
    for (const size_t idx : ordered) {
        StaticUnit& unit = units[idx];
        if (unit.m_scopep != currentScopep) {
            if (currentSubFuncp) V3Sched::util::splitCheck(currentSubFuncp);
            currentScopep = unit.m_scopep;
            currentSubFuncp
                = createScopeSubFunc(funcp, currentScopep, "__Vstatic" + cvtToStr(subFuncNum++));
        }
        currentSubFuncp->addStmtsp(unit.m_nodep);
    }
    if (currentSubFuncp) V3Sched::util::splitCheck(currentSubFuncp);
    cleanupOld();
}

}  // namespace

void V3SchedStatic::scheduleStatic(AstNetlist* netlistp) {
    AstCFunc* const evalStaticp = findTopEvalStatic(netlistp);
    if (!evalStaticp) return;

    ScopeVarListMap allVarMap;
    netlistp->topScopep()->foreach([&](AstScope* scopep) {
        for (AstVarScope* vscp = scopep->varsp(); vscp; vscp = VN_AS(vscp->nextp(), VarScope)) {
            allVarMap[vscp->varp()].push_back(vscp);
        }
    });

    orderStaticEval(evalStaticp, allVarMap);
}
