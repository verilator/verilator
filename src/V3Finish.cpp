// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Analyze and lower source $finish propagation
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026-2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
//
// V3Finish runs in three phases.  Before V3Task, analyze() builds a
// callee-to-caller graph of source tasks, functions, procedures, and fork
// branches.  Direct $finish statements and opaque DPI imports seed a fixed
// point that marks every transitively finish-capable source unit and call.
// Virtual override families are connected in both directions so dynamic
// dispatch is conservatively represented.  After mandatory finish-sensitive
// expression normalization, analyzeContainment() records which final argument
// and callback subtrees contain those calls.
//
// After V3Timing, lower() converts finish epoch markers inserted by intervening
// passes into ordinary assignments, conditions, and control-flow nodes.  This
// ensures scheduling and later optimizations see all finish-induced branches.
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Finish.h"

#include "V3Control.h"
#include "V3Graph.h"
#include "V3Stats.h"

VL_DEFINE_DEBUG_FUNCTIONS;

bool V3FinishEffects::mayFinish(const AstNodeFTaskRef* nodep) const {
    return m_callsp.count(nodep) || (nodep->taskp() && m_unitsp.count(nodep->taskp()));
}

//######################################################################
// Finish effect analysis

class FinishVertex final : public V3GraphVertex {
    VL_RTTI_IMPL(FinishVertex, V3GraphVertex)

    AstNode* const m_nodep;  // Source unit represented by this vertex
    bool m_entryRoot = true;  // Procedure is a direct eval/final entry root
    bool m_seed = false;  // Unit directly executes $finish or opaque DPI
    bool m_mayFinish = false;  // Unit transitively executes $finish

public:
    FinishVertex(V3Graph* graphp, AstNode* nodep)
        : V3GraphVertex{graphp}
        , m_nodep{nodep} {}

    string dotColor() const override { return m_mayFinish ? "red" : "black"; }
    FileLine* fileline() const override { return m_nodep->fileline(); }
    string name() const override {
        return m_nodep->prettyTypeName() + " " + m_nodep->prettyName();
    }
    AstNode* nodep() const { return m_nodep; }
    bool entryRoot() const { return m_entryRoot; }
    void entryRoot(bool flag) { m_entryRoot = flag; }
    bool mayFinish() const { return m_mayFinish; }
    void mayFinish(bool flag) { m_mayFinish = flag; }
    bool seed() const { return m_seed; }
    void seed(bool flag) { m_seed = flag; }
};

class FinishAnalysisVisitor final : public VNVisitor {
    // STATE
    V3Graph m_graph;  // Callee-to-caller finish dependency graph
    std::unordered_map<AstNode*, FinishVertex*> m_vertexByNode;  // One vertex per source unit
    std::vector<AstNodeFTaskRef*> m_callsp;  // Calls to annotate after fixed-point propagation
    std::vector<AstNodeFTask*> m_classMethodsp;  // Methods to group after traversal
    std::unordered_set<AstNodeFTaskRef*> m_coverageVirtualCallsp;  // Early dynamic boundaries
    VDouble0 m_virtualFamilyVisits;  // Work spent classifying virtual method families
    const bool m_coverageMode;  // Analysis runs before exact virtual families are available
    AstClass* m_classp = nullptr;  // Current class
    AstNodeFTask* m_classCtorp = nullptr;  // Constructor owning class property initializers
    FinishVertex* m_currentp = nullptr;  // Current source unit
    FinishVertex* m_forkParentp = nullptr;  // Source unit owning current fork branches

    // METHODS
    FinishVertex* vertex(AstNode* nodep) {
        const auto pair = m_vertexByNode.emplace(nodep, nullptr);
        if (pair.second) pair.first->second = new FinishVertex{&m_graph, nodep};
        return pair.first->second;
    }
    void addEdge(FinishVertex* calleep, FinishVertex* callerp) {
        new V3GraphEdge{&m_graph, calleep, callerp, 1};
    }
    void seedCurrent(AstNode* nodep) {
        UASSERT_OBJ(m_currentp, nodep, "$finish is not inside a source unit");
        m_currentp->seed(true);
    }
    static AstNodeFTask* findConstructor(AstNode* stmtsp) {
        for (AstNode* stmtp = stmtsp; stmtp; stmtp = stmtp->nextp()) {
            AstNodeFTask* const ftaskp = VN_CAST(stmtp, NodeFTask);
            if (ftaskp && ftaskp->isConstructor()) return ftaskp;
        }
        return nullptr;
    }
    static bool isSuperReference(const AstNodeFTaskRef* nodep) {
        if (const AstFuncRef* const refp = VN_CAST(nodep, FuncRef)) {
            return refp->superReference();
        }
        if (const AstTaskRef* const refp = VN_CAST(nodep, TaskRef)) {
            return refp->superReference();
        }
        return false;
    }
    void connectVirtualFamilies() {
        std::unordered_map<AstNodeFTask*, AstNodeFTask*> representativeByRoot;
        for (AstNodeFTask* const methodp : m_classMethodsp) {
            AstNodeFTask* rootp = methodp->virtualFamilyRootp();
            if (!rootp && methodp->isVirtual()) rootp = methodp;
            if (!rootp) continue;
            ++m_virtualFamilyVisits;
            const auto pair = representativeByRoot.emplace(rootp, methodp);
            if (!pair.second) {
                addEdge(vertex(methodp), vertex(pair.first->second));
                addEdge(vertex(pair.first->second), vertex(methodp));
            }
        }
    }
    void releaseVirtualFamilies() {
        for (AstNodeFTask* const methodp : m_classMethodsp) methodp->virtualFamilyp(nullptr);
        V3Stats::addStat("Finish, Virtual family classification visits", m_virtualFamilyVisits);
    }
    void propagate() {
        std::vector<FinishVertex*> work;
        for (V3GraphVertex& graphVertex : m_graph.vertices()) {
            FinishVertex& finishVertex = static_cast<FinishVertex&>(graphVertex);
            if (!finishVertex.seed()) continue;
            finishVertex.mayFinish(true);
            work.emplace_back(&finishVertex);
        }
        while (!work.empty()) {
            FinishVertex* const calleep = work.back();
            work.pop_back();
            for (V3GraphEdge& edge : calleep->outEdges()) {
                FinishVertex* const callerp = static_cast<FinishVertex*>(edge.top());
                if (callerp->mayFinish()) continue;
                callerp->mayFinish(true);
                work.emplace_back(callerp);
            }
        }
    }
    void annotate() {
        VDouble0 finishUnitCount;
        bool evalMayFinish = false;
        bool finalMayFinish = false;
        for (V3GraphVertex& graphVertex : m_graph.vertices()) {
            FinishVertex& finishVertex = static_cast<FinishVertex&>(graphVertex);
            AstNode* const nodep = finishVertex.nodep();
            const bool mayFinish = finishVertex.mayFinish();
            if (mayFinish) ++finishUnitCount;
            if (AstNodeFTask* const ftaskp = VN_CAST(nodep, NodeFTask)) {
                ftaskp->mayFinish(mayFinish);
            } else if (AstNodeProcedure* const procedurep = VN_CAST(nodep, NodeProcedure)) {
                procedurep->mayFinish(mayFinish);
                if (mayFinish && finishVertex.entryRoot()) {
                    if (VN_IS(procedurep, Final)) {
                        finalMayFinish = true;
                    } else {
                        evalMayFinish = true;
                    }
                }
            } else if (AstBegin* const beginp = VN_CAST(nodep, Begin)) {
                beginp->mayFinish(mayFinish);
            } else {
                nodep->v3fatalSrc("Unhandled finish source unit");
            }
        }
        v3Global.currentHierBlockEvalMayFinish(evalMayFinish);
        v3Global.currentHierBlockFinalMayFinish(finalMayFinish);

        VDouble0 finishCallCount;
        for (AstNodeFTaskRef* const callp : m_callsp) {
            UASSERT_OBJ(callp->taskp(), callp, "Unlinked task or function call");
            const bool mayFinish = vertex(callp->taskp())->mayFinish();
            callp->mayFinish(mayFinish);
            if (mayFinish) ++finishCallCount;
        }
        V3Stats::addStat("Finish, Finish-capable calls", finishCallCount);
        V3Stats::addStat("Finish, Finish-capable source units", finishUnitCount);
        V3Stats::addStat("Finish, Hierarchical eval may finish", evalMayFinish);
        V3Stats::addStat("Finish, Hierarchical final may finish", finalMayFinish);
    }
    void collectEffects(V3FinishEffects& effects) {
        for (V3GraphVertex& graphVertex : m_graph.vertices()) {
            FinishVertex& finishVertex = static_cast<FinishVertex&>(graphVertex);
            effects.m_sourceUnitsp.emplace(finishVertex.nodep());
            if (finishVertex.mayFinish()) effects.m_unitsp.emplace(finishVertex.nodep());
        }
        for (AstNodeFTaskRef* const callp : m_callsp) {
            if (m_coverageVirtualCallsp.count(callp) || vertex(callp->taskp())->mayFinish()) {
                effects.m_callsp.emplace(callp);
            }
        }
    }

    // VISITORS
    void visit(AstClass* nodep) override {
        VL_RESTORER(m_classp);
        VL_RESTORER(m_classCtorp);
        m_classp = nodep;
        m_classCtorp = nullptr;
        for (AstNode* stmtp = nodep->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
            if (const AstScope* const scopep = VN_CAST(stmtp, Scope)) {
                m_classCtorp = findConstructor(scopep->blocksp());
            } else if (AstNodeFTask* const ftaskp = VN_CAST(stmtp, NodeFTask)) {
                if (ftaskp->isConstructor()) m_classCtorp = ftaskp;
            }
            if (m_classCtorp) break;
        }
        iterateChildren(nodep);
    }
    void visit(AstNodeFTask* nodep) override {
        FinishVertex* const unitp = vertex(nodep);
        VL_RESTORER(m_currentp);
        VL_RESTORER(m_forkParentp);
        m_currentp = unitp;
        m_forkParentp = nullptr;
        if (nodep->dpiImport() && (!nodep->dpiPure() || nodep->dpiContext())
            && !nodep->hierDpiNoFinish()) {
            unitp->seed(true);
        }
        iterateChildren(nodep);
        if (m_classp) m_classMethodsp.emplace_back(nodep);
    }
    void visit(AstNodeProcedure* nodep) override {
        VL_RESTORER(m_currentp);
        VL_RESTORER(m_forkParentp);
        m_currentp = vertex(nodep);
        m_forkParentp = nullptr;
        iterateChildren(nodep);
    }
    void visit(AstInitialAutomatic* nodep) override {
        FinishVertex* const unitp = vertex(nodep);
        if (m_classp) unitp->entryRoot(false);
        if (m_classCtorp) addEdge(unitp, vertex(m_classCtorp));
        VL_RESTORER(m_currentp);
        VL_RESTORER(m_forkParentp);
        m_currentp = unitp;
        m_forkParentp = nullptr;
        iterateChildren(nodep);
    }
    void visit(AstFork* nodep) override {
        UASSERT_OBJ(m_currentp, nodep, "Fork is not inside a source unit");
        VL_RESTORER(m_forkParentp);
        m_forkParentp = m_currentp;
        iterateChildren(nodep);
    }
    void visit(AstBegin* nodep) override {
        if (!m_forkParentp) {
            iterateChildren(nodep);
            return;
        }
        FinishVertex* const branchp = vertex(nodep);
        addEdge(branchp, m_forkParentp);
        VL_RESTORER(m_currentp);
        VL_RESTORER(m_forkParentp);
        m_currentp = branchp;
        m_forkParentp = nullptr;
        iterateChildren(nodep);
    }
    void visit(AstFinish* nodep) override { seedCurrent(nodep); }
    void visit(AstFinishFork* nodep) override { seedCurrent(nodep); }
    void visit(AstNodeFTaskRef* nodep) override {
        UASSERT_OBJ(nodep->taskp(), nodep, "Unlinked task or function call");
        if (m_currentp) addEdge(vertex(nodep->taskp()), m_currentp);
        // Generic coverage is inserted before scoped LinkDot constructs exact virtual families.
        // Conservatively split only dynamic virtual call sites in this early analysis; the final
        // code-generation analysis still uses exact override families.
        if (m_coverageMode && nodep->taskp()->isVirtual() && !isSuperReference(nodep)) {
            m_coverageVirtualCallsp.emplace(nodep);
            if (m_currentp) m_currentp->seed(true);
        }
        m_callsp.emplace_back(nodep);
        iterateChildren(nodep);
    }
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    FinishAnalysisVisitor(AstNetlist* nodep, V3FinishEffects* effectsp)
        : m_coverageMode{static_cast<bool>(effectsp)} {
        iterate(nodep);
        connectVirtualFamilies();
        propagate();
        if (effectsp) {
            collectEffects(*effectsp);
        } else {
            annotate();
            releaseVirtualFamilies();
            if (dumpGraphLevel() >= 6) m_graph.dumpDotFilePrefixed("finish_deps");
        }
    }
    ~FinishAnalysisVisitor() override = default;
};

class FinishContainmentVisitor final : public VNVisitor {
    // NODE STATE
    // AstNode::user1() -> bool. Subtree contains a finish-capable call
    const VNUser1InUse m_user1InUse;

    // STATE
    bool m_containsFinish = false;  // Current subtree contains a finish-capable call
    VDouble0 m_finishArgCallCount;  // Calls with finish-capable arguments
    VDouble0 m_finishCallbackCount;  // Finish-capable callbacks
    VDouble0 m_statVisits;  // Nodes visited by the post-order analysis

    // METHODS
    void analyze(AstNode* nodep, bool selfMayFinish) {
        ++m_statVisits;
        bool containsFinish = selfMayFinish;
        {
            VL_RESTORER(m_containsFinish);
            m_containsFinish = false;
            iterateChildren(nodep);
            containsFinish |= m_containsFinish;
        }
        nodep->user1(containsFinish);
        m_containsFinish |= containsFinish;
    }
    static bool containsFinishAndNext(const AstNode* nodep) {
        for (const AstNode* cursorp = nodep; cursorp; cursorp = cursorp->nextp()) {
            if (cursorp->user1()) return true;
        }
        return false;
    }

    // VISITORS
    void visit(AstNodeFTaskRef* nodep) override {
        analyze(nodep, nodep->mayFinish());
        const bool argsMayFinish = containsFinishAndNext(nodep->argsp());
        nodep->argsMayFinish(argsMayFinish);
        if (argsMayFinish) ++m_finishArgCallCount;
    }
    void visit(AstWith* nodep) override {
        analyze(nodep, false);
        const bool mayFinish = containsFinishAndNext(nodep->exprp());
        nodep->mayFinish(mayFinish);
        if (mayFinish) ++m_finishCallbackCount;
    }
    void visit(AstNode* nodep) override { analyze(nodep, false); }

public:
    explicit FinishContainmentVisitor(AstNetlist* nodep) { iterate(nodep); }
    ~FinishContainmentVisitor() override {
        V3Stats::addStat("Finish, Calls with finish-capable arguments", m_finishArgCallCount);
        V3Stats::addStat("Finish, Finish-capable callbacks", m_finishCallbackCount);
        V3Stats::addStat("Finish, Containment analysis visits", m_statVisits);
    }
};

//######################################################################
// Finish marker lowering

class FinishLowerVisitor final : public VNVisitor {
    VDouble0 m_guardCount;  // Number of finish guards lowered
    VDouble0 m_scopeCount;  // Number of finish source scopes lowered

    void visit(AstFinishScope* nodep) override {
        AstAssign* const assignp
            = new AstAssign{nodep->fileline(), nodep->baselinep()->unlinkFrBack(),
                            new AstFinishEpoch{nodep->fileline()}};
        nodep->replaceWith(assignp);
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
        ++m_scopeCount;
    }
    void visit(AstFinishGuard* nodep) override {
        AstNodeExpr* const changedp
            = new AstNeq{nodep->fileline(), new AstFinishEpoch{nodep->fileline()},
                         nodep->baselinep()->unlinkFrBack()};
        AstNode* exitp = nullptr;
        switch (nodep->guardType()) {
        case VFinishGuardType::LAMBDA_REF:
            exitp = new AstCReturn{nodep->fileline(), nodep->fallbackp()->unlinkFrBack()};
            break;
        case VFinishGuardType::LAMBDA_VALUE:
            exitp = new AstCReturn{nodep->fileline(), VCReturnType::DEFAULT};
            break;
        case VFinishGuardType::LAMBDA_VOID:
            exitp = new AstCReturn{nodep->fileline(), VCReturnType::VOID};
            break;
        case VFinishGuardType::SOURCE:
            exitp = new AstJumpGo{nodep->fileline(), nodep->blockp()};
            break;
        }
        AstIf* const ifp = new AstIf{nodep->fileline(), changedp, exitp};
        ifp->branchPred(VBranchPred::BP_UNLIKELY);
        nodep->replaceWith(ifp);
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
        ++m_guardCount;
    }
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    explicit FinishLowerVisitor(AstNetlist* nodep) { iterate(nodep); }
    ~FinishLowerVisitor() override {
        V3Stats::addStat("Finish, Guards", m_guardCount);
        V3Stats::addStat("Finish, Source scopes", m_scopeCount);
    }
};

class FinishMarkerCheckVisitor final : public VNVisitorConst {
    void visit(AstFinishScope* nodep) override {
        UASSERT_OBJ(false, nodep, "Finish scope survived V3Finish::lower");
    }
    void visit(AstFinishGuard* nodep) override {
        UASSERT_OBJ(false, nodep, "Finish guard survived V3Finish::lower");
    }
    void visit(AstNode* nodep) override { iterateChildrenConst(nodep); }

public:
    explicit FinishMarkerCheckVisitor(AstNetlist* nodep) { iterateConst(nodep); }
    ~FinishMarkerCheckVisitor() override = default;
};

//######################################################################
// Finish class functions

V3FinishEffects V3Finish::analyzeForCoverage(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ":");
    V3FinishEffects effects;
    { FinishAnalysisVisitor{nodep, &effects}; }
    return effects;
}

void V3Finish::analyze(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ":");
    { FinishAnalysisVisitor{nodep, nullptr}; }
    V3Global::dumpCheckGlobalTree("finish-analyze", 0, dumpTreeEitherLevel() >= 3);
}

void V3Finish::analyzeContainment(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ":");
    { FinishContainmentVisitor{nodep}; }
    V3Global::dumpCheckGlobalTree("finish-containment", 0, dumpTreeEitherLevel() >= 3);
}

void V3Finish::lower(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ":");
    { FinishLowerVisitor{nodep}; }
    { FinishMarkerCheckVisitor{nodep}; }
    V3Global::dumpCheckGlobalTree("finish-lower", 0, dumpTreeEitherLevel() >= 3);
}
