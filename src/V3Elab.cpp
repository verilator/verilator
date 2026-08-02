// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Convergent elaboration of dependent semantic facts
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
// ELABORATION CONVERGENCE
//
// Elaboration facts are vertices in a dependency graph.  An edge points from
// a prerequisite fact to a consumer.  A fact is published at most once.  The
// worklist wakes a consumer only after all of its prerequisites are published,
// and stops at quiescence.  Ownership-changing AST replacements are committed
// at explicit convergence boundaries.  Publishing a fact may fill semantic
// cross-references or constify its declaration, which is the answer consumers
// named by outgoing edges are waiting for.
//
// Parameter bindings are specialization-scoped facts.  Each parameterized module
// or interface instance and each parameterized class or virtual interface reference
// has one fact per formal parameter.  Explicit actuals are initially published facts.
// Defaults are queries whose references to other formals form dependency edges.
// Resolving a default clones it and substitutes the already published actuals,
// preserving the complete AST type or expression rather than reducing it to a width
// or an encoded type name.  A reference-environment fact publishes only after every
// binding is resolved and its default actuals have been installed on the reference.
// Nested defaults depend on those environment facts, so nested specialization
// identity also converges before V3Param names it.
//
// Deferred parameter values are declaration-scoped facts.  V3Param registers
// values whose names cannot be finalized until linkDotParamed.  After linking,
// references to other registered parameters become edges, and values are
// constified in dependency order.  The phase context is owned by V3Elab rather
// than stored as transient pointers on the AST.
//
// Bindings, substitutions, specializations, projections, aliases, and deferred
// parameters use the same worklist and quiescence classifier.  Cycles are SCCs
// of unresolved defined facts; unresolved acyclic facts are blocked, and facts
// without definitions are missing.  Binding cycles are diagnosed here and their
// invalid defaults are replaced on the error path, preventing later internal
// errors.  Other fact kinds retain their existing semantic diagnostics.
//
// Projection facts live through V3Param because class specialization is their external
// producer.  Generic definitions are queries, not concrete demands; projections are
// collected from the instantiated subtrees exposed during parameterization.  V3Param
// defers removal of subtrees that can own projection facts until the final projection
// convergence call.  The graph is then destroyed before those deferred deletions run,
// so a fact never outlives its source or consumer allocation.
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Elab.h"

#include "V3Const.h"
#include "V3Graph.h"
#include "V3MemberMap.h"
#include "V3Stats.h"

#include <deque>
#include <memory>
#include <unordered_map>
#include <unordered_set>
#include <vector>

VL_DEFINE_DEBUG_FUNCTIONS;

namespace {

class ElabBindingVertex;
class ElabMaterializationVertex;
class ElabReference;

using BindingMap = std::unordered_map<const AstNode*, ElabBindingVertex*>;
using BindingNameMap = std::unordered_map<string, ElabBindingVertex*>;
using AnswerMap = std::unordered_map<const AstNode*, AstNode*>;

AstNode* formalDefaultp(AstNode* formalp) {
    if (AstParamTypeDType* const typep = VN_CAST(formalp, ParamTypeDType)) {
        AstNodeDType* const childp = typep->getChildDTypep();
        AstNode* const nodep
            = VN_IS(childp, RequireDType) ? VN_AS(childp, RequireDType)->lhsp() : childp;
        return VN_IS(nodep, VoidDType) ? nullptr : nodep;
    }
    if (AstVar* const varp = VN_CAST(formalp, Var)) return varp->valuep();
    return nullptr;
}

class ElabFactVertex VL_NOT_FINAL : public V3GraphVertex {
    VL_RTTI_IMPL(ElabFactVertex, V3GraphVertex)

    enum class State : uint8_t { WAITING, QUEUED, RESOLVED, MISSING, CYCLIC, BLOCKED };

    State m_state = State::WAITING;
    virtual bool resolveFact() = 0;
    virtual bool hasDefinition() const = 0;
    virtual bool worklistResolvable() const { return true; }

public:
    explicit ElabFactVertex(V3Graph* graphp)
        : V3GraphVertex{graphp} {}

    string dotColor() const override {
        if (resolved()) return "green";
        if (cyclic()) return "red";
        if (missing()) return "grey";
        return "orange";
    }

    bool resolved() const { return m_state == State::RESOLVED; }
    bool waiting() const { return m_state == State::WAITING; }
    bool missing() const { return m_state == State::MISSING; }
    bool cyclic() const { return m_state == State::CYCLIC; }
    bool blocked() const { return m_state == State::BLOCKED; }
    bool defined() const { return hasDefinition(); }
    bool worklistDriven() const { return worklistResolvable(); }

    void markQueued() {
        UASSERT(waiting(), "Queuing non-waiting elaboration fact");
        m_state = State::QUEUED;
    }
    void markResolved() {
        UASSERT(m_state == State::WAITING || m_state == State::QUEUED,
                "Publishing invalid elaboration fact");
        m_state = State::RESOLVED;
    }
    bool tryResolve() {
        UASSERT(m_state == State::QUEUED, "Resolving non-queued elaboration fact");
        if (resolveFact()) {
            markResolved();
            return true;
        }
        m_state = State::WAITING;
        return false;
    }
    void markMissing() {
        UASSERT(waiting() && !defined(), "Invalid missing elaboration fact");
        m_state = State::MISSING;
    }
    void markCyclic() {
        UASSERT(waiting() && defined(), "Invalid cyclic elaboration fact");
        m_state = State::CYCLIC;
    }
    void markBlocked() {
        UASSERT(waiting() && defined(), "Invalid blocked elaboration fact");
        m_state = State::BLOCKED;
    }
};

class ElabFactGraph VL_NOT_FINAL : public V3Graph {
    std::vector<ElabFactVertex*> m_facts;

    static bool ready(const ElabFactVertex* vertexp) {
        if (!vertexp->waiting() || !vertexp->defined() || !vertexp->worklistDriven()) return false;
        for (const V3GraphEdge& edge : vertexp->inEdges()) {
            if (!edge.fromp()->as<ElabFactVertex>()->resolved()) return false;
        }
        return true;
    }
    static void enqueueIfReady(ElabFactVertex* vertexp, std::deque<ElabFactVertex*>& worklist) {
        if (!ready(vertexp)) return;
        vertexp->markQueued();
        worklist.push_back(vertexp);
    }

    static bool followUnresolvedDefined(const V3GraphEdge* edgep) {
        const ElabFactVertex* const fromp = edgep->fromp()->as<ElabFactVertex>();
        const ElabFactVertex* const top = edgep->top()->as<ElabFactVertex>();
        return fromp->waiting() && fromp->defined() && top->waiting() && top->defined();
    }

    void drain(std::deque<ElabFactVertex*>& worklist) {
        while (!worklist.empty()) {
            ElabFactVertex* const vertexp = worklist.front();
            worklist.pop_front();
            if (!vertexp->tryResolve()) continue;
            for (V3GraphEdge& edge : vertexp->outEdges()) {
                enqueueIfReady(edge.top()->as<ElabFactVertex>(), worklist);
            }
        }
    }

protected:
    void addFact(ElabFactVertex* vertexp) { m_facts.push_back(vertexp); }

public:
    void converge() {
        std::deque<ElabFactVertex*> worklist;
        for (ElabFactVertex* const vertexp : m_facts) enqueueIfReady(vertexp, worklist);
        drain(worklist);
    }

    void publish(ElabFactVertex* vertexp) {
        UASSERT(vertexp->waiting(), "Publishing non-waiting elaboration fact");
        vertexp->markResolved();
        std::deque<ElabFactVertex*> worklist;
        for (V3GraphEdge& edge : vertexp->outEdges()) {
            enqueueIfReady(edge.top()->as<ElabFactVertex>(), worklist);
        }
        drain(worklist);
    }

    void classifyQuiescence() {
        stronglyConnected(&followUnresolvedDefined);
        for (ElabFactVertex* const vertexp : m_facts) {
            if (!vertexp->waiting()) continue;
            if (!vertexp->defined()) {
                vertexp->markMissing();
                continue;
            }
            bool selfEdge = false;
            for (const V3GraphEdge& edge : vertexp->outEdges()) {
                if (edge.top() == vertexp && followUnresolvedDefined(&edge)) selfEdge = true;
            }
            // V3Graph deliberately resets acyclic singleton SCCs to color zero.  A nonzero
            // color therefore already means this vertex belongs to a multi-vertex SCC; grouping
            // all color-zero vertices would falsely classify unrelated blocked facts as a cycle.
            if (selfEdge || vertexp->color()) {
                vertexp->markCyclic();
            } else {
                vertexp->markBlocked();
            }
        }
    }

    uint64_t factCount() const { return m_facts.size(); }
    uint64_t published() const {
        uint64_t count = 0;
        for (const ElabFactVertex* const vertexp : m_facts) {
            if (vertexp->resolved()) ++count;
        }
        return count;
    }
    uint64_t unresolved() const {
        uint64_t count = 0;
        for (const ElabFactVertex* const vertexp : m_facts) {
            if (!vertexp->resolved() && vertexp->defined()) ++count;
        }
        return count;
    }
    uint64_t cyclicFacts() const {
        uint64_t count = 0;
        for (const ElabFactVertex* const vertexp : m_facts) {
            if (vertexp->cyclic()) ++count;
        }
        return count;
    }
    uint64_t blockedFacts() const {
        uint64_t count = 0;
        for (const ElabFactVertex* const vertexp : m_facts) {
            if (vertexp->blocked()) ++count;
        }
        return count;
    }
    uint64_t missingFacts() const {
        uint64_t count = 0;
        for (const ElabFactVertex* const vertexp : m_facts) {
            if (vertexp->missing()) ++count;
        }
        return count;
    }
    bool dependsOnCycle(const ElabFactVertex* vertexp) const {
        std::unordered_set<const ElabFactVertex*> seen;
        std::vector<const ElabFactVertex*> pending{vertexp};
        while (!pending.empty()) {
            const ElabFactVertex* const currentp = pending.back();
            pending.pop_back();
            if (!seen.insert(currentp).second) continue;
            if (currentp->cyclic()) return true;
            if (currentp->resolved() || currentp->missing()) continue;
            for (const V3GraphEdge& edge : currentp->inEdges()) {
                pending.push_back(edge.fromp()->as<ElabFactVertex>());
            }
        }
        return false;
    }
};

class ElabBindingVertex final : public ElabFactVertex {
    VL_RTTI_IMPL(ElabBindingVertex, ElabFactVertex)

    AstNode* const m_formalp;
    AstNode* const m_defaultp;
    ElabReference* const m_referencep;
    AstNode* m_answerp = nullptr;
    const int m_referenceNumber;
    const int m_pinNumber;
    bool m_answerOwned = false;
    bool m_explicit = false;

    bool resolveFact() override;
    bool hasDefinition() const override { return m_defaultp; }

public:
    ElabBindingVertex(V3Graph* graphp, ElabReference* referencep, AstNode* formalp,
                      AstNode* defaultp, int referenceNumber, int pinNumber)
        : ElabFactVertex{graphp}
        , m_formalp{formalp}
        , m_defaultp{defaultp}
        , m_referencep{referencep}
        , m_referenceNumber{referenceNumber}
        , m_pinNumber{pinNumber} {}
    ~ElabBindingVertex() override {
        if (m_answerOwned) m_answerp->deleteTree();
    }

    string name() const override {
        return "ref" + cvtToStr(m_referenceNumber) + "." + m_formalp->name();
    }
    string dotShape() const override {
        return VN_IS(m_formalp, ParamTypeDType) ? "box" : "ellipse";
    }
    FileLine* fileline() const override { return m_formalp->fileline(); }

    AstNode* formalp() const { return m_formalp; }
    AstNode* defaultp() const { return m_defaultp; }
    ElabReference* referencep() const { return m_referencep; }
    AstNode* answerp() const { return m_answerp; }
    int pinNumber() const { return m_pinNumber; }
    bool hasDefault() const { return m_defaultp; }
    bool isExplicit() const { return m_explicit; }

    void publish(AstNode* answerp, bool answerOwned, bool isExplicit = false) {
        UASSERT(!resolved() && answerp, "Publishing invalid elaboration fact");
        m_answerp = answerp;
        m_answerOwned = answerOwned;
        m_explicit = isExplicit;
        markResolved();
    }
    AstNode* releaseAnswerp() {
        UASSERT(resolved() && m_answerOwned, "Releasing non-owned elaboration fact");
        m_answerOwned = false;
        return m_answerp;
    }
};

class ElabReference final {
    AstNode* const m_refp;
    AstNodeModule* const m_definitionp;
    std::vector<ElabBindingVertex*> m_bindings;
    std::vector<AstPin*> m_emptyPinps;
    std::unordered_map<ElabBindingVertex*, AstPin*> m_explicitPinMap;
    BindingMap m_formalMap;
    BindingNameMap m_nameMap;
    ElabMaterializationVertex* m_materializationp = nullptr;

    static AstNodeModule* findDefinitionp(AstNode* nodep) {
        if (AstCell* const cellp = VN_CAST(nodep, Cell)) return cellp->modp();
        if (AstClassOrPackageRef* const classRefp = VN_CAST(nodep, ClassOrPackageRef)) {
            return VN_CAST(classRefp->classOrPackageSkipp(), Class);
        }
        if (AstIfaceRefDType* const ifaceRefp = VN_CAST(nodep, IfaceRefDType)) {
            return ifaceRefp->ifacep();
        }
        return VN_AS(nodep, ClassRefDType)->classp();
    }

public:
    explicit ElabReference(AstNode* refp)
        : m_refp{refp}
        , m_definitionp{findDefinitionp(refp)} {}

    AstNode* refp() const { return m_refp; }
    AstNodeModule* definitionp() const { return m_definitionp; }
    std::vector<ElabBindingVertex*>& bindings() { return m_bindings; }
    const std::vector<ElabBindingVertex*>& bindings() const { return m_bindings; }
    std::vector<AstPin*>& emptyPinps() { return m_emptyPinps; }
    std::unordered_map<ElabBindingVertex*, AstPin*>& explicitPinMap() { return m_explicitPinMap; }
    BindingMap& formalMap() { return m_formalMap; }
    const BindingMap& formalMap() const { return m_formalMap; }
    BindingNameMap& nameMap() { return m_nameMap; }
    const BindingNameMap& nameMap() const { return m_nameMap; }
    ElabMaterializationVertex* materializationp() const { return m_materializationp; }
    void materializationp(ElabMaterializationVertex* vertexp) {
        UASSERT(!m_materializationp && vertexp, "Replacing elaboration environment fact");
        m_materializationp = vertexp;
    }

    AstPin* paramsp() const {
        if (const AstCell* const cellp = VN_CAST(m_refp, Cell)) return cellp->paramsp();
        if (const AstClassOrPackageRef* const classRefp = VN_CAST(m_refp, ClassOrPackageRef)) {
            return classRefp->paramsp();
        }
        if (const AstIfaceRefDType* const ifaceRefp = VN_CAST(m_refp, IfaceRefDType)) {
            return ifaceRefp->paramsp();
        }
        return VN_AS(m_refp, ClassRefDType)->paramsp();
    }
    void addParamsp(AstPin* pinp) {
        if (AstCell* const cellp = VN_CAST(m_refp, Cell)) {
            cellp->addParamsp(pinp);
        } else if (AstClassOrPackageRef* const classRefp = VN_CAST(m_refp, ClassOrPackageRef)) {
            classRefp->addParamsp(pinp);
        } else if (AstIfaceRefDType* const ifaceRefp = VN_CAST(m_refp, IfaceRefDType)) {
            ifaceRefp->addParamsp(pinp);
        } else {
            VN_AS(m_refp, ClassRefDType)->addParamsp(pinp);
        }
    }
};

class ElabMaterializationVertex final : public ElabFactVertex {
    VL_RTTI_IMPL(ElabMaterializationVertex, ElabFactVertex)

    ElabReference* const m_referencep;
    const int m_referenceNumber;

    // Materializing an environment changes AST ownership and is therefore performed only at a
    // convergence boundary by ElabBindingGraph.  This fact is published explicitly afterward.
    bool resolveFact() override { return false; }
    bool hasDefinition() const override { return true; }
    bool worklistResolvable() const override { return false; }

public:
    ElabMaterializationVertex(V3Graph* graphp, ElabReference* referencep, int referenceNumber)
        : ElabFactVertex{graphp}
        , m_referencep{referencep}
        , m_referenceNumber{referenceNumber} {}

    string name() const override { return "ref" + cvtToStr(m_referenceNumber) + ".environment"; }
    string dotShape() const override { return "hexagon"; }
    FileLine* fileline() const override { return m_referencep->refp()->fileline(); }
};

class ElabDependencyVisitor final : public VNVisitorConst {
    V3Graph* const m_graphp;
    const BindingMap& m_formalMap;
    const std::unordered_map<AstNode*, ElabReference*>& m_referenceMap;
    ElabFactVertex* const m_consumerp;
    std::unordered_set<ElabFactVertex*> m_seen;
    std::unordered_set<const ElabBindingVertex*> m_walkedAnswers;
    std::unordered_set<AstNodeDType*> m_semanticTargets;

    void addFormalDependency(const AstNode* formalp) {
        const auto it = m_formalMap.find(formalp);
        if (it == m_formalMap.end()) return;
        ElabBindingVertex* const prerequisitep = it->second;
        if (m_seen.insert(prerequisitep).second) {
            new V3GraphEdge{m_graphp, prerequisitep, m_consumerp, 1};
        }
        // An explicit actual is a published binding, but a nested reference inside it
        // materializes its default actuals later.  A consumer cloning this answer must also
        // wait for those nested environments, or the clone captures a pinless reference.
        if (prerequisitep->isExplicit() && prerequisitep->answerp()
            && m_walkedAnswers.insert(prerequisitep).second) {
            iterateConst(prerequisitep->answerp());
        }
    }
    void addReferenceDependency(AstNode* refp) {
        const auto it = m_referenceMap.find(refp);
        if (it == m_referenceMap.end()) return;
        ElabMaterializationVertex* const prerequisitep = it->second->materializationp();
        if (!prerequisitep || !m_seen.insert(prerequisitep).second) return;
        new V3GraphEdge{m_graphp, prerequisitep, m_consumerp, 1};
    }

    void visit(AstRefDType* nodep) override {
        addFormalDependency(VN_CAST(nodep->refDTypep(), ParamTypeDType));
        iterateChildrenConst(nodep);
        // A typedef alias reaches its definition through a semantic pointer rather than an owned
        // child.  Follow that edge explicitly so a default aliased to a nested specialization
        // waits for the nested reference environment instead of relying on declaration order.
        AstNodeDType* targetp = nullptr;
        if (AstTypedef* const typedefp = nodep->typedefp()) targetp = typedefp->subDTypep();
        if (!targetp) targetp = nodep->refDTypep();
        if (targetp && targetp != nodep && !VN_IS(targetp, ParamTypeDType)
            && m_semanticTargets.insert(targetp).second) {
            iterateConst(targetp);
        }
    }
    void visit(AstVarRef* nodep) override {
        // A local VarRef to a formal belongs to this specialization environment.  A VarXRef
        // retains a hierarchical instance scope; different interface instances share the same
        // template formal pointer, so substituting an XRef by pointer would collapse scopes and
        // can recursively replace an explicit actual such as iface.FOO with itself.
        addFormalDependency(nodep->varp());
        iterateChildrenConst(nodep);
    }
    void visit(AstClassRefDType* nodep) override {
        addReferenceDependency(nodep);
        iterateChildrenConst(nodep);
    }
    void visit(AstClassOrPackageRef* nodep) override {
        addReferenceDependency(nodep);
        iterateChildrenConst(nodep);
    }
    void visit(AstIfaceRefDType* nodep) override {
        if (nodep->isVirtual()) addReferenceDependency(nodep);
        iterateChildrenConst(nodep);
    }
    void visit(AstNode* nodep) override { iterateChildrenConst(nodep); }

public:
    ElabDependencyVisitor(V3Graph* graphp, const BindingMap& formalMap,
                          const std::unordered_map<AstNode*, ElabReference*>& referenceMap,
                          ElabFactVertex* consumerp, AstNode* definitionp)
        : m_graphp{graphp}
        , m_formalMap{formalMap}
        , m_referenceMap{referenceMap}
        , m_consumerp{consumerp} {
        iterateConst(definitionp);
    }
};

class ElabSubstituteVisitor final : public VNVisitor {
    const AnswerMap& m_answers;

    AstNode* findAnswerp(const AstNode* formalp) const {
        const auto it = m_answers.find(formalp);
        return it == m_answers.end() ? nullptr : it->second;
    }
    void replaceWithAnswer(AstNode* nodep, AstNode* answerp) {
        UASSERT_OBJ(answerp, nodep, "Substituting empty elaboration fact");
        AstNode* const newp = answerp->cloneTree(false);
        nodep->replaceWith(newp);
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }

    void visit(AstRefDType* nodep) override {
        if (AstNode* const answerp = findAnswerp(VN_CAST(nodep->refDTypep(), ParamTypeDType))) {
            replaceWithAnswer(nodep, answerp);
            return;
        }
        iterateChildren(nodep);
    }
    void visit(AstVarRef* nodep) override {
        if (AstNode* const answerp = findAnswerp(nodep->varp())) {
            replaceWithAnswer(nodep, answerp);
            return;
        }
        iterateChildren(nodep);
    }
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    ElabSubstituteVisitor(AstNode* nodep, const AnswerMap& answers)
        : m_answers{answers} {
        iterate(nodep);
    }
};

class ElabAstCollector final : public VNVisitorConst {
    const bool m_skipGenericDefinitions;
    std::vector<AstRefDType*> m_refDTypeps;
    std::vector<AstDot*> m_dotps;
    std::vector<AstClassRefDType*> m_classRefDTypeps;
    std::vector<AstClassOrPackageRef*> m_classOrPackageRefps;
    std::vector<AstVarRef*> m_varRefps;
    std::vector<AstNodeVarRef*> m_nodeVarRefps;
    std::vector<AstVar*> m_varps;

    void visit(AstNodeModule* nodep) override {
        // A generic definition is a query template, not a concrete specialization demand.
        // Projection facts are collected from instantiated subtrees during V3Param.
        if (m_skipGenericDefinitions && nodep->hasGParam()) return;
        iterateChildrenConst(nodep);
    }
    void visit(AstRefDType* nodep) override {
        m_refDTypeps.push_back(nodep);
        iterateChildrenConst(nodep);
    }
    void visit(AstDot* nodep) override {
        m_dotps.push_back(nodep);
        iterateChildrenConst(nodep);
    }
    void visit(AstClassRefDType* nodep) override {
        m_classRefDTypeps.push_back(nodep);
        iterateChildrenConst(nodep);
    }
    void visit(AstClassOrPackageRef* nodep) override {
        m_classOrPackageRefps.push_back(nodep);
        iterateChildrenConst(nodep);
    }
    void visit(AstVarRef* nodep) override {
        m_varRefps.push_back(nodep);
        m_nodeVarRefps.push_back(nodep);
        iterateChildrenConst(nodep);
    }
    void visit(AstVarXRef* nodep) override {
        m_nodeVarRefps.push_back(nodep);
        iterateChildrenConst(nodep);
    }
    void visit(AstVar* nodep) override {
        m_varps.push_back(nodep);
        iterateChildrenConst(nodep);
    }
    void visit(AstNode* nodep) override { iterateChildrenConst(nodep); }

public:
    explicit ElabAstCollector(AstNode* nodep, bool skipGenericDefinitions = false)
        : m_skipGenericDefinitions{skipGenericDefinitions} {
        iterateConst(nodep);
    }

    const std::vector<AstRefDType*>& refDTypeps() const { return m_refDTypeps; }
    const std::vector<AstDot*>& dotps() const { return m_dotps; }
    const std::vector<AstClassRefDType*>& classRefDTypeps() const { return m_classRefDTypeps; }
    const std::vector<AstClassOrPackageRef*>& classOrPackageRefps() const {
        return m_classOrPackageRefps;
    }
    const std::vector<AstVarRef*>& varRefps() const { return m_varRefps; }
    const std::vector<AstNodeVarRef*>& nodeVarRefps() const { return m_nodeVarRefps; }
    const std::vector<AstVar*>& varps() const { return m_varps; }
};

class ElabSubstitutionVertex;
using SubstitutionMap = std::unordered_map<const AstNode*, ElabSubstitutionVertex*>;

class ElabSubstitutionVertex final : public ElabFactVertex {
    VL_RTTI_IMPL(ElabSubstitutionVertex, ElabFactVertex)

    AstNode* const m_formalp;
    AstNode* const m_definitionp;
    const SubstitutionMap& m_factMap;
    AstNode* m_answerp = nullptr;

    bool resolveFact() override {
        AstNode* const clonedp = m_definitionp->cloneTree(false);
        AstPin* const holderp = new AstPin{m_definitionp->fileline(), 0, "", clonedp};
        AnswerMap answers;
        for (const auto& pair : m_factMap) {
            if (pair.second->resolved()) answers.emplace(pair.first, pair.second->answerp());
        }
        { ElabSubstituteVisitor{holderp, answers}; }
        m_answerp = holderp->exprp()->unlinkFrBack();
        holderp->deleteTree();
        return true;
    }
    bool hasDefinition() const override { return m_definitionp; }

public:
    ElabSubstitutionVertex(V3Graph* graphp, AstNode* formalp, AstNode* definitionp,
                           const SubstitutionMap& factMap)
        : ElabFactVertex{graphp}
        , m_formalp{formalp}
        , m_definitionp{definitionp}
        , m_factMap{factMap} {}
    ~ElabSubstitutionVertex() override {
        if (m_answerp) m_answerp->deleteTree();
    }

    string name() const override { return "environment." + m_formalp->name(); }
    string dotShape() const override {
        return VN_IS(m_formalp, ParamTypeDType) ? "box" : "ellipse";
    }
    FileLine* fileline() const override { return m_formalp->fileline(); }
    AstNode* answerp() const { return m_answerp; }
};

class ElabSubstitutionGraph final : public ElabFactGraph {
    SubstitutionMap m_factMap;
    std::unordered_map<const AstNode*, AstNode*> m_overrides;

    ElabSubstitutionVertex* factFor(AstNode* formalp) {
        const auto found = m_factMap.find(formalp);
        if (found != m_factMap.end()) return found->second;

        const auto overrideIt = m_overrides.find(formalp);
        AstNode* const definitionp
            = overrideIt != m_overrides.end() ? overrideIt->second : formalDefaultp(formalp);
        ElabSubstitutionVertex* const vertexp
            = new ElabSubstitutionVertex{this, formalp, definitionp, m_factMap};
        m_factMap.emplace(formalp, vertexp);
        addFact(vertexp);
        if (definitionp) addDependencies(definitionp, vertexp);
        return vertexp;
    }

    void addDependencies(AstNode* nodep, ElabSubstitutionVertex* consumerp) {
        std::unordered_set<AstNode*> dependencies;
        const ElabAstCollector collector{nodep};
        // Only local references participate in formal substitution.  A VarXRef carries an
        // instance path and can share its declaration pointer with another specialization; its
        // scope must remain intact.
        for (AstVarRef* const refp : collector.varRefps()) {
            if (refp->varp()) dependencies.insert(refp->varp());
        }
        for (AstRefDType* const refp : collector.refDTypeps()) {
            if (AstParamTypeDType* const typep = VN_CAST(refp->refDTypep(), ParamTypeDType)) {
                dependencies.insert(typep);
            }
        }
        for (AstNode* const formalp : dependencies) {
            ElabSubstitutionVertex* const prerequisitep = factFor(formalp);
            if (consumerp) new V3GraphEdge{this, prerequisitep, consumerp, 1};
        }
    }

public:
    explicit ElabSubstitutionGraph(AstPin* pinsp) {
        for (AstPin* pinp = pinsp; pinp; pinp = VN_AS(pinp->nextp(), Pin)) {
            AstNode* const formalp = pinp->modPTypep() ? static_cast<AstNode*>(pinp->modPTypep())
                                                       : static_cast<AstNode*>(pinp->modVarp());
            if (formalp && pinp->exprp()) m_overrides.emplace(formalp, pinp->exprp());
        }
    }

    void substitute(AstNode* nodep) {
        addDependencies(nodep, nullptr);
        converge();
        classifyQuiescence();

        AnswerMap answers;
        for (const auto& pair : m_factMap) {
            if (pair.second->resolved()) answers.emplace(pair.first, pair.second->answerp());
        }
        { ElabSubstituteVisitor{nodep, answers}; }

        V3Stats::addStatSum("Elab, substitution facts", factCount());
        V3Stats::addStatSum("Elab, substitutions published", published());
        V3Stats::addStatSum("Elab, cyclic substitutions", cyclicFacts());
        V3Stats::addStatSum("Elab, blocked substitutions", blockedFacts());
        V3Stats::addStatSum("Elab, missing substitutions", missingFacts());
    }
};

bool ElabBindingVertex::resolveFact() {
    UASSERT_OBJ(m_referencep, m_formalp, "Elaboration fact has no reference");
    AstNode* const clonedp = m_defaultp->cloneTree(false);
    AstPin* const holderp = new AstPin{m_defaultp->fileline(), 0, "", clonedp};
    AnswerMap answers;
    for (const auto& pair : m_referencep->formalMap()) {
        if (pair.second->resolved()) answers.emplace(pair.first, pair.second->answerp());
    }
    { ElabSubstituteVisitor{holderp, answers}; }
    m_answerp = holderp->exprp()->unlinkFrBack();
    m_answerOwned = true;
    holderp->deleteTree();
    return true;
}

class ElabBindingGraph final : public ElabFactGraph {
    std::vector<std::unique_ptr<ElabReference>> m_references;
    std::unordered_map<AstNode*, ElabReference*> m_referenceMap;
    static AstNode* pinFormalp(AstPin* pinp) {
        if (pinp->modPTypep()) return pinp->modPTypep();
        AstVar* const varp = pinp->modVarp();
        return varp && varp->isGParam() ? varp : nullptr;
    }

    static bool isPositionalPin(const AstPin* pinp) {
        return pinp->name() == "__paramNumber" + cvtToStr(pinp->pinNum());
    }

    static AstNode* newFallbackp(const ElabBindingVertex* vertexp) {
        if (VN_IS(vertexp->formalp(), ParamTypeDType)) {
            return new AstBasicDType{vertexp->fileline(), VBasicDTypeKwd::LOGIC};
        }
        return new AstConst{vertexp->fileline(), 0};
    }

    static ElabBindingVertex* bindingForPin(ElabReference* referencep, AstPin* pinp) {
        const BindingMap& formalMap = referencep->formalMap();
        const auto exactIt = formalMap.find(pinFormalp(pinp));
        if (exactIt != formalMap.end()) return exactIt->second;

        // Cloning a class reference can leave a pin linked to the corresponding formal in an
        // earlier class clone.  Its semantic name remains authoritative for named bindings.
        if (!isPositionalPin(pinp)) {
            const BindingNameMap& nameMap = referencep->nameMap();
            const auto nameIt = nameMap.find(pinp->name());
            return nameIt == nameMap.end() ? nullptr : nameIt->second;
        }

        // LinkDot normally replaces positional placeholders with formal pointers.  References
        // embedded in a class specialization can be collected before that relink, however.  The
        // parser's pin number is the declaration-order binding identity, not an extra synthetic
        // parameter.
        const int index = pinp->pinNum() - 1;
        if (index < 0 || index >= static_cast<int>(referencep->bindings().size())) return nullptr;
        return referencep->bindings().at(index);
    }

    static void linkPinToFormal(AstPin* pinp, ElabBindingVertex* vertexp) {
        pinp->name(vertexp->formalp()->name());
        pinp->elabBinding(true);
        if (AstParamTypeDType* const formalp = VN_CAST(vertexp->formalp(), ParamTypeDType)) {
            pinp->modPTypep(formalp);
            pinp->modVarp(nullptr);
        } else {
            pinp->modVarp(VN_AS(vertexp->formalp(), Var));
            pinp->modPTypep(nullptr);
        }
    }

    uint64_t materialize(ElabReference* referencep, bool errorFallback = false) {
        uint64_t committed = 0;
        VNDeleter deleter;
        std::vector<AstPin*> originalPinps;
        for (AstPin* pinp = referencep->paramsp(); pinp;) {
            AstPin* const nextp = VN_CAST(pinp->nextp(), Pin);
            originalPinps.push_back(pinp->unlinkFrBack());
            pinp = nextp;
        }
        const std::unordered_set<AstPin*> emptyPinps{referencep->emptyPinps().begin(),
                                                     referencep->emptyPinps().end()};
        std::unordered_set<AstPin*> canonicalPinps;
        for (ElabBindingVertex* const vertexp : referencep->bindings()) {
            AstPin* pinp = nullptr;
            const auto explicitIt = referencep->explicitPinMap().find(vertexp);
            if (explicitIt != referencep->explicitPinMap().end()) {
                pinp = explicitIt->second;
            } else {
                if (!vertexp->resolved() && !errorFallback) continue;
                AstNode* const answerp
                    = vertexp->resolved() ? vertexp->releaseAnswerp() : newFallbackp(vertexp);
                pinp = new AstPin{answerp->fileline(), vertexp->pinNumber(),
                                  vertexp->formalp()->name(), answerp};
                pinp->param(true);
                pinp->elabBinding(true);
                pinp->elabDefault(true);
                if (AstParamTypeDType* const formalp
                    = VN_CAST(vertexp->formalp(), ParamTypeDType)) {
                    pinp->modPTypep(formalp);
                } else {
                    pinp->modVarp(VN_AS(vertexp->formalp(), Var));
                }
                ++committed;
            }
            referencep->addParamsp(pinp);
            canonicalPinps.insert(pinp);
        }
        // V3Elab's answer is the declaration-order tuple above.  Preserve unrelated synthetic
        // pins afterward, but discard parser-only empty actuals now that their defaults exist.
        for (AstPin* const pinp : originalPinps) {
            if (canonicalPinps.count(pinp)) continue;
            if (emptyPinps.count(pinp)) {
                deleter.pushDeletep(pinp);
            } else {
                referencep->addParamsp(pinp);
            }
        }
        return committed;
    }

public:
    void addReference(AstNode* nodep) {
        std::unique_ptr<ElabReference> referencep{new ElabReference{nodep}};
        AstNodeModule* const definitionp = referencep->definitionp();
        if (!definitionp || !definitionp->hasGParam()) return;

        const int referenceNumber = static_cast<int>(m_references.size()) + 1;
        int pinNumber = 0;
        for (AstNode* stmtp = definitionp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
            AstNode* formalp = nullptr;
            if (AstParamTypeDType* const typep = VN_CAST(stmtp, ParamTypeDType)) {
                if (typep->isGParam()) formalp = typep;
            } else if (AstVar* const varp = VN_CAST(stmtp, Var)) {
                if (varp->isGParam()) formalp = varp;
            }
            if (!formalp) continue;
            ++pinNumber;
            AstNode* const defaultp = formalDefaultp(formalp);
            ElabBindingVertex* const vertexp = new ElabBindingVertex{
                this, referencep.get(), formalp, defaultp, referenceNumber, pinNumber};
            addFact(vertexp);
            referencep->bindings().push_back(vertexp);
            referencep->formalMap().emplace(formalp, vertexp);
            referencep->nameMap().emplace(formalp->name(), vertexp);
        }
        if (referencep->bindings().empty()) return;

        ElabMaterializationVertex* const materializationp
            = new ElabMaterializationVertex{this, referencep.get(), referenceNumber};
        addFact(materializationp);
        referencep->materializationp(materializationp);
        for (ElabBindingVertex* const vertexp : referencep->bindings()) {
            new V3GraphEdge{this, vertexp, materializationp, 1};
        }

        for (AstPin* pinp = referencep->paramsp(); pinp; pinp = VN_AS(pinp->nextp(), Pin)) {
            ElabBindingVertex* const vertexp = bindingForPin(referencep.get(), pinp);
            if (!pinp->exprp()) {
                // The parser represents an explicitly empty parameter list, #(), as one empty
                // positional pin, and an empty named actual, .N(), keeps its formal at the
                // default.  Both are syntax provenance rather than bindings and must not
                // become extra specialization-name components after defaults are materialized.
                if (vertexp) referencep->emptyPinps().push_back(pinp);
                continue;
            }
            if (!vertexp) continue;
            // Once linking has established formal identity, discard parser-only positional
            // spelling.  Specialized-class clones later relink their pins by semantic name.
            linkPinToFormal(pinp, vertexp);
            if (!vertexp->resolved()) {
                referencep->explicitPinMap().emplace(vertexp, pinp);
                vertexp->publish(pinp->exprp(), false, true);
            }
        }
        m_referenceMap.emplace(nodep, referencep.get());
        m_references.emplace_back(std::move(referencep));
    }

    void buildDependencies() {
        for (const std::unique_ptr<ElabReference>& referencep : m_references) {
            for (ElabBindingVertex* const vertexp : referencep->bindings()) {
                if (!vertexp->resolved() && vertexp->hasDefault()) {
                    ElabDependencyVisitor{this, referencep->formalMap(), m_referenceMap, vertexp,
                                          vertexp->defaultp()};
                } else if (vertexp->isExplicit()) {
                    // An explicit actual is already a published binding, but it can own a nested
                    // parameterized reference.  The enclosing environment is not complete until
                    // that nested environment has materialized its own default actuals.
                    ElabDependencyVisitor{this, referencep->formalMap(), m_referenceMap,
                                          referencep->materializationp(), vertexp->answerp()};
                }
            }
        }
    }

    uint64_t convergeAndMaterialize() {
        uint64_t committed = 0;
        while (true) {
            converge();
            bool progressed = false;
            for (const std::unique_ptr<ElabReference>& referencep : m_references) {
                ElabMaterializationVertex* const materializationp = referencep->materializationp();
                if (materializationp->resolved()) continue;
                // All in-edges, not just this reference's bindings: buildDependencies adds
                // edges from nested reference environments inside explicit actuals, and a
                // dependent default cloned before those environments materialize their pins
                // would capture a nested reference without its default actuals.
                bool prerequisitesResolved = true;
                for (const V3GraphEdge& edge : materializationp->inEdges()) {
                    if (!edge.fromp()->as<ElabFactVertex>()->resolved()) {
                        prerequisitesResolved = false;
                    }
                }
                if (!prerequisitesResolved) continue;
                committed += materialize(referencep.get());
                publish(materializationp);
                progressed = true;
            }
            if (!progressed) break;
        }
        return committed;
    }

    uint64_t recoverUnresolved() {
        uint64_t committed = 0;
        VNDeleter deleter;
        std::unordered_set<AstNode*> diagnosedFormals;
        for (const std::unique_ptr<ElabReference>& referencep : m_references) {
            ElabMaterializationVertex* const materializationp = referencep->materializationp();
            if (materializationp->resolved()) continue;
            const bool cyclicEnvironment = dependsOnCycle(materializationp);
            // V3Param retains the established class missing-actual diagnostics, including
            // specialization instance context.  Interfaces require fallbacks here so an invalid
            // physical cell remains structurally linked for later error recovery.
            if (VN_IS(referencep->definitionp(), Class) && !cyclicEnvironment) continue;
            for (ElabBindingVertex* const vertexp : referencep->bindings()) {
                if (!vertexp->resolved() && !vertexp->hasDefault()) {
                    const bool isClass = VN_IS(referencep->definitionp(), Class);
                    if (VN_IS(vertexp->formalp(), ParamTypeDType)) {
                        referencep->refp()->v3error(
                            (isClass ? "Class parameter type" : "Parameter type")
                            << " without default value is never given value"
                            << " (IEEE 1800-2023 6.20.1): " << vertexp->formalp()->prettyNameQ());
                    } else {
                        referencep->refp()->v3error(
                            (isClass ? "Class parameter" : "Parameter")
                            << " without default value is never given value"
                            << " (IEEE 1800-2023 6.20.1): " << vertexp->formalp()->prettyNameQ());
                    }
                }
                if (cyclicEnvironment && vertexp->cyclic()
                    && diagnosedFormals.insert(vertexp->formalp()).second) {
                    vertexp->formalp()->v3error("Parameter default dependency is circular"
                                                " (IEEE 1800-2023 6.20.1): Parameter "
                                                << vertexp->formalp()->prettyNameQ() << " of "
                                                << referencep->definitionp()->prettyNameQ()
                                                << ".");
                    // Later passes keep running after an error.  Replace the illegal template
                    // default as well as materializing fallback actuals below, so a nested
                    // reference in the cycle cannot reach V3Width or post-parameter LinkDot and
                    // cause an internal error.
                    if (AstNode* const defaultNodep = vertexp->defaultp()) {
                        defaultNodep->replaceWith(newFallbackp(vertexp));
                        deleter.pushDeletep(defaultNodep);
                    }
                }
            }
            committed += materialize(referencep.get(), true);
        }
        return committed;
    }
};

class ElabCollectVisitor final : public VNVisitorConst {
    ElabBindingGraph& m_graph;

    void visit(AstCell* nodep) override {
        if (!nodep->virtIfaceScopeAnchor()) m_graph.addReference(nodep);
        iterateChildrenConst(nodep);
    }
    void visit(AstClassOrPackageRef* nodep) override {
        // A typedef projection consumes the specialization stored in the typedef's dtype.  It is
        // not a new reference to the underlying generic class and must not acquire fresh defaults.
        if (!VN_IS(nodep->classOrPackageNodep(), Typedef)) m_graph.addReference(nodep);
        iterateChildrenConst(nodep);
    }
    void visit(AstClassRefDType* nodep) override {
        m_graph.addReference(nodep);
        iterateChildrenConst(nodep);
    }
    void visit(AstIfaceRefDType* nodep) override {
        // Physical interface specializations are represented by their cells.  A virtual
        // interface reference is an independent specialization demand with the same binding
        // semantics, while LinkDot's dummy cell remains only its symbol-scope anchor.
        if (nodep->isVirtual()) m_graph.addReference(nodep);
        iterateChildrenConst(nodep);
    }
    void visit(AstNode* nodep) override { iterateChildrenConst(nodep); }

public:
    ElabCollectVisitor(AstNetlist* nodep, ElabBindingGraph& graph)
        : m_graph{graph} {
        iterateConst(nodep);
    }
};

class ElabDeferredParamVertex;
using DeferredParamMap = std::unordered_map<const AstVar*, ElabDeferredParamVertex*>;

class ElabDeferredParamVertex final : public ElabFactVertex {
    VL_RTTI_IMPL(ElabDeferredParamVertex, ElabFactVertex)

    AstVar* const m_varp;
    const int m_number;

    bool resolveFact() override {
        if (!m_varp->valuep()) return false;
        if (!VN_IS(m_varp->valuep(), Const)) V3Const::constifyParamsEdit(m_varp);
        // Aggregate parameters and type-valued expressions need not reduce to AstConst.  The
        // semantic fact is the now-linked value AST, which consumers may clone or further fold.
        return m_varp->valuep() != nullptr;
    }
    bool hasDefinition() const override { return m_varp->valuep(); }

public:
    ElabDeferredParamVertex(V3Graph* graphp, AstVar* varp, int number)
        : ElabFactVertex{graphp}
        , m_varp{varp}
        , m_number{number} {}

    string name() const override { return "param" + cvtToStr(m_number) + "." + m_varp->name(); }
    string dotShape() const override { return "diamond"; }
    FileLine* fileline() const override { return m_varp->fileline(); }

    AstVar* varp() const { return m_varp; }
};

class ElabDeferredParamDependencyVisitor final : public VNVisitorConst {
    V3Graph* const m_graphp;
    const DeferredParamMap& m_vertexMap;
    ElabDeferredParamVertex* const m_consumerp;
    std::unordered_set<ElabDeferredParamVertex*> m_seen;

    void visit(AstNodeVarRef* nodep) override {
        const auto it = m_vertexMap.find(nodep->varp());
        if (it != m_vertexMap.end() && m_seen.insert(it->second).second) {
            new V3GraphEdge{m_graphp, it->second, m_consumerp, 1};
        }
        iterateChildrenConst(nodep);
    }
    void visit(AstNode* nodep) override { iterateChildrenConst(nodep); }

public:
    ElabDeferredParamDependencyVisitor(V3Graph* graphp, const DeferredParamMap& vertexMap,
                                       ElabDeferredParamVertex* consumerp)
        : m_graphp{graphp}
        , m_vertexMap{vertexMap}
        , m_consumerp{consumerp} {
        iterateConst(consumerp->varp()->valuep());
    }
};

class ElabDeferredParamGraph final : public ElabFactGraph {
    std::vector<ElabDeferredParamVertex*> m_vertices;
    DeferredParamMap m_vertexMap;

public:
    void addParam(AstVar* varp) {
        if (!varp->valuep() || VN_IS(varp->valuep(), Const)) return;
        ElabDeferredParamVertex* const vertexp
            = new ElabDeferredParamVertex{this, varp, static_cast<int>(m_vertices.size()) + 1};
        addFact(vertexp);
        m_vertices.push_back(vertexp);
        m_vertexMap.emplace(varp, vertexp);
    }
    void buildDependencies() {
        for (ElabDeferredParamVertex* const vertexp : m_vertices) {
            ElabDeferredParamDependencyVisitor{this, m_vertexMap, vertexp};
        }
    }
};

AstClassRefDType* projectionClassRefDTypeOfNode(AstNode* nodep) {
    if (AstParamTypeDType* const typep = VN_CAST(nodep, ParamTypeDType)) {
        nodep = typep->subDTypep();
    }
    while (AstTypedef* const typedefp = VN_CAST(nodep, Typedef)) { nodep = typedefp->subDTypep(); }
    AstNodeDType* const dtypep = VN_CAST(nodep, NodeDType);
    return dtypep ? VN_CAST(dtypep->skipRefOrNullp(), ClassRefDType) : nullptr;
}

AstNode* projectionSourcep(AstClassOrPackageRef* classRefp) {
    if (!classRefp) return nullptr;
    if (AstClassRefDType* const dtypep
        = projectionClassRefDTypeOfNode(classRefp->classOrPackageNodep())) {
        return dtypep;
    }
    // Parameter pins are consumed during specialization, but projections cloned with the
    // reference still depend on that exact source node.  Class identity, not transient pin
    // ownership, determines whether this is a specialization producer.
    return VN_IS(classRefp->classOrPackageSkipp(), Class) ? classRefp : nullptr;
}

AstNode* projectionSourcep(AstRefDType* refp) {
    return projectionSourcep(VN_CAST(refp->classOrPackageOpp(), ClassOrPackageRef));
}

AstNode* projectionSourcep(AstDot* dotp) {
    if (!VN_IS(dotp->rhsp(), ParseRef)) return nullptr;
    return projectionSourcep(VN_CAST(dotp->lhsp(), ClassOrPackageRef));
}

AstClass* projectionClassp(AstNode* sourcep) {
    if (AstClassRefDType* const dtypep = VN_CAST(sourcep, ClassRefDType)) {
        return dtypep->classp();
    }
    if (AstClassOrPackageRef* const refp = VN_CAST(sourcep, ClassOrPackageRef)) {
        return VN_CAST(refp->classOrPackageSkipp(), Class);
    }
    return nullptr;
}

class ElabSpecializationVertex final : public ElabFactVertex {
    VL_RTTI_IMPL(ElabSpecializationVertex, ElabFactVertex)

    AstClass* m_classp = nullptr;
    AstNode* const m_sourcep;
    FileLine* const m_filelinep;
    const int m_number;

    bool resolveFact() override { return false; }
    bool hasDefinition() const override { return false; }
    bool worklistResolvable() const override { return false; }

public:
    ElabSpecializationVertex(V3Graph* graphp, AstNode* sourcep, int number)
        : ElabFactVertex{graphp}
        , m_sourcep{sourcep}
        , m_filelinep{sourcep->fileline()}
        , m_number{number} {}

    string name() const override { return "specialization" + cvtToStr(m_number); }
    string dotShape() const override { return "hexagon"; }
    FileLine* fileline() const override { return m_filelinep; }

    AstNode* sourcep() const { return m_sourcep; }
    AstClass* classp() const { return m_classp; }
    void classp(AstClass* classp) {
        UASSERT(!m_classp && classp, "Republishing class specialization fact");
        m_classp = classp;
    }
};

class ElabProjectionVertex final : public ElabFactVertex {
    VL_RTTI_IMPL(ElabProjectionVertex, ElabFactVertex)

    AstRefDType* const m_refp;
    ElabSpecializationVertex* const m_sourcep;
    VMemberMap& m_memberMap;
    const string m_name;
    FileLine* const m_filelinep;
    const int m_number;
    bool m_retired = false;
    bool m_definitionDependenciesBuilt = false;

    AstTypedef* projectedTypedefp() const {
        if (!m_sourcep->classp()) return nullptr;
        return VN_CAST(m_memberMap.findMember(m_sourcep->classp(), m_refp->name()), Typedef);
    }
    bool resolveFact() override {
        AstTypedef* const typedefp = projectedTypedefp();
        UASSERT_OBJ(typedefp && typedefp->subDTypep(), m_refp,
                    "Resolving undefined type projection fact");
        AstClass* const classp = m_sourcep->classp();
        m_refp->typedefp(typedefp);
        m_refp->classOrPackagep(classp);
        m_refp->refDTypep(typedefp->subDTypep());
        if (m_refp->dtypep()) m_refp->dtypep(typedefp->subDTypep());
        UINFO(9, "Published type projection " << m_refp << " from " << classp->name());
        return true;
    }
    bool hasDefinition() const override {
        if (!m_sourcep->resolved()) return true;
        AstTypedef* const typedefp = projectedTypedefp();
        return typedefp && typedefp->subDTypep();
    }

public:
    ElabProjectionVertex(V3Graph* graphp, AstRefDType* refp, ElabSpecializationVertex* sourcep,
                         VMemberMap& memberMap, int number)
        : ElabFactVertex{graphp}
        , m_refp{refp}
        , m_sourcep{sourcep}
        , m_memberMap{memberMap}
        , m_name{refp->name()}
        , m_filelinep{refp->fileline()}
        , m_number{number} {}

    string name() const override { return "projection" + cvtToStr(m_number) + "." + m_name; }
    string dotShape() const override { return "box"; }
    FileLine* fileline() const override { return m_filelinep; }

    AstRefDType* refp() const { return m_refp; }
    ElabSpecializationVertex* sourceVertexp() const { return m_sourcep; }
    AstNodeDType* definitionDTypep() const {
        AstTypedef* const typedefp = projectedTypedefp();
        return typedefp ? typedefp->subDTypep() : nullptr;
    }
    bool definitionDependenciesBuilt() const { return m_definitionDependenciesBuilt; }
    void definitionDependenciesBuilt(bool flag) { m_definitionDependenciesBuilt = flag; }
    bool retired() const { return m_retired; }
    void retire() { m_retired = true; }
};

class ElabAliasProjectionVertex final : public ElabFactVertex {
    VL_RTTI_IMPL(ElabAliasProjectionVertex, ElabFactVertex)

    AstRefDType* const m_refp;
    const string m_name;
    FileLine* const m_filelinep;
    const int m_number;
    bool m_retired = false;

    AstNodeDType* targetp() const {
        if (AstTypedef* const typedefp = m_refp->typedefp()) return typedefp->subDTypep();
        return m_refp->refDTypep();
    }
    bool resolveFact() override {
        AstNodeDType* const semanticTargetp = targetp();
        AstNodeDType* const resolvedp
            = semanticTargetp ? semanticTargetp->skipRefOrNullp() : nullptr;
        if (!resolvedp) return false;
        // The typedef owns the alias chain, so keep refDTypep pointing at its immediate semantic
        // target.  Refresh dtypep only when it is already acting as a resolved-type cache.
        m_refp->refDTypep(semanticTargetp);
        if (m_refp->dtypep()) m_refp->dtypep(resolvedp);
        UINFO(9, "Published type alias " << m_refp << " as " << resolvedp);
        return true;
    }
    bool hasDefinition() const override { return targetp(); }

public:
    ElabAliasProjectionVertex(V3Graph* graphp, AstRefDType* refp, int number)
        : ElabFactVertex{graphp}
        , m_refp{refp}
        , m_name{refp->name()}
        , m_filelinep{refp->fileline()}
        , m_number{number} {}

    string name() const override { return "alias" + cvtToStr(m_number) + "." + m_name; }
    string dotShape() const override { return "parallelogram"; }
    FileLine* fileline() const override { return m_filelinep; }
    AstRefDType* refp() const { return m_refp; }
    bool retired() const { return m_retired; }
    void retire() { m_retired = true; }
};

class ElabMemberProjectionVertex;
using MemberProjectionMap = std::unordered_map<AstDot*, ElabMemberProjectionVertex*>;

class ElabMemberProjectionVertex final : public ElabFactVertex {
    VL_RTTI_IMPL(ElabMemberProjectionVertex, ElabFactVertex)

    AstDot* const m_dotp;
    ElabSpecializationVertex* const m_sourcep;
    VNDeleter& m_deleter;
    VMemberMap& m_memberMap;
    MemberProjectionMap& m_projectionMap;
    const string m_name;
    FileLine* const m_filelinep;
    const int m_number;
    AstNode* m_answerp = nullptr;
    bool m_answerOwned = false;
    bool m_committed = false;
    bool m_retired = false;
    bool m_definitionDependenciesBuilt = false;

    AstNode* projectedMemberp() const {
        if (!m_sourcep->classp()) return nullptr;
        return m_memberMap.findMember(m_sourcep->classp(), m_name);
    }
    bool resolveFact() override {
        AstNode* const memberp = projectedMemberp();
        AstClass* const classp = m_sourcep->classp();
        UINFO(9, "Resolving member projection " << m_name << " from "
                                                << (classp ? classp->name() : "<unresolved>")
                                                << " member=" << memberp);
        if (AstTypedef* const typedefp = VN_CAST(memberp, Typedef)) {
            if (!typedefp->subDTypep()) return false;
            AstRefDType* const refp = new AstRefDType{m_filelinep, typedefp->name()};
            refp->typedefp(typedefp);
            refp->classOrPackagep(classp);
            refp->refDTypep(typedefp->subDTypep());
            refp->dtypep(typedefp->subDTypep());
            m_answerp = refp;
        } else if (AstVar* const varp = VN_CAST(memberp, Var)) {
            if (!varp->isParam() || !varp->valuep()) return false;
            AstNode* const clonedp = varp->valuep()->cloneTree(false);
            AstPin* const holderp = new AstPin{varp->fileline(), 0, "", clonedp};
            // clonep() is valid only until the next cloneTree call advances the clone epoch,
            // so capture every prerequisite's cloned Dot before any answer is cloned below.
            std::vector<std::pair<AstDot*, ElabMemberProjectionVertex*>> replacements;
            const auto collectPrerequisite = [&](AstDot* nestedDotp) {
                const auto it = m_projectionMap.find(nestedDotp);
                if (it != m_projectionMap.end() && it->second != this) {
                    if (AstDot* const clonep = nestedDotp->clonep()) {
                        replacements.emplace_back(clonep, it->second);
                    }
                }
            };
            const ElabAstCollector collector{varp->valuep()};
            for (AstDot* const nestedDotp : collector.dotps()) { collectPrerequisite(nestedDotp); }
            // Replace inner cloned projections first so replacing an outer Dot never deletes a
            // cloned descendant before its semantic answer is installed.
            for (auto it = replacements.rbegin(); it != replacements.rend(); ++it) {
                AstDot* clonep = it->first;
                ElabMemberProjectionVertex* const prerequisitep = it->second;
                if (!prerequisitep->resolved() || !prerequisitep->m_answerp) continue;
                clonep->replaceWith(prerequisitep->m_answerp->cloneTree(false));
                VL_DO_DANGLING(clonep->deleteTree(), clonep);
            }
            V3Const::constifyParamsEdit(holderp->exprp());
            AstConst* const constp = VN_CAST(holderp->exprp(), Const);
            if (!constp) {
                holderp->deleteTree();
                return false;
            }
            m_answerp = constp->unlinkFrBack();
            holderp->deleteTree();
        } else {
            return false;
        }
        m_answerOwned = true;
        UINFO(9, "Published member projection " << m_name << " from " << classp->name());
        return true;
    }
    bool hasDefinition() const override {
        if (!m_sourcep->resolved()) return true;
        AstNode* const memberp = projectedMemberp();
        if (const AstTypedef* const typedefp = VN_CAST(memberp, Typedef)) {
            return typedefp->subDTypep();
        }
        const AstVar* const varp = VN_CAST(memberp, Var);
        return varp && varp->isParam() && varp->valuep();
    }

public:
    ElabMemberProjectionVertex(V3Graph* graphp, AstDot* dotp, ElabSpecializationVertex* sourcep,
                               VNDeleter& deleter, VMemberMap& memberMap,
                               MemberProjectionMap& projectionMap, int number)
        : ElabFactVertex{graphp}
        , m_dotp{dotp}
        , m_sourcep{sourcep}
        , m_deleter{deleter}
        , m_memberMap{memberMap}
        , m_projectionMap{projectionMap}
        , m_name{VN_AS(dotp->rhsp(), ParseRef)->name()}
        , m_filelinep{dotp->fileline()}
        , m_number{number} {}
    ~ElabMemberProjectionVertex() override {
        if (m_answerOwned) m_answerp->deleteTree();
    }

    string name() const override { return "member" + cvtToStr(m_number) + "." + m_name; }
    string dotShape() const override { return "ellipse"; }
    FileLine* fileline() const override { return m_filelinep; }

    AstDot* dotp() const { return m_dotp; }
    ElabSpecializationVertex* sourceVertexp() const { return m_sourcep; }
    AstNode* definitionp() const {
        AstNode* const memberp = projectedMemberp();
        if (AstTypedef* const typedefp = VN_CAST(memberp, Typedef)) {
            return typedefp->subDTypep();
        }
        if (AstVar* const varp = VN_CAST(memberp, Var)) return varp->valuep();
        return nullptr;
    }
    bool definitionDependenciesBuilt() const { return m_definitionDependenciesBuilt; }
    void definitionDependenciesBuilt(bool flag) { m_definitionDependenciesBuilt = flag; }
    bool committed() const { return m_committed; }
    bool retired() const { return m_retired; }
    void retire() { m_retired = true; }
    void commit() {
        UASSERT(resolved() && m_answerp && !m_committed && !m_retired,
                "Committing invalid member projection fact");
        // Keep the fact's canonical answer alive until graph destruction.  A later specialized
        // definition may still depend on this projection after its original use is committed;
        // transferring the answer into the mutable AST would leave that dependency with a
        // dangling pointer once subsequent passes replace or delete the committed node.
        AstNode* const committedp = m_answerp->cloneTree(false);
        m_dotp->replaceWith(committedp);
        m_committed = true;
        const size_t erased = m_projectionMap.erase(m_dotp);
        UASSERT(erased == 1, "Committing unregistered member projection fact");
        // A source vertex may point into the detached Dot subtree.  Keep all such nodes alive
        // until after the graph is destroyed, so raw AST addresses remain stable fact identities
        // throughout convergence and cannot be recycled for an unrelated specialization source.
        VL_DO_DANGLING(m_deleter.pushDeletep(m_dotp), m_dotp);
    }
};

class ElabProjectionGraph final : public ElabFactGraph {
public:
    void add(ElabFactVertex* vertexp) { addFact(vertexp); }
};

}  // namespace

//######################################################################
// Type projection facts

class V3Elab::ProjectionState final {
    AstNetlist* const m_rootp;
    // Declared before the graph so reverse-order destruction drops all fact pointers before
    // deleting committed source-bearing subtrees.
    VNDeleter m_deleter;
    ElabProjectionGraph m_graph;
    VMemberMap m_memberMap;
    std::unordered_map<AstNode*, ElabSpecializationVertex*> m_sourceMap;
    std::unordered_map<AstRefDType*, ElabFactVertex*> m_typeFactMap;
    MemberProjectionMap m_memberProjectionMap;
    std::vector<ElabProjectionVertex*> m_projections;
    std::vector<ElabAliasProjectionVertex*> m_aliasProjections;
    std::vector<ElabMemberProjectionVertex*> m_memberProjections;
    std::unordered_set<AstRefDType*> m_collectingTypeRefs;
    bool m_finalized = false;

    ElabSpecializationVertex* sourceVertexp(AstNode* sourcep) {
        const auto pair = m_sourceMap.emplace(sourcep, nullptr);
        if (pair.second) {
            pair.first->second = new ElabSpecializationVertex{
                &m_graph, sourcep, static_cast<int>(m_sourceMap.size())};
            m_graph.add(pair.first->second);
        }
        return pair.first->second;
    }

    ElabFactVertex* typeFactp(AstRefDType* refp) {
        const auto found = m_typeFactMap.find(refp);
        if (found != m_typeFactMap.end()) return found->second;
        if (!m_collectingTypeRefs.insert(refp).second) return nullptr;

        AstNode* const directSourcep = projectionSourcep(refp);
        if (AstNode* const sourcep = directSourcep) {
            ElabSpecializationVertex* const specializationp = sourceVertexp(sourcep);
            ElabProjectionVertex* const vertexp
                = new ElabProjectionVertex{&m_graph, refp, specializationp, m_memberMap,
                                           static_cast<int>(m_projections.size()) + 1};
            m_graph.add(vertexp);
            new V3GraphEdge{&m_graph, specializationp, vertexp, 1};
            m_typeFactMap.emplace(refp, vertexp);
            m_projections.push_back(vertexp);
            m_collectingTypeRefs.erase(refp);
            return vertexp;
        }

        // A reference to an ordinary typedef can still be a dependent consumer.  Its defining
        // dtype is reached through a semantic pointer rather than an AST child, so explicitly
        // discover projection facts in that definition and make the alias wait for them.
        AstNodeDType* targetp = nullptr;
        if (AstTypedef* const typedefp = refp->typedefp()) targetp = typedefp->subDTypep();
        if (!targetp) targetp = refp->refDTypep();
        std::unordered_set<ElabFactVertex*> prerequisites;
        const auto addPrerequisite = [&](AstRefDType* nestedp) {
            if (!nestedp || nestedp == refp) return;
            if (ElabFactVertex* const prerequisitep = typeFactp(nestedp)) {
                prerequisites.insert(prerequisitep);
            }
        };
        if (targetp && targetp != refp) {
            const ElabAstCollector collector{targetp};
            for (AstRefDType* const nestedp : collector.refDTypeps()) { addPrerequisite(nestedp); }
        }
        m_collectingTypeRefs.erase(refp);
        if (prerequisites.empty()) return nullptr;

        ElabAliasProjectionVertex* const vertexp = new ElabAliasProjectionVertex{
            &m_graph, refp, static_cast<int>(m_aliasProjections.size()) + 1};
        m_graph.add(vertexp);
        for (ElabFactVertex* const prerequisitep : prerequisites) {
            new V3GraphEdge{&m_graph, prerequisitep, vertexp, 1};
        }
        m_typeFactMap.emplace(refp, vertexp);
        m_aliasProjections.push_back(vertexp);
        return vertexp;
    }

    void addDefinitionDependencies(AstNode* definitionp, ElabFactVertex* consumerp) {
        if (!definitionp) return;
        std::unordered_set<ElabFactVertex*> prerequisites;
        const auto addPrerequisite = [&](AstRefDType* refp) {
            if (!refp) return;
            if (ElabFactVertex* const prerequisitep = typeFactp(refp)) {
                if (prerequisitep != consumerp) prerequisites.insert(prerequisitep);
            }
        };
        const auto addMemberPrerequisite = [&](AstDot* dotp) {
            if (!dotp) return;
            const auto it = m_memberProjectionMap.find(dotp);
            if (it != m_memberProjectionMap.end() && it->second != consumerp) {
                prerequisites.insert(it->second);
            }
        };
        const ElabAstCollector collector{definitionp};
        for (AstRefDType* const refp : collector.refDTypeps()) addPrerequisite(refp);
        for (AstDot* const dotp : collector.dotps()) addMemberPrerequisite(dotp);
        for (ElabFactVertex* const prerequisitep : prerequisites) {
            UINFO(9, "Adding semantic dependency " << prerequisitep->name() << " -> "
                                                   << consumerp->name());
            new V3GraphEdge{&m_graph, prerequisitep, consumerp, 1};
        }
    }

    void buildDefinitionDependencies() {
        // The vectors may grow while a definition is scanned, as semantic typedef links expose
        // further projection facts.  Index iteration deliberately includes those newly added
        // facts in the same derivation step.
        for (size_t i = 0; i < m_projections.size(); ++i) {
            ElabProjectionVertex* const projectionp = m_projections.at(i);
            if (projectionp->definitionDependenciesBuilt()
                || !projectionp->sourceVertexp()->classp()) {
                continue;
            }
            AstNodeDType* const dtypep = projectionp->definitionDTypep();
            if (!dtypep) continue;
            addDefinitionDependencies(dtypep, projectionp);
            projectionp->definitionDependenciesBuilt(true);
        }
        for (size_t i = 0; i < m_memberProjections.size(); ++i) {
            ElabMemberProjectionVertex* const projectionp = m_memberProjections.at(i);
            if (projectionp->definitionDependenciesBuilt()
                || !projectionp->sourceVertexp()->classp()) {
                continue;
            }
            AstNode* const definitionp = projectionp->definitionp();
            if (!definitionp) continue;
            addDefinitionDependencies(definitionp, projectionp);
            projectionp->definitionDependenciesBuilt(true);
        }
    }

    void collectSpecializationSources(ElabFactVertex* vertexp,
                                      std::unordered_set<ElabFactVertex*>& seenFacts,
                                      std::unordered_set<ElabSpecializationVertex*>& seenSources,
                                      std::vector<ElabSpecializationVertex*>& sources) const {
        if (!vertexp || vertexp->resolved() || !seenFacts.insert(vertexp).second) return;
        if (ElabSpecializationVertex* const specializationp
            = vertexp->cast<ElabSpecializationVertex>()) {
            if (seenSources.insert(specializationp).second) sources.push_back(specializationp);
            return;
        }
        for (const V3GraphEdge& edge : vertexp->inEdges()) {
            collectSpecializationSources(edge.fromp()->as<ElabFactVertex>(), seenFacts,
                                         seenSources, sources);
        }
    }

    std::vector<ElabSpecializationVertex*> specializationSources(AstNode* nodep) {
        std::unordered_set<ElabFactVertex*> seenFacts;
        std::unordered_set<ElabSpecializationVertex*> seenSources;
        std::vector<ElabSpecializationVertex*> sources;
        const auto collectSource = [&](AstNode* sourcep) {
            if (!sourcep) return;
            AstClass* const classp = projectionClassp(sourcep);
            if (!classp || !classp->hasGParam()) return;
            ElabSpecializationVertex* const vertexp = sourceVertexp(sourcep);
            collectSpecializationSources(vertexp, seenFacts, seenSources, sources);
        };
        const auto collectType = [&](AstRefDType* refp) {
            const auto it = m_typeFactMap.find(refp);
            if (it != m_typeFactMap.end()) {
                collectSpecializationSources(it->second, seenFacts, seenSources, sources);
            }
        };
        const auto collectMember = [&](AstDot* dotp) {
            const auto it = m_memberProjectionMap.find(dotp);
            if (it != m_memberProjectionMap.end()) {
                collectSpecializationSources(it->second, seenFacts, seenSources, sources);
            }
        };
        const auto collectClassRef = [&](AstClassRefDType* refp) { collectSource(refp); };
        const auto collectClassOrPackageRef
            = [&](AstClassOrPackageRef* refp) { collectSource(projectionSourcep(refp)); };
        const ElabAstCollector collector{nodep, true};
        for (AstRefDType* const refp : collector.refDTypeps()) collectType(refp);
        for (AstDot* const dotp : collector.dotps()) collectMember(dotp);
        for (AstClassRefDType* const refp : collector.classRefDTypeps()) { collectClassRef(refp); }
        for (AstClassOrPackageRef* const refp : collector.classOrPackageRefps()) {
            collectClassOrPackageRef(refp);
        }
        return sources;
    }

    void collect(AstNode* nodep) {
        const auto collectRef = [this](AstRefDType* refp) {
            if (!refp) return;
            typeFactp(refp);
        };
        const auto collectDot = [this](AstDot* dotp) {
            if (!dotp) return;
            if (m_memberProjectionMap.count(dotp)) return;
            AstNode* const sourcep = projectionSourcep(dotp);
            if (!sourcep) return;
            ElabSpecializationVertex* const specializationp = sourceVertexp(sourcep);
            ElabMemberProjectionVertex* const vertexp
                = new ElabMemberProjectionVertex{&m_graph,
                                                 dotp,
                                                 specializationp,
                                                 m_deleter,
                                                 m_memberMap,
                                                 m_memberProjectionMap,
                                                 static_cast<int>(m_memberProjections.size()) + 1};
            m_graph.add(vertexp);
            new V3GraphEdge{&m_graph, specializationp, vertexp, 1};
            m_memberProjectionMap.emplace(dotp, vertexp);
            m_memberProjections.push_back(vertexp);
        };
        const ElabAstCollector collector{nodep, true};
        for (AstRefDType* const refp : collector.refDTypeps()) collectRef(refp);
        for (AstDot* const dotp : collector.dotps()) collectDot(dotp);
    }

public:
    explicit ProjectionState(AstNetlist* nodep)
        : m_rootp{nodep} {
        collect(nodep);
    }

    void publish(AstNode* sourcep) {
        UASSERT(!m_finalized, "Publishing a specialization after projection quiescence");
        const auto it = m_sourceMap.find(sourcep);
        if (it == m_sourceMap.end()) {
            UINFO(9, "Ignoring unobserved specialization source " << sourcep);
            return;
        }
        if (it->second->resolved()) return;
        AstClass* const classp = projectionClassp(sourcep);
        if (!classp) {
            UINFO(9, "Specialization source has no class " << sourcep);
            return;
        }
        UINFO(9, "Publishing specialization source " << sourcep << " as " << classp->name());
        // A specialized class may contain projections cloned after the initial collection.
        it->second->classp(classp);
        collect(classp);
        // A projected member can itself be a typedef alias containing further projections.  Its
        // defining dtype only becomes authoritative after the source class is specialized, so
        // derive those result dependencies now, before publishing the source wakes consumers.
        buildDefinitionDependencies();
        m_graph.publish(it->second);
        buildDefinitionDependencies();
        m_graph.converge();
    }

    void commitMembers(AstNode* nodep) {
        collect(nodep);
        buildDefinitionDependencies();
        // Cloned parameter pins may first expose a projection after the exact class
        // specialization event has passed.  Publish its already-concrete source before trying
        // to commit the consumer; the graph edge remains the only resolution trigger.
        for (ElabSpecializationVertex* const specializationp : specializationSources(nodep)) {
            AstNode* const sourcep = specializationp->sourcep();
            AstClass* const classp = projectionClassp(sourcep);
            if (classp && !classp->hasGParam()) publish(sourcep);
        }
        buildDefinitionDependencies();
        m_graph.converge();
        std::vector<ElabMemberProjectionVertex*> vertices;
        const ElabAstCollector collector{nodep, true};
        for (AstDot* const dotp : collector.dotps()) {
            const auto it = m_memberProjectionMap.find(dotp);
            if (it != m_memberProjectionMap.end()) vertices.push_back(it->second);
        }
        // Commit inner expressions first, preserving the ownership of outer Dot nodes until all
        // descendants have consumed their answers.
        for (auto it = vertices.rbegin(); it != vertices.rend(); ++it) {
            ElabMemberProjectionVertex* const vertexp = *it;
            if (vertexp->resolved() && !vertexp->committed() && !vertexp->retired()) {
                vertexp->commit();
            }
        }
    }

    void resolveDependentProjections(AstNode* nodep,
                                     const std::function<void(AstNode*, AstClass*)>& specialize) {
        // Specialization is an external fact producer owned by V3Param.  Keep its scheduling in
        // this graph: discover the exact unresolved producers, request each at most once in this
        // convergence step, and rederive dependencies after every AST-changing callback.
        std::unordered_set<ElabSpecializationVertex*> attempted;
        while (true) {
            collect(nodep);
            buildDefinitionDependencies();
            ElabSpecializationVertex* pendingp = nullptr;
            const std::vector<ElabSpecializationVertex*> sources = specializationSources(nodep);
            for (auto it = sources.rbegin(); it != sources.rend(); ++it) {
                ElabSpecializationVertex* const specializationp = *it;
                if (specializationp->sourcep() == nodep || specializationp->resolved()
                    || attempted.count(specializationp)) {
                    continue;
                }
                AstClass* const classp = projectionClassp(specializationp->sourcep());
                if (classp && classp->hasGParam()) {
                    pendingp = specializationp;
                    break;
                }
            }
            if (!pendingp) break;
            attempted.insert(pendingp);
            AstNode* const sourcep = pendingp->sourcep();
            AstClass* const classp = projectionClassp(sourcep);
            UASSERT_OBJ(classp, sourcep, "Dependent projection source has no class");
            UINFO(9, "Requesting specialization source " << sourcep);
            specialize(sourcep, classp);
            // The callback publishes successful specializations.  It may also clone definitions
            // containing new facts, so collect again before choosing the next producer.
            collect(nodep);
            buildDefinitionDependencies();
            m_graph.converge();
        }
        commitMembers(nodep);
    }

    void converge() {
        UASSERT(!m_finalized, "Type projections converged twice");
        collect(m_rootp);
        buildDefinitionDependencies();

        std::unordered_set<AstRefDType*> liveRefps;
        std::unordered_set<AstNode*> liveSourceps;
        const ElabAstCollector collector{m_rootp, true};
        for (AstRefDType* const refp : collector.refDTypeps()) {
            liveRefps.insert(refp);
            if (AstNode* const sourcep = projectionSourcep(refp)) liveSourceps.insert(sourcep);
        }
        for (AstDot* const dotp : collector.dotps()) {
            if (AstNode* const sourcep = projectionSourcep(dotp)) liveSourceps.insert(sourcep);
        }

        // Specializations normally publish at the exact V3Param event.  Also accept classes
        // already known to be concrete, for facts collected from newly cloned subtrees.
        for (AstNode* const sourcep : liveSourceps) {
            const auto it = m_sourceMap.find(sourcep);
            if (it == m_sourceMap.end() || it->second->resolved()) continue;
            AstClass* const classp = projectionClassp(sourcep);
            if (classp && !classp->hasGParam()) publish(sourcep);
        }

        m_graph.converge();
        commitMembers(m_rootp);

        uint64_t retired = 0;
        for (ElabProjectionVertex* const vertexp : m_projections) {
            if (vertexp->resolved() || liveRefps.count(vertexp->refp())) continue;
            vertexp->retire();
            m_graph.publish(vertexp);
            ++retired;
        }
        for (ElabAliasProjectionVertex* const vertexp : m_aliasProjections) {
            if (vertexp->resolved() || liveRefps.count(vertexp->refp())) continue;
            vertexp->retire();
            m_graph.publish(vertexp);
            ++retired;
        }
        std::unordered_set<AstDot*> liveDotps;
        for (AstDot* const dotp : collector.dotps()) liveDotps.insert(dotp);
        for (ElabMemberProjectionVertex* const vertexp : m_memberProjections) {
            if (vertexp->committed() || vertexp->retired()) continue;
            if (liveDotps.count(vertexp->dotp())) continue;
            vertexp->retire();
            if (!vertexp->resolved()) m_graph.publish(vertexp);
            ++retired;
        }
        m_graph.classifyQuiescence();
        m_finalized = true;

        uint64_t published = 0;
        uint64_t missing = 0;
        uint64_t blocked = 0;
        uint64_t cyclic = 0;
        for (const ElabProjectionVertex* const vertexp : m_projections) {
            if (vertexp->retired()) continue;
            if (vertexp->resolved()) ++published;
            if (vertexp->missing()) ++missing;
            if (vertexp->blocked()) ++blocked;
            if (vertexp->cyclic()) ++cyclic;
        }
        for (const ElabAliasProjectionVertex* const vertexp : m_aliasProjections) {
            if (vertexp->retired()) continue;
            if (vertexp->resolved()) ++published;
            if (vertexp->missing()) ++missing;
            if (vertexp->blocked()) ++blocked;
            if (vertexp->cyclic()) ++cyclic;
        }
        for (const ElabMemberProjectionVertex* const vertexp : m_memberProjections) {
            if (vertexp->retired()) continue;
            if (vertexp->resolved()) ++published;
            if (vertexp->missing()) ++missing;
            if (vertexp->blocked()) ++blocked;
            if (vertexp->cyclic()) ++cyclic;
        }
        const uint64_t projectionFacts
            = m_projections.size() + m_aliasProjections.size() + m_memberProjections.size();
        V3Stats::addStatSum("Elab, projection facts", projectionFacts);
        V3Stats::addStatSum("Elab, projections published", published);
        V3Stats::addStatSum("Elab, missing projections", missing);
        V3Stats::addStatSum("Elab, blocked projections", blocked);
        V3Stats::addStatSum("Elab, cyclic projections", cyclic);
        V3Stats::addStatSum("Elab, retired projections", retired);
        UINFO(4, "Projection quiescence: facts="
                     << projectionFacts << " published=" << published << " missing=" << missing
                     << " blocked=" << blocked << " cyclic=" << cyclic << " retired=" << retired);
        if (dumpGraphLevel() >= 6) m_graph.dumpDotFilePrefixed("elab-projections");
    }
};

//######################################################################
// V3Elab entry

V3Elab::V3Elab() = default;
V3Elab::~V3Elab() = default;

void V3Elab::elab(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ":");
    ElabBindingGraph graph;
    { ElabCollectVisitor{nodep, graph}; }
    graph.buildDependencies();
    const uint64_t committed = graph.convergeAndMaterialize();
    graph.classifyQuiescence();
    const uint64_t fallbackBindings = graph.recoverUnresolved();
    const uint64_t unresolved = graph.unresolved();
    V3Stats::addStatSum("Elab, facts published", graph.published());
    V3Stats::addStatSum("Elab, defaults committed", committed);
    V3Stats::addStatSum("Elab, fallback bindings committed", fallbackBindings);
    V3Stats::addStatSum("Elab, unresolved facts", unresolved);
    V3Stats::addStatSum("Elab, cyclic facts", graph.cyclicFacts());
    V3Stats::addStatSum("Elab, blocked facts", graph.blockedFacts());
    V3Stats::addStatSum("Elab, missing facts", graph.missingFacts());
    UINFO(4, "Elaboration quiescence: unresolved="
                 << unresolved << " cyclic=" << graph.cyclicFacts()
                 << " blocked=" << graph.blockedFacts() << " missing=" << graph.missingFacts()
                 << " fallback-bindings=" << fallbackBindings);
    if (dumpGraphLevel() >= 6) graph.dumpDotFilePrefixed("elab-dependencies");
    m_projectionStatep.reset(new ProjectionState{nodep});
    // LinkInc deliberately leaves some typedef projections pointing into parameterized class
    // templates; V3Param retargets them while cloning specializations.  Dump this boundary for
    // inspection, but its cross-links are not yet valid enough for V3Broken.
    V3Global::dumpCheckGlobalTree("elab", 0, dumpTreeEitherLevel() >= 3, false);
}

void V3Elab::publishClassSpecialization(AstNode* nodep) {
    UASSERT(m_projectionStatep, "Publishing a specialization before elaboration");
    m_projectionStatep->publish(nodep);
}

void V3Elab::resolveDependentProjections(
    AstNode* nodep, const std::function<void(AstNode*, AstClass*)>& specialize) {
    UASSERT(m_projectionStatep, "Resolving dependent projections before elaboration");
    m_projectionStatep->resolveDependentProjections(nodep, specialize);
}

void V3Elab::convergeTypeProjections() {
    UASSERT(m_projectionStatep, "Converging type projections before elaboration");
    m_projectionStatep->converge();
    // ParamVisitor and ParamProcessor still own deferred-deletion queues at this point.  Drop all
    // projection pointers before those queues free the source and consumer nodes.
    m_projectionStatep.reset();
}

void V3Elab::beginDeferredParams() {
    UASSERT(!m_collectingDeferredParams && m_deferredParamVarps.empty(),
            "Deferred elaboration phase already active");
    m_collectingDeferredParams = true;
}

void V3Elab::deferParam(AstVar* varp) {
    UASSERT(m_collectingDeferredParams && varp, "Registering a parameter outside elaboration");
    m_deferredParamVarps.insert(varp);
}

bool V3Elab::deferParamIfDependent(AstVar* varp) {
    UASSERT(m_collectingDeferredParams && varp,
            "Discovering a deferred parameter outside elaboration");
    AstNode* const valuep = varp->valuep();
    if (!valuep) return false;

    const ElabAstCollector collector{valuep};
    for (AstDot* const dotp : collector.dotps()) {
        if (!VN_IS(dotp->lhsp(), ClassOrPackageRef)) continue;
        deferParam(varp);
        return true;
    }
    for (AstNodeVarRef* const refp : collector.nodeVarRefps()) {
        const AstVar* const prerequisitep = refp->varp();
        if (!prerequisitep || prerequisitep->varType() != VVarType::LPARAM
            || VN_IS(prerequisitep->valuep(), Const)) {
            continue;
        }
        deferParam(varp);
        return true;
    }
    return false;
}

void V3Elab::convergeDeferredParams(AstNetlist* nodep) {
    UASSERT(m_collectingDeferredParams, "Deferred elaboration phase is not active");
    std::vector<AstVar*> liveVarps;
    const ElabAstCollector collector{nodep};
    for (AstVar* const varp : collector.varps()) {
        if (m_deferredParamVarps.count(varp)) liveVarps.push_back(varp);
    }
    const uint64_t retired = m_deferredParamVarps.size() - liveVarps.size();
    m_deferredParamVarps.clear();
    m_collectingDeferredParams = false;

    ElabDeferredParamGraph graph;
    for (AstVar* const varp : liveVarps) graph.addParam(varp);
    graph.buildDependencies();
    graph.converge();
    graph.classifyQuiescence();

    V3Stats::addStatSum("Elab, deferred parameter facts", graph.factCount());
    V3Stats::addStatSum("Elab, deferred parameters published", graph.published());
    V3Stats::addStatSum("Elab, deferred parameters retired", retired);
    V3Stats::addStatSum("Elab, unresolved deferred parameters", graph.unresolved());
    V3Stats::addStatSum("Elab, cyclic deferred parameters", graph.cyclicFacts());
    V3Stats::addStatSum("Elab, blocked deferred parameters", graph.blockedFacts());
    UINFO(4, "Deferred parameter quiescence: facts="
                 << graph.factCount() << " published=" << graph.published()
                 << " unresolved=" << graph.unresolved() << " cyclic=" << graph.cyclicFacts()
                 << " blocked=" << graph.blockedFacts() << " retired=" << retired);
    if (dumpGraphLevel() >= 6) graph.dumpDotFilePrefixed("elab-param-dependencies");
    V3Global::dumpCheckGlobalTree("elab-param", 0, dumpTreeEitherLevel() >= 3);
}

void V3Elab::substituteParams(AstNode* nodep, AstPin* pinsp) {
    ElabSubstitutionGraph{pinsp}.substitute(nodep);
}
