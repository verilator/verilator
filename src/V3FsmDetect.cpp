// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: FSM coverage detect pass
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
// FSM COVERAGE DETECT:
//      Walk clocked always blocks while the original FSM structure is still
//      present, build a per-FSM V3Graph representation of the extracted
//      states/transitions, then immediately lower that completed graph state
//      into the final coverage declarations, previous-state tracking, and
//      active blocks needed to implement FSM state and arc coverage in the
//      generated model.
//
//*************************************************************************

#include "V3PchAstNoMT.h"

#include "V3FsmDetect.h"

#include "V3Ast.h"
#include "V3FsmGraph.h"

#include <cctype>
#include <map>
#include <memory>
#include <unordered_map>

VL_DEFINE_DEBUG_FUNCTIONS;

namespace {

struct DetectedFsm final {
    std::unique_ptr<FsmGraph> graphp;
    AstNodeModule* modp = nullptr;
    AstAlways* alwaysp = nullptr;
};
using DetectedFsmMap = std::map<string, DetectedFsm>;

// Local shared state between the two adjacent FSM coverage phases. Detection
// fills this with recovered FSM graphs; lowering consumes the completed graphs
// immediately afterward without needing any AST serialization bridge.
struct FsmState final {
    // All detected FSMs keyed by state varscope name. This is the only bridge
    // between the adjacent detect and lower phases, so the second phase never
    // needs to rediscover or serialize the extracted machine.
    DetectedFsmMap byVar;
};

// Normalize the supported reset-condition shapes into a compact description so
// the lowering phase can regenerate the same predicate after detection.
static FsmResetCondDesc describeResetCond(AstNodeExpr* condp) {
    FsmResetCondDesc desc;
    if (AstVarRef* const vrefp = VN_CAST(condp, VarRef)) {
        AstVarScope* const vscp = vrefp->varScopep();
        desc.varScopeName = vscp ? vscp->name() : "";
        desc.varName = vrefp->varp() ? vrefp->varp()->name() : "";
        return desc;
    }
    if (AstNot* const notp = VN_CAST(condp, Not)) {
        if (AstVarRef* const vrefp = VN_CAST(notp->lhsp(), VarRef)) {
            AstVarScope* const vscp = vrefp->varScopep();
            desc.varScopeName = vscp ? vscp->name() : "";
            desc.varName = vrefp->varp() ? vrefp->varp()->name() : "";
            desc.negated = true;
        }
    }
    return desc;
}

// Snapshot the original event control so the lowering phase can rebuild an
// active block with the same edge semantics.
static std::vector<FsmSenDesc> describeSenTree(AstSenTree* sentreep) {
    std::vector<FsmSenDesc> senses;
    for (AstSenItem* itemp = sentreep->sensesp(); itemp; itemp = VN_AS(itemp->nextp(), SenItem)) {
        AstNodeVarRef* const vrefp = itemp->varrefp();
        if (!vrefp) continue;
        FsmSenDesc desc;
        desc.edgeType = static_cast<uint8_t>(itemp->edgeType());
        AstVarScope* const vscp = vrefp->varScopep();
        desc.varScopeName = vscp->name();
        desc.varName = vrefp->varp()->name();
        senses.push_back(desc);
    }
    return senses;
}

// Align FSM graph debugging with the existing V3Graph dump flow so review and
// bring-up can inspect extracted state/transition structure using the same
// --dumpi-graph machinery as other graph-based passes.
static string dumpTagForGraph(const FsmGraph& graph, size_t index) {
    string tag = graph.stateVarInternalName().empty() ? graph.stateVarScopeName() : graph.stateVarInternalName();
    if (tag.empty()) tag = "fsm";
    for (char& ch : tag) {
        if (!std::isalnum(static_cast<unsigned char>(ch))) ch = '_';
    }
    return "fsm_" + cvtToStr(index) + "_" + tag;
}

// Rebuild a state-typed constant using the tracked state variable width/sign so
// emitted comparisons match the original state representation.
static AstConst* makeStateConst(FileLine* flp, AstVarScope* vscp, int value) {
    V3Number num{flp, vscp->width(), static_cast<uint32_t>(value)};
    num.isSigned(vscp->dtypep()->isSigned());
    return new AstConst{flp, num};
}

// Build guards incrementally without forcing callers to special-case the first
// predicate; this keeps the emitted state/arc conditions readable.
static AstNodeExpr* andExpr(FileLine* flp, AstNodeExpr* lhsp, AstNodeExpr* rhsp) {
    if (!lhsp) return rhsp;
    return new AstLogAnd{flp, lhsp, rhsp};
}

// Resolve saved names from the detected FSM graphs back onto the current AST
// before lowering them into concrete coverage declarations and increments.
class ScopeVarResolver final : public VNVisitor {
    // STATE - across all visitors
    std::unordered_map<string, AstScope*> m_scopeps;
    std::unordered_map<string, AstVarScope*> m_varScopeps;

    // METHODS
    void visit(AstScope* nodep) override {
        m_scopeps.emplace(nodep->name(), nodep);
        iterateChildren(nodep);
    }
    void visit(AstVarScope* nodep) override {
        m_varScopeps.emplace(nodep->name(), nodep);
        iterateChildren(nodep);
    }
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    explicit ScopeVarResolver(AstNetlist* rootp) { iterate(rootp); }

    AstScope* findScope(const string& name) const {
        const auto it = m_scopeps.find(name);
        return it == m_scopeps.end() ? nullptr : it->second;
    }
    AstVarScope* findVarScope(const string& name) const {
        const auto it = m_varScopeps.find(name);
        return it == m_varScopeps.end() ? nullptr : it->second;
    }
};

static AstNodeExpr* buildResetCond(FileLine* flp, AstVarScope* resetVscp,
                                   const FsmResetCondDesc& resetCond) {
    AstNodeExpr* condp = new AstVarRef{flp, resetVscp, VAccess::READ};
    if (resetCond.negated) condp = new AstNot{flp, condp};
    return condp;
}

// Rebuild the original event control from the saved sense description so the
// post-state coverage sampling runs on the same triggering edges as the FSM
// process being instrumented.
static AstSenTree* buildSenTree(
    FileLine* flp, const std::vector<std::pair<FsmSenDesc, AstVarScope*>>& senses) {
    AstSenTree* const sentreep = new AstSenTree{flp, nullptr};
    for (const auto& entry : senses) {
        const FsmSenDesc& sense = entry.first;
        AstVarScope* const vscp = entry.second;
        if (!vscp) continue;
        auto* const senItemp = new AstSenItem{
            flp, VEdgeType{static_cast<int>(sense.edgeType)},
            new AstVarRef{flp, vscp, VAccess::READ}};
        sentreep->addSensesp(senItemp);
    }
    return sentreep;
}

// Detection runs while the original clocked/case structure is still intact and
// populates graph-backed FSM models without mutating the tree mid-traversal.
class FsmDetectVisitor final : public VNVisitor {
    // STATE - for current visit position (use VL_RESTORER)
    FsmState& m_state;
    AstScope* m_scopep = nullptr;

    // METHODS
    // Enum-backed FSMs may be wrapped in refs/typedefs; normalize to the
    // underlying enum type before deciding whether a case is a candidate.
    static AstNodeDType* unwrapEnumCandidate(AstNodeDType* dtypep) {
        return dtypep ? dtypep->skipRefToEnump() : nullptr;
    }

    // Reset arcs are only modeled for simple signal or !signal forms so build
    // can reproduce them later without needing a general expression serializer.
    static bool isSimpleResetCond(AstNodeExpr* condp) {
        if (VN_IS(condp, VarRef)) return true;
        if (const AstNot* const notp = VN_CAST(condp, Not)) return VN_IS(notp->lhsp(), VarRef);
        return false;
    }

    // Accept either a bare case or a trivial begin-wrapped case so detection
    // tolerates common structural wrapping around the FSM body.
    static AstCase* caseFromStmt(AstNode* stmtp) {
        if (!stmtp) return nullptr;
        if (AstCase* const casep = VN_CAST(stmtp, Case)) return casep;
        if (AstBegin* const beginp = VN_CAST(stmtp, Begin)) {
            if (beginp->stmtsp() && !beginp->stmtsp()->nextp()) return VN_CAST(beginp->stmtsp(), Case);
        }
        return nullptr;
    }

    // Many helpers operate on a single logical statement; this strips a
    // one-level begin/end wrapper so those checks stay simple.
    static AstNode* unwrapSingleBlock(AstNode* stmtp) {
        if (AstBegin* const beginp = VN_CAST(stmtp, Begin)) return beginp->stmtsp();
        return stmtp;
    }

    // Ignore existing coverage increments so FSM detection sees the user logic
    // rather than other instrumentation already attached to the block.
    static bool isIgnorableStmt(AstNode* nodep) { return VN_IS(nodep, CoverInc); }

    // Conservative extractor: only treat a branch as simple when exactly one
    // non-coverage statement remains after unwrapping.
    static AstNode* singleMeaningfulStmt(AstNode* stmtp) {
        AstNode* resultp = nullptr;
        for (AstNode* nodep = unwrapSingleBlock(stmtp); nodep; nodep = nodep->nextp()) {
            if (isIgnorableStmt(nodep)) continue;
            if (resultp) return nullptr;
            resultp = nodep;
        }
        return resultp;
    }

    // Recognize the direct "state <= X" form that gives us an unambiguous arc
    // target without needing deeper control-flow reasoning.
    static AstNodeAssign* directStateAssign(AstNode* stmtp, AstVarScope* stateVscp) {
        AstNode* const nodep = singleMeaningfulStmt(stmtp);
        if (!nodep) return nullptr;
        AstNodeAssign* const assp = VN_CAST(nodep, NodeAssign);
        if (!assp) return nullptr;
        AstVarRef* const vrefp = VN_CAST(assp->lhsp(), VarRef);
        if (!vrefp || vrefp->varScopep() != stateVscp) return nullptr;
        return assp;
    }

    // Nested conditionals are currently outside the conservative extractor, so
    // this helps distinguish the supported simple if/else arc shape.
    static bool branchHasNestedIf(AstNode* stmtp) {
        for (AstNode* nodep = unwrapSingleBlock(stmtp); nodep; nodep = nodep->nextp()) {
            if (isIgnorableStmt(nodep)) continue;
            if (VN_IS(nodep, If)) return true;
        }
        return false;
    }

    // Prefer enum labels in reports; fall back to synthetic labels for forced
    // non-enum FSMs so coverage points remain human-readable.
    static string labelForValue(const std::unordered_map<int, string>& labels, int value) {
        const auto it = labels.find(value);
        return it == labels.end() ? ("S" + cvtToStr(value)) : it->second;
    }

    // The extractor only models constant-valued state transitions, so normalize
    // enum item refs and raw constants to the same integer form here.
    static bool exprConstValue(AstNodeExpr* exprp, int& value) {
        if (!exprp) return false;
        if (AstConst* const constp = VN_CAST(exprp, Const)) {
            value = constp->toSInt();
            return true;
        }
        if (AstEnumItemRef* const itemRefp = VN_CAST(exprp, EnumItemRef)) {
            AstConst* const constp = itemRefp->itemp() ? VN_CAST(itemRefp->itemp()->valuep(), Const)
                                                       : nullptr;
            if (!constp) return false;
            value = constp->toSInt();
            return true;
        }
        return false;
    }

    // Centralize arc creation so every supported transition shape becomes the
    // same graph edge form before lowering and debug dumping.
    static void addArc(FsmGraph& graph, int fromValue, int toValue, bool isReset, bool isCond,
                       bool isDefault, FileLine* flp) {
        graph.addArc(fromValue, toValue, isReset, isCond, isDefault, flp);
    }

    // Extract supported case-item transitions in one place so the conservative
    // policy for direct, ternary, and simple if/else forms stays consistent.
    static bool emitCaseItemArcs(FsmGraph& graph, AstCaseItem* itemp, AstVarScope* stateVscp,
                                 const std::unordered_map<int, string>& labels, bool inclCond) {
        std::vector<std::pair<string, int>> froms;
        if (itemp->isDefault()) {
            if (!inclCond) return false;
            froms.emplace_back("default", 0);
        } else {
            for (AstNodeExpr* condp = itemp->condsp(); condp;
                 condp = VN_CAST(condp->nextp(), NodeExpr)) {
                int value = 0;
                if (!exprConstValue(condp, value)) continue;
                froms.emplace_back(labelForValue(labels, value), value);
            }
            if (froms.empty()) return false;
        }

        if (AstNodeAssign* const assp = directStateAssign(itemp->stmtsp(), stateVscp)) {
            int toValue = 0;
            if (exprConstValue(assp->rhsp(), toValue)) {
                for (const auto& from : froms) {
                    addArc(graph, from.second, toValue, false, false, itemp->isDefault(),
                           assp->fileline());
                }
                return true;
            }

            if (AstCond* const condp = VN_CAST(assp->rhsp(), Cond)) {
                int thenValue = 0;
                int elseValue = 0;
                const bool simpleCond = exprConstValue(condp->thenp(), thenValue)
                                        && exprConstValue(condp->elsep(), elseValue);
                if (simpleCond || inclCond) {
                    for (const int branchValue : {thenValue, elseValue}) {
                        for (const auto& from : froms) {
                            addArc(graph, from.second, branchValue, false, true,
                                   itemp->isDefault(), assp->fileline());
                        }
                    }
                    return true;
                }
            }
        }

        AstNode* const itemStmtp = singleMeaningfulStmt(itemp->stmtsp());
        if (AstIf* const ifp = VN_CAST(itemStmtp, If)) {
            const bool tier2 = !branchHasNestedIf(ifp->thensp()) && !branchHasNestedIf(ifp->elsesp())
                               && directStateAssign(ifp->thensp(), stateVscp)
                               && directStateAssign(ifp->elsesp(), stateVscp);
            if (tier2 || inclCond) {
                for (AstNode* branchp : {ifp->thensp(), ifp->elsesp()}) {
                    if (AstNodeAssign* const assp = directStateAssign(branchp, stateVscp)) {
                        int toValue = 0;
                        if (exprConstValue(assp->rhsp(), toValue)) {
                            for (const auto& from : froms) {
                                addArc(graph, from.second, toValue, false, true,
                                       itemp->isDefault(), assp->fileline());
                            }
                        }
                    }
                }
                return true;
            }
        }
        return false;
    }

    // Reset transitions are described separately because they live in the reset
    // branch outside the steady-state case statement.
    static void addResetArcs(FsmGraph& graph, AstNode* stmtsp, AstVarScope* stateVscp,
                             const std::unordered_map<int, string>& labels) {
        for (AstNode* nodep = unwrapSingleBlock(stmtsp); nodep; nodep = nodep->nextp()) {
            if (AstNodeAssign* const assp = VN_CAST(nodep, NodeAssign)) {
                AstVarRef* const vrefp = VN_CAST(assp->lhsp(), VarRef);
                int toValue = 0;
                if (vrefp && vrefp->varScopep() == stateVscp && exprConstValue(assp->rhsp(), toValue)) {
                    addArc(graph, 0, toValue, true, false, false, assp->fileline());
                }
            }
        }
    }

    // Turn one candidate case statement into the graph representation that the
    // later lowering phase will consume directly, while reviewers can still
    // inspect the extracted machine via DOT dumps.
    void processCase(AstCase* casep, AstNodeExpr* resetCondp, AstAlways* alwaysp) {
        AstVarRef* const selp = VN_CAST(casep->exprp(), VarRef);
        if (!selp) return;
        AstVarScope* const stateVscp = selp->varScopep();
        if (!stateVscp) return;
        AstVar* const stateVarp = selp->varp();
        AstEnumDType* enump = VN_CAST(unwrapEnumCandidate(stateVscp->dtypep()), EnumDType);
        if (!enump) enump = VN_CAST(unwrapEnumCandidate(stateVarp->dtypep()), EnumDType);
        const bool forced = stateVarp->attrFsmState();
        if (!enump && !forced) return;

        std::vector<std::pair<string, int>> states;
        std::unordered_map<int, string> labels;
        if (enump) {
            for (AstEnumItem* itemp = enump->itemsp(); itemp; itemp = VN_AS(itemp->nextp(), EnumItem)) {
                int value = 0;
                if (!exprConstValue(itemp->valuep(), value)) continue;
                states.emplace_back(itemp->name(), value);
                labels.emplace(value, itemp->name());
            }
            if (states.size() < 2) return;
        } else {
            const int width = stateVarp->width();
            if (width < 1 || width >= 31) return;
            const unsigned stateCount = 1U << width;
            for (unsigned value = 0; value < stateCount; ++value) {
                const string label = "S" + cvtToStr(value);
                states.emplace_back(label, static_cast<int>(value));
                labels.emplace(static_cast<int>(value), label);
            }
        }

        DetectedFsm& entry = m_state.byVar[stateVscp->name()];
        if (!entry.graphp) {
            entry.graphp.reset(new FsmGraph{});
            entry.modp = m_scopep->modp();
            entry.alwaysp = alwaysp;
            entry.graphp->scopeName(m_scopep->name());
            entry.graphp->stateVarName(stateVscp->prettyName());
            entry.graphp->stateVarInternalName(stateVarp->name());
            entry.graphp->stateVarScopeName(stateVscp->name());
            entry.graphp->senses() = describeSenTree(alwaysp->sentreep());
            entry.graphp->resetCond() = describeResetCond(resetCondp);
            entry.graphp->hasResetCond(!entry.graphp->resetCond().varScopeName.empty());
            entry.graphp->resetInclude(stateVarp->attrFsmResetArc());
            entry.graphp->inclCond(stateVarp->attrFsmArcInclCond());
            entry.graphp->fileline(casep->fileline());
            for (const auto& state : states) {
                entry.graphp->addStateVertex(state.first, state.second);
            }
        }
        for (AstCaseItem* itemp = casep->itemsp(); itemp; itemp = VN_AS(itemp->nextp(), CaseItem)) {
            emitCaseItemArcs(*entry.graphp, itemp, stateVscp, labels, entry.graphp->inclCond());
        }
    }

    // Find the first supported FSM candidate in a clocked always block, warn on
    // additional candidates, and attach reset arcs when present.
    void processAlways(AstAlways* alwaysp) {
        if (!alwaysp->sentreep() || !alwaysp->sentreep()->hasClocked()) return;
        std::vector<std::pair<AstCase*, AstNodeExpr*>> candidates;
        AstNode* stmtsp = unwrapSingleBlock(alwaysp->stmtsp());
        AstIf* const firstIfp = VN_CAST(stmtsp, If);
        if (firstIfp && firstIfp == stmtsp) {
            if (AstCase* const casep = caseFromStmt(firstIfp->elsesp())) {
                candidates.emplace_back(casep, isSimpleResetCond(firstIfp->condp()) ? firstIfp->condp()
                                                                                     : nullptr);
            }
        }
        for (AstNode* nodep = stmtsp; nodep; nodep = nodep->nextp()) {
            if (AstCase* const casep = VN_CAST(nodep, Case)) candidates.emplace_back(casep, nullptr);
        }
        if (candidates.empty()) return;

        AstVarScope* firstVscp = nullptr;
        for (const auto& cand : candidates) {
            AstVarRef* const selp = VN_CAST(cand.first->exprp(), VarRef);
            AstVarScope* const vscp = selp ? selp->varScopep() : nullptr;
            if (!vscp) continue;
            if (!firstVscp) {
                firstVscp = vscp;
                processCase(cand.first, cand.second, alwaysp);
            } else if (vscp != firstVscp) {
                cand.first->v3warn(FSMMULTI,
                                   "FSM coverage: multiple enum-typed case statements found in "
                                   "the same always block. Only the first candidate will be "
                                   "instrumented.");
            } else {
                processCase(cand.first, cand.second, alwaysp);
            }
        }

        if (firstIfp && firstVscp) {
            const auto it = m_state.byVar.find(firstVscp->name());
            if (it != m_state.byVar.end()) {
                FsmGraph* const graphp = it->second.graphp.get();
                if (graphp->hasResetCond()) {
                    std::unordered_map<int, string> labels;
                    for (const V3GraphVertex& vtx : graphp->vertices()) {
                        const FsmVertex* const vertexp = vtx.as<FsmVertex>();
                        if (!vertexp->isState()) continue;
                        labels.emplace(vertexp->value(), vertexp->label());
                    }
                    addResetArcs(*graphp, firstIfp->thensp(), firstVscp, labels);
                }
            }
        }
    }

    // Track the current scope so each detected FSM records the module/scope
    // where instrumentation must later be inserted.
    void visit(AstScope* nodep) override {
        VL_RESTORER(m_scopep);
        m_scopep = nodep;
        iterateChildren(nodep);
    }

    // FSM extraction only cares about clocked always processes.
    void visit(AstAlways* nodep) override { processAlways(nodep); }

    // Continue the walk through the rest of the design hierarchy.
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    // Collect all FSM graphs into the shared local state before the lowering
    // phase starts mutating the AST with coverage machinery.
    FsmDetectVisitor(FsmState& state, AstNetlist* rootp)
        : m_state{state} {
        iterate(rootp);
    }
};

// Lower the completed FSM graphs into the concrete coverage declarations,
// previous-state tracking, and pre/post-triggered instrumentation that the
// runtime uses to record state and transition coverage.
class FsmLowerVisitor final {
    // STATE - across all visitors
    ScopeVarResolver m_resolver;
    const FsmState& m_state;

    // METHODS
    // Lower one fully detected FSM graph into the concrete coverage machinery
    // used by generated models: declarations, previous-state tracking, and the
    // pre/post-triggered increment logic for states and arcs.
    void buildOne(const FsmGraph& graph) {
        const auto it = m_state.byVar.find(graph.stateVarScopeName());
        AstAlways* const alwaysp = (it == m_state.byVar.end()) ? nullptr : it->second.alwaysp;
        AstScope* const scopep = m_resolver.findScope(graph.scopeName());
        AstVarScope* const stateVscp = m_resolver.findVarScope(graph.stateVarScopeName());
        if (!scopep || !stateVscp || !alwaysp) return;
        FileLine* const flp = graph.fileline() ? graph.fileline() : stateVscp->fileline();
        AstNodeModule* const modp = scopep->modp();
        AstNodeDType* const prevDTypep
            = scopep->findLogicDType(stateVscp->width(), stateVscp->width(),
                                     stateVscp->dtypep()->numeric());
        AstVarScope* const prevVscp
            = scopep->createTemp("__Vfsmcov_prev__" + stateVscp->varp()->shortName(), prevDTypep);
        // The saved previous-state temp crosses the scheduler's pre/post split
        // in the same way as Verilator's built-in NBA shadow variables, so keep
        // both vars marked as post-life participants for stable MT ordering.
        stateVscp->optimizeLifePost(true);
        prevVscp->optimizeLifePost(true);

        AstActive* const initActivep
            = new AstActive{flp, "fsm-coverage-init",
                            new AstSenTree{flp, new AstSenItem{flp, AstSenItem::Initial{}}}};
        initActivep->senTreeStorep(initActivep->sentreep());
        // Seed the previous-state temp during initialization so the first
        // clock edge compares against a defined state value.
        initActivep->addStmtsp(new AstInitialStatic{
            flp, new AstAssign{flp, new AstVarRef{flp, prevVscp, VAccess::WRITE},
                               new AstVarRef{flp, stateVscp, VAccess::READ}}});
        scopep->addBlocksp(initActivep);

        AstAlwaysPost* const covPostp = new AstAlwaysPost{flp};
        // Save the previous state as plain sequential logic at the front of
        // the original always_ff body, then evaluate coverage in post logic
        // after the delayed state update commits. This avoids a scheduler race
        // between a separate AstAlwaysPre task and the real state commit.
        AstNode* const bodysp = alwaysp->stmtsp() ? alwaysp->stmtsp()->unlinkFrBackWithNext() : nullptr;
        alwaysp->addStmtsp(new AstAssign{flp, new AstVarRef{flp, prevVscp, VAccess::WRITE},
                                         new AstVarRef{flp, stateVscp, VAccess::READ}});
        if (bodysp) alwaysp->addStmtsp(bodysp);

        std::vector<std::pair<FsmSenDesc, AstVarScope*>> senses;
        senses.reserve(graph.senses().size());
        for (const FsmSenDesc& sense : graph.senses()) {
            AstVarScope* const senseVscp = m_resolver.findVarScope(sense.varScopeName);
            senses.emplace_back(sense, senseVscp);
        }

        for (const V3GraphVertex& vtx : graph.vertices()) {
            const FsmVertex* const vertexp = vtx.as<FsmVertex>();
            if (!vertexp->isState()) continue;
            const FsmStateVertex* const statep = vtx.as<FsmStateVertex>();
            // State coverage fires when the FSM enters a state from any other
            // value, so repeated self-holds do not count as new entries.
            AstCoverOtherDecl* const declp = new AstCoverOtherDecl{
                flp, "v_fsm_state/" + modp->prettyName(),
                graph.stateVarName() + "::" + statep->label(), "", 0};
            declp->hier(scopep->prettyName());
            modp->addStmtsp(declp);
            AstNodeExpr* guardp
                = andExpr(flp,
                          new AstNeq{flp, new AstVarRef{flp, prevVscp, VAccess::READ},
                                     makeStateConst(flp, prevVscp, statep->value())},
                          new AstEq{flp, new AstVarRef{flp, stateVscp, VAccess::READ},
                                    makeStateConst(flp, stateVscp, statep->value())});
            covPostp->addStmtsp(new AstIf{flp, guardp, new AstCoverInc{flp, declp}});
        }

        for (const V3GraphVertex& vtx : graph.vertices()) {
            const FsmVertex* const fromVertexp = vtx.as<FsmVertex>();
            for (const V3GraphEdge& edge : fromVertexp->outEdges()) {
                const FsmArcEdge* const arcp = edge.as<FsmArcEdge>();
                const FsmStateVertex* const toStatep = arcp->top()->as<FsmStateVertex>();
                // Arc coverage mirrors the extracted graph exactly, including
                // reset and synthetic-default sources, so reports match the
                // reviewer-visible graph dump and the user-visible annotation.
                const string resetTag
                    = arcp->isReset() ? (graph.resetInclude() ? "[reset_include]" : "[reset]") : "";
                AstCoverOtherDecl* const declp = new AstCoverOtherDecl{
                    flp, "v_fsm_arc/" + modp->prettyName(),
                    graph.stateVarName() + "::" + fromVertexp->label() + "->" + toStatep->label()
                        + resetTag,
                    "",
                    0};
                declp->hier(scopep->prettyName());
                modp->addStmtsp(declp);
                AstNodeExpr* guardp = nullptr;
                if (fromVertexp->isResetAny()) {
                    // Reset arcs are modeled as pseudo-source edges in the
                    // graph, then reconstructed here into the original simple
                    // reset predicate combined with the destination state.
                    if (!graph.hasResetCond()) continue;
                    AstVarScope* const resetVscp
                        = m_resolver.findVarScope(graph.resetCond().varScopeName);
                    if (!resetVscp) continue;
                    guardp = buildResetCond(flp, resetVscp, graph.resetCond());
                    guardp = andExpr(flp, guardp,
                                     new AstEq{flp, new AstVarRef{flp, stateVscp, VAccess::READ},
                                               makeStateConst(flp, stateVscp, toStatep->value())});
                } else if (fromVertexp->isDefaultAny()) {
                    // Synthetic default arcs mean "none of the explicit
                    // source states matched", so rebuild that as a conjunction
                    // of previous-state != known-state tests.
                    for (const V3GraphVertex& stateVtx : graph.vertices()) {
                        const FsmVertex* const stateVertexp = stateVtx.as<FsmVertex>();
                        if (!stateVertexp->isState()) continue;
                        guardp = andExpr(
                            flp, guardp,
                            new AstNeq{flp, new AstVarRef{flp, prevVscp, VAccess::READ},
                                       makeStateConst(flp, prevVscp, stateVertexp->value())});
                    }
                    guardp = andExpr(flp, guardp,
                                     new AstEq{flp, new AstVarRef{flp, stateVscp, VAccess::READ},
                                               makeStateConst(flp, stateVscp, toStatep->value())});
                } else {
                    guardp = andExpr(
                        flp,
                        new AstEq{flp, new AstVarRef{flp, prevVscp, VAccess::READ},
                                  makeStateConst(flp, prevVscp, fromVertexp->value())},
                        new AstEq{flp, new AstVarRef{flp, stateVscp, VAccess::READ},
                                  makeStateConst(flp, stateVscp, toStatep->value())});
                }
                covPostp->addStmtsp(new AstIf{flp, guardp, new AstCoverInc{flp, declp}});
            }
        }

        AstSenTree* const sentreep = buildSenTree(flp, senses);
        AstActive* const activep = new AstActive{flp, "fsm-coverage", sentreep};
        activep->senTreeStorep(sentreep);
        scopep->addBlocksp(activep);
        activep->addStmtsp(covPostp);
    }

public:
    // CONSTRUCTORS
    // Resolve the current scoped AST once, then lower every detected FSM graph
    // from the shared local state into concrete coverage instrumentation.
    FsmLowerVisitor(const FsmState& state, AstNetlist* rootp)
        : m_resolver{rootp}
        , m_state{state} {
        for (const auto& it : m_state.byVar) buildOne(*it.second.graphp);
    }
};

}  // namespace

void V3FsmDetect::detect(AstNetlist* rootp) {
    UINFO(2, __FUNCTION__ << ":");
    FsmState state;
    // Phase 1: recover each supported FSM into a complete graph while the
    // original clocked/case structure is still easy to recognize.
    FsmDetectVisitor detect{state, rootp};
    if (dumpGraphLevel() >= 6) {
        size_t index = 0;
        for (const auto& it : state.byVar) {
            it.second.graphp->dumpDotFilePrefixed(dumpTagForGraph(*it.second.graphp, index++));
        }
    }
    // Phase 2: lower the completed in-memory graph state immediately, without
    // crossing into another pass owner or serializing through AST placeholders.
    { FsmLowerVisitor lower{state, rootp}; }
    V3Global::dumpCheckGlobalTree("fsm-detect", 0, dumpTreeEitherLevel() >= 3);
}
