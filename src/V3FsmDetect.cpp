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
#include "V3Graph.h"

#include <cctype>
#include <map>
#include <memory>
#include <unordered_map>

VL_DEFINE_DEBUG_FUNCTIONS;

namespace {

// Captures one sensitivity-list entry so the lowering phase can later rebuild
// an active block with the same triggering event control.
struct FsmSenDesc final {
    // Encoded edge kind copied from AstSenItem::edgeType() so lowering can
    // rebuild the same trigger semantics on the synthesized coverage block.
    VEdgeType::en edgeType = static_cast<VEdgeType::en>(0);
    // Triggering signal in the saved scoped AST.
    AstVarScope* varScopep = nullptr;
};

// Captures the simple reset predicate shape that survives to this pass after
// earlier normalization so reset arcs can be reconstructed during lowering.
struct FsmResetCondDesc final {
    // Reset signal used by the FSM in the saved scoped AST.
    AstVarScope* varScopep = nullptr;
};

class FsmGraph;

class FsmVertex VL_NOT_FINAL : public V3GraphVertex {
    VL_RTTI_IMPL(FsmVertex, V3GraphVertex)

public:
    enum class Kind : uint8_t { STATE, RESET_ANY, DEFAULT_ANY };

private:
    Kind m_kind;     // State vs synthetic ANY/default vertex role.
    string m_label;  // User-facing state or pseudo-state label.
    int m_value = 0;  // Encoded state value for real state vertices.

protected:
    FsmVertex(V3Graph* graphp, Kind kind, string label, int value) VL_MT_DISABLED
        : V3GraphVertex{graphp}
        , m_kind{kind}
        , m_label{label}
        , m_value{value} {}
    ~FsmVertex() override = default;

public:
    Kind kind() const { return m_kind; }
    bool isState() const { return m_kind == Kind::STATE; }
    bool isResetAny() const { return m_kind == Kind::RESET_ANY; }
    bool isDefaultAny() const { return m_kind == Kind::DEFAULT_ANY; }
    const string& label() const { return m_label; }
    int value() const { return m_value; }

    string name() const override VL_MT_SAFE { return m_label + "=" + cvtToStr(m_value); }
};

class FsmStateVertex final : public FsmVertex {
    VL_RTTI_IMPL(FsmStateVertex, FsmVertex)

public:
    FsmStateVertex(V3Graph* graphp, string label, int value) VL_MT_DISABLED
        : FsmVertex{graphp, Kind::STATE, label, value} {}
    ~FsmStateVertex() override = default;

    string dotColor() const override { return "lightblue"; }
    string dotShape() const override { return "ellipse"; }
};

class FsmPseudoVertex final : public FsmVertex {
    VL_RTTI_IMPL(FsmPseudoVertex, FsmVertex)

public:
    FsmPseudoVertex(V3Graph* graphp, Kind kind, string label) VL_MT_DISABLED
        : FsmVertex{graphp, kind, label, 0} {}
    ~FsmPseudoVertex() override = default;

    string name() const override VL_MT_SAFE { return label(); }
    string dotColor() const override { return isResetAny() ? "darkgreen" : "orange"; }
    string dotShape() const override { return "diamond"; }
};

class FsmArcEdge final : public V3GraphEdge {
    VL_RTTI_IMPL(FsmArcEdge, V3GraphEdge)
    bool m_isReset = false;  // Arc originates from the synthetic reset source.
    bool m_isCond = false;   // Arc came from a conditional next-state split.
    bool m_isDefault = false;  // Arc represents a case default source.
    FileLine* m_flp = nullptr;  // Source location for emitted coverage metadata.

public:
    FsmArcEdge(V3Graph* graphp, FsmVertex* fromp, FsmStateVertex* top, bool isReset,
               bool isCond, bool isDefault, FileLine* flp) VL_MT_DISABLED
        : V3GraphEdge{graphp, fromp, top, 1}
        , m_isReset{isReset}
        , m_isCond{isCond}
        , m_isDefault{isDefault}
        , m_flp{flp} {}
    ~FsmArcEdge() override = default;

    bool isReset() const { return m_isReset; }
    bool isCond() const { return m_isCond; }
    bool isDefault() const { return m_isDefault; }
    FileLine* fileline() const { return m_flp; }

    string dotLabel() const override {
        if (m_isReset) return "reset";
        if (m_isDefault) return "default";
        if (m_isCond) return "cond";
        return "";
    }
    string dotColor() const override {
        if (m_isReset) return "darkgreen";
        if (m_isDefault) return "orange";
        if (m_isCond) return "blue";
        return "black";
    }
};

// One graph per detected FSM. Graph-level metadata captures the non-graph
// context needed to lower states/arcs back into the AST after detection.
class FsmGraph final : public V3Graph {
    AstScope* m_scopep = nullptr;  // Owning scoped block for the detected FSM.
    AstAlways* m_alwaysp = nullptr;  // Original always block being instrumented.
    string m_stateVarName;  // Pretty state variable name for user-visible output.
    string m_stateVarInternalName;  // Internal state symbol name for dump tags.
    AstVarScope* m_stateVarScopep = nullptr;  // Scoped state variable being tracked.
    std::vector<FsmSenDesc> m_senses;  // Saved event controls for recreated active blocks.
    FsmResetCondDesc m_resetCond;  // Saved reset predicate shape, if one exists.
    bool m_hasResetCond = false;   // Whether the detected FSM had a reset branch.
    bool m_resetInclude = false;  // Whether reset arcs count toward coverage totals.
    bool m_inclCond = false;      // Whether conditional arcs should be kept explicitly.
    FileLine* m_flp = nullptr;    // Representative source location for declarations/arcs.
    std::unordered_map<int, FsmStateVertex*> m_stateVertices;  // Value to state-vertex map.
    FsmPseudoVertex* m_resetVertexp = nullptr;  // Synthetic ANY source for reset arcs.
    FsmPseudoVertex* m_defaultVertexp = nullptr;  // Synthetic default source for case defaults.

public:
    FsmGraph() VL_MT_DISABLED
        : m_resetVertexp{new FsmPseudoVertex{this, FsmVertex::Kind::RESET_ANY, "ANY"}}
        , m_defaultVertexp{new FsmPseudoVertex{this, FsmVertex::Kind::DEFAULT_ANY, "default"}} {}

    AstScope* scopep() const { return m_scopep; }
    void scopep(AstScope* scopep) { m_scopep = scopep; }
    AstAlways* alwaysp() const { return m_alwaysp; }
    void alwaysp(AstAlways* alwaysp) { m_alwaysp = alwaysp; }
    const string& stateVarName() const { return m_stateVarName; }
    void stateVarName(const string& name) { m_stateVarName = name; }
    const string& stateVarInternalName() const { return m_stateVarInternalName; }
    void stateVarInternalName(const string& name) { m_stateVarInternalName = name; }
    AstVarScope* stateVarScopep() const { return m_stateVarScopep; }
    void stateVarScopep(AstVarScope* vscp) { m_stateVarScopep = vscp; }
    const std::vector<FsmSenDesc>& senses() const { return m_senses; }
    std::vector<FsmSenDesc>& senses() { return m_senses; }
    const FsmResetCondDesc& resetCond() const { return m_resetCond; }
    FsmResetCondDesc& resetCond() { return m_resetCond; }
    bool hasResetCond() const { return m_hasResetCond; }
    void hasResetCond(bool flag) { m_hasResetCond = flag; }
    bool resetInclude() const { return m_resetInclude; }
    void resetInclude(bool flag) { m_resetInclude = flag; }
    bool inclCond() const { return m_inclCond; }
    void inclCond(bool flag) { m_inclCond = flag; }
    FileLine* fileline() const { return m_flp; }
    void fileline(FileLine* flp) { m_flp = flp; }

    FsmStateVertex* addStateVertex(string label, int value) VL_MT_DISABLED {
        FsmStateVertex* const vertexp = new FsmStateVertex{this, label, value};
        m_stateVertices.emplace(value, vertexp);
        return vertexp;
    }
    FsmPseudoVertex* resetAnyVertex() VL_MT_DISABLED { return m_resetVertexp; }
    FsmPseudoVertex* defaultAnyVertex() VL_MT_DISABLED { return m_defaultVertexp; }
    FsmArcEdge* addArc(int fromValue, int toValue, bool isReset, bool isCond, bool isDefault,
                       FileLine* flp) VL_MT_DISABLED {
        FsmStateVertex* const top = m_stateVertices.at(toValue);
        FsmVertex* fromp = nullptr;
        if (isReset) {
            fromp = resetAnyVertex();
        } else if (isDefault) {
            fromp = defaultAnyVertex();
        } else {
            fromp = m_stateVertices.at(fromValue);
        }
        return new FsmArcEdge{this, fromp, top, isReset, isCond, isDefault, flp};
    }

    string name() const VL_MT_SAFE {
        return "FSM "
               + (m_stateVarName.empty() ? (m_stateVarScopep ? m_stateVarScopep->name() : "")
                                         : m_stateVarName);
    }
    string dumpTag(size_t index) const {
        string tag = stateVarInternalName();
        for (char& ch : tag) {
            if (!std::isalnum(static_cast<unsigned char>(ch))) ch = '_';
        }
        return "fsm_" + cvtToStr(index) + "_" + tag;
    }
};

struct DetectedFsm final {
    std::unique_ptr<FsmGraph> graphp;  // Extracted graph for one detected FSM candidate.
};
using DetectedFsmMap = std::map<string, DetectedFsm>;

// Local shared state between the two adjacent FSM coverage phases. Detection
// fills this with recovered FSM graphs; lowering consumes the completed graphs
// immediately afterward without needing any AST serialization bridge.
class FsmState final {
    // All detected FSMs keyed by state varscope name. This is the only bridge
    // between the adjacent detect and lower phases, so the second phase never
    // needs to rediscover or serialize the extracted machine.
    DetectedFsmMap m_fsms;

public:
    DetectedFsmMap& fsms() { return m_fsms; }
    const DetectedFsmMap& fsms() const { return m_fsms; }
};

// Detection runs while the original clocked/case structure is still intact and
// populates graph-backed FSM models without mutating the tree mid-traversal.
// This pass is intentionally conservative: for this PR we only lock down the
// small set of transition/selector forms that are already stable in the
// normalized AST we see here. The remaining reject branches are therefore
// mostly future-feature boundaries, not accidental dead code.
class FsmDetectVisitor final : public VNVisitor {
    // STATE - for current visit position (use VL_RESTORER)
    FsmState& m_state;
    AstScope* m_scopep = nullptr;

    // METHODS
    // Enum-backed FSMs may be wrapped in refs/typedefs; normalize to the
    // underlying enum type before deciding whether a case is a candidate.
    static AstNodeDType* unwrapEnumCandidate(AstNodeDType* dtypep) {
        return dtypep->skipRefToEnump();
    }

    // Reset arcs are only modeled for the simple signal form that survives to
    // this pass after earlier normalization.
    static bool isSimpleResetCond(AstNodeExpr* condp) {
        return VN_IS(condp, VarRef);
    }

    // Normalize the reset condition into a compact description so the lowering
    // phase can regenerate the same predicate after detection. By the time
    // this pass runs, active-low source forms such as "!rst_n" have already
    // been canonicalized to a positive-condition if/else shape, so only a
    // plain VarRef survives here.
    static FsmResetCondDesc describeResetCond(AstNodeExpr* condp) {
        FsmResetCondDesc desc;
        if (AstVarRef* const vrefp = VN_CAST(condp, VarRef)) {
            desc.varScopep = vrefp->varScopep();
        }
        return desc;
    }

    // Snapshot the original event control so the lowering phase can rebuild an
    // active block with the same edge semantics.
    static std::vector<FsmSenDesc> describeSenTree(AstSenTree* sentreep) {
        std::vector<FsmSenDesc> senses;
        for (AstSenItem* itemp = sentreep->sensesp(); itemp;
             itemp = VN_AS(itemp->nextp(), SenItem)) {
            AstNodeVarRef* const vrefp = itemp->varrefp();
            if (!vrefp) continue;
            FsmSenDesc desc;
            desc.edgeType = itemp->edgeType().m_e;
            desc.varScopep = vrefp->varScopep();
            senses.push_back(desc);
        }
        return senses;
    }

    // Ignore existing coverage increments so FSM detection sees the user logic
    // rather than other instrumentation already attached to the block.
    static bool isIgnorableStmt(AstNode* nodep) { return VN_IS(nodep, CoverInc); }

    // Conservative extractor: only treat a branch as simple when exactly one
    // non-coverage statement remains after unwrapping. Richer multi-statement
    // or control-flow forms are intentionally left for follow-on FSM-detection
    // work instead of being partially inferred here.
    static AstNode* singleMeaningfulStmt(AstNode* stmtp) {
        AstNode* resultp = nullptr;
        for (AstNode* nodep = stmtp; nodep; nodep = nodep->nextp()) {
            if (isIgnorableStmt(nodep)) continue;
            if (resultp) return nullptr;
            resultp = nodep;
        }
        return resultp;
    }

    // Recognize the direct "state <= X" form that gives us an unambiguous arc
    // target without needing deeper control-flow reasoning. Branches that fall
    // out here represent currently unsupported next-state shapes rather than
    // bugs in the implemented subset.
    static AstNodeAssign* directStateAssign(AstNode* stmtp, AstVarScope* stateVscp) {
        AstNode* const nodep = singleMeaningfulStmt(stmtp);
        if (!nodep) return nullptr;
        AstNodeAssign* const assp = VN_CAST(nodep, NodeAssign);
        if (!assp) return nullptr;
        AstVarRef* const vrefp = VN_CAST(assp->lhsp(), VarRef);
        if (!vrefp || vrefp->varScopep() != stateVscp) return nullptr;
        return assp;
    }

    // Prefer enum labels in reports; fall back to synthetic labels for forced
    // non-enum FSMs so coverage points remain human-readable.
    static string labelForValue(const std::unordered_map<int, string>& labels, int value) {
        const std::unordered_map<int, string>::const_iterator it = labels.find(value);
        return it == labels.end() ? ("S" + cvtToStr(value)) : it->second;
    }

    // The extractor only models constant-valued state transitions, and by the
    // time detect runs those values have already been constant-folded.
    static bool exprConstValue(AstNodeExpr* exprp, int& value) {
        if (AstConst* const constp = VN_CAST(exprp, Const)) {
            value = constp->toSInt();
            return true;
        }
        return false;
    }

    // Enum-backed FSMs should only transition to values that were interned as
    // known states. If a constant transition targets some other encoding, warn
    // and skip FSM instrumentation for that edge rather than silently dropping
    // it or turning optional coverage into a hard compile failure.
    static bool validateKnownStateValue(AstNode* nodep,
                                        const std::unordered_map<int, string>& labels, int value) {
        if (labels.find(value) != labels.end()) return true;
        nodep->v3warn(COVERIGN,
                      "Ignoring unsupported: FSM coverage on enum state transitions "
                      "that assign a constant not present in the declared enum");
        return false;
    }

    // Extract supported case-item transitions in one place so the conservative
    // policy for direct and ternary forms stays consistent. The false exits in
    // this helper are deliberate subset boundaries: they document shapes we do
    // not yet model in this PR and that future FSM-detection work may widen.
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
                if (!validateKnownStateValue(assp, labels, toValue)) return true;
                for (const std::pair<string, int>& from : froms) {
                    graph.addArc(from.second, toValue, false, false, itemp->isDefault(),
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
                    if (!validateKnownStateValue(condp->thenp(), labels, thenValue)) return true;
                    if (!validateKnownStateValue(condp->elsep(), labels, elseValue)) return true;
                    for (const int branchValue : {thenValue, elseValue}) {
                        for (const std::pair<string, int>& from : froms) {
                            graph.addArc(from.second, branchValue, false, true,
                                         itemp->isDefault(), assp->fileline());
                        }
                    }
                    return true;
                }
            }
        }

        return false;
    }

    // Reset transitions are described separately because they live in the reset
    // branch outside the steady-state case statement.
    static void addResetArcs(FsmGraph& graph, AstNode* stmtsp, AstVarScope* stateVscp,
                             const std::unordered_map<int, string>& labels) {
        for (AstNode* nodep = stmtsp; nodep; nodep = nodep->nextp()) {
            if (AstNodeAssign* const assp = VN_CAST(nodep, NodeAssign)) {
                AstVarRef* const vrefp = VN_CAST(assp->lhsp(), VarRef);
                int toValue = 0;
                if (vrefp && vrefp->varScopep() == stateVscp && exprConstValue(assp->rhsp(), toValue)) {
                    if (!validateKnownStateValue(assp, labels, toValue)) continue;
                    graph.addArc(0, toValue, true, false, false, assp->fileline());
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
        AstVar* const stateVarp = selp->varp();
        AstEnumDType* enump = VN_CAST(unwrapEnumCandidate(stateVscp->dtypep()), EnumDType);
        if (!enump) enump = VN_CAST(unwrapEnumCandidate(stateVarp->dtypep()), EnumDType);
        const bool forced = stateVarp->attrFsmState();
        if (!enump && !forced) return;

        std::vector<std::pair<string, int>> states;
        std::unordered_map<int, string> labels;
        if (enump) {
            if (stateVscp->width() < 1 || stateVscp->width() > 32) {
                casep->v3warn(COVERIGN,
                              "Ignoring unsupported: FSM coverage on enum-typed state "
                              "variables wider than 32 bits");
                return;
            }
            for (AstEnumItem* itemp = enump->itemsp(); itemp; itemp = VN_AS(itemp->nextp(), EnumItem)) {
                const AstConst* const constp = VN_AS(itemp->valuep(), Const);
                const int value = constp->toSInt();
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

        DetectedFsm& entry = m_state.fsms()[stateVscp->name()];
        if (!entry.graphp) {
            entry.graphp.reset(new FsmGraph{});
            entry.graphp->scopep(m_scopep);
            entry.graphp->alwaysp(alwaysp);
            entry.graphp->stateVarName(stateVscp->prettyName());
            entry.graphp->stateVarInternalName(stateVarp->name());
            entry.graphp->stateVarScopep(stateVscp);
            entry.graphp->senses() = describeSenTree(alwaysp->sentreep());
            entry.graphp->resetCond() = describeResetCond(resetCondp);
            entry.graphp->hasResetCond(entry.graphp->resetCond().varScopep != nullptr);
            entry.graphp->resetInclude(stateVarp->attrFsmResetArc());
            entry.graphp->inclCond(stateVarp->attrFsmArcInclCond());
            entry.graphp->fileline(casep->fileline());
            for (const std::pair<string, int>& state : states) {
                entry.graphp->addStateVertex(state.first, state.second);
            }
        }
        for (AstCaseItem* itemp = casep->itemsp(); itemp; itemp = VN_AS(itemp->nextp(), CaseItem)) {
            emitCaseItemArcs(*entry.graphp, itemp, stateVscp, labels, entry.graphp->inclCond());
        }
    }

    // Find the first supported FSM candidate in a clocked always block, warn on
    // additional candidates, and attach reset arcs when present. Candidate
    // filtering stays narrow on purpose: we prefer to skip ambiguous shapes now
    // and expand detection in a later PR rather than over-infer coverage from
    // forms we do not yet model confidently.
    void processAlways(AstAlways* alwaysp) {
        if (!alwaysp->sentreep() || !alwaysp->sentreep()->hasClocked()) return;
        std::vector<std::pair<AstCase*, AstNodeExpr*>> candidates;
        AstNode* stmtsp = alwaysp->stmtsp();
        AstIf* const firstIfp = VN_CAST(stmtsp, If);
        if (firstIfp) {
            if (AstCase* const casep = VN_CAST(firstIfp->elsesp(), Case)) {
                candidates.emplace_back(casep, isSimpleResetCond(firstIfp->condp()) ? firstIfp->condp()
                                                                                     : nullptr);
            }
        }
        for (AstNode* nodep = stmtsp; nodep; nodep = nodep->nextp()) {
            if (AstCase* const casep = VN_CAST(nodep, Case)) candidates.emplace_back(casep, nullptr);
        }
        if (candidates.empty()) return;

        AstVarScope* firstVscp = nullptr;
        for (const std::pair<AstCase*, AstNodeExpr*>& cand : candidates) {
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
                cand.first->v3warn(
                    COVERIGN,
                    "Ignoring unsupported: FSM coverage on multiple supported case "
                    "statements found in the same always block. Only the first "
                    "candidate will be instrumented.");
            }
        }

        if (firstIfp && firstVscp) {
            const DetectedFsmMap::const_iterator it = m_state.fsms().find(firstVscp->name());
            if (it == m_state.fsms().end()) return;
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
    const FsmState& m_state;

    // METHODS
    // Rebuild a state-typed constant using the tracked state variable
    // width/sign so emitted comparisons match the original representation.
    static AstConst* makeStateConst(FileLine* flp, AstVarScope* vscp, int value) {
        V3Number num{flp, vscp->width(), static_cast<uint32_t>(value)};
        num.isSigned(vscp->dtypep()->isSigned());
        return new AstConst{flp, num};
    }

    // Build guards incrementally without forcing callers to special-case the
    // first predicate; this keeps emitted state/arc conditions readable.
    static AstNodeExpr* andExpr(FileLine* flp, AstNodeExpr* lhsp, AstNodeExpr* rhsp) {
        if (!lhsp) return rhsp;
        return new AstLogAnd{flp, lhsp, rhsp};
    }

    static AstNodeExpr* buildResetCond(FileLine* flp, AstVarScope* resetVscp,
                                       const FsmResetCondDesc&) {
        return new AstVarRef{flp, resetVscp, VAccess::READ};
    }

    // Rebuild the original event control from the saved sense description so
    // post-state coverage sampling runs on the same triggering edges.
    static AstSenTree* buildSenTree(
        FileLine* flp, const std::vector<FsmSenDesc>& senses) {
        AstSenTree* const sentreep = new AstSenTree{flp, nullptr};
        for (const FsmSenDesc& sense : senses) {
            AstSenItem* const senItemp = new AstSenItem{
                flp, VEdgeType{sense.edgeType},
                new AstVarRef{flp, sense.varScopep, VAccess::READ}};
            sentreep->addSensesp(senItemp);
        }
        return sentreep;
    }

    // Lower one fully detected FSM graph into the concrete coverage machinery
    // used by generated models: declarations, previous-state tracking, and the
    // pre/post-triggered increment logic for states and arcs.
    void buildOne(const FsmGraph& graph) {
        AstAlways* const alwaysp = graph.alwaysp();
        AstScope* const scopep = graph.scopep();
        AstVarScope* const stateVscp = graph.stateVarScopep();
        FileLine* const flp = graph.fileline();
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
        AstNode* const bodysp = alwaysp->stmtsp()->unlinkFrBackWithNext();
        alwaysp->addStmtsp(new AstAssign{flp, new AstVarRef{flp, prevVscp, VAccess::WRITE},
                                         new AstVarRef{flp, stateVscp, VAccess::READ}});
        alwaysp->addStmtsp(bodysp);

        for (const V3GraphVertex& vtx : graph.vertices()) {
            const FsmVertex* const vertexp = vtx.as<FsmVertex>();
            if (!vertexp->isState()) continue;
            const FsmStateVertex* const statep = vtx.as<FsmStateVertex>();
            // State coverage fires when the FSM enters a state from any other
            // value, so repeated self-holds do not count as new entries.
            AstCoverOtherDecl* const declp = new AstCoverOtherDecl{
                flp, "v_fsm_state/" + modp->prettyName(),
                graph.stateVarName() + "::" + statep->label(), "", 0, graph.stateVarName(), "",
                statep->label()};
            declp->hier(scopep->prettyName());
            modp->addStmtsp(declp);
            AstNodeExpr* const guardp
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
                const string fsmTag = arcp->isReset()   ? (graph.resetInclude() ? "reset_include"
                                                        : "reset")
                                     : arcp->isDefault() ? "default"
                                                         : "";
                AstCoverOtherDecl* const declp = new AstCoverOtherDecl{
                    flp, "v_fsm_arc/" + modp->prettyName(),
                    graph.stateVarName() + "::" + fromVertexp->label() + "->" + toStatep->label()
                        + resetTag,
                    "",
                    0,
                    graph.stateVarName(),
                    fromVertexp->label(),
                    toStatep->label(),
                    fsmTag};
                declp->hier(scopep->prettyName());
                modp->addStmtsp(declp);
                AstNodeExpr* guardp = nullptr;
                if (fromVertexp->isResetAny()) {
                    // Reset arcs are modeled as pseudo-source edges in the
                    // graph, then reconstructed here into the original simple
                    // reset predicate combined with the destination state.
                    guardp = buildResetCond(flp, graph.resetCond().varScopep, graph.resetCond());
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

        AstSenTree* const sentreep = buildSenTree(flp, graph.senses());
        AstActive* const activep = new AstActive{flp, "fsm-coverage", sentreep};
        activep->senTreeStorep(sentreep);
        scopep->addBlocksp(activep);
        activep->addStmtsp(covPostp);
    }

public:
    // CONSTRUCTORS
    // Lower every detected FSM graph from the shared local state into
    // concrete coverage instrumentation while the saved scoped pointers are
    // still valid in the same pass.
    explicit FsmLowerVisitor(const FsmState& state)
        : m_state{state} {
        for (const std::pair<const string, DetectedFsm>& it : m_state.fsms()) {
            buildOne(*it.second.graphp);
        }
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
        for (const std::pair<const string, DetectedFsm>& it : state.fsms()) {
            it.second.graphp->dumpDotFilePrefixed(it.second.graphp->dumpTag(index++));
        }
    }
    // Phase 2: lower the completed in-memory graph state immediately, without
    // crossing into another pass owner or serializing through AST placeholders.
    { FsmLowerVisitor lower{state}; }
    V3Global::dumpCheckGlobalTree("fsm-detect", 0, dumpTreeEitherLevel() >= 3);
}
