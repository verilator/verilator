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
#include "V3Control.h"
#include "V3Graph.h"

#include <algorithm>
#include <cctype>
#include <map>
#include <memory>
#include <unordered_map>
#include <unordered_set>

VL_DEFINE_DEBUG_FUNCTIONS;

namespace {

// Width-preserving FSM state identity. FSM detection needs a stable key for
// graph vertices and lookup tables, but lowering still needs the original
// folded Verilog value so emitted comparisons keep the correct width and bits.
class FsmStateValue final {
    // Hash/equality key only. It deliberately ignores signedness because
    // signed and unsigned constants with the same width and bits denote the
    // same encoded FSM state.
    string m_key;  // Canonical "width:value" identity, independent of signedness

    // Semantic value. This is what diagnostics and lowering use when printing
    // values or rebuilding AstConst nodes for instrumentation.
    V3Number m_num;  // Original folded value, preserving width for lowered comparisons

    static string makeKey(const V3Number& num) {
        V3Number keyNum = num;
        // Signedness does not change FSM state identity: same width and bits
        // should address the same graph vertex.
        keyNum.isSigned(false);
        return cvtToStr(keyNum.width()) + ":" + keyNum.ascii(true, true);
    }

public:
    // Default value is used only for synthetic pseudo-states such as ANY and
    // default, which never use m_num as a real Verilog state encoding.
    FsmStateValue()
        : m_key{"1:1'h0"}
        , m_num{static_cast<AstNode*>(nullptr), 1, 0} {}
    explicit FsmStateValue(const V3Number& num)
        : m_key{makeKey(num)}
        , m_num{num} {}

    const string& key() const { return m_key; }
    const V3Number& num() const { return m_num; }
    string ascii() const { return m_num.ascii(true, true); }
    string warnText() const {
        // Preserve legacy diagnostics for old <=32-bit FSMs, but print wide
        // values without truncation.
        if (m_num.width() <= 32) return cvtToStr(m_num.toUInt());
        return ascii();
    }

    bool operator==(const FsmStateValue& rhs) const { return m_key == rhs.m_key; }
};

// unordered_map needs an explicit hash for this custom key type. Keep the
// hash definition paired with operator== by hashing the same canonical key.
struct FsmStateValueHash final {
    size_t operator()(const FsmStateValue& value) const {
        return std::hash<string>{}(value.key());
    }
};

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
    bool activeLow = false;
};

class FsmResetArcDesc final {
    FsmStateValue m_toValue;  // Encoded reset target state.
    AstNode* m_nodep = nullptr;  // Source node for warnings and emitted metadata.
    AstNodeExpr* m_valuep = nullptr;  // Expression that provided the reset value.

public:
    FsmResetArcDesc() = default;
    FsmResetArcDesc(FsmStateValue toValue, AstNodeAssign* nodep)
        : m_toValue{toValue}
        , m_nodep{nodep}
        , m_valuep{nodep->rhsp()} {}
    FsmResetArcDesc(FsmStateValue toValue, AstNode* nodep, AstNodeExpr* valuep)
        : m_toValue{toValue}
        , m_nodep{nodep}
        , m_valuep{valuep} {}

    FsmStateValue toValue() const { return m_toValue; }
    AstNode* nodep() const { return m_nodep; }
    AstNodeExpr* valuep() const { return m_valuep; }
};

struct FsmWrapperRoles final {
    string dPort;
    string qPort;
    string clkPort;
    string rstPort;
    string rstValParam;
    bool hasRstActiveLow = false;
    bool rstActiveLow = false;
};

static bool fsmWrapperResetPolarityFromWrapperAst(AstCell* cellp, const string& portName,
                                                  bool& activeLow) {
    bool matched = false;
    cellp->modp()->foreach([&](AstSenItem* itemp) {
        AstNodeVarRef* const vrefp = itemp->varrefp();
        if (!vrefp) return;
        if (vrefp->varp()->name() != portName) return;
        activeLow = itemp->edgeType() == VEdgeType::ET_NEGEDGE;
        matched = true;
    });
    return matched;
}

static const V3Control::FsmRegisterWrapper* fsmRegisterWrapperDesc(AstCell* cellp) {
    AstNodeModule* const modp = cellp->modp();
    const string origName = modp->origName();
    if (const V3Control::FsmRegisterWrapper* const descp
        = V3Control::getFsmRegisterWrapper(origName)) {
        return descp;
    }
    return V3Control::getFsmRegisterWrapper(modp->prettyDehashOrigOrName());
}

static FsmWrapperRoles rolesFromDesc(const V3Control::FsmRegisterWrapper& desc) {
    FsmWrapperRoles roles;
    roles.dPort = desc.d;
    roles.qPort = desc.q;
    roles.clkPort = desc.clock;
    roles.rstPort = desc.reset;
    roles.rstValParam = desc.resetValue;
    return roles;
}

class FsmRegisterCandidate final {
    AstScope* m_scopep = nullptr;  // Owning scope for the paired FSM.
    AstAlways* m_alwaysp = nullptr;  // Register process that commits the state.
    AstVarScope* m_stateVscp = nullptr;  // Registered FSM state variable.
    AstVarScope* m_nextVscp = nullptr;  // Next-state variable or same state var for 1-block FSMs.
    std::vector<FsmSenDesc> m_senses;  // Event controls for recreated coverage blocks.
    FsmResetCondDesc m_resetCond;  // Saved reset predicate, if any.
    std::vector<FsmResetArcDesc> m_resetArcs;  // Reset target arcs recovered during detect.
    bool m_hasResetCond = false;  // Whether the FSM had a modeled reset predicate.
    bool m_resetInclude = false;  // Whether reset arcs count toward summary totals.
    bool m_inclCond = false;  // Whether conditional/default arcs are kept explicitly.
    FileLine* m_flp = nullptr;  // Representative source location.

public:
    AstScope* scopep() const { return m_scopep; }
    void scopep(AstScope* scopep) { m_scopep = scopep; }
    AstAlways* alwaysp() const { return m_alwaysp; }
    void alwaysp(AstAlways* alwaysp) { m_alwaysp = alwaysp; }
    AstVarScope* stateVscp() const { return m_stateVscp; }
    void stateVscp(AstVarScope* vscp) { m_stateVscp = vscp; }
    AstVarScope* nextVscp() const { return m_nextVscp; }
    void nextVscp(AstVarScope* vscp) { m_nextVscp = vscp; }
    const std::vector<FsmSenDesc>& senses() const { return m_senses; }
    std::vector<FsmSenDesc>& senses() { return m_senses; }
    const FsmResetCondDesc& resetCond() const { return m_resetCond; }
    FsmResetCondDesc& resetCond() { return m_resetCond; }
    const std::vector<FsmResetArcDesc>& resetArcs() const { return m_resetArcs; }
    std::vector<FsmResetArcDesc>& resetArcs() { return m_resetArcs; }
    bool hasResetCond() const { return m_hasResetCond; }
    void hasResetCond(bool flag) { m_hasResetCond = flag; }
    bool resetInclude() const { return m_resetInclude; }
    void resetInclude(bool flag) { m_resetInclude = flag; }
    bool inclCond() const { return m_inclCond; }
    void inclCond(bool flag) { m_inclCond = flag; }
    FileLine* fileline() const { return m_flp; }
    void fileline(FileLine* flp) { m_flp = flp; }
};

class FsmComboAlways final {
    AstScope* const m_scopep = nullptr;  // Owning scope for the combinational process.
    AstAlways* const m_alwaysp = nullptr;  // Candidate transition process.

public:
    FsmComboAlways() = default;
    FsmComboAlways(AstScope* scopep, AstAlways* alwaysp)
        : m_scopep{scopep}
        , m_alwaysp{alwaysp} {}

    AstScope* scopep() const { return m_scopep; }
    AstAlways* alwaysp() const { return m_alwaysp; }
};

class FsmGraph;

class FsmVertex VL_NOT_FINAL : public V3GraphVertex {
    VL_RTTI_IMPL(FsmVertex, V3GraphVertex)

public:
    enum class Kind : uint8_t { STATE, RESET_ANY, DEFAULT_ANY };

private:
    Kind m_kind;  // State vs synthetic ANY/default vertex role.
    string m_label;  // User-facing state or pseudo-state label.
    FsmStateValue m_value;  // Encoded state value for real state vertices.

protected:
    FsmVertex(V3Graph* graphp, Kind kind, string label, FsmStateValue value) VL_MT_DISABLED
        : V3GraphVertex{graphp},
          m_kind{kind},
          m_label{label},
          m_value{value} {}
    ~FsmVertex() override = default;

public:
    Kind kind() const { return m_kind; }
    bool isState() const { return m_kind == Kind::STATE; }
    bool isResetAny() const { return m_kind == Kind::RESET_ANY; }
    bool isDefaultAny() const { return m_kind == Kind::DEFAULT_ANY; }
    const string& label() const { return m_label; }
    FsmStateValue value() const { return m_value; }

    string name() const override VL_MT_SAFE { return m_label + "=" + m_value.ascii(); }
};

class FsmStateVertex final : public FsmVertex {
    VL_RTTI_IMPL(FsmStateVertex, FsmVertex)

public:
    FsmStateVertex(V3Graph* graphp, string label, FsmStateValue value) VL_MT_DISABLED
        : FsmVertex{graphp, Kind::STATE, label, value} {}
    ~FsmStateVertex() override = default;

    string dotColor() const override { return "lightblue"; }
    string dotShape() const override { return "ellipse"; }
};

class FsmPseudoVertex final : public FsmVertex {
    VL_RTTI_IMPL(FsmPseudoVertex, FsmVertex)

public:
    FsmPseudoVertex(V3Graph* graphp, Kind kind, string label) VL_MT_DISABLED
        : FsmVertex{graphp, kind, label, FsmStateValue{}} {}
    ~FsmPseudoVertex() override = default;

    string name() const override VL_MT_SAFE { return label(); }
    string dotColor() const override { return isResetAny() ? "darkgreen" : "orange"; }
    string dotShape() const override { return "diamond"; }
};

class FsmArcEdge final : public V3GraphEdge {
    VL_RTTI_IMPL(FsmArcEdge, V3GraphEdge)
    bool m_isReset = false;  // Arc originates from the synthetic reset source.
    bool m_isCond = false;  // Arc came from a conditional next-state split.
    bool m_isDefault = false;  // Arc represents a case default source.
    FileLine* m_flp = nullptr;  // Source location for emitted coverage metadata.

public:
    FsmArcEdge(V3Graph* graphp, FsmVertex* fromp, FsmStateVertex* top, bool isReset, bool isCond,
               bool isDefault, FileLine* flp) VL_MT_DISABLED : V3GraphEdge{graphp, fromp, top, 1},
                                                               m_isReset{isReset},
                                                               m_isCond{isCond},
                                                               m_isDefault{isDefault},
                                                               m_flp{flp} {}
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
    AstAlways* m_stateAlwaysp = nullptr;  // Register always block being instrumented.
    string m_stateVarName;  // Pretty state variable name for user-visible output.
    string m_stateVarInternalName;  // Internal state symbol name for dump tags.
    AstVarScope* m_stateVarScopep = nullptr;  // Scoped state variable being tracked.
    std::vector<FsmSenDesc> m_senses;  // Saved event controls for recreated active blocks.
    FsmResetCondDesc m_resetCond;  // Saved reset predicate shape, if one exists.
    bool m_hasResetCond = false;  // Whether the detected FSM had a reset branch.
    bool m_resetInclude = false;  // Whether reset arcs count toward coverage totals.
    bool m_inclCond = false;  // Whether conditional arcs should be kept explicitly.
    FileLine* m_flp = nullptr;  // Representative source location for declarations/arcs.
    std::unordered_map<FsmStateValue, FsmStateVertex*, FsmStateValueHash>
        m_stateVertices;  // Value to state map.
    FsmPseudoVertex* m_resetVertexp = nullptr;  // Synthetic ANY source for reset arcs.
    FsmPseudoVertex* m_defaultVertexp = nullptr;  // Synthetic default source for case defaults.

public:
    FsmGraph() VL_MT_DISABLED
        : m_resetVertexp{new FsmPseudoVertex{this, FsmVertex::Kind::RESET_ANY, "ANY"}},
          m_defaultVertexp{new FsmPseudoVertex{this, FsmVertex::Kind::DEFAULT_ANY, "default"}} {}

    AstScope* scopep() const { return m_scopep; }
    void scopep(AstScope* scopep) { m_scopep = scopep; }
    AstAlways* stateAlwaysp() const { return m_stateAlwaysp; }
    void stateAlwaysp(AstAlways* alwaysp) { m_stateAlwaysp = alwaysp; }
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

    FsmStateVertex* addStateVertex(string label, FsmStateValue value) VL_MT_DISABLED {
        FsmStateVertex* const vertexp = new FsmStateVertex{this, label, value};
        m_stateVertices.emplace(value, vertexp);
        return vertexp;
    }
    FsmPseudoVertex* resetAnyVertex() VL_MT_DISABLED { return m_resetVertexp; }
    FsmPseudoVertex* defaultAnyVertex() VL_MT_DISABLED { return m_defaultVertexp; }
    FsmArcEdge* addArc(FsmStateValue fromValue, FsmStateValue toValue, bool isReset, bool isCond,
                       bool isDefault, FileLine* flp) VL_MT_DISABLED {
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

struct FsmCaseCandidate final {
    AstNode* warnNodep = nullptr;  // Transition node that made the candidate supported.
    AstVarScope* stateVscp = nullptr;  // FSM state variable associated with that candidate.
};

// Keep the source expression with the encoded value so inferred literal FSMs can
// reuse the same state-space policy as case-item dispatch.
struct FsmStateComparison final {
    AstVarScope* stateVscp = nullptr;  // Compared state variable
    AstNodeExpr* valuep = nullptr;  // Compared constant value expression
    FsmStateValue value;  // Encoded compared state value
};

// A branch is usable only after its predicate has exactly one state comparison;
// any extra predicate term is treated as an arc guard.
struct FsmIfBranch final {
    AstIf* ifp = nullptr;  // Source if/else-if node
    AstNode* stmtsp = nullptr;  // Branch body
    AstNodeExpr* valuep = nullptr;  // Source state value expression
    FsmStateValue fromValue;  // Encoded source state value
    bool hasTopGuard = false;  // Branch condition had extra guard terms
};

// If-chains are kept separate from cases until graph construction so the
// existing case path remains the preferred candidate when both forms appear.
struct FsmIfChainCandidate final {
    AstIf* ifp = nullptr;  // Top-level if-chain node
    AstVarScope* compareVscp = nullptr;  // Variable used by every state comparison
    std::vector<FsmIfBranch> branches;  // Recognized state-dispatch branches
    AstNode* defaultStmtsp = nullptr;  // Optional final else body
};

// Aliases are accepted only when they are equivalent to spelling the state
// comparison inline; this avoids inferring FSM semantics from arbitrary logic.
using FsmAliasMap = std::unordered_map<const AstVarScope*, FsmStateComparison>;
using FsmCellPortMap = std::unordered_map<string, AstVarScope*>;
using FsmCellPortAliasMap = std::unordered_map<const AstCell*, FsmCellPortMap>;

struct StateConstLabel final {
    string text;
    bool fromParam = false;
    size_t stateIndex = 0;
};

struct FsmStateSpace final {
    std::vector<std::pair<string, FsmStateValue>> states;  // User label and encoded value
    std::unordered_map<FsmStateValue, StateConstLabel, FsmStateValueHash>
        labels;  // Encoded value to label
    AstVar* stateVarp = nullptr;  // Tracked FSM state variable
    bool enumBacked = false;  // Whether states came from an enum declaration
};

// Local shared state between the two adjacent FSM coverage phases. Detection
// fills this with recovered FSM graphs; lowering consumes the completed graphs
// immediately afterward without needing any AST serialization bridge.
class FsmState final {
    // All detected FSMs in discovery order. This is the only bridge between
    // the adjacent detect and lower phases, so the second phase never needs to
    // rediscover or serialize the extracted machine.
    std::vector<DetectedFsm> m_fsms;
    std::map<const AstVarScope*, size_t> m_fsmIndex;

public:
    DetectedFsm& fsmFor(AstVarScope* stateVscp) {
        const std::map<const AstVarScope*, size_t>::const_iterator it = m_fsmIndex.find(stateVscp);
        if (it != m_fsmIndex.end()) return m_fsms.at(it->second);
        const size_t index = m_fsms.size();
        m_fsmIndex.emplace(stateVscp, index);
        m_fsms.emplace_back();
        return m_fsms.back();
    }
    const std::vector<DetectedFsm>& fsms() const { return m_fsms; }
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
    std::vector<FsmRegisterCandidate> m_registerCandidates;
    // Deferring one-block detection avoids making continuous alias support
    // depend on whether the assign appears before or after the always block.
    std::vector<FsmComboAlways> m_oneBlockAlwayss;
    std::vector<FsmComboAlways> m_comboAlwayss;
    std::vector<FsmComboAlways> m_nonComboAlwayss;
    // Wrapper FSM detection has a second path for designs compiled without
    // inlining. In that shape the state register stays behind an AstCell, so we
    // remember candidate cells and resolve them only after the surrounding
    // transition logic and post-link port wiring have both been seen.
    std::vector<std::pair<AstScope*, AstCell*>> m_wrapperCells;
    std::unordered_map<const AstVarScope*, FsmCaseCandidate> m_comboPaired;
    // Continuous aliases are order-independent, while procedural aliases must
    // remain source-order scoped to avoid using assignments not yet executed.
    FsmAliasMap m_stateAliases;
    std::unordered_set<const AstVarScope*> m_ambiguousStateAliases;
    // A surviving wrapper's semantic d/q relationship is split across the
    // parent scope and the child module scope. This table is the narrow bridge
    // between those scopes: only transparent port aliases are recorded, so the
    // detector does not become a general cross-module dataflow engine.
    FsmCellPortAliasMap m_cellPortAliases;

    // METHODS
    // Enum-backed FSMs may be wrapped in refs/typedefs; normalize to the
    // underlying enum type before deciding whether a case is a candidate.
    static AstNodeDType* unwrapEnumCandidate(AstNodeDType* dtypep) {
        return dtypep->skipRefToEnump();
    }

    static string candidateConflictContext(AstNode* laterNodep,
                                           const FsmCaseCandidate& firstCand) {
        return '\n' + laterNodep->warnContextPrimary() + firstCand.warnNodep->warnOther()
               + "... Location of first supported candidate for "
               + firstCand.stateVscp->prettyNameQ() + '\n'
               + firstCand.warnNodep->warnContextSecondary();
    }

    static bool rejectFsmWrapperCell(AstCell* cellp, const string& reason) {
        cellp->v3warn(COVERIGN, "Ignoring unsupported: " + reason);
        return false;
    }

    static bool simpleParamStateValue(AstCell* cellp, const string& name, FsmStateValue& value,
                                      AstNodeExpr*& valuepr) {
        // Cell-path reset recovery must behave like the inlined path when the
        // instance relies on a parameter default. Looking into the linked module
        // default preserves that equivalence while keeping the cell detector's
        // contract narrow: only static, known reset encodings become reset arcs.
        valuepr = nullptr;
        for (AstNode* stmtp = cellp->modp()->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
            AstVar* const varp = VN_CAST(stmtp, Var);
            if (!varp || !varp->isParam() || varp->name() != name) continue;
            valuepr = VN_AS(varp->valuep(), NodeExpr);
            return constValueStatus(valuepr, value) == ConstValueStatus::OK;
        }
        return false;
    }

    static bool childPortInScope(AstVarScope* vscp, AstScope* parentScopep, AstCell*& cellpr) {
        if (!vscp->varp()->isIO()) return false;
        AstScope* const scopep = vscp->scopep();
        UASSERT_OBJ(scopep, vscp, "VarScope without scope");
        if (scopep->aboveScopep() != parentScopep) return false;
        UASSERT_OBJ(scopep->aboveCellp(), vscp,
                    "Child port scope should retain the instance that created it");
        cellpr = scopep->aboveCellp();
        return true;
    }

    static AstVarScope* simpleAssignVarScope(AstNodeExpr* exprp) {
        AstVarRef* const vrefp = VN_CAST(exprp, VarRef);
        return vrefp ? vrefp->varScopep() : nullptr;
    }

    void addWrapperCell(AstScope* scopep, AstCell* cellp) {
        m_cellPortAliases.emplace(cellp, FsmCellPortMap{});
        const std::pair<AstScope*, AstCell*> item{scopep, cellp};
        if (std::find(m_wrapperCells.cbegin(), m_wrapperCells.cend(), item)
            != m_wrapperCells.cend()) {
            return;
        }
        m_wrapperCells.emplace_back(item);
    }

    void collectCellPortAlias(AstAssignW* nodep) {
        UASSERT_OBJ(m_scopep, nodep, "Cell port alias collection requires a scoped assignment");
        AstVarScope* const lhsVscp = simpleAssignVarScope(nodep->lhsp());
        AstVarScope* const rhsVscp = simpleAssignVarScope(nodep->rhsp());
        if (!lhsVscp || !rhsVscp) return;
        AstCell* cellp = nullptr;
        // The cell path is intentionally a transparent-wrapper recognizer. A
        // direct parent<->child variable assignment preserves the register's
        // identity across the hierarchy boundary; any expression, slice, or
        // transform is outside this phase's contract and therefore not recorded.
        if (childPortInScope(lhsVscp, m_scopep, cellp)) {
            if (!fsmRegisterWrapperDesc(cellp)) return;
            UASSERT_OBJ(lhsVscp->varp()->isInput(), nodep,
                        "Child-side port alias lhs should be an input");
            UASSERT_OBJ(rhsVscp->scopep() == m_scopep, nodep,
                        "Child input port alias should connect from the parent scope");
            m_cellPortAliases[cellp][lhsVscp->varp()->name()] = rhsVscp;
            addWrapperCell(m_scopep, cellp);
        } else if (childPortInScope(rhsVscp, m_scopep, cellp)) {
            if (!fsmRegisterWrapperDesc(cellp)) return;
            UASSERT_OBJ(rhsVscp->varp()->isWritable(), nodep,
                        "Child-side port alias rhs should be writable");
            UASSERT_OBJ(lhsVscp->scopep() == m_scopep, nodep,
                        "Child output port alias should connect into the parent scope");
            m_cellPortAliases[cellp][rhsVscp->varp()->name()] = lhsVscp;
            addWrapperCell(m_scopep, cellp);
        }
    }

    AstVarScope* roleVarScope(AstCell* cellp, const string& portName) const {
        // At this point explicit AstPin expressions have been lowered away, so
        // role resolution crosses the wrapper boundary only through the
        // transparent alias table above. This keeps wrapper support aligned with
        // direct-register detection instead of growing into interprocedural FSM
        // inference.
        const FsmCellPortMap& ports = m_cellPortAliases.at(cellp);
        const FsmCellPortMap::const_iterator portIt = ports.find(portName);
        return portIt == ports.end() ? nullptr : portIt->second;
    }

    class RegisterAlwaysAnalyzer final {
        AstScope* const m_scopep;

    public:
        explicit RegisterAlwaysAnalyzer(AstScope* scopep)
            : m_scopep{scopep} {}

        std::vector<std::pair<AstCase*, AstNodeExpr*>>
        oneBlockCandidates(AstAlways* alwaysp) const {
            std::vector<std::pair<AstCase*, AstNodeExpr*>> candidates;
            AstNode* const stmtsp = alwaysp->stmtsp();
            if (AstIf* const firstIfp = VN_CAST(stmtsp, If)) {
                if (AstCase* const casep = VN_CAST(firstIfp->elsesp(), Case)) {
                    candidates.emplace_back(casep,
                                            FsmDetectVisitor::isSimpleResetCond(firstIfp->condp())
                                                ? firstIfp->condp()
                                                : nullptr);
                }
            }
            for (AstNode* nodep = stmtsp; nodep; nodep = nodep->nextp()) {
                if (AstCase* const casep = VN_CAST(nodep, Case))
                    candidates.emplace_back(casep, nullptr);
            }
            return candidates;
        }

        std::vector<std::pair<AstIf*, AstNodeExpr*>>
        oneBlockIfCandidates(AstAlways* alwaysp) const {
            std::vector<std::pair<AstIf*, AstNodeExpr*>> candidates;
            AstNode* const stmtsp = alwaysp->stmtsp();
            // Reset-else FSMs should behave like the existing case path: reset
            // information is metadata, not part of steady-state dispatch.
            if (AstIf* const firstIfp = VN_CAST(stmtsp, If)) {
                if (AstIf* const chainp
                    = VN_CAST(FsmDetectVisitor::singleMeaningfulBranch(firstIfp->elsesp()), If)) {
                    candidates.emplace_back(chainp,
                                            FsmDetectVisitor::isSimpleResetCond(firstIfp->condp())
                                                ? firstIfp->condp()
                                                : nullptr);
                }
            }
            for (AstNode* nodep = stmtsp; nodep; nodep = nodep->nextp()) {
                if (AstIf* const ifp = VN_CAST(nodep, If)) candidates.emplace_back(ifp, nullptr);
            }
            return candidates;
        }

        bool matchRegisterCandidate(AstAlways* alwaysp, FsmRegisterCandidate& cand) const {
            return FsmDetectVisitor::matchRegisterAlways(alwaysp, m_scopep, cand);
        }

        void buildOneBlockCandidate(AstAlways* alwaysp, AstVarScope* vscp, AstNodeExpr* resetCondp,
                                    FsmRegisterCandidate& reg) const {
            reg.scopep(m_scopep);
            reg.alwaysp(alwaysp);
            reg.stateVscp(vscp);
            reg.nextVscp(vscp);
            reg.senses() = FsmDetectVisitor::describeSenTree(alwaysp->sentreep());
            reg.resetCond() = FsmDetectVisitor::describeResetCond(resetCondp);
            reg.hasResetCond(reg.resetCond().varScopep != nullptr);
            reg.resetInclude(vscp->varp()->attrFsmResetArc());
            reg.inclCond(vscp->varp()->attrFsmArcInclCond());
            AstIf* const firstIfp = VN_CAST(alwaysp->stmtsp(), If);
            if (firstIfp && reg.hasResetCond()) {
                AstVarScope* resetStateVscp = nullptr;
                const ResetAssignStatus resetStatus = FsmDetectVisitor::collectConstStateAssigns(
                    firstIfp->thensp(), resetStateVscp, reg.resetArcs());
                if (resetStatus == ResetAssignStatus::NONE || resetStateVscp != vscp) {
                    reg.resetArcs().clear();
                    FsmStateValue resetValue;
                    AstNode* const thenNodep
                        = FsmDetectVisitor::singleMeaningfulBranch(firstIfp->thensp());
                    UASSERT_OBJ(thenNodep, firstIfp,
                                "one-block reset fallback requires a non-empty reset branch");
                    AstNodeAssign* const resetAssp = FsmDetectVisitor::directConstStateAssignNode(
                        thenNodep, resetStateVscp, resetValue);
                    if (resetAssp && resetStateVscp == vscp) {
                        reg.resetArcs().emplace_back(resetValue, resetAssp);
                    }
                } else if (resetStatus == ResetAssignStatus::MULTI_SAME_STATE) {
                    reg.resetArcs().clear();
                }
            }
        }
    };

    bool matchFsmWrapperCell(AstScope* scopep, AstCell* cellp, FsmRegisterCandidate& cand) const {
        FsmWrapperRoles roles = rolesFromDesc(*fsmRegisterWrapperDesc(cellp));

        AstVarScope* const nextVscp = roleVarScope(cellp, roles.dPort);
        AstVarScope* const stateVscp = roleVarScope(cellp, roles.qPort);
        if (!nextVscp || !stateVscp) {
            return rejectFsmWrapperCell(
                cellp, "fsm_register_wrapper d and q connections must be simple variables");
        }
        AstVarScope* const clkVscp = roleVarScope(cellp, roles.clkPort);
        if (!clkVscp) {
            return rejectFsmWrapperCell(
                cellp, "fsm_register_wrapper instance requires a simple clock connection");
        }

        FsmSenDesc clkSense;
        clkSense.edgeType = VEdgeType::ET_POSEDGE;
        clkSense.varScopep = clkVscp;
        cand.senses().push_back(clkSense);

        AstVarScope* resetVscp = nullptr;
        if (!roles.rstPort.empty()) resetVscp = roleVarScope(cellp, roles.rstPort);
        if (resetVscp) {
            // The descriptor identifies the reset port but not its polarity. Use
            // the wrapper's own event control AST as the contract for sampling
            // the connected parent signal.
            bool inferredActiveLow = false;
            if (fsmWrapperResetPolarityFromWrapperAst(cellp, roles.rstPort, inferredActiveLow)) {
                roles.hasRstActiveLow = true;
                roles.rstActiveLow = inferredActiveLow;
            }
        }

        AstNodeExpr* resetValuep = nullptr;
        FsmStateValue resetValue;
        const bool hasResetValue
            = !roles.rstValParam.empty()
              && simpleParamStateValue(cellp, roles.rstValParam, resetValue, resetValuep);
        if (resetVscp && roles.hasRstActiveLow && hasResetValue) {
            FsmSenDesc rstSense;
            rstSense.edgeType = roles.rstActiveLow ? VEdgeType::ET_NEGEDGE : VEdgeType::ET_POSEDGE;
            rstSense.varScopep = resetVscp;
            cand.senses().push_back(rstSense);
            cand.resetCond().varScopep = resetVscp;
            cand.resetCond().activeLow = roles.rstActiveLow;
            cand.hasResetCond(true);
            cand.resetArcs().emplace_back(resetValue, cellp, resetValuep);
        } else if (!roles.rstPort.empty() || !roles.rstValParam.empty()) {
            string reason;
            if (roles.rstPort.empty()) {
                reason = "reset port is not configured";
            } else if (!resetVscp) {
                reason = "reset connection is missing or not a simple variable";
            } else if (!roles.hasRstActiveLow) {
                reason = "reset polarity could not be inferred from the wrapper";
            } else if (roles.rstValParam.empty()) {
                reason = "reset_value parameter is not configured";
            } else {
                reason = "reset_value parameter is missing or not static";
            }
            cellp->v3warn(COVERIGN,
                          "Ignoring unsupported: fsm_register_wrapper reset arcs require both "
                          "reset polarity and static reset value; " + reason);
        }

        // This candidate represents a register proven through an instance
        // boundary, so there is no parent always_ff body to annotate. Lowering
        // treats null alwaysp as the explicit cell-path contract and builds its
        // sampling block from the recovered clock/reset interface instead.
        cand.scopep(scopep);
        cand.alwaysp(nullptr);
        cand.stateVscp(stateVscp);
        cand.nextVscp(nextVscp);
        cand.resetInclude(stateVscp->varp()->attrFsmResetArc());
        cand.inclCond(stateVscp->varp()->attrFsmArcInclCond());
        cand.fileline(cellp->fileline());
        return true;
    }

    class ComboAlwaysAnalyzer final {
    public:
        struct ComboMatch final {
            const FsmRegisterCandidate* matchedp = nullptr;
            AstNode* warnNodep = nullptr;
        };

    private:
        const std::vector<FsmRegisterCandidate>& m_registerCandidates;

    public:
        explicit ComboAlwaysAnalyzer(const std::vector<FsmRegisterCandidate>& registerCandidates)
            : m_registerCandidates{registerCandidates} {}

        ComboMatch matchCase(AstNode* stmtsp, AstCase* casep) const {
            ComboMatch match;
            AstVarRef* const selp = VN_CAST(casep->exprp(), VarRef);
            if (!selp) return match;
            for (const FsmRegisterCandidate& reg : m_registerCandidates) {
                if (selp->varScopep() == reg.nextVscp()) {
                    if (!FsmDetectVisitor::hasCanonicalNextStateDefaultBeforeCase(
                            stmtsp, casep, reg.stateVscp(), reg.nextVscp())) {
                        continue;
                    }
                } else if (selp->varScopep() != reg.stateVscp()) {
                    continue;
                }
                AstNode* const warnNodep = FsmDetectVisitor::caseSupportedTransitionNode(
                    casep, reg.nextVscp(), reg.inclCond());
                if (!warnNodep) continue;
                match.matchedp = &reg;
                match.warnNodep = warnNodep;
            }
            return match;
        }

        ComboMatch matchIfChain(AstNode* stmtsp, const FsmIfChainCandidate& chain) const {
            ComboMatch match;
            for (const FsmRegisterCandidate& reg : m_registerCandidates) {
                // Comparing state_d is safe only with the canonical default;
                // otherwise the chain may be dispatching on already-mutated data.
                if (chain.compareVscp == reg.nextVscp()) {
                    if (!FsmDetectVisitor::hasCanonicalNextStateDefaultBeforeCase(
                            stmtsp, chain.ifp, reg.stateVscp(), reg.nextVscp())) {
                        continue;
                    }
                } else if (chain.compareVscp != reg.stateVscp()) {
                    continue;
                }
                AstNode* const warnNodep
                    = FsmDetectVisitor::ifChainSupportedTransitionNode(chain, reg.nextVscp());
                if (!warnNodep) continue;
                match.matchedp = &reg;
                match.warnNodep = warnNodep;
            }
            return match;
        }

        bool shouldWarnUnsupported(AstNode* stmtsp, AstCase* casep) const {
            const AstVarRef* const selp = VN_CAST(casep->exprp(), VarRef);
            if (!selp) return false;

            return std::any_of(
                m_registerCandidates.cbegin(), m_registerCandidates.cend(),
                [&](const FsmRegisterCandidate& reg) -> bool {
                    const bool matchesNext = selp->varScopep() == reg.nextVscp();
                    const bool matchesState = selp->varScopep() == reg.stateVscp();

                    if (!matchesNext && !matchesState) return false;
                    if (matchesNext
                        && !FsmDetectVisitor::hasCanonicalNextStateDefaultBeforeCase(
                            stmtsp, casep, reg.stateVscp(), reg.nextVscp())) {
                        return false;
                    }
                    return FsmDetectVisitor::caseSupportedTransitionNode(casep, reg.nextVscp(),
                                                                         reg.inclCond());
                });
        }
    };

    // Reset arcs are only modeled for the simple signal form that survives to
    // this pass after earlier normalization.
    static bool isSimpleResetCond(AstNodeExpr* condp) { return VN_IS(condp, VarRef); }

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

    static AstNode* skipLeadingIgnorableStmt(AstNode* nodep) {
        while (nodep && isIgnorableStmt(nodep)) nodep = nodep->nextp();
        return nodep;
    }

    // Conservative extractor for statement lists: only treat a list as simple
    // when exactly one non-coverage statement remains after unwrapping.
    // Richer multi-statement or control-flow forms are intentionally left for
    // follow-on FSM-detection work instead of being partially inferred here.
    static AstNode* singleMeaningfulStmt(AstNode* stmtp) {
        AstNode* resultp = nullptr;
        for (AstNode* nodep = stmtp; nodep; nodep = nodep->nextp()) {
            if (isIgnorableStmt(nodep)) continue;
            if (resultp) return nullptr;
            resultp = nodep;
        }
        return resultp;
    }

    // If/else branches are a single subtree, not a statement list, so do not
    // walk nextp() here or we may accidentally consume the sibling else-arm.
    static AstNode* singleMeaningfulBranch(AstNode* branchp) {
        if (!branchp) return nullptr;
        return branchp;
    }

    // By fsm-detect time, non-clocked always @* blocks are already admitted through
    // a missing sentree. This helper therefore only needs to recognize
    // explicit changed-sensitivity lists such as always @(a or b); clocked and
    // event-driven forms remain out of scope.
    static bool isPlainComboSentree(const AstSenTree* sentreep) {
        UASSERT(sentreep, "plain combo sensitivity check requires a sensitivity tree");
        for (const AstSenItem* senp = sentreep->sensesp(); senp;
             senp = VN_AS(senp->nextp(), SenItem)) {
            if (senp->edgeType() == VEdgeType::ET_CHANGED) continue;
            return false;
        }
        return true;
    }

    void warnUnsupportedComboAlways(const FsmComboAlways& combo) {
        const ComboAlwaysAnalyzer analyzer{m_registerCandidates};
        AstNode* const stmtsp = skipLeadingIgnorableStmt(combo.alwaysp()->stmtsp());
        bool warned = false;
        for (AstNode* nodep = stmtsp; nodep; nodep = nodep->nextp()) {
            AstCase* const casep = VN_CAST(nodep, Case);
            if (!casep) continue;
            if (analyzer.shouldWarnUnsupported(stmtsp, casep)) {
                casep->v3warn(COVERIGN, "Ignoring unsupported: FSM coverage on non-clocked always "
                                        "blocks requires a combinational sensitivity list or "
                                        "always_comb");
                warned = true;
            }
            if (warned) break;
        }
    }

    // Case-item bodies are single subtrees like if/else arms, not statement
    // lists, so unwrap only local begin/end wrappers here rather than walking
    // sibling case items via nextp().
    static AstNodeAssign* directStateAssign(AstNode* stmtp, AstVarScope* stateVscp) {
        AstNode* const nodep = singleMeaningfulBranch(stmtp);
        if (!nodep) return nullptr;
        AstNodeAssign* const assp = VN_CAST(nodep, NodeAssign);
        if (!assp) return nullptr;
        AstVarRef* const vrefp = VN_CAST(assp->lhsp(), VarRef);
        if (!vrefp || vrefp->varScopep() != stateVscp) return nullptr;
        return assp;
    }

    static AstNodeAssign* nodeStateVarAssign(AstNode* nodep, AstVarScope*& stateVscp,
                                             AstVarScope*& fromVscp) {
        AstNodeAssign* const assp = VN_CAST(nodep, NodeAssign);
        if (!assp) return nullptr;
        AstVarRef* const lhsp = VN_AS(assp->lhsp(), VarRef);
        UASSERT_OBJ(lhsp, assp, "register commit lhs should be normalized to a VarRef");
        AstVarRef* const rhsp = VN_CAST(assp->rhsp(), VarRef);
        if (!rhsp) return nullptr;
        stateVscp = lhsp->varScopep();
        fromVscp = rhsp->varScopep();
        return assp;
    }

    static AstNodeAssign* directCondStateVarAssign(AstNode* nodep, AstVarScope*& stateVscp,
                                                   AstVarScope*& fromVscp, AstNodeExpr*& condp,
                                                   bool& resetActiveLow,
                                                   FsmStateValue& resetValue) {
        AstNodeAssign* const assp = VN_CAST(nodep, NodeAssign);
        if (!assp) return nullptr;
        AstVarRef* const lhsp = VN_AS(assp->lhsp(), VarRef);
        UASSERT_OBJ(lhsp, assp,
                    "conditional register commit lhs should be normalized to a VarRef");
        AstCond* const rhsp = VN_CAST(assp->rhsp(), Cond);
        if (!rhsp) return nullptr;
        if (AstVarRef* const elsep = VN_CAST(rhsp->elsep(), VarRef)) {
            if (constValueStatus(rhsp->thenp(), resetValue) != ConstValueStatus::OK) return nullptr;
            fromVscp = elsep->varScopep();
            resetActiveLow = false;
        } else if (AstVarRef* const thenp = VN_CAST(rhsp->thenp(), VarRef)) {
            if (constValueStatus(rhsp->elsep(), resetValue) != ConstValueStatus::OK) return nullptr;
            fromVscp = thenp->varScopep();
            resetActiveLow = true;
        } else {
            return nullptr;
        }
        stateVscp = lhsp->varScopep();
        condp = rhsp->condp();
        return assp;
    }

    static AstNodeAssign* directConstStateAssignNode(AstNode* nodep, AstVarScope*& stateVscp,
                                                     FsmStateValue& value) {
        AstNodeAssign* const assp = VN_CAST(nodep, NodeAssign);
        if (!assp) return nullptr;
        AstVarRef* const lhsp = VN_AS(assp->lhsp(), VarRef);
        UASSERT_OBJ(lhsp, assp,
                    "direct constant state assignment lhs should be normalized to a VarRef");
        if (constValueStatus(assp->rhsp(), value) != ConstValueStatus::OK) return nullptr;
        stateVscp = lhsp->varScopep();
        return assp;
    }

    enum class ResetAssignStatus : uint8_t {
        NONE,  // Reset branch was not the supported direct-constant shape.
        SINGLE,  // Exactly one supported reset assignment was collected.
        MULTI_SAME_STATE  // Multiple assignments to the same FSM state var; warn and ignore.
    };

    // Reset arcs are only extracted from the single direct-constant form. If
    // user RTL assigns the same state register multiple times in the reset
    // branch, warn and skip reset-arc modeling rather than inventing multiple
    // reset transitions for an odd but legal coding style.
    static ResetAssignStatus collectConstStateAssigns(AstNode* stmtp, AstVarScope*& stateVscp,
                                                      std::vector<FsmResetArcDesc>& resetArcs) {
        AstNode* nodep = skipLeadingIgnorableStmt(stmtp);
        UASSERT_OBJ(nodep, stmtp, "Empty reset branch unexpectedly survived to FSM detection");
        for (;; nodep = nodep->nextp()) {
            AstVarScope* assignStateVscp = nullptr;
            FsmStateValue value;
            AstNodeAssign* const assp = directConstStateAssignNode(nodep, assignStateVscp, value);
            if (!assp) return ResetAssignStatus::NONE;
            if (!stateVscp) stateVscp = assignStateVscp;
            if (assignStateVscp != stateVscp) return ResetAssignStatus::NONE;
            if (!resetArcs.empty()) {
                assp->v3warn(COVERIGN, "Ignoring unsupported: FSM coverage on reset branches with "
                                       "multiple assignments to the state variable");
                resetArcs.clear();
                return ResetAssignStatus::MULTI_SAME_STATE;
            }
            resetArcs.emplace_back(value, assp);
            if (!nodep->nextp()) return ResetAssignStatus::SINGLE;
        }
    }

    static bool hasCanonicalNextStateDefaultBeforeCase(AstNode* stmtsp, AstNode* targetp,
                                                       AstVarScope* stateVscp,
                                                       AstVarScope* nextVscp) {
        AstNode* const bodyp = skipLeadingIgnorableStmt(stmtsp);
        bool sawCanonicalDefault = false;
        for (AstNode* nodep = bodyp;; nodep = nodep->nextp()) {
            UASSERT_OBJ(nodep, targetp,
                        "next-state candidate not found in scanned statement list");
            if (nodep == targetp) return sawCanonicalDefault;
            if (AstNodeAssign* const assp = VN_CAST(nodep, NodeAssign)) {
                AstVarRef* const lhsp = VN_CAST(assp->lhsp(), VarRef);
                AstVarRef* const rhsp = VN_CAST(assp->rhsp(), VarRef);
                if (!lhsp || lhsp->varScopep() != nextVscp) continue;
                if (sawCanonicalDefault) {
                    const string nextName = nextVscp->varp()->prettyNameQ();
                    const string stateName = stateVscp->varp()->prettyNameQ();
                    assp->v3warn(COVERIGN,
                                 "Ignoring unsupported: FSM coverage on case(" + nextName
                                     + ") when the canonical " + nextName + " = " + stateName
                                     + " default is overwritten before the case statement");
                    return false;
                }
                if (!rhsp || rhsp->varScopep() != stateVscp) return false;
                sawCanonicalDefault = true;
            }
        }
    }

    static bool ifStateConstAssign(AstNode* stmtp, AstVarScope* stateVscp,
                                   FsmStateValue& thenValue, FsmStateValue& elseValue) {
        AstIf* const ifp = VN_CAST(singleMeaningfulBranch(stmtp), If);
        if (!ifp || !ifp->elsesp()) return false;
        AstVarScope* thenVscp = nullptr;
        AstVarScope* elseVscp = nullptr;
        AstNode* const thenNodep = singleMeaningfulBranch(skipLeadingIgnorableStmt(ifp->thensp()));
        UASSERT_OBJ(thenNodep, ifp, "Empty then-branch unexpectedly survived to FSM detection");
        AstNode* const elseNodep = singleMeaningfulBranch(skipLeadingIgnorableStmt(ifp->elsesp()));
        if (!elseNodep) return false;
        if (!directConstStateAssignNode(thenNodep, thenVscp, thenValue)) return false;
        if (!directConstStateAssignNode(elseNodep, elseVscp, elseValue)) return false;
        if (thenVscp == stateVscp && elseVscp == stateVscp) return true;
        if (thenVscp != elseVscp) return false;
        AstNode* const followp = skipLeadingIgnorableStmt(ifp->nextp());
        AstVarScope* finalStateVscp = nullptr;
        AstVarScope* finalFromVscp = nullptr;
        AstNode* const finalNodep = singleMeaningfulBranch(followp);
        if (!finalNodep) return false;
        if (!nodeStateVarAssign(finalNodep, finalStateVscp, finalFromVscp)) return false;
        if (finalStateVscp != stateVscp) return false;
        if (finalFromVscp != thenVscp) return false;
        return true;
    }

    static bool directStateCondConstAssign(AstNode* stmtp, AstVarScope* stateVscp,
                                           FsmStateValue& thenValue, FsmStateValue& elseValue) {
        AstNodeAssign* const assp = directStateAssign(stmtp, stateVscp);
        if (!assp) return false;
        AstCond* const condp = VN_CAST(assp->rhsp(), Cond);
        if (!condp) return false;
        return constValueStatus(condp->thenp(), thenValue) == ConstValueStatus::OK
               && constValueStatus(condp->elsep(), elseValue) == ConstValueStatus::OK;
    }

    static AstNode* caseItemSupportedArcNode(AstCaseItem* itemp, AstVarScope* stateVscp,
                                             bool inclCond) {
        if (itemp->isDefault()) {
            if (!inclCond) return nullptr;
        }
        AstNodeAssign* const assp = directStateAssign(itemp->stmtsp(), stateVscp);
        if (assp) {
            FsmStateValue toValue;
            if (constValueStatus(assp->rhsp(), toValue) == ConstValueStatus::OK) return assp;
        }
        FsmStateValue thenValue;
        FsmStateValue elseValue;
        if (directStateCondConstAssign(itemp->stmtsp(), stateVscp, thenValue, elseValue)) {
            return assp;
        }
        if (ifStateConstAssign(itemp->stmtsp(), stateVscp, thenValue, elseValue)) {
            return singleMeaningfulBranch(itemp->stmtsp());
        }
        return nullptr;
    }

    // Combinational transition blocks are paired only through supported case
    // items that assign to the recorded next-state variable.
    static AstNode* caseSupportedTransitionNode(AstCase* casep, AstVarScope* stateVscp,
                                                bool inclCond) {
        for (AstCaseItem* itemp = casep->itemsp(); itemp;
             itemp = VN_AS(itemp->nextp(), CaseItem)) {
            if (AstNode* const nodep = caseItemSupportedArcNode(itemp, stateVscp, inclCond))
                return nodep;
        }
        return nullptr;
    }

    static AstNode* caseItemSupportedArcNodeLike(AstNode* stmtsp, AstVarScope* stateVscp) {
        if (AstNodeAssign* const assp = directStateAssign(stmtsp, stateVscp)) {
            FsmStateValue toValue;
            if (constValueStatus(assp->rhsp(), toValue) == ConstValueStatus::OK) return assp;
            FsmStateValue thenValue;
            FsmStateValue elseValue;
            if (directStateCondConstAssign(stmtsp, stateVscp, thenValue, elseValue)) return assp;
        }
        return nullptr;
    }

    static AstNode* ifChainSupportedTransitionNode(const FsmIfChainCandidate& chain,
                                                   AstVarScope* stateVscp) {
        for (size_t i = 0; i < chain.branches.size(); ++i) {
            const FsmIfBranch& branch = chain.branches[i];
            AstNode* const nodep = caseItemSupportedArcNodeLike(branch.stmtsp, stateVscp);
            if (!nodep) return nullptr;
        }
        return chain.branches.front().ifp;
    }

    // Prefer user labels in reports. Forced non-enum FSMs prepopulate synthetic
    // labels, so all emitted arcs should already have a known label here.
    static string labelForValue(
        const std::unordered_map<FsmStateValue, StateConstLabel, FsmStateValueHash>& labels,
        const FsmStateValue& value) {
        return labels.at(value).text;
    }

    // The extractor only models constant-valued state transitions, and by the
    // time detect runs those values have already been constant-folded.
    enum class ConstValueStatus : uint8_t { OK, NOT_CONST, XZ };

    static ConstValueStatus constValueStatus(AstNodeExpr* exprp, FsmStateValue& value) {
        const AstConst* const constp = VN_CAST(exprp, Const);
        if (!constp) return ConstValueStatus::NOT_CONST;
        const V3Number& num = constp->num();
        if (num.isAnyXZ()) return ConstValueStatus::XZ;
        value = FsmStateValue{num};
        return ConstValueStatus::OK;
    }

    static bool pureStateComparisonNoAlias(AstNodeExpr* exprp, FsmStateComparison& cmp) {
        AstEq* const eqp = VN_CAST(exprp, Eq);
        if (!eqp) return false;

        // Operand order is not semantically meaningful for state dispatch, so
        // both normalized forms should classify identically.
        AstVarRef* vrefp = VN_CAST(eqp->lhsp(), VarRef);
        AstNodeExpr* valuep = eqp->rhsp();
        if (!vrefp) {
            vrefp = VN_AS(eqp->rhsp(), VarRef);
            valuep = eqp->lhsp();
        }

        FsmStateValue value;
        if (constValueStatus(valuep, value) != ConstValueStatus::OK) return false;
        cmp.stateVscp = vrefp->varScopep();
        cmp.valuep = valuep;
        cmp.value = value;
        return true;
    }

    static bool pureStateComparison(AstNodeExpr* exprp, const FsmAliasMap& aliases,
                                    FsmStateComparison& cmp) {
        if (pureStateComparisonNoAlias(exprp, cmp)) return true;
        // Bare predicates are too broad for FSM inference unless a prior alias
        // proves they are exactly a state comparison.
        if (AstVarRef* const vrefp = VN_CAST(exprp, VarRef)) {
            const FsmAliasMap::const_iterator it = aliases.find(vrefp->varScopep());
            if (it == aliases.end()) return false;
            cmp = it->second;
            return true;
        }
        return false;
    }

    static bool supportedTopLevelGuard(AstNodeExpr* exprp) {
        // These terms can combine multiple dispatch choices into one branch, so
        // treating them as ordinary guards would over-infer the FSM shape.
        if (VN_IS(exprp, Or)) return false;
        if (VN_IS(exprp, RedAnd)) return false;
        if (VN_IS(exprp, RedOr)) return false;
        if (VN_IS(exprp, RedXor)) return false;
        return true;
    }

    static bool resolveIfPredicate(AstNodeExpr* exprp, const FsmAliasMap& aliases,
                                   FsmStateComparison& cmp, bool& hasGuard) {
        std::vector<AstNodeExpr*> terms;
        std::vector<AstNodeExpr*> pending;
        pending.push_back(exprp);
        // Top-level conjunction is the only decomposition we can map cleanly to
        // one source state plus optional transition guards.
        while (!pending.empty()) {
            AstNodeExpr* const nodep = pending.back();
            pending.pop_back();
            if (AstAnd* const andp = VN_CAST(nodep, And)) {
                pending.push_back(andp->rhsp());
                pending.push_back(andp->lhsp());
            } else {
                terms.push_back(nodep);
            }
        }

        bool sawComparison = false;
        for (size_t i = 0; i < terms.size(); ++i) {
            AstNodeExpr* const termp = terms[i];
            FsmStateComparison termCmp;
            if (pureStateComparison(termp, aliases, termCmp /*ref*/)) {
                if (sawComparison) return false;
                cmp = termCmp;
                sawComparison = true;
                continue;
            }
            if (!supportedTopLevelGuard(termp)) return false;
            hasGuard = true;
        }
        return sawComparison;
    }

    static void addAlias(FsmAliasMap& aliases, std::unordered_set<const AstVarScope*>& ambiguous,
                         AstVarScope* aliasVscp, const FsmStateComparison& cmp) {
        if (ambiguous.find(aliasVscp) != ambiguous.end()) return;
        const FsmAliasMap::iterator it = aliases.find(aliasVscp);
        if (it == aliases.end()) {
            aliases.emplace(aliasVscp, cmp);
            return;
        }
        // Conflicting alias definitions make the predicate ambiguous, and
        // ambiguous aliases are worse than missing an optional FSM.
        if (it->second.stateVscp == cmp.stateVscp && it->second.value == cmp.value) return;
        aliases.erase(aliasVscp);
        ambiguous.emplace(aliasVscp);
        return;
    }

    static void collectAliasFromAssign(AstNodeAssign* assp, FsmAliasMap& aliases,
                                       std::unordered_set<const AstVarScope*>& ambiguous) {
        AstVarRef* const lhsp = VN_CAST(assp->lhsp(), VarRef);
        if (!lhsp) return;
        FsmStateComparison cmp;
        // Guarded aliases blur dispatch and transition conditions, so require a
        // pure comparison and let guards live at the use site.
        if (!pureStateComparisonNoAlias(assp->rhsp(), cmp /*ref*/)) return;
        addAlias(aliases /*ref*/, ambiguous /*ref*/, lhsp->varScopep(), cmp);
    }

    FsmAliasMap localAliasesBefore(AstNode* stmtsp, AstNode* limitp) const {
        FsmAliasMap aliases = m_stateAliases;
        std::unordered_set<const AstVarScope*> ambiguous = m_ambiguousStateAliases;
        // Procedural aliases cannot be applied before their assignment without
        // changing the meaning of the surrounding always block.
        for (AstNode* nodep = skipLeadingIgnorableStmt(stmtsp); nodep && nodep != limitp;
             nodep = nodep->nextp()) {
            if (AstNodeAssign* const assp = VN_CAST(nodep, NodeAssign)) {
                collectAliasFromAssign(assp, aliases /*ref*/, ambiguous /*ref*/);
            }
        }
        for (const AstVarScope* const vscp : ambiguous) aliases.erase(vscp);
        return aliases;
    }

    static bool collectIfChain(AstIf* ifp, const FsmAliasMap& aliases,
                               FsmIfChainCandidate& chain) {
        chain.ifp = ifp;
        std::unordered_set<string> seenValues;
        AstIf* curp = ifp;
        // Only the top-level spine represents dispatch; treating nested branch
        // logic as additional source states would invent transitions.
        while (true) {
            FsmStateComparison cmp;
            bool hasGuard = false;
            if (!resolveIfPredicate(curp->condp(), aliases, cmp, hasGuard)) return false;
            if (chain.compareVscp && chain.compareVscp != cmp.stateVscp) return false;
            if (!seenValues.insert(cmp.value.key()).second) return false;
            chain.compareVscp = cmp.stateVscp;
            chain.branches.push_back(
                FsmIfBranch{curp, curp->thensp(), cmp.valuep, cmp.value, hasGuard});

            AstNode* const elseNodep
                = singleMeaningfulBranch(skipLeadingIgnorableStmt(curp->elsesp()));
            if (!elseNodep) break;
            if (AstIf* const elseIfp = VN_CAST(elseNodep, If)) {
                curp = elseIfp;
                continue;
            }
            chain.defaultStmtsp = elseNodep;
            break;
        }
        return chain.branches.size() >= 2;
    }

    // Enum-backed FSMs should only use values that were interned as known states.
    // If a constant transition references some other encoding, warn and skip FSM
    // instrumentation for that edge rather than silently dropping it or turning
    // optional coverage into a hard compile failure.
    static bool validateKnownStateValue(AstNode* nodep, const FsmStateSpace& stateSpace,
                                        const FsmStateValue& value, const string& role) {
        if (stateSpace.labels.find(value) != stateSpace.labels.end()) return true;
        if (stateSpace.enumBacked) {
            const string enumRole = role == "source" ? "case item value" : "assigned value";
            nodep->v3warn(COVERIGN, "Ignoring unsupported: FSM coverage on enum state variable "
                                        + stateSpace.stateVarp->prettyNameQ() + ": " + enumRole
                                        + " " + value.warnText()
                                        + " is not present in the declared enum");
            return false;
        }
        nodep->v3warn(COVERIGN, "Ignoring unsupported: FSM coverage on non-enum state variable "
                                    + stateSpace.stateVarp->prettyNameQ() + ": " + role + " value "
                                    + value.warnText()
                                    + " is not present in the inferred state space");
        return false;
    }

    static StateConstLabel stateLabelForConst(AstConst* constp) {
        const string name = constp->origParamName();
        if (!name.empty()) return StateConstLabel{AstNode::prettyName(name), true, 0};
        return StateConstLabel{constp->name(), false, 0};
    }

    static void updateStateLabel(FsmStateSpace& stateSpace, const FsmStateValue& value,
                                 const StateConstLabel& label) {
        stateSpace.states.at(stateSpace.labels.at(value).stateIndex).first = label.text;
    }

    // Strict Phase 1 matcher for register processes: either a bare state
    // commit, or a top-level reset guard whose else path is that commit.
    static bool matchRegisterAlways(AstAlways* alwaysp, AstScope* scopep,
                                    FsmRegisterCandidate& cand) {
        if (!alwaysp->sentreep() || !alwaysp->sentreep()->hasEdge()) return false;

        AstNode* const stmtsp = skipLeadingIgnorableStmt(alwaysp->stmtsp());
        AstNode* const nodep = singleMeaningfulStmt(stmtsp);
        if (!nodep) return false;

        AstVarScope* stateVscp = nullptr;
        AstVarScope* nextVscp = nullptr;
        if (AstIf* const ifp = VN_CAST(nodep, If)) {
            if (!ifp->elsesp() || !isSimpleResetCond(ifp->condp())) return false;
            AstVarScope* resetStateVscp = nullptr;
            const ResetAssignStatus resetStatus
                = collectConstStateAssigns(ifp->thensp(), resetStateVscp, cand.resetArcs());
            if (resetStatus == ResetAssignStatus::NONE) {
                cand.resetArcs().clear();
                FsmStateValue resetValue;
                AstNode* const thenNodep = singleMeaningfulBranch(ifp->thensp());
                UASSERT_OBJ(thenNodep, ifp, "reset fallback requires a non-empty reset branch");
                AstNodeAssign* const resetAssp
                    = directConstStateAssignNode(thenNodep, resetStateVscp, resetValue);
                if (!resetAssp) return false;
                cand.resetArcs().emplace_back(resetValue, resetAssp);
            } else if (resetStatus == ResetAssignStatus::MULTI_SAME_STATE) {
                cand.resetArcs().clear();
            }
            AstNode* const elseNodep = singleMeaningfulBranch(ifp->elsesp());
            UASSERT_OBJ(elseNodep, ifp, "register reset match requires a non-empty commit branch");
            if (!nodeStateVarAssign(elseNodep, stateVscp, nextVscp)) return false;
            if (resetStateVscp != stateVscp) return false;
            cand.resetCond() = describeResetCond(ifp->condp());
            cand.hasResetCond(cand.resetCond().varScopep != nullptr);
        } else {
            AstNodeExpr* resetCondp = nullptr;
            bool resetActiveLow = false;
            FsmStateValue resetValue;
            if (AstNodeAssign* const assp
                = directCondStateVarAssign(nodep, stateVscp, nextVscp, resetCondp, resetActiveLow,
                                           resetValue)) {
                // Inlined wrappers can normalize into a compact active-low
                // assignment form that earlier direct-register FSM support did
                // not accept. The pre-inline marker is the architectural fence:
                // it lets wrapper-derived registers use that shape without
                // changing the meaning of unrelated legacy RTL.
                if (resetActiveLow && !stateVscp->varp()->attrFsmRegisterWrapper()) return false;
                cand.resetArcs().emplace_back(resetValue, assp);
                cand.resetCond() = describeResetCond(resetCondp);
                cand.resetCond().activeLow = resetActiveLow;
                cand.hasResetCond(cand.resetCond().varScopep != nullptr);
            } else if (!nodeStateVarAssign(nodep, stateVscp, nextVscp)) {
                return false;
            }
        }
        cand.scopep(scopep);
        cand.alwaysp(alwaysp);
        cand.stateVscp(stateVscp);
        cand.nextVscp(nextVscp);
        cand.senses() = describeSenTree(alwaysp->sentreep());
        cand.resetInclude(stateVscp->varp()->attrFsmResetArc());
        cand.inclCond(stateVscp->varp()->attrFsmArcInclCond());
        cand.fileline(alwaysp->fileline());
        return true;
    }

    static bool addValueToStateSpace(AstNode* nodep, FsmStateSpace& stateSpace,
                                     const FsmStateValue& value, StateConstLabel label) {
        const auto labelIt = stateSpace.labels.find(value);
        if (labelIt != stateSpace.labels.end()) {
            StateConstLabel& existingLabel = labelIt->second;
            if (existingLabel.text != label.text && existingLabel.fromParam && label.fromParam) {
                nodep->v3warn(COVERIGN, "Ignoring unsupported: FSM coverage on non-enum "
                                        "state variable "
                                            + stateSpace.stateVarp->prettyNameQ()
                                            + " with multiple labels for the same value "
                                            + value.warnText() + ": " + existingLabel.text
                                            + " and " + label.text);
                return false;
            }
            if (!existingLabel.fromParam && label.fromParam) {
                existingLabel.text = label.text;
                existingLabel.fromParam = label.fromParam;
                updateStateLabel(stateSpace, value, label);
            }
        } else {
            StateConstLabel storedLabel = label;
            storedLabel.stateIndex = stateSpace.states.size();
            stateSpace.states.emplace_back(label.text, value);
            stateSpace.labels.emplace(value, storedLabel);
        }
        return true;
    }

    // Helper: process a single observed state expression and add it to the state space
    // Returns true on success, false if the state space is invalid
    static bool addExprToStateSpace(AstNodeExpr* valuep, FsmStateSpace& stateSpace) {
        FsmStateValue value;
        const ConstValueStatus status = constValueStatus(valuep, value);
        if (status != ConstValueStatus::OK) {
            if (status == ConstValueStatus::XZ) {
                valuep->v3warn(COVERIGN, "Ignoring unsupported: FSM coverage on non-enum "
                                         "state variable "
                                             + stateSpace.stateVarp->prettyNameQ()
                                             + " with X/Z state encoding values");
            }
            return false;
        }
        AstConst* const constp = VN_AS(valuep, Const);
        return addValueToStateSpace(valuep, stateSpace, value, stateLabelForConst(constp));
    }

    static bool addOptionalTargetExprToStateSpace(AstNodeExpr* valuep, FsmStateSpace& stateSpace) {
        FsmStateValue value;
        const ConstValueStatus status = constValueStatus(valuep, value);
        if (status != ConstValueStatus::OK) {
            valuep->v3warn(COVERIGN, "Ignoring unsupported: FSM coverage on non-enum "
                                     "state variable "
                                         + stateSpace.stateVarp->prettyNameQ()
                                         + " with non-constant target state values");
            return false;
        }
        AstConst* const constp = VN_AS(valuep, Const);
        return addValueToStateSpace(valuep, stateSpace, value, stateLabelForConst(constp));
    }

    static void addResetTargetsToStateSpace(const std::vector<FsmResetArcDesc>& resetArcs,
                                            FsmStateSpace& stateSpace) {
        for (const FsmResetArcDesc& resetArc : resetArcs) {
            StateConstLabel label{resetArc.toValue().ascii(), false, 0};
            if (AstConst* const constp = VN_CAST(resetArc.valuep(), Const)) {
                label = stateLabelForConst(constp);
            }
            UASSERT_OBJ(
                addValueToStateSpace(resetArc.nodep(), stateSpace, resetArc.toValue(), label),
                resetArc.nodep(), "reset target labels should be unambiguous");
        }
    }

    // Build the Phase 1 state space from the tracked registered state
    // variable, not from whichever signal the transition statement happened to use.
    static bool collectDeclaredStateSpace(AstNode* warnNodep, AstVarScope* stateVscp,
                                          FsmStateSpace& stateSpace, bool& needsSourceValues) {
        AstVar* const stateVarp = stateVscp->varp();
        AstEnumDType* enump = VN_CAST(unwrapEnumCandidate(stateVscp->dtypep()), EnumDType);
        if (!enump) enump = VN_CAST(unwrapEnumCandidate(stateVarp->dtypep()), EnumDType);
        const bool forced = stateVarp->attrFsmState();
        stateSpace.stateVarp = stateVarp;

        if (enump) {
            stateSpace.enumBacked = true;
            for (AstEnumItem* itemp = enump->itemsp(); itemp;
                 itemp = VN_AS(itemp->nextp(), EnumItem)) {
                const AstConst* const constp = VN_AS(itemp->valuep(), Const);
                const FsmStateValue value{constp->num()};
                const size_t stateIndex = stateSpace.states.size();
                stateSpace.states.emplace_back(itemp->name(), value);
                stateSpace.labels.emplace(value,
                                          StateConstLabel{itemp->name(), false, stateIndex});
            }
            return stateSpace.states.size() >= 2;
        }

        if (forced) {
            needsSourceValues = true;
            return true;
        }

        needsSourceValues = true;
        return true;
    }

    template <typename T_ValuepVisitor>
    static bool collectStateSpaceFromValues(AstNode* warnNodep, AstVarScope* stateVscp,
                                            const std::vector<FsmResetArcDesc>& resetArcs,
                                            FsmStateSpace& stateSpace,
                                            const T_ValuepVisitor& visitValueps) {
        bool needsSourceValues = false;
        // Cases and if-chains should share the same state-space policy; only
        // the source of inferred literal values differs between the forms.
        if (!collectDeclaredStateSpace(warnNodep, stateVscp, stateSpace, needsSourceValues)) {
            return false;
        }
        if (!needsSourceValues) return true;
        addResetTargetsToStateSpace(resetArcs, stateSpace);
        if (!visitValueps(
                [&](AstNodeExpr* valuep) { return addExprToStateSpace(valuep, stateSpace); })) {
            return false;
        }
        return stateSpace.states.size() >= 2;
    }

    static bool collectStateSpace(AstCase* casep, AstVarScope* stateVscp, AstVarScope* assignVscp,
                                  const std::vector<FsmResetArcDesc>& resetArcs,
                                  FsmStateSpace& stateSpace) {
        return collectStateSpaceFromValues(
            casep, stateVscp, resetArcs, stateSpace,
            [casep, assignVscp, &stateSpace](const auto& visitValuep) {
                for (AstCaseItem* itemp = casep->itemsp(); itemp;
                     itemp = VN_AS(itemp->nextp(), CaseItem)) {
                    if (!itemp->isDefault()) {
                        for (AstNodeExpr* condp = itemp->condsp(); condp;
                             condp = VN_AS(condp->nextp(), NodeExpr)) {
                            if (!visitValuep(condp)) return false;
                        }
                    }
                    if (AstNodeAssign* const assp
                        = directStateAssign(itemp->stmtsp(), assignVscp)) {
                        FsmStateValue thenValue;
                        FsmStateValue elseValue;
                        AstCond* const condp = VN_CAST(assp->rhsp(), Cond);
                        if (condp
                            && directStateCondConstAssign(itemp->stmtsp(), assignVscp, thenValue,
                                                          elseValue)) {
                            if (!visitValuep(condp->thenp())) return false;
                            if (!visitValuep(condp->elsep())) return false;
                        } else if (!addOptionalTargetExprToStateSpace(assp->rhsp(), stateSpace)) {
                            return false;
                        }
                    }
                }
                return true;
            });
    }

    static bool collectStateSpace(const FsmIfChainCandidate& chain, AstVarScope* stateVscp,
                                  AstVarScope* assignVscp,
                                  const std::vector<FsmResetArcDesc>& resetArcs,
                                  FsmStateSpace& stateSpace) {
        return collectStateSpaceFromValues(
            chain.ifp, stateVscp, resetArcs, stateSpace,
            [&chain, assignVscp, &stateSpace](const auto& visitValuep) {
                for (const FsmIfBranch& branch : chain.branches) {
                    // Reaching this point with an unresolvable source value
                    // would mean the if-chain classifier and emitter disagree.
                    UASSERT_OBJ(visitValuep(branch.valuep), branch.valuep,
                                "FSM if-chain source values should be prevalidated");
                    AstNodeAssign* const assp = directStateAssign(branch.stmtsp, assignVscp);
                    UASSERT_OBJ(assp, branch.stmtsp,
                                "FSM if-chain target values should be prevalidated");
                    FsmStateValue thenValue;
                    FsmStateValue elseValue;
                    AstCond* const condp = VN_CAST(assp->rhsp(), Cond);
                    if (condp) {
                        UASSERT_OBJ(directStateCondConstAssign(branch.stmtsp, assignVscp,
                                                               thenValue, elseValue),
                                    condp, "FSM if-chain ternary targets should be prevalidated");
                        if (!visitValuep(condp->thenp())) return false;
                        if (!visitValuep(condp->elsep())) return false;
                    } else if (!addOptionalTargetExprToStateSpace(assp->rhsp(), stateSpace)) {
                        return false;
                    }
                }
                return true;
            });
    }

    // Extract supported case-item transitions in one place so the conservative
    // policy for direct and ternary forms stays consistent. The false exits in
    // this helper are deliberate subset boundaries: they document shapes we do
    // not yet model in this PR and that future FSM-detection work may widen.
    static bool emitCaseItemArcs(FsmGraph& graph, AstCaseItem* itemp, AstVarScope* stateVscp,
                                 const FsmStateSpace& stateSpace, bool inclCond) {
        std::vector<std::pair<string, FsmStateValue>> froms;
        if (itemp->isDefault()) {
            if (!inclCond) return false;
            froms.emplace_back("default", FsmStateValue{});
        } else {
            for (AstNodeExpr* condp = itemp->condsp(); condp;
                 condp = VN_AS(condp->nextp(), NodeExpr)) {
                FsmStateValue value;
                if (constValueStatus(condp, value) != ConstValueStatus::OK) continue;
                if (!validateKnownStateValue(condp, stateSpace, value, "source")) return true;
                froms.emplace_back(labelForValue(stateSpace.labels, value), value);
            }
            if (froms.empty()) return false;
        }

        if (AstNodeAssign* const assp = directStateAssign(itemp->stmtsp(), stateVscp)) {
            FsmStateValue toValue;
            const ConstValueStatus status = constValueStatus(assp->rhsp(), toValue);
            if (status == ConstValueStatus::OK) {
                if (!validateKnownStateValue(assp, stateSpace, toValue, "target")) return true;
                for (const std::pair<string, FsmStateValue>& from : froms) {
                    graph.addArc(from.second, toValue, false, false, itemp->isDefault(),
                                 assp->fileline());
                }
                return true;
            }
        }

        FsmStateValue thenValue;
        FsmStateValue elseValue;
        if (directStateCondConstAssign(itemp->stmtsp(), stateVscp, thenValue, elseValue)
            || ifStateConstAssign(itemp->stmtsp(), stateVscp, thenValue, elseValue)) {
            if (!validateKnownStateValue(itemp->stmtsp(), stateSpace, thenValue, "target"))
                return true;
            if (!validateKnownStateValue(itemp->stmtsp(), stateSpace, elseValue, "target"))
                return true;
            for (const FsmStateValue& branchValue : {thenValue, elseValue}) {
                for (const std::pair<string, FsmStateValue>& from : froms) {
                    graph.addArc(from.second, branchValue, false, true, itemp->isDefault(),
                                 itemp->stmtsp()->fileline());
                }
            }
            return true;
        }

        return false;
    }

    static void emitStmtArcsFrom(FsmGraph& graph, AstNode* stmtsp, AstVarScope* stateVscp,
                                 const FsmStateSpace& stateSpace, FsmStateValue fromValue,
                                 bool isDefault, bool forceCond) {
        AstNodeAssign* const assp = directStateAssign(stmtsp, stateVscp);
        UASSERT_OBJ(assp, stmtsp, "FSM if-chain branch should have been prevalidated");
        FsmStateValue toValue;
        const ConstValueStatus status = constValueStatus(assp->rhsp(), toValue);
        if (status == ConstValueStatus::OK) {
            if (!validateKnownStateValue(assp, stateSpace, toValue, "target")) return;
            // Preserve the user's guard in coverage by marking this arc
            // conditional even when the branch body is a direct assignment.
            graph.addArc(fromValue, toValue, false, forceCond, isDefault, assp->fileline());
            return;
        }

        FsmStateValue thenValue;
        FsmStateValue elseValue;
        const bool condAssign
            = directStateCondConstAssign(stmtsp, stateVscp, thenValue, elseValue);
        UASSERT_OBJ(condAssign, stmtsp,
                    "FSM if-chain branch should be a direct constant transition");
        if (!validateKnownStateValue(stmtsp, stateSpace, thenValue, "target")) return;
        if (!validateKnownStateValue(stmtsp, stateSpace, elseValue, "target")) return;
        for (const FsmStateValue& branchValue : {thenValue, elseValue}) {
            graph.addArc(fromValue, branchValue, false, true, isDefault, stmtsp->fileline());
        }
    }

    static void emitIfChainArcs(FsmGraph& graph, const FsmIfChainCandidate& chain,
                                AstVarScope* stateVscp, const FsmStateSpace& stateSpace) {
        for (size_t i = 0; i < chain.branches.size(); ++i) {
            const FsmIfBranch& branch = chain.branches[i];
            // Invalid source labels mean the extracted graph would no longer
            // match the resolved state space, so abandon the candidate.
            if (!validateKnownStateValue(branch.ifp, stateSpace, branch.fromValue, "source"))
                return;
            emitStmtArcsFrom(graph, branch.stmtsp, stateVscp, stateSpace, branch.fromValue, false,
                             branch.hasTopGuard);
        }
    }

    // Reset transitions are described separately because they live in the reset
    // branch outside the steady-state case statement.
    static void addResetArcs(FsmGraph& graph, const std::vector<FsmResetArcDesc>& resetArcs,
                             const FsmStateSpace& stateSpace) {
        for (const FsmResetArcDesc& resetArc : resetArcs) {
            if (!validateKnownStateValue(resetArc.nodep(), stateSpace, resetArc.toValue(),
                                         "target"))
                continue;
            graph.addArc(FsmStateValue{}, resetArc.toValue(), true, false, false,
                         resetArc.nodep()->fileline());
        }
    }

    // Turn one candidate case statement into the graph representation that the
    // later lowering phase will consume directly, while reviewers can still
    // inspect the extracted machine via DOT dumps.
    void processCase(AstCase* casep, AstVarScope* assignVscp, const FsmRegisterCandidate& reg) {
        UASSERT_OBJ(assignVscp, casep, "FSM case processing requires a non-null assignment var");
        AstVarScope* const stateVscp = reg.stateVscp();
        FsmStateSpace stateSpace;
        if (!collectStateSpace(casep, stateVscp, assignVscp, reg.resetArcs(), stateSpace)) return;
        DetectedFsm& entry = m_state.fsmFor(stateVscp);
        if (!entry.graphp) {
            entry.graphp.reset(new FsmGraph{});
            entry.graphp->scopep(reg.scopep());
            entry.graphp->stateAlwaysp(reg.alwaysp());
            entry.graphp->stateVarName(stateVscp->prettyName());
            entry.graphp->stateVarInternalName(stateVscp->varp()->name());
            entry.graphp->stateVarScopep(stateVscp);
            entry.graphp->senses() = reg.senses();
            entry.graphp->resetCond() = reg.resetCond();
            entry.graphp->hasResetCond(reg.hasResetCond());
            entry.graphp->resetInclude(reg.resetInclude());
            entry.graphp->inclCond(reg.inclCond());
            entry.graphp->fileline(casep->fileline());
            for (const std::pair<string, FsmStateValue>& state : stateSpace.states) {
                entry.graphp->addStateVertex(state.first, state.second);
            }
            addResetArcs(*entry.graphp, reg.resetArcs(), stateSpace);
        }
        for (AstCaseItem* itemp = casep->itemsp(); itemp;
             itemp = VN_AS(itemp->nextp(), CaseItem)) {
            emitCaseItemArcs(*entry.graphp, itemp, assignVscp, stateSpace,
                             entry.graphp->inclCond());
        }
    }

    void processIfChain(const FsmIfChainCandidate& chain, AstVarScope* assignVscp,
                        const FsmRegisterCandidate& reg) {
        UASSERT_OBJ(assignVscp, chain.ifp,
                    "FSM if-chain processing requires a non-null assignment var");
        AstVarScope* const stateVscp = reg.stateVscp();
        FsmStateSpace stateSpace;
        if (!collectStateSpace(chain, stateVscp, assignVscp, reg.resetArcs(), stateSpace)) return;
        DetectedFsm& entry = m_state.fsmFor(stateVscp);
        // Case candidates keep ownership of existing graphs; reaching this path
        // means the if-chain is the only supported dispatch for this FSM.
        UASSERT_OBJ(!entry.graphp, chain.ifp, "FSM if-chain graph should not already exist");
        entry.graphp.reset(new FsmGraph{});
        entry.graphp->scopep(reg.scopep());
        entry.graphp->stateAlwaysp(reg.alwaysp());
        entry.graphp->stateVarName(stateVscp->prettyName());
        entry.graphp->stateVarInternalName(stateVscp->varp()->name());
        entry.graphp->stateVarScopep(stateVscp);
        entry.graphp->senses() = reg.senses();
        entry.graphp->resetCond() = reg.resetCond();
        entry.graphp->hasResetCond(reg.hasResetCond());
        entry.graphp->resetInclude(reg.resetInclude());
        entry.graphp->inclCond(reg.inclCond());
        entry.graphp->fileline(chain.ifp->fileline());
        for (const std::pair<string, FsmStateValue>& state : stateSpace.states) {
            entry.graphp->addStateVertex(state.first, state.second);
        }
        addResetArcs(*entry.graphp, reg.resetArcs(), stateSpace);
        emitIfChainArcs(*entry.graphp, chain, assignVscp, stateSpace);
    }

    // Find the first supported FSM candidate in a clocked always block, warn on
    // additional candidates, and attach reset arcs when present. Candidate
    // filtering stays narrow on purpose: we prefer to skip ambiguous shapes now
    // and expand detection in a later PR rather than over-infer coverage from
    // forms we do not yet model confidently.
    void processOneBlockAlways(const FsmComboAlways& oneBlock) {
        const RegisterAlwaysAnalyzer analyzer{oneBlock.scopep()};
        AstAlways* const alwaysp = oneBlock.alwaysp();
        if (!alwaysp->sentreep() || !alwaysp->sentreep()->hasEdge()) return;
        const std::vector<std::pair<AstCase*, AstNodeExpr*>> candidates
            = analyzer.oneBlockCandidates(alwaysp);

        FsmCaseCandidate firstCand;
        for (const std::pair<AstCase*, AstNodeExpr*>& cand : candidates) {
            AstVarRef* const selp = VN_CAST(cand.first->exprp(), VarRef);
            AstVarScope* const vscp = selp ? selp->varScopep() : nullptr;
            if (!vscp) continue;
            if (!firstCand.stateVscp) {
                firstCand.warnNodep = cand.first;
                firstCand.stateVscp = vscp;
                FsmRegisterCandidate reg;
                analyzer.buildOneBlockCandidate(alwaysp, vscp, cand.second, reg);
                processCase(cand.first, vscp, reg);
            } else if (vscp != firstCand.stateVscp) {
                cand.first->v3warn(FSMMULTI,
                                   "FSM coverage: multiple enum-typed case statements found in "
                                   "the same always block. Only the first candidate will be "
                                   "instrumented."
                                       << candidateConflictContext(cand.first, firstCand));
            } else {
                cand.first->v3warn(COVERIGN,
                                   "Ignoring unsupported: FSM coverage on multiple supported case "
                                   "statements found in the same always block. Only the first "
                                   "candidate will be instrumented."
                                       << candidateConflictContext(cand.first, firstCand));
            }
        }

        if (firstCand.stateVscp) return;

        // Case dispatch is more explicit and pre-existing behavior depends on
        // it winning when both shapes are present.
        const std::vector<std::pair<AstIf*, AstNodeExpr*>> ifCandidates
            = analyzer.oneBlockIfCandidates(alwaysp);
        for (const std::pair<AstIf*, AstNodeExpr*>& cand : ifCandidates) {
            const FsmAliasMap aliases = localAliasesBefore(alwaysp->stmtsp(), cand.first);
            FsmIfChainCandidate chain;
            if (!collectIfChain(cand.first, aliases, chain)) continue;
            AstVarScope* const vscp = chain.compareVscp;
            if (!ifChainSupportedTransitionNode(chain, vscp)) continue;
            if (!firstCand.stateVscp) {
                firstCand.warnNodep = cand.first;
                firstCand.stateVscp = vscp;
                FsmRegisterCandidate reg;
                analyzer.buildOneBlockCandidate(alwaysp, vscp, cand.second, reg);
                processIfChain(chain, vscp, reg);
            } else if (vscp != firstCand.stateVscp) {
                cand.first->v3warn(FSMMULTI,
                                   "FSM coverage: multiple enum-typed transition candidates found "
                                   "in the same always block. Only the first candidate will be "
                                   "instrumented."
                                       << candidateConflictContext(cand.first, firstCand));
            } else {
                cand.first->v3warn(COVERIGN,
                                   "Ignoring unsupported: FSM coverage on multiple supported "
                                   "transition candidates found in the same always block. Only "
                                   "the first candidate will be instrumented."
                                       << candidateConflictContext(cand.first, firstCand));
            }
        }
    }

    // Phase 1 two-process pairing scans combinational always blocks only after
    // all strict register candidates have been collected, so source order does
    // not matter.
    static void warnComboSameAlways(AstNode* warnNodep, const FsmCaseCandidate& firstCand) {
        warnNodep->v3warn(FSMMULTI,
                          "FSM coverage: multiple supported transition candidates found in "
                          "the same combinational always block. Only the first candidate "
                          "will be instrumented."
                              << candidateConflictContext(warnNodep, firstCand));
    }

    void processComboAlways(const FsmComboAlways& combo) {
        const ComboAlwaysAnalyzer analyzer{m_registerCandidates};
        AstNode* const stmtsp = skipLeadingIgnorableStmt(combo.alwaysp()->stmtsp());
        FsmCaseCandidate firstCand;
        for (AstNode* nodep = stmtsp; nodep; nodep = nodep->nextp()) {
            AstCase* const casep = VN_CAST(nodep, Case);
            if (!casep) continue;
            const ComboAlwaysAnalyzer::ComboMatch match = analyzer.matchCase(stmtsp, casep);
            const FsmRegisterCandidate* const matchedp = match.matchedp;
            AstNode* const matchedWarnNodep = match.warnNodep;
            if (!matchedp) continue;
            if (!firstCand.stateVscp) {
                const auto insertPair = m_comboPaired.emplace(
                    matchedp->stateVscp(),
                    FsmCaseCandidate{matchedWarnNodep,
                                     const_cast<AstVarScope*>(matchedp->stateVscp())});
                if (!insertPair.second) {
                    matchedWarnNodep->v3warn(
                        FSMMULTI, "FSM coverage: multiple supported transition candidates found "
                                  "for the same FSM in combinational always blocks. Only the "
                                  "first candidate will be instrumented."
                                      << candidateConflictContext(matchedWarnNodep,
                                                                  insertPair.first->second));
                    continue;
                }
                firstCand.warnNodep = matchedWarnNodep;
                firstCand.stateVscp = const_cast<AstVarScope*>(matchedp->stateVscp());
                processCase(casep, matchedp->nextVscp(), *matchedp);
                continue;
            }
            if (matchedp->stateVscp() != firstCand.stateVscp) {
                warnComboSameAlways(matchedWarnNodep, firstCand);
                continue;
            }
            matchedWarnNodep->v3warn(COVERIGN,
                                     "Ignoring unsupported: FSM coverage on multiple "
                                     "supported case statements found in the same "
                                     "combinational always block. Only the first "
                                     "candidate will be instrumented."
                                         << candidateConflictContext(matchedWarnNodep, firstCand));
        }
        if (firstCand.stateVscp) return;

        // Keep the same priority in paired combinational logic: if-chain
        // support must not change which existing case FSM is instrumented.
        for (AstNode* nodep = stmtsp; nodep; nodep = nodep->nextp()) {
            AstIf* const ifp = VN_CAST(nodep, If);
            if (!ifp) continue;
            FsmIfChainCandidate chain;
            const FsmAliasMap aliases = localAliasesBefore(stmtsp, nodep);
            if (!collectIfChain(ifp, aliases, chain)) continue;
            const ComboAlwaysAnalyzer::ComboMatch match = analyzer.matchIfChain(stmtsp, chain);
            const FsmRegisterCandidate* const matchedp = match.matchedp;
            AstNode* const matchedWarnNodep = match.warnNodep;
            if (!matchedp) continue;
            if (!firstCand.stateVscp) {
                const std::pair<std::unordered_map<const AstVarScope*, FsmCaseCandidate>::iterator,
                                bool>
                    insertPair = m_comboPaired.emplace(
                        matchedp->stateVscp(),
                        FsmCaseCandidate{matchedWarnNodep,
                                         const_cast<AstVarScope*>(matchedp->stateVscp())});
                if (!insertPair.second) {
                    matchedWarnNodep->v3warn(
                        FSMMULTI, "FSM coverage: multiple supported transition candidates found "
                                  "for the same FSM in combinational always blocks. Only the "
                                  "first candidate will be instrumented."
                                      << candidateConflictContext(matchedWarnNodep,
                                                                  insertPair.first->second));
                    continue;
                }
                firstCand.warnNodep = matchedWarnNodep;
                firstCand.stateVscp = const_cast<AstVarScope*>(matchedp->stateVscp());
                processIfChain(chain, matchedp->nextVscp(), *matchedp);
                continue;
            }
            if (matchedp->stateVscp() != firstCand.stateVscp) {
                warnComboSameAlways(matchedWarnNodep, firstCand);
                continue;
            }
            matchedWarnNodep->v3warn(COVERIGN,
                                     "Ignoring unsupported: FSM coverage on multiple "
                                     "supported if-chain statements found in the same "
                                     "combinational always block. Only the first "
                                     "candidate will be instrumented."
                                         << candidateConflictContext(matchedWarnNodep, firstCand));
        }
    }

    // Track the current scope so each detected FSM records the module/scope
    // where instrumentation must later be inserted.
    void visit(AstScope* nodep) override {
        VL_RESTORER(m_scopep);
        m_scopep = nodep;
        iterateChildren(nodep);
    }

    // Collect processes first, then analyze FSM candidates once all alias and
    // register information is available.
    void visit(AstAlways* nodep) override {
        if (nodep->keyword() == VAlwaysKwd::CONT_ASSIGN) {
            iterateChildren(nodep);
            return;
        }
        // This avoids making one-block if-chain detection sensitive to whether
        // a continuous alias appears before or after the always block.
        m_oneBlockAlwayss.emplace_back(m_scopep, nodep);
        const RegisterAlwaysAnalyzer analyzer{m_scopep};
        FsmRegisterCandidate reg;
        if (analyzer.matchRegisterCandidate(nodep, reg)) {
            AstVarScope* const stateVscp = reg.stateVscp();
            const bool found
                = std::any_of(m_registerCandidates.cbegin(), m_registerCandidates.cend(),
                              [stateVscp](const FsmRegisterCandidate& existing) {
                                  return existing.stateVscp() == stateVscp;
                              });
            if (!found) { m_registerCandidates.emplace_back(reg); }
        }
        if (nodep->keyword() == VAlwaysKwd::ALWAYS_COMB) {
            m_comboAlwayss.emplace_back(m_scopep, nodep);
        } else if (nodep->keyword() == VAlwaysKwd::ALWAYS) {
            if (!nodep->sentreep() || isPlainComboSentree(nodep->sentreep())) {
                m_comboAlwayss.emplace_back(m_scopep, nodep);
            } else {
                m_nonComboAlwayss.emplace_back(m_scopep, nodep);
            }
        }
    }

    void visit(AstAssignW* nodep) override {
        // Continuous aliases are unordered hardware connections, so source
        // order should not affect whether an if-chain FSM is recognized.
        collectAliasFromAssign(nodep, m_stateAliases, m_ambiguousStateAliases);
        collectCellPortAlias(nodep);
        iterateChildren(nodep);
    }

    void visit(AstCell* nodep) override {
        // Cells are matched after the full traversal because linkdot lowers
        // uninlined port connections into sibling continuous assignments.
        if (m_scopep && fsmRegisterWrapperDesc(nodep)) addWrapperCell(m_scopep, nodep);
        iterateChildren(nodep);
    }

    // Continue the walk through the rest of the design hierarchy.
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    // Collect all FSM graphs into the shared local state before the lowering
    // phase starts mutating the AST with coverage machinery.
    FsmDetectVisitor(FsmState& state, AstNetlist* rootp)
        : m_state{state} {
        iterate(rootp);
        for (const std::pair<AstScope*, AstCell*>& wrapperCell : m_wrapperCells) {
            FsmRegisterCandidate reg;
            if (matchFsmWrapperCell(wrapperCell.first, wrapperCell.second, reg)) {
                m_registerCandidates.emplace_back(reg);
            }
        }
        for (const FsmComboAlways& oneBlock : m_oneBlockAlwayss) processOneBlockAlways(oneBlock);
        for (const FsmComboAlways& combo : m_comboAlwayss) processComboAlways(combo);
        for (const FsmComboAlways& combo : m_nonComboAlwayss) warnUnsupportedComboAlways(combo);
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
    static AstConst* makeStateConst(FileLine* flp, AstVarScope* vscp, const FsmStateValue& value) {
        V3Number num{static_cast<AstNode*>(nullptr), vscp->width()};
        num.opAssign(value.num());
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
                                       const FsmResetCondDesc& desc) {
        AstNodeExpr* const refp = new AstVarRef{flp, resetVscp, VAccess::READ};
        return desc.activeLow ? static_cast<AstNodeExpr*>(new AstLogNot{flp, refp}) : refp;
    }

    // Rebuild the original event control from the saved sense description so
    // post-state coverage sampling runs on the same triggering edges.
    static AstSenTree* buildSenTree(FileLine* flp, const std::vector<FsmSenDesc>& senses) {
        AstSenTree* const sentreep = new AstSenTree{flp, nullptr};
        for (const FsmSenDesc& sense : senses) {
            AstSenItem* const senItemp
                = new AstSenItem{flp, VEdgeType{sense.edgeType},
                                 new AstVarRef{flp, sense.varScopep, VAccess::READ}};
            sentreep->addSensesp(senItemp);
        }
        return sentreep;
    }

    // Lower one fully detected FSM graph into the concrete coverage machinery
    // used by generated models: declarations, previous-state tracking, and the
    // pre/post-triggered increment logic for states and arcs.
    void buildOne(const FsmGraph& graph) {
        UINFO(1, "buildOne lowering FSM " << graph.stateVarName()
                                          << " vertices=" << graph.vertices().size() << endl);
        AstAlways* const alwaysp = graph.stateAlwaysp();
        AstScope* const scopep = graph.scopep();
        AstVarScope* const stateVscp = graph.stateVarScopep();
        FileLine* const flp = graph.fileline();
        AstNodeModule* const modp = scopep->modp();
        AstNodeDType* const prevDTypep = scopep->findLogicDType(
            stateVscp->width(), stateVscp->width(), stateVscp->dtypep()->numeric());
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
        bool updatePrevAfterPost = false;
        if (alwaysp) {
            // Save the previous state as plain sequential logic at the front of
            // the original always_ff body, then evaluate coverage in post logic
            // after the delayed state update commits. This avoids a scheduler
            // race between a separate AstAlwaysPre task and the real state
            // commit for direct parent-level registers.
            AstNode* const bodysp = alwaysp->stmtsp()->unlinkFrBackWithNext();
            alwaysp->addStmtsp(new AstAssign{flp, new AstVarRef{flp, prevVscp, VAccess::WRITE},
                                             new AstVarRef{flp, stateVscp, VAccess::READ}});
            alwaysp->addStmtsp(bodysp);
        } else {
            // Wrapper-derived register candidates do not have a parent
            // always_ff body to splice into. Sample coverage first, then save
            // the current state for the next clock tick; this survives cell
            // boundary scheduling where the real flop update lives elsewhere.
            updatePrevAfterPost = true;
            prevVscp->varp()->setIgnorePostRead();
        }

        for (const V3GraphVertex& vtx : graph.vertices()) {
            const FsmVertex* const vertexp = vtx.as<FsmVertex>();
            if (!vertexp->isState()) continue;
            const FsmStateVertex* const statep = vtx.as<FsmStateVertex>();
            // State coverage fires when the FSM enters a state from any other
            // value, so repeated self-holds do not count as new entries.
            AstCoverOtherDecl* const declp
                = new AstCoverOtherDecl{flp,
                                        "v_fsm_state/" + modp->prettyName(),
                                        graph.stateVarName() + "::" + statep->label(),
                                        "",
                                        0,
                                        graph.stateVarName(),
                                        "",
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
                    = arcp->isReset() ? (graph.resetInclude() ? "[reset_include]" : "[reset]")
                                      : "";
                const string fsmTag = arcp->isReset()
                                          ? (graph.resetInclude() ? "reset_include" : "reset")
                                      : arcp->isDefault() ? "default"
                                                          : "";
                AstCoverOtherDecl* const declp
                    = new AstCoverOtherDecl{flp,
                                            "v_fsm_arc/" + modp->prettyName(),
                                            graph.stateVarName() + "::" + fromVertexp->label()
                                                + "->" + toStatep->label() + resetTag,
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
                    guardp
                        = andExpr(flp,
                                  new AstEq{flp, new AstVarRef{flp, prevVscp, VAccess::READ},
                                            makeStateConst(flp, prevVscp, fromVertexp->value())},
                                  new AstEq{flp, new AstVarRef{flp, stateVscp, VAccess::READ},
                                            makeStateConst(flp, stateVscp, toStatep->value())});
                }
                covPostp->addStmtsp(new AstIf{flp, guardp, new AstCoverInc{flp, declp}});
            }
        }
        if (updatePrevAfterPost) {
            covPostp->addStmtsp(new AstAssign{flp, new AstVarRef{flp, prevVscp, VAccess::WRITE},
                                              new AstVarRef{flp, stateVscp, VAccess::READ}});
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
        for (const DetectedFsm& fsm : m_state.fsms()) { buildOne(*fsm.graphp); }
    }
};

// Wrapper FSM support has two architectural paths. If V3Inline removes the
// wrapper, the main detector will later see an ordinary parent-scope always_ff;
// this pre-inline visitor leaves just enough provenance on the q-side state
// variable for that direct path to accept wrapper-specific normalized shapes.
// If the wrapper survives, this marker is harmless and the cell-path detector
// builds a register candidate from the instance itself.
class FsmWrapperMarkerVisitor final : public VNVisitor {
    static AstPin* findPin(AstCell* cellp, const string& name) {
        for (AstPin* pinp = cellp->pinsp(); pinp; pinp = VN_AS(pinp->nextp(), Pin)) {
            if (pinp->name() == name) return pinp;
        }
        return nullptr;
    }

    void visit(AstCell* cellp) override {
        if (const V3Control::FsmRegisterWrapper* const descp = fsmRegisterWrapperDesc(cellp)) {
            AstPin* const qp = findPin(cellp, descp->q);
            if (qp && VN_IS(qp->exprp(), VarRef)) {
                AstVarRef* const qrefp = VN_AS(qp->exprp(), VarRef);
                // The q-side parent variable is the point where the wrapper
                // abstraction collapses into direct RTL after inlining.
                // Marking only that variable keeps the provenance narrow:
                // transition detection still has to prove the d/q FSM pair.
                qrefp->varp()->attrFsmRegisterWrapper(true);
            }
        }
        iterateChildren(cellp);
    }

    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    explicit FsmWrapperMarkerVisitor(AstNetlist* rootp) { iterate(rootp); }
};

}  // namespace

void V3FsmDetect::markWrapperStateVars(AstNetlist* rootp) {
    UINFO(2, __FUNCTION__ << ":");
    FsmWrapperMarkerVisitor marker{rootp};
}

void V3FsmDetect::detect(AstNetlist* rootp) {
    UINFO(2, __FUNCTION__ << ":");
    FsmState state;
    // Phase 1: recover each supported FSM into a complete graph while the
    // original clocked/case structure is still easy to recognize.
    FsmDetectVisitor detect{state, rootp};
    if (dumpGraphLevel() >= 6) {
        size_t index = 0;
        for (const DetectedFsm& fsm : state.fsms()) {
            fsm.graphp->dumpDotFilePrefixed(fsm.graphp->dumpTag(index++));
        }
    }
    // Phase 2: lower the completed in-memory graph state immediately, without
    // crossing into another pass owner or serializing through AST placeholders.
    { FsmLowerVisitor lower{state}; }
    V3Global::dumpCheckGlobalTree("fsm-detect", 0, dumpTreeEitherLevel() >= 3);
}
