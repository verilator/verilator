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
//      For each register written by a clocked always block, or held by a
//      configured register wrapper cell, build its next value as a decision
//      DAG over the block's statements: an assignment sets the value, an if,
//      case or ?: chooses between values by its condition, and a path that
//      does not write the register holds it. Reads of variables driven by
//      combinational logic resolve through their own DAGs. The register is
//      an FSM if, with the register equal to each of its state values in
//      turn (the constants the logic assigns to it or compares it with), the
//      DAG reaches only constants and holds, and some condition depends on
//      the state. Each constant reached is an arc from that state. A
//      top-level split on a state-independent condition with a constant on
//      one side is the reset. The graphs are then lowered into coverage
//      declarations, previous-state tracking, and the active blocks that
//      count states and arcs in the generated model.
//
//*************************************************************************

#include "V3PchAstNoMT.h"

#include "V3FsmDetect.h"

#include "V3Ast.h"
#include "V3Const.h"
#include "V3Control.h"
#include "V3Graph.h"
#include "V3SharedTmps.h"
#include "V3Stats.h"

#include <algorithm>
#include <deque>
#include <map>
#include <memory>
#include <set>
#include <unordered_map>
#include <unordered_set>
#include <vector>

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

class FsmGraph;

class FsmVertex VL_NOT_FINAL : public V3GraphVertex {
    VL_RTTI_IMPL(FsmVertex, V3GraphVertex)

public:
    enum class Kind : uint8_t { STATE, RESET_ANY };

private:
    Kind m_kind;  // State vs synthetic ANY vertex role.
    string m_label;  // User-facing state or pseudo-state label.
    FsmStateValue m_value;  // Encoded state value for real state vertices.

protected:
    FsmVertex(V3Graph* graphp, Kind kind, string label, const FsmStateValue& value) VL_MT_DISABLED
        : V3GraphVertex{graphp},
          m_kind{kind},
          m_label{label},
          m_value{value} {}
    ~FsmVertex() override = default;

public:
    Kind kind() const { return m_kind; }
    bool isState() const { return m_kind == Kind::STATE; }
    bool isResetAny() const { return m_kind == Kind::RESET_ANY; }
    const string& label() const { return m_label; }
    const FsmStateValue& value() const { return m_value; }

    string name() const override VL_MT_SAFE { return m_label + "=" + m_value.ascii(); }
};

class FsmStateVertex final : public FsmVertex {
    VL_RTTI_IMPL(FsmStateVertex, FsmVertex)

public:
    FsmStateVertex(V3Graph* graphp, const string& label, const FsmStateValue& value) VL_MT_DISABLED
        : FsmVertex{graphp, Kind::STATE, label, value} {}
    ~FsmStateVertex() override = default;

    string dotColor() const override { return "lightblue"; }
    string dotShape() const override { return "ellipse"; }
};

class FsmPseudoVertex final : public FsmVertex {
    VL_RTTI_IMPL(FsmPseudoVertex, FsmVertex)

public:
    FsmPseudoVertex(V3Graph* graphp, Kind kind, const string& label) VL_MT_DISABLED
        : FsmVertex{graphp, kind, label, FsmStateValue{}} {}
    ~FsmPseudoVertex() override = default;

    string name() const override VL_MT_SAFE { return label(); }
    string dotColor() const override { return isResetAny() ? "darkgreen" : "orange"; }
    string dotShape() const override { return "diamond"; }
};

class FsmArcEdge final : public V3GraphEdge {
    VL_RTTI_IMPL(FsmArcEdge, V3GraphEdge)
    bool m_isReset = false;  // Arc originates from the synthetic reset source.
    FileLine* m_flp = nullptr;  // Source location for emitted coverage metadata.

public:
    FsmArcEdge(V3Graph* graphp, FsmVertex* fromp, FsmStateVertex* top, bool isReset,
               FileLine* flp) VL_MT_DISABLED : V3GraphEdge{graphp, fromp, top, 1},
                                               m_isReset{isReset},
                                               m_flp{flp} {}
    ~FsmArcEdge() override = default;

    bool isReset() const { return m_isReset; }
    FileLine* fileline() const { return m_flp; }

    string dotLabel() const override { return m_isReset ? "reset" : ""; }
    string dotColor() const override { return m_isReset ? "darkgreen" : "black"; }
};

// One graph per detected FSM. Graph-level metadata captures the non-graph
// context needed to lower states/arcs back into the AST after detection.
class FsmGraph final : public V3Graph {
    AstScope* m_scopep = nullptr;  // Owning scoped block for the detected FSM.
    AstAlways* m_stateAlwaysp = nullptr;  // Register always block being instrumented.
    string m_stateVarName;  // Pretty state variable name for user-visible output.
    string m_stateVarInternalName;  // Internal state symbol name for dump tags.
    AstVarScope* m_stateVarScopep = nullptr;  // Scoped state variable being tracked.
    AstVarScope* m_sampleVarScopep = nullptr;  // Scoped variable sampled by coverage logic.
    std::vector<FsmSenDesc> m_senses;  // Saved event controls for recreated active blocks.
    FileLine* m_flp = nullptr;  // Representative source location for declarations/arcs.
    std::unordered_map<FsmStateValue, FsmStateVertex*, FsmStateValueHash>
        m_stateVertices;  // Value to state map.
    FsmPseudoVertex* m_resetVertexp = nullptr;  // Synthetic ANY source for reset arcs.

public:
    FsmGraph() VL_MT_DISABLED
        : m_resetVertexp{new FsmPseudoVertex{this, FsmVertex::Kind::RESET_ANY, "ANY"}} {}

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
    AstVarScope* sampleVarScopep() const {
        return m_sampleVarScopep ? m_sampleVarScopep : m_stateVarScopep;
    }
    void sampleVarScopep(AstVarScope* vscp) { m_sampleVarScopep = vscp; }
    const std::vector<FsmSenDesc>& senses() const { return m_senses; }
    std::vector<FsmSenDesc>& senses() { return m_senses; }
    FileLine* fileline() const { return m_flp; }
    void fileline(FileLine* flp) { m_flp = flp; }

    FsmStateVertex* addStateVertex(const string& label,
                                   const FsmStateValue& value) VL_MT_DISABLED {
        FsmStateVertex* const vertexp = new FsmStateVertex{this, label, value};
        m_stateVertices.emplace(value, vertexp);
        return vertexp;
    }
    FsmArcEdge* addArc(const FsmStateValue& fromValue, const FsmStateValue& toValue, bool isReset,
                       FileLine* flp) VL_MT_DISABLED {
        FsmStateVertex* const top = m_stateVertices.at(toValue);
        FsmVertex* const fromp
            = isReset ? static_cast<FsmVertex*>(m_resetVertexp) : m_stateVertices.at(fromValue);
        return new FsmArcEdge{this, fromp, top, isReset, flp};
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

//######################################################################
// The next value of a register as a decision DAG

struct FsmNextNode;

// A condition, with the values the block had assigned to the variables it reads
struct FsmCond final {
    AstNodeExpr* exprp = nullptr;
    std::vector<std::pair<AstVarScope*, const FsmNextNode*>> bindings;
    size_t index = 0;  // Creation order, so a path lists its conditions the same way
    size_t size = 0;  // Nodes in the expression
};
// Conditions in creation order, so a path lists the same way on every run
struct FsmCondOrder final {
    bool operator()(const FsmCond* ap, const FsmCond* bp) const { return ap->index < bp->index; }
};

// A node of the DAG giving a register's next value
struct FsmNextNode final {
    enum class Kind : uint8_t {
        CONSTANT,  // A constant
        UNMODELED,  // Not modeled: a write through a select, a call, a loop
        EXPR,  // An expression over variables, kept for conditions that read the variable
        REF,  // A variable's value from before the block ran
        MUX,  // One of two values, chosen by a condition
        LOW  // The low bits of a value, narrowed when the DAG is resolved
    };
    Kind kind = Kind::UNMODELED;
    V3Number num{static_cast<AstNode*>(nullptr), 1, 0};  // CONSTANT: the value, as assigned
    string label;  // CONSTANT: name of the parameter the value came from, if any
    const AstNode* srcp = nullptr;  // CONSTANT: the assignment, or the constant
    AstVarScope* refVscp = nullptr;  // REF: the variable
    // MUX: the condition; EXPR: the expression; LOW: the select, as an expression
    const FsmCond* condp = nullptr;
    const FsmNextNode* thenp = nullptr;  // MUX: value when the condition holds; LOW: the value
    const FsmNextNode* elsep = nullptr;  // MUX: value when it does not
};

// Values a block has assigned so far, by variable
using FsmEnv = std::unordered_map<AstVarScope*, const FsmNextNode*>;
// Variable connected to each port of each register wrapper cell; a few entries, looked up
// by a pair, which has no std::hash
using FsmCellPortMap = std::map<std::pair<const AstCell*, string>, AstVarScope*>;

// A register to try as an FSM, and where its coverage logic goes
struct FsmCandidate final {
    AstScope* scopep = nullptr;  // Scope of the register
    AstAlways* alwaysp = nullptr;  // Clocked block writing it; nullptr for a register wrapper
    AstVarScope* stateVscp = nullptr;  // The register
    AstVarScope* sampleVscp = nullptr;  // Variable the coverage logic samples
    std::vector<FsmSenDesc> senses;  // Edges the register updates on
    FileLine* flp = nullptr;
};

// The states of a candidate: labeled values at the register's width
class FsmStateSet final {
    const int m_width;
    std::vector<std::pair<string, V3Number>> m_states;  // Label and value
    std::unordered_map<string, size_t> m_indexes;  // Index of each value, by its text

    static string key(const V3Number& num) { return num.ascii(false, true); }

public:
    explicit FsmStateSet(int width)
        : m_width{width} {}
    const std::vector<std::pair<string, V3Number>>& states() const { return m_states; }
    size_t size() const { return m_states.size(); }
    static V3Number toWidth(const V3Number& num, int width) {
        V3Number result{static_cast<AstNode*>(nullptr), width, 0};
        result.opAssign(num);  // Truncates or zero extends
        return result;
    }
    // Index of a value, or size() when it is not a state
    size_t index(const V3Number& num) const {
        const std::unordered_map<string, size_t>::const_iterator it
            = m_indexes.find(key(toWidth(num, m_width)));
        return it == m_indexes.end() ? m_states.size() : it->second;
    }  // LCOV_EXCL_LINE
    void add(const string& labelin, const V3Number& num) {
        const string label = AstNode::prettyName(labelin);  // Parameter names may be escaped
        const V3Number wnum = toWidth(num, m_width);
        const auto pair = m_indexes.emplace(key(wnum), m_states.size());
        if (pair.second) {
            m_states.emplace_back(label.empty() ? wnum.ascii() : label, wnum);
            return;
        }
        // A parameter name is a better label than the value; the first one seen is kept
        std::pair<string, V3Number>& state = m_states[pair.first->second];
        if (!label.empty() && state.first == wnum.ascii()) state.first = label;
    }
};

//######################################################################
// Detection: build each register's next-value DAG and evaluate it in each of its states

class FsmDetectVisitor final : public VNVisitorConst {
    // TYPES
    // A leaf reached when a DAG is evaluated for one state
    struct Leaf final {
        enum class Kind : uint8_t { CONSTANT, HOLD, UNMODELED };
        Kind kind;
        V3Number num;  // CONSTANT: the value
        const AstNode* srcp;  // CONSTANT: the assignment, or the constant
        bool topWhen;  // The value the register's top-level condition had on the leaf's path
    };
    enum class Tri : uint8_t { IS_FALSE, IS_TRUE, UNKNOWN };
    // A condition, and the undecided conditions taken on the path to it; kept in std::map,
    // as a pair with a vector has no std::hash, and only looked up or folded over
    using SeenKey = std::pair<const FsmCond*, std::vector<std::pair<const FsmCond*, bool>>>;
    using ResolveMemo = std::unordered_map<const FsmNextNode*, const FsmNextNode*>;
    // Evaluation of a DAG for one state
    struct Eval final {
        AstVarScope* const stateVscp;
        const V3Number stateNum;  // The state's value
        std::unordered_map<const FsmCond*, Tri> condMemo;
        std::map<SeenKey, std::set<Tri>>& seen;  // Results per condition and path
        ResolveMemo resolveMemo;
        // Undecided conditions taken on this path; ordered, as a SeenKey copies it
        std::map<const FsmCond*, bool, FsmCondOrder> path;
        const FsmCond* splitp = nullptr;  // An undecided condition to split the path on
        int pathUses = 0;  // Lookups of 'path': a result that used one isn't memoized
        int steps = 0;  // DAG nodes visited
        const FsmCond* undecidedp = nullptr;  // First undecided condition met, depth first
        const FsmNextNode* topp = nullptr;  // The register's DAG, whose condition leaves record
        bool topWhen = false;  // Value of 'topp's condition on this path
        Eval(AstVarScope* vscp, const V3Number& num, std::map<SeenKey, std::set<Tri>>& seenr)
            : stateVscp{vscp}
            , stateNum{num}
            , seen{seenr} {}
    };
    struct Arc final {
        size_t from;
        size_t to;
    };
    // Values the logic gives a register or compares it with, each with its label
    using NamedValues = std::vector<std::pair<string, V3Number>>;
    // What is known of one bit of a value
    enum class Bit : uint8_t { ZERO, ONE, DONT_CARE, UNKNOWN };

    // Limits on following variables through each other's logic, which may loop
    static constexpr int VALUE_DEPTH_MAX = 6;  // Variables given a value in a condition
    static constexpr int SUBST_DEPTH_MAX = 4;  // Copies and expressions substituted in a condition
    static constexpr int EVAL_STEPS_MAX = 1 << 16;  // DAG nodes visited for one state

    // STATE - across all visitors
    FsmState& m_state;
    std::deque<FsmNextNode> m_nodes;  // Arena of DAG nodes
    std::deque<FsmCond> m_conds;  // Arena of conditions
    std::vector<AstNode*> m_ownedExprps;  // Synthesized condition expressions
    const FsmNextNode* m_opaquep = nullptr;  // Shared UNMODELED node
    std::unordered_map<AstVarScope*, const FsmNextNode*> m_refs;  // Shared REF nodes
    std::unordered_map<const AstScope*, std::vector<AstCell*>>
        m_wrapperCells;  // Register wrappers, by scope
    std::vector<AstScope*> m_scopeps;  // Every scope, in tree order
    std::unordered_map<const AstScope*, std::vector<const AstCase*>>
        m_casesByScope;  // Case statements, by scope
    AstScope* m_scopep = nullptr;  // Scope being traversed
    VDouble0 m_statRegisters;  // Registers tried as FSMs
    VDouble0 m_statFsms;  // FSMs found
    VDouble0 m_statStates;  // States of the FSMs found
    VDouble0 m_statArcs;  // Arcs of the FSMs found, without reset arcs
    VDouble0 m_statTooManyPaths;  // Registers given up on at EVAL_STEPS_MAX

    // STATE - for the current scope
    std::unordered_map<AstVarScope*, const FsmNextNode*>
        m_combVals;  // Combinationally driven values
    std::unordered_map<AstVarScope*, int> m_clockedWriters;  // Clocked blocks writing each var
    std::unordered_map<const AstVarScope*, std::vector<const AstCase*>>
        m_casesByVar;  // Case statements on each variable, directly or through copies
    std::unordered_set<const AstVarScope*>
        m_dlyVscps;  // Variables the block being walked writes with '<='
    FsmCellPortMap m_cellPorts;  // Variables connected to the ports of wrapper cells
    FsmCellPortMap m_cellChildPorts;  // The port variables themselves

    // METHODS - DAG construction
    const FsmNextNode* opaque() {
        if (!m_opaquep) {
            m_nodes.emplace_back();
            m_opaquep = &m_nodes.back();
        }
        return m_opaquep;
    }
    const FsmNextNode* ref(AstVarScope* vscp) {
        const auto pair = m_refs.emplace(vscp, nullptr);
        if (!pair.second) return pair.first->second;
        m_nodes.emplace_back();
        FsmNextNode& node = m_nodes.back();
        node.kind = FsmNextNode::Kind::REF;
        node.refVscp = vscp;
        pair.first->second = &node;
        return &node;
    }  // LCOV_EXCL_LINE
    const FsmNextNode* constant(const V3Number& num, const AstNode* srcp, const string& label) {
        m_nodes.emplace_back();
        FsmNextNode& node = m_nodes.back();
        node.kind = FsmNextNode::Kind::CONSTANT;
        node.num = num;
        node.srcp = srcp;
        node.label = label;
        return &node;
    }
    const FsmNextNode* expression(const FsmCond* condp) {
        m_nodes.emplace_back();
        FsmNextNode& node = m_nodes.back();
        node.kind = FsmNextNode::Kind::EXPR;
        node.condp = condp;
        return &node;
    }
    const FsmNextNode* low(const FsmCond* selp, const FsmNextNode* valuep) {
        m_nodes.emplace_back();
        FsmNextNode& node = m_nodes.back();
        node.kind = FsmNextNode::Kind::LOW;
        node.condp = selp;
        node.thenp = valuep;
        return &node;
    }
    const FsmNextNode* mux(const FsmCond* condp, const FsmNextNode* thenp,
                           const FsmNextNode* elsep) {
        if (thenp == elsep) return thenp;
        m_nodes.emplace_back();
        FsmNextNode& node = m_nodes.back();
        node.kind = FsmNextNode::Kind::MUX;
        node.condp = condp;
        node.thenp = thenp;
        node.elsep = elsep;
        return &node;
    }
    // A variable written with '<=', in the block or the tasks it calls, keeps its old value for
    // the block's reads
    void collectDlyWrites(AstNode* stmtsp) {
        m_dlyVscps.clear();
        std::unordered_set<const AstNodeFTask*> seen;
        for (AstNode* const stmtp : VNList<AstNode>{stmtsp}) collectDlyWritesRecurse(stmtp, seen);
    }
    void collectDlyWritesRecurse(AstNode* nodep, std::unordered_set<const AstNodeFTask*>& seen) {
        nodep->foreach([&](AstNode* subp) {
            if (const AstAssignDly* const assp = VN_CAST(subp, AssignDly)) {
                assp->lhsp()->foreach([&](const AstVarRef* refp) {
                    if (refp->access().isWriteOrRW()) m_dlyVscps.insert(refp->varScopep());
                });
            } else if (const AstNodeFTaskRef* const callp = VN_CAST(subp, NodeFTaskRef)) {
                if (seen.insert(callp->taskp()).second)
                    collectDlyWritesRecurse(callp->taskp(), seen);
            }
        });
    }
    const FsmCond* makeCond(AstNodeExpr* exprp, const FsmEnv& env) {
        m_conds.emplace_back();
        FsmCond& cond = m_conds.back();
        cond.exprp = exprp;
        cond.index = m_conds.size() - 1;
        exprp->foreach([&](const AstNode* nodep) {
            ++cond.size;
            const AstVarRef* const refp = VN_CAST(nodep, VarRef);
            if (!refp || m_dlyVscps.count(refp->varScopep())) return;
            const FsmEnv::const_iterator it = env.find(refp->varScopep());
            if (it != env.end()) cond.bindings.emplace_back(it->first, it->second);
        });  // LCOV_EXCL_LINE
        return &cond;
    }
    // The value of a constant; parameters were folded into constants long before this pass
    static bool foldConst(AstNodeExpr* exprp, V3Number& num, string& label) {
        const AstConst* const constp = VN_CAST(exprp, Const);
        if (!constp) return false;
        num = constp->num();
        label = constp->origParamName();
        return true;
    }
    // A constant, a variable's value, or a choice between values (a zero extension keeps the
    // value, and a select of the low bits of one, such as a wider next state or an unsized
    // parameter given to a narrower variable, keeps its low bits); nullptr for other
    // expressions
    const FsmNextNode* knownValueOf(AstNodeExpr* exprp, const FsmEnv& env, const AstNode* srcp) {
        if (AstSel* const selp = VN_CAST(exprp, Sel)) {
            const AstConst* const lsbp = VN_CAST(selp->lsbp(), Const);
            const FsmNextNode* const nodep
                = lsbp && lsbp->isZero() ? knownValueOf(selp->fromp(), env, srcp) : nullptr;
            return nodep ? low(makeCond(selp, env), nodep) : nullptr;
        }
        if (AstExtend* const extp = VN_CAST(exprp, Extend)) {
            return knownValueOf(extp->lhsp(), env, srcp);
        }
        if (AstCond* const condp = VN_CAST(exprp, Cond)) {
            return mux(makeCond(condp->condp(), env), valueOf(condp->thenp(), env, srcp),
                       valueOf(condp->elsep(), env, srcp));
        }
        if (AstVarRef* const refp = VN_CAST(exprp, VarRef)) {
            const FsmEnv::const_iterator it
                = m_dlyVscps.count(refp->varScopep()) ? env.end() : env.find(refp->varScopep());
            return it != env.end() ? it->second : ref(refp->varScopep());
        }  // LCOV_EXCL_LINE
        V3Number num{static_cast<AstNode*>(nullptr), 1, 0};
        string label;
        if (foldConst(exprp, num, label)) return constant(num, srcp, label);
        return nullptr;
    }
    const FsmNextNode* valueOf(AstNodeExpr* exprp, const FsmEnv& env, const AstNode* srcp) {
        if (const FsmNextNode* const nodep = knownValueOf(exprp, env, srcp)) return nodep;
        return expression(makeCond(exprp, env));
    }
    // A variable's value after a branch: assigned there, assigned before, or its old value
    const FsmNextNode* envValue(const FsmEnv& env, const FsmEnv& before, AstVarScope* vscp) {
        FsmEnv::const_iterator it = env.find(vscp);
        if (it != env.end()) return it->second;
        it = before.find(vscp);
        if (it != before.end()) return it->second;
        return ref(vscp);
    }  // LCOV_EXCL_LINE
    // Merge the variables two branches assign into 'env' as MUXes on the condition
    void join(const FsmCond* condp, const FsmEnv& before, const FsmEnv& thenEnv,
              const FsmEnv& elseEnv, FsmEnv& env) {
        std::unordered_set<AstVarScope*> vscps;
        for (const FsmEnv::value_type& it : thenEnv) vscps.insert(it.first);
        for (const FsmEnv::value_type& it : elseEnv) vscps.insert(it.first);
        for (AstVarScope* const vscp : vscps) {
            env[vscp]
                = mux(condp, envValue(thenEnv, before, vscp), envValue(elseEnv, before, vscp));
        }  // LCOV_EXCL_LINE
    }
    // The variables a statement writes, including in the tasks it calls, which are not inlined
    // until later, get values the DAG doesn't model
    void writeOpaque(AstNode* nodep, FsmEnv& env) {
        std::unordered_set<const AstNodeFTask*> seen;
        writeOpaqueRecurse(nodep, env, seen);
    }
    void writeOpaqueRecurse(AstNode* nodep, FsmEnv& env,
                            std::unordered_set<const AstNodeFTask*>& seen) {
        nodep->foreach([&](AstNode* subp) {
            if (const AstNodeVarRef* const refp = VN_CAST(subp, NodeVarRef)) {
                if (refp->access().isWriteOrRW()) env[refp->varScopep()] = opaque();
            } else if (const AstNodeFTaskRef* const callp = VN_CAST(subp, NodeFTaskRef)) {
                if (seen.insert(callp->taskp()).second) {
                    writeOpaqueRecurse(callp->taskp(), env, seen);
                }
            }
        });
    }
    // The condition under which a case item is taken, as an expression; nullptr for a 'case
    // inside' item with a range
    AstNodeExpr* caseItemCond(AstCase* casep, AstCaseItem* itemp) {
        for (const AstNodeExpr* const labelp : itemp->condspList()) {
            if (casep->caseInside() && !VN_IS(labelp, Const)) return nullptr;
        }
        AstNodeExpr* resultp = new AstConst{casep->fileline(), AstConst::BitFalse{}};
        const bool wild = casep->casez() || casep->casex() || casep->caseInside();
        for (AstNodeExpr* const labelp : itemp->condspList()) {
            if (neverMatches(casep, labelp)) continue;
            // The case statement's line, which the FSM's points are attributed to
            AstNodeExpr* const lhsp = casep->exprp()->cloneTree(false);
            AstNodeExpr* const rhsp = labelp->cloneTree(false);
            AstNodeExpr* const eqp
                = wild ? static_cast<AstNodeExpr*>(new AstEqWild{casep->fileline(), lhsp, rhsp})
                       : new AstEq{casep->fileline(), lhsp, rhsp};
            resultp = new AstLogOr{casep->fileline(), resultp, eqp};
        }
        m_ownedExprps.push_back(resultp);
        return resultp;
    }
    // A label no value matches in two-state simulation, as V3Case finds: an X in a 'casez'
    // label, or an X or Z in a 'case' label
    static bool neverMatches(const AstCase* casep, const AstNodeExpr* labelp) {
        const AstConst* const constp = VN_CAST(labelp, Const);
        if (!constp || casep->casex() || casep->caseInside()) return false;
        return casep->casez() ? constp->num().isAnyX() : constp->num().isFourState();
    }
    // The variables a branch assigns, with the values it gives them
    void walkBranch(AstNode* stmtsp, const FsmEnv& env, FsmEnv& assigned) {
        FsmEnv inner = env;
        walk(stmtsp, inner);
        for (const FsmEnv::value_type& it : inner) {
            const FsmEnv::const_iterator bit = env.find(it.first);
            // Unchanged by the branch
            if (bit != env.end() && bit->second == it.second) continue;
            assigned.insert(it);
        }  // LCOV_EXCL_LINE
    }
    // Build the DAGs of the variables a statement list assigns, in 'env'
    void walk(AstNode* stmtsp, FsmEnv& env) {
        for (AstNode* const stmtp : VNList<AstNode>{stmtsp}) {
            if (AstNodeAssign* const assp = VN_CAST(stmtp, NodeAssign)) {
                if (AstVarRef* const lhsp = VN_CAST(assp->lhsp(), VarRef)) {
                    env[lhsp->varScopep()] = valueOf(assp->rhsp(), env, assp);
                } else {
                    writeOpaque(assp->lhsp(), env);
                }
            } else if (AstIf* const ifp = VN_CAST(stmtp, If)) {
                FsmEnv thenEnv;
                FsmEnv elseEnv;
                walkBranch(ifp->thensp(), env, thenEnv);
                walkBranch(ifp->elsesp(), env, elseEnv);
                FsmEnv joined;
                join(makeCond(ifp->condp(), env), env, thenEnv, elseEnv, joined);
                for (const FsmEnv::value_type& it : joined) env[it.first] = it.second;
            } else if (AstCase* const casep = VN_CAST(stmtp, Case)) {
                // Items in order: the first match wins, the default (or no match) is last; each
                // arm keeps only what it assigns
                std::vector<std::pair<const FsmCond*, FsmEnv>> arms;
                FsmEnv defaultEnv;
                bool unknownItem = false;
                for (AstCaseItem* const itemp : casep->itemspList()) {
                    FsmEnv inner;
                    walkBranch(itemp->stmtsp(), env, inner);
                    if (itemp->isDefault()) {
                        defaultEnv = inner;
                        continue;
                    }
                    AstNodeExpr* const condp = caseItemCond(casep, itemp);
                    if (!condp) {
                        unknownItem = true;
                        break;
                    }
                    arms.emplace_back(makeCond(condp, env), inner);
                }
                if (unknownItem) {
                    writeOpaque(casep, env);
                    continue;
                }
                FsmEnv result = defaultEnv;
                for (std::vector<std::pair<const FsmCond*, FsmEnv>>::const_reverse_iterator it
                     = arms.rbegin();
                     it != arms.rend(); ++it) {
                    FsmEnv joined;
                    join(it->first, env, it->second, result, joined);
                    result = std::move(joined);
                }
                for (const FsmEnv::value_type& it : result) env[it.first] = it.second;
            } else {
                // Coverage probes, displays, loops, calls: only their writes matter
                writeOpaque(stmtp, env);
            }
        }
    }

    // METHODS - resolving one register's DAG
    // The low 'width' bits of a resolved value, leaf by leaf: a constant is cut to the width,
    // and the register's own value stays a hold if no bits are dropped; any other leaf is a
    // value the states don't name, as an expression leaf is
    const FsmNextNode* lowBits(const FsmNextNode* nodep, int width, ResolveMemo& memo) {
        if (nodep->kind == FsmNextNode::Kind::CONSTANT) {
            return constant(FsmStateSet::toWidth(nodep->num, width), nodep->srcp, nodep->label);
        }
        if (nodep->kind == FsmNextNode::Kind::REF && nodep->refVscp->width() <= width) {
            return nodep;
        }
        if (nodep->kind != FsmNextNode::Kind::MUX) return opaque();
        const ResolveMemo::const_iterator it = memo.find(nodep);
        if (it != memo.end()) return it->second;
        const FsmNextNode* const resultp = mux(nodep->condp, lowBits(nodep->thenp, width, memo),
                                               lowBits(nodep->elsep, width, memo));
        memo[nodep] = resultp;
        return resultp;
    }
    // REF nodes: the register itself stays a REF (a hold), a combinationally driven variable
    // becomes its own DAG, anything else is opaque; LOW nodes are narrowed
    const FsmNextNode* resolve(const FsmNextNode* nodep, AstVarScope* stateVscp,
                               ResolveMemo& memo) {
        if (nodep->kind != FsmNextNode::Kind::REF && nodep->kind != FsmNextNode::Kind::MUX
            && nodep->kind != FsmNextNode::Kind::LOW) {
            return nodep;
        }
        const ResolveMemo::const_iterator it = memo.find(nodep);
        if (it != memo.end()) return it->second;
        const FsmNextNode* resultp = opaque();
        if (nodep->kind == FsmNextNode::Kind::REF) {
            if (nodep->refVscp == stateVscp) {
                resultp = nodep;
            } else {
                const std::unordered_map<AstVarScope*, const FsmNextNode*>::const_iterator cit
                    = m_combVals.find(nodep->refVscp);
                if (cit != m_combVals.end()) {
                    memo[nodep] = opaque();  // Cycle guard
                    resultp = resolve(cit->second, stateVscp, memo);
                }
            }  // LCOV_EXCL_LINE
        } else if (nodep->kind == FsmNextNode::Kind::LOW) {
            ResolveMemo lowMemo;
            resultp = lowBits(resolve(nodep->thenp, stateVscp, memo), nodep->condp->exprp->width(),
                              lowMemo);
        } else {
            resultp = mux(nodep->condp, resolve(nodep->thenp, stateVscp, memo),
                          resolve(nodep->elsep, stateVscp, memo));
        }
        memo[nodep] = resultp;
        return resultp;
    }

    // METHODS - evaluating a DAG for one state
    // The leaves of 'nodep' in this state, and the first condition met that the state doesn't
    // decide; false past the depth limit
    bool leavesOf(const FsmNextNode* nodep, Eval& eval, std::vector<Leaf>& leaves,
                  const FsmCond*& undecidedpr, int depth) {
        if (depth > VALUE_DEPTH_MAX) return false;
        const FsmCond* const outerp = eval.undecidedp;
        eval.undecidedp = nullptr;
        evaluate(resolve(nodep, eval.stateVscp, eval.resolveMemo), eval, leaves, depth + 1);
        undecidedpr = eval.undecidedp;
        eval.undecidedp = outerp;
        return true;
    }
    // The single value of some leaves, if they have one
    static bool singleValue(const std::vector<Leaf>& leaves, const V3Number& stateNum,
                            V3Number& num) {
        bool found = false;
        for (const Leaf& leaf : leaves) {
            if (leaf.kind == Leaf::Kind::UNMODELED) return false;
            const V3Number& lnum = leaf.kind == Leaf::Kind::HOLD ? stateNum : leaf.num;
            const int width = std::max(lnum.width(), num.width());
            if (found
                && !FsmStateSet::toWidth(lnum, width).isCaseEq(FsmStateSet::toWidth(num, width))) {
                return false;
            }
            num = lnum;
            found = true;
        }  // LCOV_EXCL_LINE
        return found;
    }
    // Replace the variables of a condition by their values in this state, where known
    AstNodeExpr* substitute(AstNodeExpr* exprp, const FsmCond& cond, Eval& eval, int depth) {
        if (AstVarRef* const refp = VN_CAST(exprp, VarRef)) {
            // A real or string variable keeps its reference; its value isn't a bit pattern
            if (!refp->dtypep()->skipRefp()->isIntegralOrPacked()) return refp;
            AstVarScope* const vscp = refp->varScopep();
            V3Number num{refp, refp->width()};
            bool known = false;
            const FsmNextNode* const nodep = boundNodep(&cond, vscp, eval.stateVscp);
            if (!nodep && vscp == eval.stateVscp) {
                num.opAssign(eval.stateNum);
                known = true;
            } else if (nodep) {
                std::vector<Leaf> leaves;
                const FsmCond* undecidedp = nullptr;
                V3Number value{refp, refp->width()};
                if (leavesOf(nodep, eval, leaves, undecidedp, depth)
                    && singleValue(leaves, eval.stateNum, value)) {
                    num.opAssign(FsmStateSet::toWidth(value, refp->width()));
                    known = true;
                }
            }
            if (known) {
                AstConst* const constp = new AstConst{refp->fileline(), num};
                VL_DO_DANGLING(refp->deleteTree(), refp);
                return constp;
            }
            // An expression the variable was assigned, e.g. 'idle = state == S0' or a select,
            // substituted with the values its own variables had then
            if (nodep
                && (nodep->kind == FsmNextNode::Kind::EXPR
                    || nodep->kind == FsmNextNode::Kind::LOW)
                && nodep->condp->exprp->width() == refp->width()) {
                if (depth >= SUBST_DEPTH_MAX) return refp;
                AstNodeExpr* const clonep = nodep->condp->exprp->cloneTree(false);
                VL_DO_DANGLING(refp->deleteTree(), refp);
                return substitute(clonep, *nodep->condp, eval, depth + 1);
            }
            return refp;
        }
        std::vector<AstVarRef*> refps;
        exprp->foreach([&](AstVarRef* refp) { refps.push_back(refp); });
        for (AstVarRef* const refp : refps) {
            AstNodeExpr* const newp = substitute(refp->cloneTree(false), cond, eval, depth);
            refp->replaceWith(newp);
            VL_DO_DANGLING(refp->deleteTree(), refp);
        }  // LCOV_EXCL_LINE
        return exprp;
    }
    // Bits known after substitution: constants, including inside concatenations and zero
    // extensions; X and Z bits of constants are 'xz'
    static void knownBits(const AstNodeExpr* exprp, std::vector<Bit>& bits, int lsb, Bit xz) {
        if (const AstConst* const constp = VN_CAST(exprp, Const)) {
            for (int i = 0; i < constp->width(); ++i) {
                bits[lsb + i] = constp->num().bitIs1(i)   ? Bit::ONE
                                : constp->num().bitIs0(i) ? Bit::ZERO
                                                          : xz;
            }
        } else if (const AstConcat* const catp = VN_CAST(exprp, Concat)) {
            knownBits(catp->rhsp(), bits, lsb, xz);
            knownBits(catp->lhsp(), bits, lsb + catp->rhsp()->width(), xz);
        } else if (const AstExtend* const extp = VN_CAST(exprp, Extend)) {
            for (int i = extp->lhsp()->width(); i < extp->width(); ++i) bits[lsb + i] = Bit::ZERO;
            knownBits(extp->lhsp(), bits, lsb, xz);
        }
    }
    // An equality or inequality; case and wildcard inequalities became these before this pass
    static bool isEquality(const AstNodeBiop* biopp) {
        return VN_IS(biopp, Eq) || VN_IS(biopp, EqWild) || VN_IS(biopp, Neq);
    }
    // An equality of partly known values, e.g. {state, in} once the state is substituted, that
    // V3Const leaves alone: a known bit that differs decides it, as does every bit being known
    // and equal; X and Z bits are unknown, except in a wildcard equality's constant, where they
    // are don't cares
    static AstNodeExpr* foldKnownBits(AstNodeExpr* condp) {
        std::vector<AstNodeBiop*> cmps;
        condp->foreach([&](AstNodeBiop* biopp) {
            if (isEquality(biopp)) cmps.push_back(biopp);
        });
        // Innermost first, so replacing one never frees another still to visit
        for (std::vector<AstNodeBiop*>::const_reverse_iterator it = cmps.rbegin();
             it != cmps.rend(); ++it) {
            AstNodeBiop* const cmpp = *it;
            const int width = std::max(cmpp->lhsp()->width(), cmpp->rhsp()->width());
            std::vector<Bit> lbits(width, Bit::UNKNOWN);
            std::vector<Bit> rbits(width, Bit::UNKNOWN);
            knownBits(cmpp->lhsp(), lbits, 0, Bit::UNKNOWN);
            knownBits(cmpp->rhsp(), rbits, 0, VN_IS(cmpp, EqWild) ? Bit::DONT_CARE : Bit::UNKNOWN);
            bool differ = false;
            bool decided = true;
            for (int i = 0; i < width; ++i) {
                if (rbits[i] == Bit::DONT_CARE) continue;
                if (lbits[i] == Bit::UNKNOWN || rbits[i] == Bit::UNKNOWN) {
                    decided = false;
                } else if (lbits[i] != rbits[i]) {
                    differ = true;
                }
            }
            if (!differ && !decided) continue;
            const bool neq = VN_IS(cmpp, Neq);
            AstConst* const newp = differ == neq
                                       ? new AstConst{cmpp->fileline(), AstConst::BitTrue{}}
                                       : new AstConst{cmpp->fileline(), AstConst::BitFalse{}};
            if (cmpp == condp) {
                VL_DO_DANGLING(cmpp->deleteTree(), cmpp);
                return newp;
            }
            cmpp->replaceWith(newp);
            VL_DO_DANGLING(cmpp->deleteTree(), cmpp);
        }
        return condp;
    }
    // The first undecided condition choosing among several values of 'nodep' on this path
    const FsmCond* undecidedCond(const FsmNextNode* nodep, Eval& eval, int depth) {
        std::vector<Leaf> leaves;
        const FsmCond* undecidedp = nullptr;
        V3Number one{static_cast<AstNode*>(nullptr), 1, 0};
        if (!leavesOf(nodep, eval, leaves, undecidedp, depth)
            || singleValue(leaves, eval.stateNum, one)) {
            return nullptr;
        }
        // Choosing among values the DAG doesn't model decides nothing
        const bool anyModeled = std::any_of(leaves.begin(), leaves.end(), [](const Leaf& leaf) {
            return leaf.kind != Leaf::Kind::UNMODELED;
        });
        return anyModeled ? undecidedp : nullptr;
    }
    // A variable's value as bound in a condition; nullptr if the condition doesn't bind it
    static const FsmNextNode* bindingOf(const FsmCond& cond, const AstVarScope* vscp) {
        for (const std::pair<AstVarScope*, const FsmNextNode*>& binding : cond.bindings) {
            if (binding.first == vscp) return binding.second;
        }
        return nullptr;
    }
    // Conditions taken earlier on this path decide the same subexpressions here, when their
    // variables have the same values: 'en' in 'if (en && go) s = S1; if (en) s = S2;'
    static bool largerFirst(const std::pair<const FsmCond*, bool>& a,
                            const std::pair<const FsmCond*, bool>& b) {
        return a.first->size > b.first->size;
    }
    static AstNodeExpr* assumePath(AstNodeExpr* exprp, const FsmCond& cond, Eval& eval) {
        // Larger conditions first, so 'en && go' is decided before replacing 'en' changes it
        std::vector<std::pair<const FsmCond*, bool>> taken{eval.path.begin(), eval.path.end()};
        std::stable_sort(taken.begin(), taken.end(), largerFirst);
        for (const std::pair<const FsmCond*, bool>& it : taken) {
            const FsmCond& pathCond = *it.first;
            const bool otherValues = pathCond.exprp->exists([&](const AstVarRef* refp) {
                return bindingOf(pathCond, refp->varScopep())
                       != bindingOf(cond, refp->varScopep());
            });
            if (otherValues) continue;
            std::vector<AstNodeExpr*> matchps;
            exprp->foreach([&](AstNodeExpr* subp) {
                if (subp->sameTree(pathCond.exprp)) matchps.push_back(subp);
            });
            for (AstNodeExpr* const matchp : matchps) {
                ++eval.pathUses;
                AstConst* const constp
                    = it.second ? new AstConst{matchp->fileline(), AstConst::BitTrue{}}
                                : new AstConst{matchp->fileline(), AstConst::BitFalse{}};
                if (matchp == exprp) {
                    VL_DO_DANGLING(exprp->deleteTree(), exprp);
                    return constp;
                }
                matchp->replaceWith(constp);
                VL_DO_DANGLING(matchp->deleteTree(), matchp);
            }  // LCOV_EXCL_LINE
        }
        return exprp;
    }
    Tri evalOnce(const FsmCond* condp, Eval& eval, int depth) {
        AstNodeExpr* const clonep = foldKnownBits(substitute(
            assumePath(condp->exprp->cloneTree(false), *condp, eval), *condp, eval, depth));
        AstNode* const foldedp = V3Const::constifyEdit(clonep);
        Tri result = Tri::UNKNOWN;
        if (const AstConst* const constp = VN_CAST(foldedp, Const)) {
            result = constp->num().isNeqZero() ? Tri::IS_TRUE : Tri::IS_FALSE;
        }
        VL_DO_DANGLING(foldedp->deleteTree(), foldedp);
        return result;
    }
    Tri evalCond(const FsmCond* condp, Eval& eval, int depth) {
        const std::map<const FsmCond*, bool, FsmCondOrder>::const_iterator pit
            = eval.path.find(condp);
        if (pit != eval.path.end()) {
            ++eval.pathUses;
            return pit->second ? Tri::IS_TRUE : Tri::IS_FALSE;
        }
        const std::unordered_map<const FsmCond*, Tri>::const_iterator it
            = eval.condMemo.find(condp);
        if (it != eval.condMemo.end()) return it->second;
        const int uses = eval.pathUses;
        // A variable given one of several values, earlier in this cycle or combinationally,
        // e.g. the state after 'if (start) state = S1;': split the path on what chooses the value
        std::vector<AstVarScope*> vscps;
        std::unordered_set<const AstVarScope*> seen;
        condp->exprp->foreach([&](const AstVarRef* refp) {
            if (seen.insert(refp->varScopep()).second) vscps.push_back(refp->varScopep());
        });
        for (AstVarScope* const vscp : vscps) {
            const FsmNextNode* const nodep = boundNodep(condp, vscp, eval.stateVscp);
            if (!nodep) continue;
            if (const FsmCond* const undecidedp = undecidedCond(nodep, eval, depth)) {
                eval.splitp = undecidedp;
                eval.seen[SeenKey{condp, {eval.path.begin(), eval.path.end()}}].insert(
                    Tri::UNKNOWN);
                return Tri::UNKNOWN;
            }
        }
        const Tri result = evalOnce(condp, eval, depth);
        // A decided result that didn't use the path's conditions holds on every path; an
        // undecided one may be decided by another path's conditions, or by an evaluation that
        // starts less deep
        if (result != Tri::UNKNOWN && eval.pathUses == uses) eval.condMemo[condp] = result;
        eval.seen[SeenKey{condp, {eval.path.begin(), eval.path.end()}}].insert(result);
        return result;
    }
    // The leaf a node other than a MUX is in this state
    static Leaf leafOf(const FsmNextNode* nodep, const Eval& eval) {
        if (nodep->kind == FsmNextNode::Kind::CONSTANT) {
            return Leaf{Leaf::Kind::CONSTANT, nodep->num, nodep->srcp, eval.topWhen};
        }
        if (nodep->kind == FsmNextNode::Kind::REF) {
            // Resolving leaves only the register itself as a REF
            UASSERT_OBJ(nodep->refVscp == eval.stateVscp, nodep->refVscp, "Unresolved variable");
            return Leaf{Leaf::Kind::HOLD, eval.stateNum, nullptr, eval.topWhen};
        }
        return Leaf{Leaf::Kind::UNMODELED, eval.stateNum, nullptr, eval.topWhen};
    }
    // The leaves a DAG reaches in this state
    void evaluate(const FsmNextNode* nodep, Eval& eval, std::vector<Leaf>& leaves, int depth) {
        // Shared parts of a DAG are visited once per path through them; tryRegister gives up on
        // a register whose paths are too many
        if (++eval.steps > EVAL_STEPS_MAX) {
            leaves.push_back(Leaf{Leaf::Kind::UNMODELED, eval.stateNum, nullptr, eval.topWhen});
            return;
        }
        if (nodep->kind != FsmNextNode::Kind::MUX) {
            leaves.push_back(leafOf(nodep, eval));
            return;
        }
        const Tri result = evalCond(nodep->condp, eval, depth);
        if (result == Tri::UNKNOWN && !eval.undecidedp) {
            eval.undecidedp = eval.splitp ? eval.splitp : nodep->condp;
        }
        if (result == Tri::UNKNOWN && eval.splitp) {
            const FsmCond* const splitp = eval.splitp;
            eval.splitp = nullptr;
            for (const bool value : {true, false}) {
                eval.path[splitp] = value;
                evaluate(nodep, eval, leaves, depth);
                eval.path.erase(splitp);
            }
            return;
        }
        const bool unknown = result == Tri::UNKNOWN;
        for (const bool value : {true, false}) {
            if (result == (value ? Tri::IS_FALSE : Tri::IS_TRUE)) continue;
            // An undecided condition keeps its value for the rest of the path
            if (unknown) eval.path[nodep->condp] = value;
            if (nodep == eval.topp) eval.topWhen = value;
            evaluate(value ? nodep->thenp : nodep->elsep, eval, leaves, depth);
            if (unknown) eval.path.erase(nodep->condp);
        }
    }

    // METHODS - the state space of a register
    // The value a variable read in a condition is bound to: assigned earlier in the block, or
    // driven combinationally; through copies of other variables, which may loop
    const FsmNextNode* boundNodep(const FsmCond* condp, AstVarScope* vscp,
                                  AstVarScope* stateVscp) const {
        const FsmNextNode* nodep = bindingOf(*condp, vscp);
        for (int depth = 0; depth < SUBST_DEPTH_MAX; ++depth) {
            if (!nodep) {
                const std::unordered_map<AstVarScope*, const FsmNextNode*>::const_iterator it
                    = m_combVals.find(vscp);
                if (it == m_combVals.end()) return nullptr;
                nodep = it->second;
            }  // LCOV_EXCL_LINE
            if (nodep->kind != FsmNextNode::Kind::REF || nodep->refVscp == stateVscp) return nodep;
            vscp = nodep->refVscp;
            nodep = nullptr;
        }
        return nullptr;
    }
    // Whether a variable read in a condition holds the state: the state itself, or a copy of it
    bool isStateRef(const AstVarRef* refp, const FsmCond* condp, AstVarScope* stateVscp) const {
        if (refp->varScopep() == stateVscp) return true;
        // A widened copy is not the state field by field
        if (refp->width() != stateVscp->width()) return false;
        const FsmNextNode* const nodep = boundNodep(condp, refp->varScopep(), stateVscp);
        return nodep && nodep->kind == FsmNextNode::Kind::REF;
    }
    // Bit offset of the state in an expression: the state itself, zero-extended, or a field of
    // a concatenation; -1 if none of these
    int stateLsb(const AstNodeExpr* nodep, const FsmCond* condp, AstVarScope* stateVscp) const {
        if (const AstVarRef* const refp = VN_CAST(nodep, VarRef)) {
            return isStateRef(refp, condp, stateVscp) ? 0 : -1;
        }
        if (const AstExtend* const extp = VN_CAST(nodep, Extend)) {
            return stateLsb(extp->lhsp(), condp, stateVscp);
        }
        if (const AstConcat* const catp = VN_CAST(nodep, Concat)) {
            const int low = stateLsb(catp->rhsp(), condp, stateVscp);
            if (low >= 0) return low;
            const int high = stateLsb(catp->lhsp(), condp, stateVscp);
            return high >= 0 ? high + catp->rhsp()->width() : -1;
        }
        return -1;
    }
    // The state's field of a constant compared with an expression containing the state; false
    // if it has wildcard bits
    static bool stateField(const AstConst* constp, int lsb, int width, V3Number& field) {
        field.opSel(constp->num(), lsb + width - 1, lsb);
        return !field.isAnyXZ();
    }
    // Whether a constant can equal an expression containing the state: not if a bit the
    // expression fixes differs, as the zero extension in 'state == 5' for a two-bit state does
    static bool canMatch(const AstNodeExpr* exprp, const AstConst* constp) {
        const int width = std::max(exprp->width(), constp->width());
        std::vector<Bit> ebits(width, Bit::UNKNOWN);
        std::vector<Bit> cbits(width, Bit::DONT_CARE);
        knownBits(exprp, ebits, 0, Bit::UNKNOWN);
        knownBits(constp, cbits, 0, Bit::DONT_CARE);
        for (int i = 0; i < width; ++i) {
            if (ebits[i] != Bit::UNKNOWN && cbits[i] != Bit::DONT_CARE && ebits[i] != cbits[i]) {
                return false;
            }
        }
        return true;
    }
    // The values a condition compares the state with, including in the expressions assigned to
    // the variables it reads
    void collectCompares(AstNodeExpr* exprp, const FsmCond* condp, AstVarScope* stateVscp,
                         int width, int depth, NamedValues& named) const {
        exprp->foreach([&](const AstNodeBiop* biopp) {
            if (!isEquality(biopp)) return;
            for (const AstNode* const sidep : {biopp->lhsp(), biopp->rhsp()}) {
                const AstConst* const constp = VN_CAST(sidep, Const);
                const AstNodeExpr* const otherp
                    = sidep == biopp->lhsp() ? biopp->rhsp() : biopp->lhsp();
                const int lsb = constp ? stateLsb(otherp, condp, stateVscp) : -1;
                V3Number field{static_cast<AstNode*>(nullptr), width, 0};
                if (lsb < 0 || !canMatch(otherp, constp)
                    || !stateField(constp, lsb, width, field)) {
                    continue;
                }
                named.emplace_back(VN_IS(otherp, Concat) ? string{} : constp->origParamName(),
                                   field);
            }
        });
        if (depth >= SUBST_DEPTH_MAX) return;
        exprp->foreach([&](const AstVarRef* refp) {
            const FsmNextNode* const nodep = boundNodep(condp, refp->varScopep(), stateVscp);
            if (nodep
                && (nodep->kind == FsmNextNode::Kind::EXPR
                    || nodep->kind == FsmNextNode::Kind::LOW)) {
                collectCompares(nodep->condp->exprp, nodep->condp, stateVscp, width, depth + 1,
                                named);
            }
        });
    }
    // The labels of every case on the state in the scope, including items that leave the
    // state unchanged, whose branch merged with the hold and so isn't in the DAG
    void collectCaseLabels(AstVarScope* stateVscp, int width, NamedValues& named) const {
        const FsmCond noBindings;
        const std::unordered_map<const AstVarScope*, std::vector<const AstCase*>>::const_iterator
            it
            = m_casesByVar.find(stateVscp);
        if (it == m_casesByVar.end()) return;
        for (const AstCase* const casep : it->second) {
            const int lsb = stateLsb(casep->exprp(), &noBindings, stateVscp);
            if (lsb < 0) continue;
            for (const AstCaseItem* const itemp : casep->itemspList()) {
                for (const AstNodeExpr* const labelp : itemp->condspList()) {
                    const AstConst* const constp = VN_CAST(labelp, Const);
                    V3Number field{static_cast<AstNode*>(nullptr), width, 0};
                    if (!constp || neverMatches(casep, constp) || !canMatch(casep->exprp(), constp)
                        || !stateField(constp, lsb, width, field)) {
                        continue;
                    }
                    named.emplace_back(
                        VN_IS(casep->exprp(), Concat) ? string{} : constp->origParamName(), field);
                }
            }
        }
    }
    // The states: the values the logic assigns to the register or compares it with; for an
    // enum, the items among them
    void stateSpace(AstVarScope* stateVscp, const FsmNextNode* treep, const AstEnumDType* enump,
                    FsmStateSet& states) const {
        const int width = stateVscp->width();
        NamedValues named;
        std::vector<const FsmNextNode*> stack{treep};
        std::unordered_set<const FsmNextNode*> seen;
        while (!stack.empty()) {
            const FsmNextNode* const nodep = stack.back();
            stack.pop_back();
            if (!seen.insert(nodep).second) continue;
            if (nodep->kind == FsmNextNode::Kind::CONSTANT) {
                named.emplace_back(nodep->label, nodep->num);
            } else if (nodep->kind == FsmNextNode::Kind::MUX) {
                collectCompares(nodep->condp->exprp, nodep->condp, stateVscp, width, 0, named);
                // 'then' first, so of two names for one value the earlier one names the state
                stack.push_back(nodep->elsep);
                stack.push_back(nodep->thenp);
            }
        }
        collectCaseLabels(stateVscp, width, named);
        if (!enump) {
            for (const std::pair<string, V3Number>& it : named) states.add(it.first, it.second);
            return;
        }
        std::unordered_set<string> namedKeys;
        for (const std::pair<string, V3Number>& it : named) {
            namedKeys.insert(FsmStateSet::toWidth(it.second, width).ascii(false, true));
        }  // LCOV_EXCL_LINE
        for (const AstEnumItem* const itemp : enump->itemspList()) {
            const AstConst* const constp = VN_AS(itemp->valuep(), Const);
            if (namedKeys.count(FsmStateSet::toWidth(constp->num(), width).ascii(false, true))) {
                states.add(itemp->name(), constp->num());
            }
        }
    }

    // METHODS - one register
    // The line the FSM's points are reported on: the first condition, in source order, whose
    // result depends on the state; nullptr if the next state never depends on the state
    static FileLine* dispatchFileline(const std::map<SeenKey, std::set<Tri>>& seenResults) {
        FileLine* flp = nullptr;
        for (const std::pair<const SeenKey, std::set<Tri>>& it : seenResults) {
            if (it.second.size() < 2) continue;
            FileLine* const condFlp = it.first.first->exprp->fileline();
            if (!flp || condFlp->operatorCompare(*flp) < 0) flp = condFlp;
        }  // LCOV_EXCL_LINE
        return flp;
    }
    // The reset: the clocked process's own top-level split, 'clockedCondp', on a condition the
    // state doesn't decide but the inputs may, with a constant on one side
    static void findReset(const FsmNextNode* treep, const FsmCond* clockedCondp,
                          const std::map<SeenKey, std::set<Tri>>& seenResults,
                          const FsmNextNode*& resetpr, bool& normalWhenr) {
        if (treep->condp != clockedCondp) return;
        std::set<Tri> results;
        for (const std::pair<const SeenKey, std::set<Tri>>& it : seenResults) {
            if (it.first.first != treep->condp) continue;
            // On one path, the same result in every state
            if (it.second.size() != 1) return;
            results.insert(*it.second.begin());
        }  // LCOV_EXCL_LINE
        // Decided the same way everywhere, it isn't a reset
        if (results.size() == 1 && !results.count(Tri::UNKNOWN)) return;
        for (const FsmNextNode* const sidep : {treep->thenp, treep->elsep}) {
            if (sidep->kind == FsmNextNode::Kind::CONSTANT) {
                resetpr = sidep;
                normalWhenr = sidep != treep->thenp;
                return;
            }
        }
    }
    // A constant an enum register is given that is not in the enum
    static void warnOutsideEnum(const AstVarScope* stateVscp, const V3Number& num,
                                const AstNode* srcp) {
        srcp->v3warn(COVERIGN, "Ignoring unsupported: FSM coverage on enum state variable "
                                   << stateVscp->varp()->prettyNameQ() << ": assigned value "
                                   << FsmStateValue{num}.warnText()
                                   << " is not present in the declared enum");
    }
    // Arcs from each state: the constants its leaves reach, leaving out, when there is a reset,
    // the leaves where the reset condition holds. Returns false for a register whose value
    // isn't one of its constants.
    bool collectArcs(AstVarScope* stateVscp, const std::vector<std::vector<Leaf>>& stateLeaves,
                     bool hasReset, bool normalWhen, bool declared, const FsmStateSet& states,
                     std::vector<Arc>& arcs) {
        std::unordered_set<const AstNode*> warned;
        for (size_t from = 0; from < states.size(); ++from) {
            for (const Leaf& leaf : stateLeaves[from]) {
                if (hasReset && leaf.topWhen != normalWhen) continue;
                if (leaf.kind == Leaf::Kind::UNMODELED) {
                    if (declared) continue;  // The declaration says it is an FSM
                    return false;
                }
                if (leaf.kind == Leaf::Kind::HOLD) continue;
                const size_t to = states.index(leaf.num);
                if (to == states.size()) {
                    // All constants of a register that isn't an enum are states
                    if (warned.insert(leaf.srcp).second)
                        warnOutsideEnum(stateVscp, leaf.num, leaf.srcp);
                    continue;
                }
                if (to != from) arcs.push_back(Arc{from, to});
            }  // LCOV_EXCL_LINE
        }
        return true;
    }
    void addGraph(const FsmCandidate& cand, FileLine* flp, const FsmStateSet& states,
                  const FsmNextNode* resetp, const std::vector<Arc>& arcs) {
        ++m_statFsms;
        m_statStates += states.size();
        m_statArcs += arcs.size();
        DetectedFsm& entry = m_state.fsmFor(cand.stateVscp);
        entry.graphp.reset(new FsmGraph{});
        FsmGraph& graph = *entry.graphp;
        graph.scopep(cand.scopep);
        graph.stateAlwaysp(cand.alwaysp);
        graph.stateVarName(cand.stateVscp->prettyName());
        graph.stateVarInternalName(cand.stateVscp->varp()->name());
        graph.stateVarScopep(cand.stateVscp);
        graph.sampleVarScopep(cand.sampleVscp);
        graph.senses() = cand.senses;
        graph.fileline(flp);
        for (const std::pair<string, V3Number>& state : states.states()) {
            graph.addStateVertex(state.first, FsmStateValue{state.second});
        }  // LCOV_EXCL_LINE
        if (resetp) {
            graph.addArc(FsmStateValue{},
                         FsmStateValue{states.states()[states.index(resetp->num)].second}, true,
                         flp);
        }
        std::unordered_set<size_t> added;  // Arcs added, as from * states + to
        for (const Arc& arc : arcs) {
            if (!added.emplace(arc.from * states.size() + arc.to).second) continue;
            graph.addArc(FsmStateValue{states.states()[arc.from].second},
                         FsmStateValue{states.states()[arc.to].second}, false, flp);
        }  // LCOV_EXCL_LINE
    }
    void tryRegister(const FsmCandidate& cand, const FsmNextNode* nextp) {
        ++m_statRegisters;
        AstVarScope* const stateVscp = cand.stateVscp;
        if (!stateVscp->dtypep()->skipRefp()->isIntegralOrPacked()) return;  // real, string
        const int width = stateVscp->width();
        ResolveMemo memo;
        const FsmNextNode* const treep = resolve(nextp, stateVscp, memo);
        if (treep->kind != FsmNextNode::Kind::MUX) return;
        const AstEnumDType* const enump
            = VN_CAST(stateVscp->varp()->dtypep()->skipRefToEnump(), EnumDType);
        const bool declared = enump || stateVscp->varp()->attrFsmState();
        // A one-bit register is a flag, which toggle coverage covers, unless declared a state
        if (!declared && width < 2) return;
        FsmStateSet states{width};
        stateSpace(stateVscp, treep, enump, states);
        if (states.size() < 2) return;
        // Evaluate the DAG with the state equal to each state value; the next state must depend
        // on the state through some condition
        std::map<SeenKey, std::set<Tri>> seenResults;
        std::vector<std::vector<Leaf>> stateLeaves(states.size());
        for (size_t i = 0; i < states.size(); ++i) {
            Eval eval{stateVscp, states.states()[i].second, seenResults};
            eval.topp = treep;
            evaluate(treep, eval, stateLeaves[i], 0);
            if (eval.steps > EVAL_STEPS_MAX) {  // Too many paths to follow
                ++m_statTooManyPaths;
                return;
            }
        }
        FileLine* const dispatchFlp = dispatchFileline(seenResults);
        if (!dispatchFlp && !stateVscp->varp()->attrFsmState()) return;
        const FsmNextNode* resetp = nullptr;
        bool normalWhen = false;
        // The clocked process's top split, also under a select of the low bits of the next state
        const FsmNextNode* const topp
            = nextp->kind == FsmNextNode::Kind::LOW ? nextp->thenp : nextp;
        findReset(treep, topp->kind == FsmNextNode::Kind::MUX ? topp->condp : nullptr, seenResults,
                  resetp, normalWhen);
        const bool hasReset = resetp;
        // No reset arc to a value outside the enum
        if (resetp && states.index(resetp->num) == states.size()) {
            warnOutsideEnum(stateVscp, resetp->num, resetp->srcp);
            resetp = nullptr;
        }
        std::vector<Arc> arcs;
        if (!collectArcs(stateVscp, stateLeaves, hasReset, normalWhen, declared, states, arcs)) {
            return;
        }
        addGraph(cand, dispatchFlp ? dispatchFlp : cand.flp, states, resetp, arcs);
    }

    // METHODS - register wrapper cells
    // A continuous assignment connecting a variable of this scope to a port of a wrapper cell
    void collectCellPortAlias(AstScope* scopep, AstNodeAssign* nodep) {
        AstVarRef* const lhsp = VN_CAST(nodep->lhsp(), VarRef);
        AstVarRef* const rhsp = VN_CAST(nodep->rhsp(), VarRef);
        if (!lhsp || !rhsp) return;
        for (const bool childIsLhs : {true, false}) {
            AstVarScope* const childVscp = (childIsLhs ? lhsp : rhsp)->varScopep();
            AstVarScope* const parentVscp = (childIsLhs ? rhsp : lhsp)->varScopep();
            if (!childVscp->varp()->isIO() || childVscp->scopep()->aboveScopep() != scopep) {
                continue;
            }
            AstCell* const cellp = childVscp->scopep()->aboveCellp();
            if (!fsmRegisterWrapperDesc(cellp)) continue;
            m_cellPorts[{cellp, childVscp->varp()->name()}] = parentVscp;
            m_cellChildPorts[{cellp, childVscp->varp()->name()}] = childVscp;
        }
    }
    static AstVarScope* portVscp(const FsmCellPortMap& ports, const AstCell* cellp,
                                 const string& portName) {
        const FsmCellPortMap::const_iterator it = ports.find({cellp, portName});
        return it == ports.end() ? nullptr : it->second;
    }  // LCOV_EXCL_LINE
    // The value of a parameter of the wrapper module, as instantiated; nullptr if there is no
    // such parameter or its value is not a constant
    static const AstConst* wrapperParamValuep(AstCell* cellp, const string& name) {
        for (AstNode* const stmtp : cellp->modp()->stmtspList()) {
            const AstVar* const varp = VN_CAST(stmtp, Var);
            if (varp && varp->isParam() && varp->name() == name) {
                return VN_CAST(varp->valuep(), Const);
            }
        }
        return nullptr;
    }
    static void warnWrapper(AstCell* cellp, const string& reason) {
        cellp->v3warn(COVERIGN, "Ignoring unsupported: fsm_register_wrapper " + reason);
    }
    // The register a wrapper cell holds: its next value is the connected 'd' variable, with
    // the reset value under the connected reset
    void processWrapperCell(AstScope* scopep, AstCell* cellp) {
        const FsmWrapperRoles roles = rolesFromDesc(*fsmRegisterWrapperDesc(cellp));
        AstVarScope* const nextVscp = portVscp(m_cellPorts, cellp, roles.dPort);
        AstVarScope* const stateVscp = portVscp(m_cellPorts, cellp, roles.qPort);
        if (!nextVscp || !stateVscp) {
            warnWrapper(cellp, "d and q connections must be simple variables");
            return;
        }
        AstVarScope* const clkVscp = portVscp(m_cellPorts, cellp, roles.clkPort);
        if (!clkVscp) {
            warnWrapper(cellp, "instance requires a simple clock connection");
            return;
        }
        FsmCandidate cand;
        cand.scopep = scopep;
        cand.stateVscp = stateVscp;
        cand.sampleVscp = portVscp(m_cellChildPorts, cellp, roles.qPort);
        cand.flp = cellp->fileline();
        FsmSenDesc clkSense;
        clkSense.edgeType = VEdgeType::ET_POSEDGE;
        clkSense.varScopep = clkVscp;
        cand.senses.push_back(clkSense);
        const FsmNextNode* nextp = ref(nextVscp);
        AstVarScope* const resetVscp
            = roles.rstPort.empty() ? nullptr : portVscp(m_cellPorts, cellp, roles.rstPort);
        // The descriptor names the reset port; the wrapper's own event control gives its polarity
        bool activeLow = false;
        const bool hasPolarity
            = resetVscp && fsmWrapperResetPolarityFromWrapperAst(cellp, roles.rstPort, activeLow);
        const AstConst* const resetValuep
            = roles.rstValParam.empty() ? nullptr : wrapperParamValuep(cellp, roles.rstValParam);
        if (resetVscp && hasPolarity && resetValuep) {
            FsmSenDesc rstSense;
            rstSense.edgeType = activeLow ? VEdgeType::ET_NEGEDGE : VEdgeType::ET_POSEDGE;
            rstSense.varScopep = resetVscp;
            cand.senses.push_back(rstSense);
            AstVarRef* const rstRefp = new AstVarRef{cellp->fileline(), resetVscp, VAccess::READ};
            m_ownedExprps.push_back(rstRefp);
            const FsmCond* const condp = makeCond(rstRefp, FsmEnv{});
            const FsmNextNode* const resetp
                = constant(resetValuep->num(), resetValuep, resetValuep->origParamName());
            nextp = activeLow ? mux(condp, nextp, resetp) : mux(condp, resetp, nextp);
        } else if (!roles.rstPort.empty() || !roles.rstValParam.empty()) {
            string reason;
            if (roles.rstPort.empty()) {
                reason = "reset port is not configured";
            } else if (!resetVscp) {
                reason = "reset connection is missing or not a simple variable";
            } else if (!hasPolarity) {
                reason = "reset polarity could not be inferred from the wrapper";
            } else if (roles.rstValParam.empty()) {
                reason = "reset_value parameter is not configured";
            } else {
                reason = "reset_value parameter is missing or not static";
            }
            warnWrapper(cellp, "reset arcs require both reset polarity and static reset value; "
                                   + reason);
        }
        tryRegister(cand, nextp);
    }

    // METHODS - a scope
    static bool isClocked(const AstAlways* alwaysp) {
        return alwaysp->sentreep() && alwaysp->sentreep()->hasEdge();
    }
    // The edges a clocked block runs on; false if one is an expression rather than a variable,
    // which the coverage logic can't sample on
    static bool collectSenses(const AstAlways* alwaysp, std::vector<FsmSenDesc>& senses) {
        for (const AstSenItem* const itemp : alwaysp->sentreep()->sensespList()) {
            const AstNodeVarRef* const vrefp = itemp->varrefp();
            if (!vrefp) return false;
            FsmSenDesc desc;
            desc.edgeType = itemp->edgeType().m_e;
            desc.varScopep = vrefp->varScopep();
            senses.push_back(desc);
        }
        return true;
    }
    // Index a case under each variable its expression reads, and the variables those copy, as
    // isStateRef follows them
    void indexCase(const AstCase* casep) {
        casep->exprp()->foreach([&](const AstVarRef* refp) {
            AstVarScope* vscp = refp->varScopep();
            for (int depth = 0; vscp && depth <= SUBST_DEPTH_MAX; ++depth) {
                m_casesByVar[vscp].push_back(casep);
                const std::unordered_map<AstVarScope*, const FsmNextNode*>::const_iterator it
                    = m_combVals.find(vscp);
                const bool copy
                    = it != m_combVals.end() && it->second->kind == FsmNextNode::Kind::REF;
                vscp = copy ? it->second->refVscp : nullptr;
            }
        });
    }
    // Declaration order, so the FSMs are found, and their coverage emitted, in a fixed order
    using Written = std::pair<AstVarScope*, const FsmNextNode*>;
    static bool declaredBefore(const Written& a, const Written& b) {
        const int cmp = a.first->varp()->fileline()->operatorCompare(*b.first->varp()->fileline());
        return cmp != 0 ? cmp < 0 : a.first->varp()->name() < b.first->varp()->name();
    }
    void processScope(AstScope* scopep) {
        m_combVals.clear();
        m_clockedWriters.clear();
        m_cellPorts.clear();
        m_cellChildPorts.clear();
        std::vector<AstAlways*> clocked;
        for (AstNode* const nodep : VNList<AstNode>{scopep->blocksp()}) {
            AstAlways* const alwaysp = VN_CAST(nodep, Always);
            if (!alwaysp) continue;
            if (isClocked(alwaysp)) {
                clocked.push_back(alwaysp);
                continue;
            }
            // Combinational: a continuous assignment, in a block of its own at this stage (as
            // an if, for a tristate), or an always block
            if (AstNodeAssign* const assp = VN_CAST(alwaysp->stmtsp(), NodeAssign)) {
                collectCellPortAlias(scopep, assp);
            }
            FsmEnv env;
            collectDlyWrites(alwaysp->stmtsp());
            walk(alwaysp->stmtsp(), env);
            for (const FsmEnv::value_type& it : env) m_combVals[it.first] = it.second;
        }
        m_casesByVar.clear();
        for (const AstCase* const casep : m_casesByScope[scopep]) indexCase(casep);
        std::vector<FsmEnv> envs(clocked.size());
        for (size_t i = 0; i < clocked.size(); ++i) {
            collectDlyWrites(clocked[i]->stmtsp());
            walk(clocked[i]->stmtsp(), envs[i]);
            for (const FsmEnv::value_type& it : envs[i]) ++m_clockedWriters[it.first];
        }
        for (size_t i = 0; i < clocked.size(); ++i) {
            std::vector<FsmSenDesc> senses;
            if (!collectSenses(clocked[i], senses)) continue;
            std::vector<Written> regs{envs[i].begin(), envs[i].end()};
            std::stable_sort(regs.begin(), regs.end(), declaredBefore);
            for (const Written& it : regs) {
                // A register written by two blocks is not a state
                if (m_clockedWriters[it.first] != 1) continue;
                FsmCandidate cand;
                cand.scopep = scopep;
                cand.alwaysp = clocked[i];
                cand.stateVscp = it.first;
                cand.sampleVscp = it.first;
                cand.senses = senses;
                cand.flp = clocked[i]->fileline();
                tryRegister(cand, it.second);
            }
        }
        const std::unordered_map<const AstScope*, std::vector<AstCell*>>::const_iterator it
            = m_wrapperCells.find(scopep);
        if (it == m_wrapperCells.end()) return;
        for (AstCell* const cellp : it->second) processWrapperCell(scopep, cellp);
    }

    // VISITORS
    void visit(AstScope* nodep) override {
        VL_RESTORER(m_scopep);
        m_scopep = nodep;
        m_scopeps.push_back(nodep);
        // A scope whose module is a described wrapper is a register wrapper cell of its parent
        if (nodep->aboveCellp() && fsmRegisterWrapperDesc(nodep->aboveCellp())) {
            m_wrapperCells[nodep->aboveScopep()].push_back(nodep->aboveCellp());
        }
        iterateChildrenConst(nodep);
    }
    void visit(AstCase* nodep) override {
        m_casesByScope[m_scopep].push_back(nodep);
        iterateChildrenConst(nodep);
    }
    void visit(AstNode* nodep) override { iterateChildrenConst(nodep); }

public:
    // CONSTRUCTORS
    FsmDetectVisitor(FsmState& state, AstNetlist* rootp)
        : m_state{state} {
        iterateConst(rootp);
        for (AstScope* const scopep : m_scopeps) processScope(scopep);
    }
    ~FsmDetectVisitor() override {
        for (AstNode* const nodep : m_ownedExprps) VL_DO_DANGLING(nodep->deleteTree(), nodep);
        V3Stats::addStat("Coverage, FSM registers tried", m_statRegisters);
        V3Stats::addStat("Coverage, FSMs found", m_statFsms);
        V3Stats::addStat("Coverage, FSM states", m_statStates);
        V3Stats::addStat("Coverage, FSM arcs", m_statArcs);
        V3Stats::addStat("Coverage, FSM registers with too many paths", m_statTooManyPaths);
    }
};

// Builder of statements that will handle incrementation of proper AstNodeCoverDecls - which will
// be also created here
class FsmCoverIncBuilder final {
    const FsmGraph& m_graph;  // Fsm graph
    std::vector<const FsmStateVertex*> m_states;  // States vertexes inside fsm graph
    std::unordered_set<uint64_t>
        m_undefinedStates;  // States that have no enum value but are possible to represent with a
                            // variable of given width.
                            // This variable keeps uint64_t instead of V3Numebr because it is safe
                            // to assume that nobody has over 16M TB of RAM
    const FsmVertex* m_resetVertexp = nullptr;  // Reset vertex
    size_t m_edgesCount = 0;  // Total count of edges
    AstVarScope* const m_prevVscp;  // Previous state of fsm
    FileLine* const m_flp;  // Fileline pointer to use across the builder
    const std::string m_modPrettyName;  // Pretty fsm mode name
    AstNodeStmt* m_coverIncp = nullptr;  // Increments proper CoverDecl after each change
    AstNodeStmt* m_initialCoverIncp = nullptr;  // Increments CoverDecl at the beggining of the sim
    AstCoverOtherDecl* m_declsp = nullptr;  // List of CoverDecls
    bool m_isComplete;  // Whether all possible values of state variable are covered by some state
    // (e.g.: when state variable has two bits this will be true if exactly
    // four states exist)

    AstConst* makeConst(const uint64_t value) {
        V3Number num{static_cast<AstNode*>(nullptr), m_prevVscp->width()};
        num.setQuad(value);
        num.isSigned(m_prevVscp->dtypep()->isSigned());
        return new AstConst{m_flp, num};
    }

    std::string quadToBitStirngLabel(const uint64_t val) {
        int width = m_prevVscp->width();
        UASSERT(width < 64, "We should not expand values that wide");
        std::string result = std::to_string(width) + "'b";
        // Binary not hex because in future we want to represent
        // four-state values accuratelly as well
        while (--width >= 0) result.push_back("01"[(val >> width) & 1]);
        return result;
    }

    void initExistingStates() {
        for (const V3GraphVertex& vtx : m_graph.vertices()) {
            const FsmVertex* const vertexp = vtx.as<FsmVertex>();
            m_edgesCount += vertexp->inEdges().size();
            if (const FsmStateVertex* const statep = vertexp->cast<FsmStateVertex>()) {
                m_states.push_back(statep);
            } else /* if (vertexp->isResetAny()) */ {
                UASSERT_OBJ(!std::exchange(m_resetVertexp, vertexp), m_graph.sampleVarScopep(),
                            "Two resets?");
            }
        }
        const int width = m_graph.sampleVarScopep()->width();
        m_isComplete = width < 64 && m_states.size() == (static_cast<size_t>(1) << width);
    }

    void initUndefinedStates() {
        UASSERT_OBJ(m_graph.sampleVarScopep()->width() < 64, m_graph.sampleVarScopep(),
                    "This FSM is too wide to expand - this should be caught earlier");
        const uint64_t combinationsCount = static_cast<size_t>(1)
                                           << m_graph.sampleVarScopep()->width();
        // Rolling trick allows to cut peak memory usage
        bool undefRolled = false;
        auto rollUndefs = [this, combinationsCount] {
            for (uint64_t i = 0; i < combinationsCount; ++i) {
                const auto insert = m_undefinedStates.insert(i);
                if (!insert.second) m_undefinedStates.erase(insert.first);
            }
        };
        for (const FsmStateVertex* const statep : m_states) {
            const V3Number& num = statep->value().num();
            const uint64_t value = num.toUQuad();
            if (!m_isComplete) {
                if (undefRolled) {
                    UASSERT_OBJ(m_undefinedStates.erase(value) == 1, m_graph.sampleVarScopep(),
                                "Two states has the same value?");
                } else {
                    UASSERT_OBJ(m_undefinedStates.insert(value).second, m_graph.sampleVarScopep(),
                                "Two states has the same value?");
                    if (m_undefinedStates.size() * 2 >= combinationsCount) {
                        undefRolled = true;
                        rollUndefs();
                    }
                }
            }
        }
        if (!(m_isComplete || undefRolled)) rollUndefs();
    }

    size_t getArcCountWithExpansion(const VFsmExpandType expand) const {
        size_t arcCountWithExpansion = ~0ULL;
        switch (expand) {
        case VFsmExpandType::DEFAULT: {  // LCOV_EXCL_LINE
            m_graph.sampleVarScopep()->v3fatalSrc(
                "At this point default should be substituted with a value it defaults to");
            break;
        }
        case VFsmExpandType::AUTO: {
            arcCountWithExpansion = m_edgesCount;
            if (m_resetVertexp) {
                UASSERT_OBJ(m_states.size() >= m_resetVertexp->outEdges().size(),
                            m_graph.sampleVarScopep(),
                            "Reset has more out edges than possible states?");
                arcCountWithExpansion += m_states.size() - m_resetVertexp->outEdges().size();
            }
            break;
        }
        case VFsmExpandType::AUTO_EXPAND: {
            arcCountWithExpansion = m_states.size() * m_states.size() - m_states.size();
            break;
        }
        case VFsmExpandType::FULL: {
            const int width = m_graph.sampleVarScopep()->width();
            // 32 is derived from:
            // tranitionsCount <= std::numeric_limits<uint64_t>::max()
            // (2^width)^2 - (2^width) <= 2^64 - 1
            // (2^width)^2 - (2^width) < 2^64 since we operate on integral values we can trade 1
            // log_2((2^width)^2 - (2^width)) < 64
            // log_2((2^width)^2) < 64 - `(2^width)` is negigible so, it may be dropped
            // 2width < 64
            if (width < 32) {
                const uint64_t combinationsCount = static_cast<size_t>(1) << width;
                arcCountWithExpansion = combinationsCount * combinationsCount - combinationsCount;
            }
            break;
        }
        }
        return arcCountWithExpansion;
    }

    AstCoverOtherDecl* buildStateCoverDecl(const std::string& label,
                                           const std::string& fsmTag = "") {
        AstCoverOtherDecl* const declp
            = new AstCoverOtherDecl{m_flp,
                                    "v_fsm_state/" + m_modPrettyName,
                                    m_graph.stateVarName() + "::" + label,
                                    "",
                                    0,
                                    m_graph.stateVarName(),
                                    "",
                                    label,
                                    fsmTag};
        // We run after scoping, so this is declared for one instance only
        declp->perInstance(true);
        m_declsp = AstNode::addNext(m_declsp, declp);
        return declp;
    }

    AstNodeStmt* buildCoverIncStmtp(const std::string& fromStateLabel,
                                    const std::string& toStateLabel,
                                    const std::string& baseLabel = "") {
        // Whole builder is designed in such a way that this function won't be called twice with
        // the same arguments - but if it will ever change in future, `AstCoverOtherDecl` shall be
        // cached for particular args set
        AstCoverOtherDecl* const declp = new AstCoverOtherDecl{
            m_flp,
            "v_fsm_arc/" + m_modPrettyName,
            m_graph.stateVarName() + "::" + fromStateLabel + "->" + toStateLabel,
            "",
            0,
            m_graph.stateVarName(),
            fromStateLabel,
            toStateLabel,
            baseLabel};
        // We run after scoping, so this is declared for one instance only
        declp->perInstance(true);
        m_declsp = AstNode::addNext(m_declsp, declp);
        return new AstCoverInc{m_flp, declp};
    }
    AstNodeStmt* buildExpandedTransitionHandler(const std::string& toStateLabel,
                                                const bool considerUndefs,
                                                const FsmStateVertex* const toStatep = nullptr) {
        AstCase* const arcCasep = new AstCase{
            m_flp, VCaseType::CT_CASE, new AstVarRef{m_flp, m_prevVscp, VAccess::READ}, nullptr};
        std::unordered_set<const FsmStateVertex*> handledSoureces;
        if (toStatep) {
            for (const V3GraphEdge& edge : toStatep->inEdges()) {
                if (const FsmStateVertex* const fromp = edge.fromp()->cast<FsmStateVertex>()) {
                    if (!handledSoureces.emplace(fromp).second) continue;
                    arcCasep->addItemsp(new AstCaseItem{
                        m_flp, makeConst(fromp->value().num().toUQuad()),
                        (fromp != toStatep) ? buildCoverIncStmtp(fromp->label(), toStateLabel)
                                            : nullptr});
                }
            }
        }
        for (const FsmStateVertex* const fromp : m_states) {
            if (handledSoureces.find(fromp) != handledSoureces.end()) continue;
            arcCasep->addItemsp(new AstCaseItem{
                m_flp, makeConst(fromp->value().num().toUQuad()),
                (fromp != toStatep)
                    ? buildCoverIncStmtp(fromp->label(), toStateLabel, "artificial")
                    : nullptr});
        }
        if (!m_isComplete) {
            if (considerUndefs) {
                for (const uint64_t from : m_undefinedStates) {
                    const std::string& label = quadToBitStirngLabel(from);
                    arcCasep->addItemsp(
                        new AstCaseItem{m_flp, makeConst(from),
                                        (label != toStateLabel)
                                            ? buildCoverIncStmtp(label, toStateLabel, "artificial")
                                            : nullptr});
                }
            } else {
                arcCasep->addItemsp(new AstCaseItem{m_flp, nullptr, nullptr});
            }
        }
        return arcCasep;
    }
    AstNodeStmt* buildUnxpandedTransitionHandler(const FsmStateVertex* const toStatep) {
        AstCase* const arcCasep = new AstCase{
            m_flp, VCaseType::CT_CASE, new AstVarRef{m_flp, m_prevVscp, VAccess::READ}, nullptr};
        for (const V3GraphEdge& edge : toStatep->inEdges()) {
            const FsmArcEdge* const arcp = edge.as<FsmArcEdge>();
            UASSERT_OBJ(!arcp->isReset(), m_graph.stateVarScopep(),
                        "This function should never be called on a target of a reset arc");
            const FsmStateVertex* const fromp = arcp->fromp()->as<FsmStateVertex>();
            if (fromp != toStatep) {
                arcCasep->addItemsp(
                    new AstCaseItem{m_flp, makeConst(fromp->value().num().toUQuad()),
                                    buildCoverIncStmtp(fromp->label(), toStatep->label())});
            }
        }
        arcCasep->addItemsp(new AstCaseItem{m_flp, nullptr, nullptr});
        return arcCasep;
    }

public:
    FsmCoverIncBuilder(const FsmGraph& graph, AstVarScope* const prevVscp)
        : m_graph{graph}
        , m_prevVscp{prevVscp}
        , m_flp{graph.fileline()}
        , m_modPrettyName{graph.scopep()->modp()->prettyName()} {
        initExistingStates();
        AstVarScope* const sampleVscp = graph.sampleVarScopep();
        const VFsmExpandType expand
            = graph.stateVarScopep()->varp()->attrFsmStateExpand() != VFsmExpandType::DEFAULT
                  ? graph.stateVarScopep()->varp()->attrFsmStateExpand()
                  : v3Global.opt.coverageFsmExpand();

        {
            const size_t arcCountWithExpansion = getArcCountWithExpansion(expand);
            if (VL_UNLIKELY(v3Global.opt.coverageFsmMaxArcs() < 0 || ~arcCountWithExpansion == 0ULL
                            || arcCountWithExpansion
                                   > static_cast<size_t>(v3Global.opt.coverageFsmMaxArcs()))) {
                sampleVscp->v3error("Exceeded size of --coverage-fsm-max-arcs "
                                    << v3Global.opt.coverageFsmMaxArcs()
                                    << " with: " << arcCountWithExpansion);
                return;
            }
        }

        AstCase* const arcCasep
            = new AstCase{m_flp, VCaseType::CT_CASE,
                          new AstVarRef{m_flp, graph.sampleVarScopep(), VAccess::READ}, nullptr};
        AstCase* const initialStateCasep
            = new AstCase{m_flp, VCaseType::CT_CASE,
                          new AstVarRef{m_flp, graph.sampleVarScopep(), VAccess::READ}, nullptr};

        const bool expandAll = expand != VFsmExpandType::AUTO;
        std::unordered_set<const FsmStateVertex*>
            resetTargets;  // States that have edge incoming from reset vertex
        if (!expandAll) {
            if (m_resetVertexp) {
                for (const V3GraphEdge& edge : m_resetVertexp->outEdges()) {
                    resetTargets.emplace(edge.top()->as<FsmStateVertex>());
                }
            }
        }
        const bool isFullExpansion = expand == VFsmExpandType::FULL;
        if (isFullExpansion) initUndefinedStates();
        for (const FsmStateVertex* const statep : m_states) {
            // State coverage fires when the FSM enters a state from any other
            // value, so repeated self-holds do not count as new entries.
            AstCoverOtherDecl* const declp = buildStateCoverDecl(statep->label());
            initialStateCasep->addItemsp(
                new AstCaseItem{m_flp, makeConst(statep->value().num().toUQuad()),
                                new AstCoverInc{m_flp, declp, true}});
            const bool expandAllOrReset
                = expandAll || (resetTargets.find(statep) != resetTargets.end());
            arcCasep->addItemsp(new AstCaseItem{
                m_flp, makeConst(statep->value().num().toUQuad()),
                AstNode::addNext<AstNodeStmt>(
                    new AstCoverInc{m_flp, declp},
                    expandAllOrReset
                        ? buildExpandedTransitionHandler(statep->label(), isFullExpansion, statep)
                        : buildUnxpandedTransitionHandler(statep))});
        }
        if (!m_isComplete) {
            // Case is incomplete default CaseItem is needed
            if (isFullExpansion) {
                for (const uint64_t value : m_undefinedStates) {
                    const std::string& label = quadToBitStirngLabel(value);
                    AstCoverOtherDecl* const declp = buildStateCoverDecl(label);
                    initialStateCasep->addItemsp(new AstCaseItem{
                        m_flp, makeConst(value), new AstCoverInc{m_flp, declp, true}});
                    arcCasep->addItemsp(
                        new AstCaseItem{m_flp, makeConst(value),
                                        AstNode::addNext<AstNodeStmt>(
                                            new AstCoverInc{m_flp, declp},
                                            buildExpandedTransitionHandler(label, true))});
                }
            } else {
                // No expansion
                arcCasep->addItemsp(new AstCaseItem{m_flp, nullptr, nullptr});
                initialStateCasep->addItemsp(new AstCaseItem{m_flp, nullptr, nullptr});
            }
        }
        m_coverIncp = arcCasep;
        m_initialCoverIncp = initialStateCasep;
    }
    VL_UNCOPYABLE(FsmCoverIncBuilder);
    ~FsmCoverIncBuilder() = default;
    AstNodeCoverDecl* getCoverDeclsp() const { return m_declsp; }
    AstNodeStmt* getCoverIncp() const { return m_coverIncp; }
    AstNodeStmt* getInitialCoverIncp() const { return m_initialCoverIncp; }
};

// Lower the completed FSM graphs into the concrete coverage declarations,
// previous-state tracking, and pre/post-triggered instrumentation that the
// runtime uses to record state and transition coverage.
class FsmLowerVisitor final {
    // STATE - across all visitors
    const FsmState& m_state;
    V3SharedTmps m_prevTmps{"__VfsmCovPrev", VVarType::MODULETEMP};  // Previous states

    // METHODS
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
        AstVarScope* const sampleVscp = graph.sampleVarScopep();
        FileLine* const flp = graph.fileline();
        AstNodeModule* const modp = scopep->modp();
        AstVarScope* const prevVscp
            = m_prevTmps.make(flp, scopep, sampleVscp->dtypep(), stateVscp->varp()->shortName());
        // The saved previous-state temp crosses the scheduler's pre/post split
        // in the same way as Verilator's built-in NBA shadow variables, so keep
        // both vars marked as post-life participants for stable MT ordering.
        stateVscp->optimizeLifePost(true);
        sampleVscp->optimizeLifePost(true);
        prevVscp->optimizeLifePost(true);

        AstActive* const initActivep
            = new AstActive{flp, "fsm-coverage-init",
                            new AstSenTree{flp, new AstSenItem{flp, AstSenItem::Initial{}}}};
        initActivep->senTreeStorep(initActivep->sentreep());
        // Seed the previous-state temp during initialization so the first
        // clock edge compares against a defined state value.
        initActivep->addProcsp(new AstInitialStatic{
            flp, new AstAssign{flp, new AstVarRef{flp, prevVscp, VAccess::WRITE},
                               new AstVarRef{flp, sampleVscp, VAccess::READ}}});
        scopep->addBlocksp(initActivep);

        AstAlwaysPost* const covPostp = new AstAlwaysPost{flp};
        bool updatePrevAfterPost = false;
        if (alwaysp) {
            // Save the previous state as plain sequential logic at the front of
            // the original always_ff body, then evaluate coverage in post logic
            // after the delayed state update commits. This avoids a scheduler
            // race between a separate AstAlwaysPre task and the real state
            // commit for direct parent-level registers.
            alwaysp->prependStmtsp(new AstAssign{flp, new AstVarRef{flp, prevVscp, VAccess::WRITE},
                                                 new AstVarRef{flp, sampleVscp, VAccess::READ}});
        } else {
            // Wrapper-derived register candidates do not have a parent
            // always_ff body to splice into. Sample coverage first, then save
            // the current state for the next clock tick; this survives cell
            // boundary scheduling where the real flop update lives elsewhere.
            updatePrevAfterPost = true;
            prevVscp->varp()->setIgnorePostRead();
        }

        {
            // Create and increment proper AstNodeCoverDecls
            const FsmCoverIncBuilder coverIncBuilder{graph, prevVscp};
            modp->addStmtsp(coverIncBuilder.getCoverDeclsp());
            initActivep->addProcsp(new AstInitial{flp, coverIncBuilder.getInitialCoverIncp()});
            covPostp->addStmtsp(
                new AstIf{flp,
                          new AstNeq{flp, new AstVarRef{flp, prevVscp, VAccess::READ},
                                     new AstVarRef{flp, sampleVscp, VAccess::READ}},
                          coverIncBuilder.getCoverIncp()});
        }

        if (updatePrevAfterPost) {
            covPostp->addStmtsp(new AstAssign{flp, new AstVarRef{flp, prevVscp, VAccess::WRITE},
                                              new AstVarRef{flp, sampleVscp, VAccess::READ}});
        }

        AstSenTree* const sentreep = buildSenTree(flp, graph.senses());
        AstActive* const activep = new AstActive{flp, "fsm-coverage", sentreep};
        activep->senTreeStorep(sentreep);
        scopep->addBlocksp(activep);
        activep->addProcsp(covPostp);
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

}  // namespace

void V3FsmDetect::detect(AstNetlist* rootp) {
    UINFO(2, __FUNCTION__ << ":");
    FsmState state;
    { FsmDetectVisitor detect{state, rootp}; }
    if (dumpGraphLevel() >= 6) {
        size_t index = 0;
        for (const DetectedFsm& fsm : state.fsms()) {
            fsm.graphp->dumpDotFilePrefixed(fsm.graphp->dumpTag(index++));
        }
    }
    { FsmLowerVisitor lower{state}; }
    V3Global::dumpCheckGlobalTree("fsm-detect", 0, dumpTreeEitherLevel() >= 3);
}
