// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Four-state logic handler
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
// - Splits four-state variables into two two-state variables
// - Handles wire conflicts
//
//*************************************************************************

#include "V3PchAstNoMT.h"

#include "V3Fourstate.h"

#include "V3UniqueNames.h"

#include <map>
#include <type_traits>
#include <utility>
#include <vector>

VL_DEFINE_DEBUG_FUNCTIONS;

/* TODOs:
 *  - Rest of operators
 *  - Statements - cases etc.
 *  - split asswignw into multiple statements
 *  - four-states printing
 */

#define VALUE_SUFFIX ""  // Needs to be empty so C++ api won't change
#define XZ_SUFFIX "__Vxz"

namespace {
struct FourstatePair final {
    AstNodeExpr* valuep;
    AstNodeExpr* xzp;
};

enum LogicType : char {
    UNINITIALIZED = 0,  // Logic type has not been evaluated
    TWO_STATE,  // Two-state expression
    TWO_STATE_WITH_FOUR_STATE_IN_SUBTREE,  // Two-state expression with four-state expression in
                                           // its subtree - this is necessary since some AstNodes
                                           // (e.g.: AstCastWrap or AstSel) may contain four-state
                                           // expression as a child but itself be a two-state. When
                                           // this occurs we need to know that for the sake of
                                           // short-circuiting (because we use precalculation
                                           // statements we need to know that we cannot put them
                                           // before current expression unconditionally)
    FOUR_STATE,  // Four-state expression
};

static void setLogicType(AstNodeExpr* const exprp, const LogicType logic) {
    exprp->user4(static_cast<int>(logic));
}

static void setFourstate(AstNodeExpr* const exprp, bool fourstate = true,
                         bool fourstateInSubTree = false) {
    setLogicType(exprp, fourstate ? FOUR_STATE
                                  : (fourstateInSubTree ? TWO_STATE_WITH_FOUR_STATE_IN_SUBTREE
                                                        : TWO_STATE));
}

static LogicType getLogicType(const AstNodeExpr* const exprp) {
    return static_cast<LogicType>(exprp->user4());
}

static bool isFourstate(const AstNodeExpr* const exprp) {
    const LogicType logic = getLogicType(exprp);
    UASSERT_OBJ(logic != UNINITIALIZED, exprp,
                "Logic type of expression: " << exprp->typeName() << " is unevaluated");
    return logic == FOUR_STATE;
}

// Return true when the expression is two-state and has four-state expression in sub-tree
static bool hasFourstateInSubtree(const AstNodeExpr* const exprp) {
    return getLogicType(exprp) == TWO_STATE_WITH_FOUR_STATE_IN_SUBTREE;
}

template <typename T, typename = void>
struct ReducerTrait final : std::false_type {};
template <typename T>
struct ReducerTrait<
    T, std::enable_if_t<std::is_same<decltype(std::declval<T>()(std::declval<FourstatePair>(),
                                                                std::declval<FourstatePair>())),
                                     FourstatePair>::value>>
    final : std::true_type {};

static bool isStaticallyGte(const V3Number& msb, const AstNodeExpr* const exprp) {
    FileLine* const flp = exprp->fileline();
    const int exprpWidth = exprp->width();
    if (V3Number{flp, 1, 0}
            .opGte(msb, V3Number{flp, exprpWidth, 0}.opSub(
                            V3Number{flp, exprpWidth, 0}.opShiftL(
                                V3Number{flp, exprpWidth, 1},
                                V3Number{flp, exprpWidth, static_cast<uint32_t>(exprpWidth)}),
                            V3Number{flp, exprpWidth, 1}))
            .isEqOne()) {
        return true;
    }
    if (const AstConst* const constp = VN_CAST(exprp, Const)) {
        if (V3Number{flp, 1, 0}.opGte(msb, constp->num()).isEqOne()) return true;
    }
    return false;
}
static bool isStaticallyNGte(const V3Number& msb, const AstNodeExpr* const exprp) {
    FileLine* const flp = exprp->fileline();
    if (const AstConst* const constp = VN_CAST(exprp, Const)) {
        return constp->num().isAnyXZ() || V3Number{flp, 1, 0}.opLt(msb, constp->num()).isNeqZero();
    }
    return false;
}
static bool needsSplitting(const AstNodeDType* const dtypep) {
    if (const AstBasicDType* const basicp = VN_CAST(dtypep->skipRefp(), BasicDType)) {
        return basicp->isFourstate();
    }
    return false;
}

class FTaskPortsHelper final {
    std::vector<AstVar*>
        m_currentFTaskRefPortps;  // Ports of FTask in order so we can connect AstArgs to them
    std::map<std::string, AstVar*>
        m_currentFTaskRefPortpsNamesToVarps;  // Ports names to their Vars so we can handle
                                              // named arguments

public:
    explicit FTaskPortsHelper(const AstNodeFTask* const ftaskp) {
        // TODO: Add caching
        UASSERT_OBJ(m_currentFTaskRefPortps.empty(), ftaskp,
                    "Tried to build a port map while another exists");
        UASSERT_OBJ(m_currentFTaskRefPortpsNamesToVarps.empty(), ftaskp,
                    "Tried to build a port map while another exists");
        for (AstNode* stmtp = ftaskp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
            if (AstVar* const varp = VN_CAST(stmtp, Var)) {
                if (varp->direction().isAny()
                    && !(varp->fourstateComplementp() || varp->isFourstateComplement())) {
                    m_currentFTaskRefPortps.push_back(varp);
                    m_currentFTaskRefPortpsNamesToVarps[varp->name()] = varp;
                }
            }
        }
    }

    AstVar* getArgPortVar(const std::string& name, const size_t idx) const {
        return name.empty() ? m_currentFTaskRefPortps.at(idx)
                            : m_currentFTaskRefPortpsNamesToVarps.at(name);
    }
    AstVar* lastp() const {
        return m_currentFTaskRefPortps.empty() ? nullptr : m_currentFTaskRefPortps.back();
    }
};
}  // namespace

// Propagates the logic type (two or four-state) on AstNodeExpr
// Needed as V3Width not always gives a correct logic type
class FourstateLogicTypePropagator final : public VNVisitor {
    bool m_fourstateInSubtree
        = false;  // Whether a four-state expression is present in a sub-tree of an expression

    void iterateChildrenSeparately(AstNode* const nodep) {
        auto foreach = [this](AstNode* nodep) {
            bool fourstateInSubtree = false;
            for (; nodep; nodep = nodep->nextp()) {
                m_fourstateInSubtree = false;
                iterate(nodep);
                fourstateInSubtree |= m_fourstateInSubtree;
            }
            return fourstateInSubtree;
        };
        // Cast to char so, there is no warnings
        m_fourstateInSubtree = static_cast<bool>(static_cast<char>(foreach(nodep->op1p()))
                                                 | static_cast<char>(foreach(nodep->op2p()))
                                                 | static_cast<char>(foreach(nodep->op3p()))
                                                 | static_cast<char>(foreach(nodep->op4p())));
    }

    void visit(AstConst* const nodep) override {
        iterateChildrenSeparately(nodep);
        setFourstate(nodep, nodep->num().isAnyXZ(), m_fourstateInSubtree);
        m_fourstateInSubtree |= isFourstate(nodep);
    }

    void visit(AstNodeVarRef* const nodep) override {
        setFourstate(nodep, needsSplitting(nodep->varp()->dtypep()), m_fourstateInSubtree);
        m_fourstateInSubtree |= isFourstate(nodep);
    }

    void visit(AstNodeFTaskRef* const nodep) override {
        iterateChildrenSeparately(nodep);
        setFourstate(nodep,
                     nodep->taskp()->fvarp() && needsSplitting(nodep->taskp()->fvarp()->dtypep()),
                     m_fourstateInSubtree);
        m_fourstateInSubtree |= isFourstate(nodep);
    }

    void visit(AstNodeUniop* const nodep) override {
        iterateChildrenSeparately(nodep);
        setFourstate(nodep, isFourstate(nodep->lhsp()), m_fourstateInSubtree);
    }

    void visit(AstCastWrap* const nodep) override {
        iterateChildrenSeparately(nodep);
        setFourstate(nodep, needsSplitting(nodep->dtypep()), m_fourstateInSubtree);
        m_fourstateInSubtree |= isFourstate(nodep);
    }

    void visit(AstNodeBiop* const nodep) override {
        iterateChildrenSeparately(nodep);
        setFourstate(nodep, isFourstate(nodep->lhsp()) || isFourstate(nodep->rhsp()),
                     m_fourstateInSubtree);
    }

    void visit(AstEqCase* const nodep) override {
        iterateChildrenSeparately(nodep);
        setFourstate(nodep, false, m_fourstateInSubtree);
    }

    void visit(AstNeqCase* const nodep) override {
        iterateChildrenSeparately(nodep);
        setFourstate(nodep, false, m_fourstateInSubtree);
    }

    void visit(AstDiv* nodep) override {
        iterateChildrenSeparately(nodep);
        if (AstConst* const constp = VN_CAST(nodep->rhsp(), Const)) {
            setFourstate(nodep,
                         isFourstate(nodep->lhsp()) || constp->num().isEqZero()
                             || constp->num().isAnyXZ(),
                         m_fourstateInSubtree);
        } else {
            setFourstate(nodep, m_fourstateInSubtree);
        }
        m_fourstateInSubtree |= isFourstate(nodep);
    }

    void visit(AstNodeTriop* const nodep) override {
        iterateChildrenSeparately(nodep);
        setFourstate(nodep,
                     isFourstate(nodep->lhsp()) || isFourstate(nodep->rhsp())
                         || isFourstate(nodep->thsp()),
                     m_fourstateInSubtree);
    }

    void visit(AstCReset* const nodep) override {
        iterateChildrenSeparately(nodep);
        setFourstate(nodep, false, m_fourstateInSubtree);
    }

    void visit(AstSFormatArg* const nodep) override {
        iterateChildrenSeparately(nodep);
        setFourstate(nodep, isFourstate(nodep->exprp()), m_fourstateInSubtree);
    }

    void visit(AstSel* const nodep) override {
        iterateChildrenSeparately(nodep);
        setFourstate(nodep, isFourstate(nodep->fromp()), m_fourstateInSubtree);
    }

    void visit(AstCExprUser* const nodep) override {
        iterateChildrenSeparately(nodep);
        setFourstate(nodep, false, m_fourstateInSubtree);
    }

    void visit(AstRedOr* const nodep) override {
        iterateChildrenSeparately(nodep);
        setFourstate(nodep, isFourstate(nodep->lhsp()), m_fourstateInSubtree);
    }

    void visit(AstTime* const nodep) override {
        iterateChildrenSeparately(nodep);
        // Time is actually a fourstate but we never put `x` or `z` there
        setFourstate(nodep, false, m_fourstateInSubtree);
    }

    void visit(AstScopeName* const nodep) override {
        iterateChildrenSeparately(nodep);
        setFourstate(nodep, false, m_fourstateInSubtree);
    }

    void visit(AstClassOrPackageRef* const nodep) override {
        iterateChildrenSeparately(nodep);
        setFourstate(nodep, false, m_fourstateInSubtree);
    }

    // void visit(AstCMethodHard* const nodep) override {
    //     iterateChildrenSeparately(nodep);
    //     setFourstate(nodep, false, m_fourstateInSubtree);
    // }

    void visit(AstCExpr* const nodep) override {
        iterateChildrenSeparately(nodep);
        setFourstate(nodep, false, m_fourstateInSubtree);
    }

    void visit(AstRand* const nodep) override {
        iterateChildrenSeparately(nodep);
        setFourstate(nodep, false, m_fourstateInSubtree);
    }

    void visit(AstRandRNG* const nodep) override {
        iterateChildrenSeparately(nodep);
        setFourstate(nodep, false, m_fourstateInSubtree);
    }

    void visit(AstMemberSel* const nodep) override {
        iterateChildrenSeparately(nodep);
        setFourstate(nodep, needsSplitting(nodep->varp()->dtypep()), m_fourstateInSubtree);
    }

    void visit(AstSFormatF* const nodep) override {
        iterateChildrenSeparately(nodep);
        setFourstate(nodep, false, m_fourstateInSubtree);
    }

    void visit(AstStructSel* const nodep) override {
        iterateChildrenSeparately(nodep);
        setFourstate(nodep, isFourstate(nodep->fromp()), m_fourstateInSubtree);
    }

    void visit(AstExprStmt* const nodep) override {
        iterateChildrenSeparately(nodep);
        setFourstate(nodep, isFourstate(nodep->resultp()), m_fourstateInSubtree);
    }

    void visit(AstConsPackMember* const nodep) override {
        iterateChildrenSeparately(nodep);
        setFourstate(nodep, isFourstate(nodep->rhsp()), m_fourstateInSubtree);
    }

    void visit(AstFOpen* const nodep) override {
        iterateChildrenSeparately(nodep);
        setFourstate(nodep, false, m_fourstateInSubtree);
    }

    // void visit(AstFOpenMcd* const nodep) override {
    //     iterateChildrenSeparately(nodep);
    //     setFourstate(nodep, false, m_fourstateInSubtree);
    // }

    void visit(AstLambdaArgRef* const nodep) override {
        iterateChildrenSeparately(nodep);
        setFourstate(nodep, needsSplitting(nodep->dtypep()), m_fourstateInSubtree);
    }

    // void visit(AstTestPlusArgs* const nodep) override {
    //     iterateChildrenSeparately(nodep);
    //     setFourstate(nodep, false, m_fourstateInSubtree);
    // }

    // void visit(AstValuePlusArgs* const nodep) override {
    //     iterateChildrenSeparately(nodep);
    //     setFourstate(nodep, false, m_fourstateInSubtree);
    // }

    void visit(AstCvtArrayToPacked* const nodep) override {
        iterateChildrenSeparately(nodep);
        setFourstate(nodep, needsSplitting(nodep->fromp()->dtypep()), m_fourstateInSubtree);
    }

    void visit(AstSScanF* const nodep) override {
        iterateChildrenSeparately(nodep);
        setFourstate(nodep, false, m_fourstateInSubtree);
    }

    // void visit(AstFScanF* const nodep) override {  // We want to get UNSUPPORTED error right now
    //     iterateChildrenSeparately(nodep);
    //     setFourstate(nodep, false, m_fourstateInSubtree);
    // }

    void visit(AstFourstateExpr* const nodep) override {
        iterateChildrenSeparately(nodep);
        // The `false` is a lie but this visitor is here just for debug purposes so, after
        // FourstateVisitor we can check whether any four-state expression has not been handled.
        // This lie is safe since before V3Fourstate no AstFourstateExpr exists
        setFourstate(nodep, false, m_fourstateInSubtree);
    }

    void visit(AstNodeExpr* const nodep) override {
        iterateChildrenSeparately(nodep);
        if (AstBasicDType* const basicp = VN_CAST(nodep->dtypep()->skipRefOrNullp(), BasicDType)) {
            if (basicp->keyword().isIntNumeric()) {
                nodep->v3warn(E_UNSUPPORTED, "Unsupported: Operator "
                                                 << nodep->typeName()
                                                 << " not supported in the four-state mode");
            }
        }
        setFourstate(nodep, false, m_fourstateInSubtree);  // Set an arbitrary logic type
    }

    void visit(AstNode* nodep) override {
        VL_RESTORER(m_fourstateInSubtree);
        iterateChildrenSeparately(nodep);
    }

public:
    FourstateLogicTypePropagator(AstNode* const nodep) { iterate(nodep); }
    ~FourstateLogicTypePropagator() override = default;
};

// Splits AstVar of four-state type into two two-states
// Transforms four-state logic expressions into two-states
// Handles AssignW conflict resolution
class FourstateVisitor final : public VNVisitor {
    const VNUser1InUse m_user1InUse;
    const VNUser2InUse m_user2InUse;
    const VNUser3InUse m_user3InUse;
    const VNUser4InUse m_user4InUse;
    // Node status
    // AstVar::user1p           ->  AstVar*.        Where is value part of splitted variable - xz
    // AstNodeExpr::user1p      ->  AstNodeExpr*.   Expression evaluating value component
    // AstNodeExpr::user2p      ->  AstNodeExpr*.   Expression evaluating xz component
    // AstSel::user3            ->  bool.           Whether it has been handled
    // AstNodeFTaskRef::user3   ->  bool.           Whether it has been handled
    // AstNodeExpr::user4       ->  LogicType.      Expression logic type (whether it is four
    //                                              or two state)

    static void setValuePartVarp(AstVar* const varp, AstVar* const valuep) {
        varp->user1p(valuep);
    }
    static AstVar* getValuePartVarp(AstVar* const varp) { return VN_AS(varp->user1p(), Var); }
    static void setSelpHandled(AstSel* const selp) { selp->user3(1); }
    static bool isSelpHandled(AstSel* const selp) { return selp->user3(); }
    static void setFTaskRefHandled(AstNodeFTaskRef* const ftaskRefp) { ftaskRefp->user3(1); }
    static bool isFTaskRefHandled(AstNodeFTaskRef* const ftaskRefp) { return ftaskRefp->user3(); }
    static void setExprValuep(AstNodeExpr* const fourstateExprp, AstNode* const valuep) {
        fourstateExprp->user1p(valuep);
    }
    static AstNodeExpr* getExprValuep(const AstNodeExpr* const fourstateExprp) {
        return VN_AS(fourstateExprp->user1p(), NodeExpr);
    }
    static void setExprXZp(AstNodeExpr* const fourstateExprp, AstNode* const xzp) {
        fourstateExprp->user2p(xzp);
    }
    static AstNodeExpr* getExprXZp(const AstNodeExpr* const fourstateExprp) {
        return VN_AS(fourstateExprp->user2p(), NodeExpr);
    }

    V3UniqueNames m_tmpNames;  // Unique names generator for temporary variables

    AstNode* m_currentTmpSpotp = nullptr;  // Node after which put AstVar* for temporary variable
    bool m_tmpFuncLocal
        = false;  // Whether temporary variables shall be created as function locals
    AstNodeStmt* m_currentStmtp = nullptr;  // Current statement
    std::vector<AstVar*> m_varpsToRemove;  // Vars to unlink and remove in destructor

    std::vector<FTaskPortsHelper> m_ftaskPortHelpers;  // Cache of FTaskPortsHelpers

    // array - whether numeric
    // map - width
    std::array<std::map<int, std::vector<AstVar*>>, 2>
        m_tmpUnusedVarps;  // Existing not in use temporary variables
    std::vector<AstVar*> m_tmpVarpsInUse;  // Temporary variables that are being currently used

    // Original AstVar* and pair of assignments <value, xz>
    using NetToAssignwps
        = std::map<const AstVar*, std::vector<std::pair<AstAssignW*, AstAssignW*>>>;
    NetToAssignwps m_assignWToTrior;  // Map from variables to their AssingWs
    NetToAssignwps m_assignWToTriand;  // Map from variables to their AssingWs
    NetToAssignwps m_assignWToWire;  // Map from variables to their AssingWs

    static FourstatePair triReducer(const FourstatePair& a, const FourstatePair& b) {
        FileLine* const flp = a.valuep->fileline();
        FourstatePair result;
        {
            // a.value | b.value
            result.valuep = new AstOr{flp, a.valuep, b.valuep};
        }
        {
            // (a.value & a.xz) | (b.value & b.xz) | (a.xz & b.xz) | (a.value & ~b.value & ~b.xz) |
            // (b.value & ~a.value & ~a.xz)
            result.xzp = new AstOr{
                flp,
                new AstOr{flp,
                          new AstOr{flp, new AstAnd{flp, a.valuep->cloneTree(false), a.xzp},
                                    new AstAnd{flp, b.valuep->cloneTree(false), b.xzp}},
                          new AstAnd{flp, a.xzp->cloneTree(false), b.xzp->cloneTree(false)}},
                new AstOr{flp,
                          new AstAnd{flp,
                                     new AstAnd{flp, a.valuep->cloneTree(false),
                                                new AstNot{flp, b.valuep->cloneTree(false)}},
                                     new AstNot{flp, b.xzp->cloneTree(false)}},
                          new AstAnd{flp,
                                     new AstAnd{flp, b.valuep->cloneTree(false),
                                                new AstNot{flp, a.valuep->cloneTree(false)}},
                                     new AstNot{flp, a.xzp->cloneTree(false)}}}};
        }
        return result;
    }
    static FourstatePair triandReducer(const FourstatePair& a, const FourstatePair& b) {
        FileLine* const flp = a.valuep->fileline();
        FourstatePair result;
        {
            // (a.value & b.xz) | (b.value & a.xz) | (a.value & b.value)
            result.valuep = new AstOr{
                flp,
                new AstOr{flp, new AstAnd{flp, a.valuep, b.xzp}, new AstAnd{flp, b.valuep, a.xzp}},
                new AstAnd{flp, a.valuep->cloneTree(false), b.valuep->cloneTree(false)}};
        }
        {
            // (a.xz & b.xz) | (a.value & b.value & a.xz) | (a.value & b.value & b.xz)
            result.xzp = new AstOr{
                flp,
                new AstOr{flp, new AstAnd{flp, a.xzp->cloneTree(false), b.xzp->cloneTree(false)},
                          new AstAnd{flp,
                                     new AstAnd{flp, a.valuep->cloneTree(false),
                                                b.valuep->cloneTree(false)},
                                     b.xzp->cloneTree(false)}},
                new AstAnd{flp,
                           new AstAnd{flp, a.valuep->cloneTree(false), b.valuep->cloneTree(false)},
                           b.xzp->cloneTree(false)}};
        }
        return result;
    }
    static FourstatePair triorReducer(const FourstatePair& a, const FourstatePair& b) {
        FileLine* const flp = a.valuep->fileline();
        FourstatePair result;
        {
            // a.value | b.value
            result.valuep = new AstOr{flp, a.valuep, b.valuep};
        }
        {
            // (a.value | b.xz) & (b.value | a.xz) & (a.xz | ~a.value) & (b.xz | ~b.value)
            result.xzp
                = new AstAnd{flp,
                             new AstAnd{flp, new AstOr{flp, a.valuep->cloneTree(false), b.xzp},
                                        new AstOr{flp, b.valuep->cloneTree(false), a.xzp}},
                             new AstAnd{flp,
                                        new AstOr{flp, a.xzp->cloneTree(false),
                                                  new AstNot{flp, a.valuep->cloneTree(false)}},
                                        new AstOr{flp, b.xzp->cloneTree(false),
                                                  new AstNot{flp, b.valuep->cloneTree(false)}}}};
        }
        return result;
    }

    template <typename Reducer_T>
    static FourstatePair buildTree(std::vector<FourstatePair> exprps, Reducer_T&& reducer) {
        static_assert(ReducerTrait<Reducer_T>::value, "Reducer_T shall fullfill reducer trait");
        while (exprps.size() > 1) {
            const size_t halfSize = exprps.size() / 2;
            for (size_t i = 0; i < halfSize; ++i) {
                exprps[i] = reducer(exprps[i], exprps.back());
                exprps.pop_back();
            }
        }
        return exprps[0];
    }

    template <typename Reducer_T>
    static void triorTriandReduce(const NetToAssignwps& assignWs, Reducer_T&& reducer) {
        for (const auto& pair : assignWs) {
            const auto& assignps = pair.second;
            if (assignps.size() < 2) continue;
            std::vector<FourstatePair> exprps;
            exprps.reserve(assignps.size());
            for (const auto& assignp : assignps) {
                exprps.push_back({assignp.first->rhsp()->unlinkFrBack(),
                                  assignp.second->rhsp()->unlinkFrBack()});
                const AstVarXRef* xarefp = nullptr;
                if (exprps.back().valuep->exists([&xarefp](const AstVarXRef* const refp) {
                        xarefp = refp;
                        return true;
                    })) {
                    // The issue is when hierarchical reference is being moved to another module.
                    // Then it shall be fixed
                    xarefp->v3warn(
                        E_UNSUPPORTED,
                        "Hierarchical references are unsupported in assigns with --fourstate");
                }
            }
            FourstatePair result = buildTree(std::move(exprps), reducer);
            assignps[0].first->rhsp(result.valuep);
            assignps[0].second->rhsp(result.xzp);
            for (size_t i = 1; i < assignps.size(); ++i) {
                assignps[i].first->unlinkFrBack()->deleteTree();
                assignps[i].second->unlinkFrBack()->deleteTree();
            }
        }
    }

    static AstConst* createZeroOrOnesp(const AstNodeExpr* const exprp, const bool ones = false) {
        AstConst* const resultp
            = new AstConst{exprp->fileline(), AstConst::WidthedValue{}, exprp->width(), 0};
        resultp->dtypeSetBitUnsized(exprp->width(), exprp->widthMin(), exprp->dtypep()->numeric());
        if (ones) resultp->num().setAllBits1();
        setFourstate(resultp, false);
        return resultp;
    }

    // {whether supported, whether four state} - second is needed for the recursion
    static std::pair<bool, bool> isDTypepSupported(const AstNodeDType* const dtypep) {
        if (const AstBasicDType* const basicp = VN_CAST(dtypep, BasicDType)) {
            return {true, basicp->isFourstate()};
        }
        if (const AstNodeUOrStructDType* const containerDTypep
            = VN_CAST(dtypep, NodeUOrStructDType)) {
            return {!containerDTypep->isFourstate(), containerDTypep->isFourstate()};
        }
        if (const AstSampleQueueDType* const containerDTypep = VN_CAST(dtypep, SampleQueueDType)) {
            std::pair<bool, bool> subDtype
                = isDTypepSupported(containerDTypep->subDTypep()->skipRefp());
            return {subDtype.first && !subDtype.second, false};
        }
        if (const AstQueueDType* const containerDTypep = VN_CAST(dtypep, QueueDType)) {
            std::pair<bool, bool> subDtype
                = isDTypepSupported(containerDTypep->subDTypep()->skipRefp());
            return {subDtype.first && !subDtype.second, false};
        }
        if (const AstAssocArrayDType* const containerDTypep = VN_CAST(dtypep, AssocArrayDType)) {
            std::pair<bool, bool> subDtype
                = isDTypepSupported(containerDTypep->subDTypep()->skipRefp());
            return {subDtype.first && !subDtype.second, false};
        }
        if (const AstUnpackArrayDType* const containerDTypep = VN_CAST(dtypep, UnpackArrayDType)) {
            std::pair<bool, bool> subDtype
                = isDTypepSupported(containerDTypep->subDTypep()->skipRefp());
            return {subDtype.first && !subDtype.second, false};
        }
        if (const AstPackArrayDType* const containerDTypep = VN_CAST(dtypep, PackArrayDType)) {
            std::pair<bool, bool> subDtype
                = isDTypepSupported(containerDTypep->subDTypep()->skipRefp());
            return {subDtype.first && !subDtype.second, false};
        }
        return {true, false};
    }

    void assignWConflictResolution(AstVar* const varp, AstAssignW* const assignwValuep,
                                   AstAssignW* const assignwXzp) {
        // Assignments to different things are unsupported
        switch (varp->varType()) {
        case VVarType::TRIOR:
            m_assignWToTrior[varp].emplace_back(assignwValuep, assignwXzp);
            break;
        case VVarType::TRIAND:
            m_assignWToTriand[varp].emplace_back(assignwValuep, assignwXzp);
            break;
        case VVarType::VAR:
        case VVarType::TRIWIRE:
        case VVarType::PORT:  // The issue with ports is that we lose information about the wire
                              // type (tri/triand/trior)
        case VVarType::WIRE: m_assignWToWire[varp].emplace_back(assignwValuep, assignwXzp); break;
        case VVarType::SUPPLY0:
        case VVarType::SUPPLY1:
        case VVarType::TRI0:
        case VVarType::TRI1:
            varp->v3warn(E_UNSUPPORTED,
                         "supply0/tri0 and supply1/tri1 are not supported with --fourstate");
            break;
        default:
            assignwValuep->v3fatalSrc(
                "Unexpected variable type on lhs of assign: " << varp->varType().ascii());
            break;
        }
    }

    class StatementPlaceHolder final {
        FourstateVisitor& m_visitor;
        AstNodeStmt* const m_prevStmtp;
        AstNodeStmt* const m_stmtp;

    public:
        explicit StatementPlaceHolder(FourstateVisitor& visitor, FileLine* const flp)
            : m_visitor{visitor}
            , m_prevStmtp{m_visitor.m_currentStmtp}
            , m_stmtp{new AstStmtExpr{flp, new AstConst{flp, 0}}} {
            m_visitor.m_currentStmtp = m_stmtp;
        }
        ~StatementPlaceHolder() {
            UASSERT_OBJ(m_stmtp->backp(), m_stmtp,
                        "Placeholder statement never used - maybe it is unnecessary?");
            m_stmtp->unlinkFrBack()->deleteTree();
            m_visitor.m_currentStmtp = m_prevStmtp;
        }
        AstNodeStmt* stmtp() const { return m_stmtp; }
    };

    struct TmpVarsReleaser final {
        FourstateVisitor& m_visitor;
        const size_t m_tmpVarpsInUseLen;
        explicit TmpVarsReleaser(FourstateVisitor& visitor)
            : m_visitor{visitor}
            , m_tmpVarpsInUseLen{m_visitor.m_tmpVarpsInUse.size()} {}
        ~TmpVarsReleaser() {
            UASSERT(m_tmpVarpsInUseLen <= m_visitor.m_tmpVarpsInUse.size(),
                    "There is less used tmp variables than before");
            for (size_t i = m_tmpVarpsInUseLen; i < m_visitor.m_tmpVarpsInUse.size(); ++i) {
                AstVar* const varp = m_visitor.m_tmpVarpsInUse[i];
                m_visitor
                    .m_tmpUnusedVarps[varp->dtypep()->numeric().isSigned() ? 1 : 0][varp->width()]
                    .push_back(varp);
            }
            m_visitor.m_tmpVarpsInUse.resize(m_tmpVarpsInUseLen);
        }
    };

    // Takes expression or AstVar and creates a new temporary variable
    AstVar* createTmp(AstNode* const nodep) {
        UASSERT_OBJ(
            VN_IS(nodep, NodeExpr) || VN_IS(nodep, Var), nodep,
            "This function shall only be called on expressions or variables, but was called on: "
                << nodep);
        UASSERT_OBJ(m_currentTmpSpotp, nodep, "No where to place tmp variable");
        AstNodeDType* const dtypep = nodep->dtypep();
        auto& pool = m_tmpUnusedVarps[dtypep->numeric().isSigned() ? 1 : 0];
        if (!pool[dtypep->width()].empty()) {
            AstVar* varp = pool[dtypep->width()].back();
            pool[dtypep->width()].pop_back();
            return varp;
        }
        AstVar* const varp = new AstVar{nodep->fileline(), VVarType::STMTTEMP,
                                        m_tmpNames.get(nodep), VFlagBitPacked{}, nodep->width()};
        m_currentTmpSpotp->addHereThisAsNext(varp);
        varp->funcLocal(m_tmpFuncLocal);
        varp->noSubst(true);
        m_tmpVarpsInUse.push_back(varp);
        return varp;
    }

    void splitVar(AstVar* const varp) {
        UASSERT_OBJ(needsSplitting(varp->dtypep()), varp,
                    "Split shall be called only on four-state variables");
        if (getValuePartVarp(varp)) return;
        m_varpsToRemove.push_back(varp);
        if (AstNodeFTask* const ftaskp = VN_CAST(varp->backp(), NodeFTask)) {
            if (ftaskp->fvarp() == varp) {
                AstVar* const portEndp = getFTaskPortHelper(ftaskp).lastp();
                AstVar* const returnValuep
                    = new AstVar{varp->fileline(), VVarType::PORT, varp->name() + VALUE_SUFFIX,
                                 VFlagBitPacked{}, varp->width()};
                AstVar* const returnXzp
                    = new AstVar{varp->fileline(), VVarType::PORT, varp->name() + XZ_SUFFIX,
                                 VFlagBitPacked{}, varp->width()};
                returnValuep->direction(VDirection::OUTPUT);
                returnXzp->direction(VDirection::OUTPUT);
                returnValuep->funcLocal(true);
                returnXzp->funcLocal(true);
                returnValuep->lifetime(VLifetime::AUTOMATIC_IMPLICIT);
                returnXzp->lifetime(VLifetime::AUTOMATIC_IMPLICIT);
                returnValuep->trace(varp->isTrace());
                returnValuep->fourstateOriginalDTypeKwd(varp->dtypep()->basicp()->keyword());
                returnXzp->fourstateOriginalDTypeKwd(varp->dtypep()->basicp()->keyword());
                if (portEndp) {
                    portEndp->addNextHere(returnXzp);
                    portEndp->addNextHere(returnValuep);
                } else if (AstNode* const stmtp = ftaskp->stmtsp()) {
                    stmtp->addHereThisAsNext(returnValuep);
                    stmtp->addHereThisAsNext(returnXzp);
                } else {
                    ftaskp->addStmtsp(returnValuep);
                    ftaskp->addStmtsp(returnXzp);
                }
                setValuePartVarp(varp, returnValuep);
                returnValuep->fourstateComplementp(returnXzp);
                ftaskp->dtypeSetVoid();
                return;
            }
        }
        AstVar* const newXzp = varp->cloneTree(false);
        newXzp->name(newXzp->name() + XZ_SUFFIX);
        newXzp->fourstateOriginalDTypeKwd(varp->dtypep()->basicp()->keyword());
        newXzp->dtypeSetBitUnsized(varp->width(), varp->widthMin(), varp->dtypep()->numeric());
        if (AstNodeExpr* const valuep = VN_CAST(newXzp->valuep(), NodeExpr)) {
            valuep->unlinkFrBack();
            newXzp->valuep(getFourstateExpressionXZ(valuep));
            valuep->deleteTree();
        }
        varp->addNextHere(newXzp);
        AstVar* const newValuep = varp->cloneTree(false);
        newValuep->name(newValuep->name() + VALUE_SUFFIX);
        newValuep->trace(varp->isTrace());
        newValuep->fourstateOriginalDTypeKwd(varp->dtypep()->basicp()->keyword());
        newValuep->dtypeSetBitUnsized(varp->width(), varp->widthMin(), varp->dtypep()->numeric());
        if (AstNodeExpr* const valuep = VN_CAST(newValuep->valuep(), NodeExpr)) {
            valuep->unlinkFrBack();
            newValuep->valuep(getFourstateExpressionValue(valuep));
            valuep->deleteTree();
        }
        newValuep->fourstateComplementp(newXzp);
        varp->addNextHere(newValuep);
        setValuePartVarp(varp, newValuep);
    }

    static AstVar* getSplittedValue(AstVar* const varp) {
        UASSERT_OBJ(needsSplitting(varp->dtypep()), varp,
                    "Split shall be called only on four-state variables");
        AstVar* const result = getValuePartVarp(varp);
        UASSERT_OBJ(result, varp, "Variable shall be split first");
        return result;
    }

    static AstVar* getSplittedXZ(AstVar* const varp) {
        return getSplittedValue(varp)->fourstateComplementp();
    }

    const FTaskPortsHelper& getFTaskPortHelper(AstNodeFTask* const ftaskp) {
        if (ftaskp->user1()) return m_ftaskPortHelpers[ftaskp->user1() - 1];
        ftaskp->user1(m_ftaskPortHelpers.size() + 1);
        m_ftaskPortHelpers.emplace_back(static_cast<const AstNodeFTask*>(ftaskp));
        return m_ftaskPortHelpers.back();
    }

    void addPrecalculation(AstNodeStmt* const nodep) {
        FourstateLogicTypePropagator{nodep};
        m_currentStmtp->addHereThisAsNext(nodep);
    }

    AstNodeExpr* getFourstateExpressionSelHandler(AstSel* const selp, AstNodeExpr* const valueExpr,
                                                  const bool defaultsToZero) {
        FileLine* const flp = selp->fileline();
        AstNodeExpr* lsbp = selp->lsbp();
        V3Number maxmsb{flp, lsbp->width(),
                        static_cast<uint32_t>(selp->fromp()->dtypep()->width() - 1)};
        if (isStaticallyNGte(maxmsb, lsbp)) {
            if (!selp->fromp()->isPure()) {
                addPrecalculation(new AstStmtExpr{flp, valueExpr});
                // No precalculation of lsbp because right now:
                // isStaticallyNGte(lsbp) => VN_IS(lsbp, Const)
            } else {
                valueExpr->deleteTree();
            }
            return createZeroOrOnesp(selp, !defaultsToZero);
        }
        AstSel* const newp = [selp] {
            AstNodeExpr* const fromp = selp->fromp()->unlinkFrBack();
            AstNodeExpr* const lsbp = selp->lsbp()->unlinkFrBack();
            AstSel* const newp = selp->cloneTree(false);
            selp->fromp(fromp);
            selp->lsbp(lsbp);
            return newp;
        }();
        setSelpHandled(newp);
        newp->fromp(valueExpr);
        const bool isStaticallyInRange = isStaticallyGte(maxmsb, lsbp);
        const bool isLsbpFourstete = isFourstate(lsbp);
        if (isStaticallyInRange && !isLsbpFourstete) {
            newp->lsbp(lsbp->cloneTree(false));
            return newp;
        }
        AstNodeExpr* conditionp;
        if (isLsbpFourstete) {
            conditionp = getFourstateExpressionXZ(lsbp, isFourstate(selp));
            if (!isStaticallyInRange) {
                conditionp = new AstOr{flp, conditionp,
                                       new AstLt{flp, new AstConst{flp, maxmsb},
                                                 getFourstateExpressionValue(lsbp, true)}};
            }
            lsbp = getFourstateExpressionValue(lsbp, true);
        } else {
            if (!VN_IS(lsbp, NodeVarRef) && !VN_IS(lsbp, Const)) {
                AstVar* const lsbTmpp = createTmp(lsbp);
                addPrecalculation(new AstAssign{flp, new AstVarRef{flp, lsbTmpp, VAccess::WRITE},
                                                lsbp->cloneTree(false)});
                lsbp = new AstVarRef{flp, lsbTmpp, VAccess::READ};
            } else {
                lsbp = lsbp->cloneTree(false);
            }
            conditionp = new AstLt{flp, new AstConst{flp, maxmsb}, lsbp->cloneTree(false)};
        }
        newp->lsbp(lsbp);
        return new AstCond{flp, conditionp, createZeroOrOnesp(selp, !defaultsToZero), newp};
    }

    // Base visitor for Value and XZ visitor, contains some common functionalities
    class FourstateExpressionVisitor VL_NOT_FINAL : public VNVisitor {
    protected:
        FourstateVisitor& m_fourstateVisitor;
        AstNodeExpr* m_result = nullptr;

    private:
        bool m_noTmp = false;
        bool m_enforceTmp = false;

        virtual AstNodeExpr* getCache(const AstNodeExpr* keyp) = 0;
        virtual void setCache(AstNodeExpr* keyp, AstNodeExpr* valuep) = 0;

    protected:
        void noTmp() { m_noTmp = true; }
        void enforceTmp() { m_enforceTmp = true; }

        void addPrecalculation(AstNodeStmt* const nodep) {
            FourstateLogicTypePropagator{nodep};
            m_fourstateVisitor.m_currentStmtp->addHereThisAsNext(nodep);
        }

        void fourstateExpressionFuncRefHandler(AstNodeFTaskRef* const funcRefp) {
            // Its ok to use this instead of output since we only need width which is the same
            AstVar* const functionReturnVarp = VN_AS(VN_AS(funcRefp->taskp(), Func)->fvarp(), Var);
            AstVar* const resultValuep = m_fourstateVisitor.createTmp(functionReturnVarp);
            AstVar* const resultXzp = m_fourstateVisitor.createTmp(functionReturnVarp);
            AstNodeFTaskRef* const newCallp = funcRefp->cloneTree(false);
            UASSERT_OBJ(!isFTaskRefHandled(newCallp), funcRefp,
                        "Trying to handle already handled four-state function call");
            setFTaskRefHandled(newCallp);
            if (newCallp->argsp()) newCallp->argsp()->unlinkFrBackWithNext()->deleteTree();
            FileLine* const flp = funcRefp->fileline();
            {
                size_t argIdx = 0;
                const FTaskPortsHelper& ftaskPortsHelper
                    = m_fourstateVisitor.getFTaskPortHelper(funcRefp->taskp());
                for (AstArg* argp = funcRefp->argsp(); argp; argp = VN_AS(argp->nextp(), Arg)) {
                    const AstVar* const varp
                        = ftaskPortsHelper.getArgPortVar(argp->name(), argIdx);
                    ++argIdx;
                    if (needsSplitting(varp->dtypep())) {
                        newCallp->addArgsp(new AstArg{
                            flp, "", getFourstateExpressionValue(argp->exprp(), false)});
                        newCallp->addArgsp(
                            new AstArg{flp, "", getFourstateExpressionXZ(argp->exprp(), false)});
                    } else if (isFourstate(argp->exprp())) {
                        newCallp->addArgsp(new AstArg{
                            flp, "", m_fourstateVisitor.getTwoStateCast(argp->exprp())});
                    } else {
                        newCallp->addArgsp(argp->cloneTree(false));
                    }
                }
            }
            AstVarRef* const resultValueRefp = new AstVarRef{flp, resultValuep, VAccess::WRITE};
            AstVarRef* const resultXzRefp = new AstVarRef{flp, resultXzp, VAccess::WRITE};
            setFourstate(resultValueRefp, false);
            setFourstate(resultXzRefp, false);
            {
                std::string resultName = funcRefp->taskp()->fvarp()->name();
                AstArg* const resultValueArgp
                    = new AstArg{flp, resultName + VALUE_SUFFIX, resultValueRefp};
                AstArg* const resultXZArgp
                    = new AstArg{flp, std::move(resultName) + XZ_SUFFIX, resultXzRefp};
                newCallp->addArgsp(resultValueArgp);
                newCallp->addArgsp(resultXZArgp);
            }
            AstStmtExpr* const newStmtExprp = new AstStmtExpr{flp, newCallp};
            addPrecalculation(newStmtExprp);
            AstVarRef* const varRefValuep = new AstVarRef{flp, resultValuep, VAccess::READ};
            AstVarRef* const varRefXzp = new AstVarRef{flp, resultXzp, VAccess::READ};
            pushDeletep(varRefValuep);
            pushDeletep(varRefXzp);
            setExprValuep(funcRefp, varRefValuep);
            setExprXZp(funcRefp, varRefXzp);
        }

        void fourstateExpressionCondHandler(AstCond* const condp) {
            FileLine* const flp = condp->fileline();
            AstVar* const resultValueTmpVarp = m_fourstateVisitor.createTmp(condp->thenp());
            AstVar* const resultXZTmpVarp = m_fourstateVisitor.createTmp(condp->thenp());
            AstIf* ifp = new AstIf{flp, isFourstate(condp->condp())
                                            ? getFourstateExpressionXZ(condp->condp())
                                            : condp->condp()->cloneTree(false)};
            // Those must be here so expr is always evaluated fully in the right place
            AstIf* twoStateIfp = ifp;
            if (isFourstate(condp->condp())) {
                // Condition is X/Z
                AstNodeExpr* conditionValuep = getFourstateExpressionValue(condp->condp());
                AstNodeExpr* const thenCopyp = condp->thenp()->cloneTree(false);
                AstNodeExpr* const elseCopyp = condp->elsep()->cloneTree(false);
                StatementPlaceHolder thenPlaceholder{m_fourstateVisitor, flp};
                ifp->addThensp(thenPlaceholder.stmtp());
                TmpVarsReleaser tmpVarsReleaser{m_fourstateVisitor};
                addPrecalculation(
                    new AstAssign{flp, new AstVarRef{flp, resultValueTmpVarp, VAccess::WRITE},
                                  getFourstateExpressionValue(thenCopyp, false)});
                addPrecalculation(
                    new AstAssign{flp, new AstVarRef{flp, resultXZTmpVarp, VAccess::WRITE},
                                  getFourstateExpressionXZ(thenCopyp, false)});
                AstIf* const thenifp = new AstIf{
                    flp, new AstOr{
                             flp,
                             new AstXor{flp, new AstVarRef{flp, resultValueTmpVarp, VAccess::READ},
                                        getFourstateExpressionValue(elseCopyp, false)},
                             new AstXor{flp, new AstVarRef{flp, resultXZTmpVarp, VAccess::READ},
                                        getFourstateExpressionXZ(elseCopyp, false)}}};
                ifp->addThensp(thenifp);
                thenifp->addThensp(
                    new AstAssign{flp, new AstVarRef{flp, resultValueTmpVarp, VAccess::WRITE},
                                  createZeroOrOnesp(thenCopyp, true)});
                thenifp->addThensp(
                    new AstAssign{flp, new AstVarRef{flp, resultXZTmpVarp, VAccess::WRITE},
                                  createZeroOrOnesp(thenCopyp, true)});
                thenCopyp->deleteTree();
                elseCopyp->deleteTree();
                twoStateIfp = new AstIf{flp, conditionValuep};
                ifp->addElsesp(twoStateIfp);
            }
            {
                // Condition is 1/0
                {
                    // Condition is 1
                    StatementPlaceHolder thenPlaceholder{m_fourstateVisitor, flp};
                    twoStateIfp->addThensp(thenPlaceholder.stmtp());
                    TmpVarsReleaser tmpVarsReleaser{m_fourstateVisitor};
                    addPrecalculation(
                        new AstAssign{flp, new AstVarRef{flp, resultValueTmpVarp, VAccess::WRITE},
                                      getFourstateExpressionValue(condp->thenp(), false)});
                    addPrecalculation(
                        new AstAssign{flp, new AstVarRef{flp, resultXZTmpVarp, VAccess::WRITE},
                                      getFourstateExpressionXZ(condp->thenp(), false)});
                }
                {
                    // Condition is 0
                    StatementPlaceHolder elsePlaceholder{m_fourstateVisitor, flp};
                    twoStateIfp->addElsesp(elsePlaceholder.stmtp());
                    TmpVarsReleaser tmpVarsReleaser{m_fourstateVisitor};
                    addPrecalculation(
                        new AstAssign{flp, new AstVarRef{flp, resultValueTmpVarp, VAccess::WRITE},
                                      getFourstateExpressionValue(condp->elsep(), false)});
                    addPrecalculation(
                        new AstAssign{flp, new AstVarRef{flp, resultXZTmpVarp, VAccess::WRITE},
                                      getFourstateExpressionXZ(condp->elsep(), false)});
                }
            }
            addPrecalculation(ifp);
            AstVarRef* const resultValueTmpVarRefp
                = new AstVarRef{flp, resultValueTmpVarp, VAccess::READ};
            AstVarRef* const resultXZTmpVarRefp
                = new AstVarRef{flp, resultXZTmpVarp, VAccess::READ};
            pushDeletep(resultValueTmpVarRefp);
            pushDeletep(resultXZTmpVarRefp);
            setExprValuep(condp, resultValueTmpVarRefp);
            setExprXZp(condp, resultXZTmpVarRefp);
        }

        void fourstateExpressionLogAndHandler(AstLogAnd* const logAndp) {
            FileLine* const flp = logAndp->fileline();
            AstVar* const resultValueTmpVarp = m_fourstateVisitor.createTmp(logAndp);
            AstVar* const resultXZTmpVarp = m_fourstateVisitor.createTmp(logAndp);
            addPrecalculation(new AstAssign{flp,
                                            new AstVarRef{flp, resultXZTmpVarp, VAccess::WRITE},
                                            getFourstateExpressionXZ(logAndp->lhsp(), false)});
            addPrecalculation(
                new AstAssign{flp, new AstVarRef{flp, resultValueTmpVarp, VAccess::WRITE},
                              new AstOr{flp, new AstVarRef{flp, resultXZTmpVarp, VAccess::READ},
                                        getFourstateExpressionValue(logAndp->lhsp(), false)}});
            AstIf* const ifp
                = new AstIf{flp, new AstVarRef{flp, resultValueTmpVarp, VAccess::READ}};
            addPrecalculation(ifp);
            {
                // Lhs is non zero
                StatementPlaceHolder placeholderStmt{m_fourstateVisitor, flp};
                ifp->addThensp(placeholderStmt.stmtp());
                TmpVarsReleaser{m_fourstateVisitor};
                addPrecalculation(new AstAssign{
                    flp, new AstVarRef{flp, resultValueTmpVarp, VAccess::WRITE},
                    new AstOr{flp, getFourstateExpressionValue(logAndp->rhsp(), false),
                              getFourstateExpressionXZ(logAndp->rhsp())}});
                addPrecalculation(new AstAssign{
                    flp, new AstVarRef{flp, resultXZTmpVarp, VAccess::WRITE},
                    new AstLogAnd{flp, new AstVarRef{flp, resultValueTmpVarp, VAccess::READ},
                                  new AstOr{flp,
                                            new AstVarRef{flp, resultXZTmpVarp, VAccess::READ},
                                            getFourstateExpressionXZ(logAndp->rhsp())}}});
            }
            AstVarRef* const resultValueTmpVarRefp
                = new AstVarRef{flp, resultValueTmpVarp, VAccess::READ};
            AstVarRef* const resultXZTmpVarRefp
                = new AstVarRef{flp, resultXZTmpVarp, VAccess::READ};
            pushDeletep(resultValueTmpVarRefp);
            pushDeletep(resultXZTmpVarRefp);
            setExprValuep(logAndp, resultValueTmpVarRefp);
            setExprXZp(logAndp, resultXZTmpVarRefp);
        }

        void fourstateExpressionLogOrHandler(AstLogOr* const logOrp) {
            FileLine* const flp = logOrp->fileline();
            AstVar* const resultValueTmpVarp = m_fourstateVisitor.createTmp(logOrp);
            AstVar* const resultXZTmpVarp = m_fourstateVisitor.createTmp(logOrp);
            addPrecalculation(new AstAssign{flp,
                                            new AstVarRef{flp, resultXZTmpVarp, VAccess::WRITE},
                                            getFourstateExpressionXZ(logOrp->lhsp(), false)});
            addPrecalculation(new AstAssign{flp,
                                            new AstVarRef{flp, resultValueTmpVarp, VAccess::WRITE},
                                            getFourstateExpressionValue(logOrp->lhsp(), false)});
            AstIf* const ifp = new AstIf{
                flp,
                new AstOr{flp,
                          new AstNot{flp, new AstVarRef{flp, resultValueTmpVarp, VAccess::READ}},
                          new AstVarRef{flp, resultXZTmpVarp, VAccess::READ}}};
            addPrecalculation(ifp);
            {
                // Lhs is non one
                StatementPlaceHolder placeholderStmt{m_fourstateVisitor, flp};
                ifp->addThensp(placeholderStmt.stmtp());
                TmpVarsReleaser{m_fourstateVisitor};
                addPrecalculation(new AstAssign{
                    flp, new AstVarRef{flp, resultValueTmpVarp, VAccess::WRITE},
                    new AstOr{flp, getFourstateExpressionValue(logOrp->rhsp()),
                              new AstOr{flp, getFourstateExpressionXZ(logOrp->rhsp()),
                                        new AstVarRef{flp, resultXZTmpVarp, VAccess::READ}}}});
                addPrecalculation(new AstAssign{
                    flp, new AstVarRef{flp, resultXZTmpVarp, VAccess::WRITE},
                    new AstLogAnd{
                        flp, new AstVarRef{flp, resultValueTmpVarp, VAccess::READ},
                        new AstOr{flp,
                                  new AstNot{flp, getFourstateExpressionValue(logOrp->rhsp())},
                                  getFourstateExpressionXZ(logOrp->rhsp())}}});
            }
            AstVarRef* const resultValueTmpVarRefp
                = new AstVarRef{flp, resultValueTmpVarp, VAccess::READ};
            AstVarRef* const resultXZTmpVarRefp
                = new AstVarRef{flp, resultXZTmpVarp, VAccess::READ};
            pushDeletep(resultValueTmpVarRefp);
            pushDeletep(resultXZTmpVarRefp);
            setExprValuep(logOrp, resultValueTmpVarRefp);
            setExprXZp(logOrp, resultXZTmpVarRefp);
        }

        AstNodeExpr* get(AstNodeExpr* const exprp, bool putIntoTmp = true) {
            // VN_AS is expected to be here (instead of VN_CAST)
            if (AstNodeExpr* result = getCache(exprp)) return result->cloneTree(false);
            m_result = nullptr;
            VL_RESTORER(m_noTmp);
            VL_RESTORER(m_enforceTmp);
            m_noTmp = false;
            m_enforceTmp = false;
            iterate(exprp);
            UASSERT_OBJ(m_result, exprp,
                        "Result shall always be returned - even if it is just a place holder");
            UASSERT_OBJ(!(m_noTmp && m_enforceTmp), exprp,
                        "Expression may not enforce and omit tmp variable at the same time");
            if (m_enforceTmp || (putIntoTmp && !m_noTmp)) {
                FileLine* const flp = exprp->fileline();
                AstVar* const varp = m_fourstateVisitor.createTmp(exprp);
                AstVarRef* const varRefp = new AstVarRef{flp, varp, VAccess::WRITE};
                AstAssign* const assignp = new AstAssign{flp, varRefp, m_result};
                addPrecalculation(assignp);
                m_result = new AstVarRef{flp, varp, VAccess::READ};
                setFourstate(m_result, false);
            }
            setCache(exprp, m_result);
            return m_result;
        }

    public:
        explicit FourstateExpressionVisitor(FourstateVisitor& fourstateVisitor)
            : m_fourstateVisitor{fourstateVisitor} {}
        ~FourstateExpressionVisitor() override = default;

        virtual AstNodeExpr* getFourstateExpressionValue(AstNodeExpr* const exprp,
                                                         bool putIntoTmp = true) {
            return m_fourstateVisitor.m_fourstateGeneratorValueVisitor.getFourstateExpressionValue(
                exprp, putIntoTmp);
        }

        virtual AstNodeExpr* getFourstateExpressionXZ(AstNodeExpr* const exprp,
                                                      const bool putIntoTmp = true) {
            return m_fourstateVisitor.m_fourstateGeneratorXZVisitor.getFourstateExpressionXZ(
                exprp, putIntoTmp);
        }
    };

    // Visitor used to get an expression with a value of a value part of a four-state expression
    // This can be thought as a function - but a Visitor was used to be able to use vtable, create
    // some enclosing namespace and benefit from inheritance
    class FourstateExpressionValueVisitor final : public FourstateExpressionVisitor {

        void visit(AstAnd* const andp) override {
            // (a.value | a.xz) & (b.value | b.xz)
            FileLine* const flp = andp->fileline();
            m_result = new AstAnd{flp,
                                  new AstOr{flp, getFourstateExpressionValue(andp->lhsp()),
                                            getFourstateExpressionXZ(andp->lhsp())},
                                  new AstOr{flp, getFourstateExpressionValue(andp->rhsp()),
                                            getFourstateExpressionXZ(andp->rhsp())}};
        }

        void visit(AstOr* const orp) override {
            // a.value | b.value | a.xz | b.xz
            FileLine* const flp = orp->fileline();
            m_result = new AstOr{flp,
                                 new AstOr{flp, getFourstateExpressionValue(orp->lhsp()),
                                           getFourstateExpressionValue(orp->rhsp())},
                                 new AstOr{flp, getFourstateExpressionXZ(orp->lhsp()),
                                           getFourstateExpressionXZ(orp->rhsp())}};
        }

        void visit(AstXor* const xorp) override {
            // (a.value ^ b.value) | a.xz | b.xz
            FileLine* const flp = xorp->fileline();
            m_result = new AstOr{flp,
                                 new AstXor{flp, getFourstateExpressionValue(xorp->lhsp(), false),
                                            getFourstateExpressionValue(xorp->rhsp(), false)},
                                 getFourstateExpressionXZ(xorp)};
        }

        void visit(AstNot* const notp) override {
            // ~a.value | a.xz
            FileLine* const flp = notp->fileline();
            m_result = new AstOr{flp, new AstNot{flp, getFourstateExpressionValue(notp->lhsp())},
                                 getFourstateExpressionXZ(notp->lhsp())};
        }

        template <typename CompoarisonOp_T>
        void visitCompare(CompoarisonOp_T* const cmpp) {
            // |(a.xz | b.xz) | (a.value op b.value)
            FileLine* const flp = cmpp->fileline();
            m_result
                = new AstOr{flp, getFourstateExpressionXZ(cmpp),
                            new CompoarisonOp_T{flp, getFourstateExpressionValue(cmpp->lhsp()),
                                                getFourstateExpressionValue(cmpp->rhsp())}};
        }

        void visit(AstEq* const eqp) override { visitCompare(eqp); }
        void visit(AstNeq* const neqp) override { visitCompare(neqp); }
        void visit(AstGt* const gtp) override { visitCompare(gtp); }
        void visit(AstGte* const gtep) override { visitCompare(gtep); }
        void visit(AstLt* const ltp) override { visitCompare(ltp); }
        void visit(AstLte* const ltep) override { visitCompare(ltep); }

        void visit(AstGtS* const gtp) override { visitCompare(gtp); }
        void visit(AstGteS* const gtep) override { visitCompare(gtep); }
        void visit(AstLtS* const ltp) override { visitCompare(ltp); }
        void visit(AstLteS* const ltep) override { visitCompare(ltep); }

        void visit(AstEqWild* const eqWildp) override {
            // ((a.value | b.xz) == (b.value | b.xz)) | |(a.xz & ~b.xz)
            FileLine* const flp = eqWildp->fileline();
            m_result = new AstOr{
                flp,
                new AstEq{flp,
                          new AstOr{flp, getFourstateExpressionValue(eqWildp->lhsp(), false),
                                    getFourstateExpressionXZ(eqWildp->rhsp())},
                          new AstOr{flp, getFourstateExpressionValue(eqWildp->rhsp(), false),
                                    getFourstateExpressionXZ(eqWildp->rhsp())}},
                getFourstateExpressionXZ(eqWildp)};
        }

        void visit(AstNeqWild* const neqWildp) override {
            // ((a.value | b.xz) != (b.value | b.xz)) | |(a.xz & ~b.xz)
            FileLine* const flp = neqWildp->fileline();
            m_result = new AstOr{
                flp,
                new AstNeq{flp,
                           new AstOr{flp, getFourstateExpressionValue(neqWildp->lhsp(), false),
                                     getFourstateExpressionXZ(neqWildp->rhsp())},
                           new AstOr{flp, getFourstateExpressionValue(neqWildp->rhsp(), false),
                                     getFourstateExpressionXZ(neqWildp->rhsp())}},
                getFourstateExpressionXZ(neqWildp)};
        }

        void visit(AstShiftL* const shiftlp) override {
            // |b.xz ? '1 : (a.value << b.value)
            FileLine* const flp = shiftlp->fileline();
            m_result = new AstCond{
                flp, new AstRedOr{flp, getFourstateExpressionXZ(shiftlp->rhsp())},
                createZeroOrOnesp(shiftlp->lhsp(), true),
                new AstShiftL{
                    flp,
                    getFourstateExpressionValue(
                        shiftlp->lhsp(), true /*must be in tmp so it always gets evaluated*/),
                    getFourstateExpressionValue(shiftlp->rhsp())}};
        }

        void visit(AstShiftR* const shiftrp) override {
            // |b.xz ? '1 : (a.value >> b.value)
            FileLine* const flp = shiftrp->fileline();
            m_result = new AstCond{
                flp, new AstRedOr{flp, getFourstateExpressionXZ(shiftrp->rhsp())},
                createZeroOrOnesp(shiftrp->lhsp(), true),
                new AstShiftR{
                    flp,
                    getFourstateExpressionValue(
                        shiftrp->lhsp(), true /*must be in tmp so it always gets evaluated*/),
                    getFourstateExpressionValue(shiftrp->rhsp())}};
        }

        void visit(AstExtend* const extendp) override {
            FileLine* const flp = extendp->fileline();
            m_result = new AstExtend{flp, getFourstateExpressionValue(extendp->lhsp(), false),
                                     extendp->width()};
        }

        void visit(AstExtendS* const extendsp) override {
            FileLine* const flp = extendsp->fileline();
            m_result = new AstExtendS{flp, getFourstateExpressionValue(extendsp->lhsp(), false),
                                      extendsp->width()};
        }

        void visit(AstCReset* const cresetp) override {
            m_result = cresetp->cloneTree(false);
            m_result->dtypeSetBitSized(cresetp->width(), cresetp->dtypep()->numeric());
        }

        void visit(AstConst* const constp) override {
            noTmp();
            AstConst* const newp = constp->cloneTree(false);
            newp->num().opBitsOneX(constp->num());
            newp->dtypeSetBitUnsized(newp->width(), newp->dtypep()->widthMin(),
                                     newp->dtypep()->numeric());
            m_result = newp;
        }

        void visit(AstNodeFTaskRef* const funcp) override {
            fourstateExpressionFuncRefHandler(funcp);
            noTmp();
            m_result = getExprValuep(funcp)->cloneTree(false);
        }

        void visit(AstCond* const condp) override {
            fourstateExpressionCondHandler(condp);
            noTmp();
            m_result = getExprValuep(condp)->cloneTree(false);
        }

        void visit(AstLogAnd* const logAndp) override {
            fourstateExpressionLogAndHandler(logAndp);
            noTmp();
            m_result = getExprValuep(logAndp)->cloneTree(false);
        }

        void visit(AstLogOr* const logOrp) override {
            fourstateExpressionLogOrHandler(logOrp);
            noTmp();
            m_result = getExprValuep(logOrp)->cloneTree(false);
        }

        void visit(AstSel* const selp) override {
            m_result = m_fourstateVisitor.getFourstateExpressionSelHandler(
                selp, getFourstateExpressionValue(selp->fromp(), false), false);
        }

        void visit(AstRedAnd* const redAndp) override {
            // &(a.value | a.xz)
            enforceTmp();
            FileLine* const flp = redAndp->fileline();
            m_result = new AstRedAnd{
                flp, new AstOr{flp, getFourstateExpressionValue(redAndp->lhsp(), false),
                               getFourstateExpressionXZ(redAndp->lhsp())}};
        }

        void visit(AstRedOr* const redOrp) override {
            // |(a.value | a.xz)
            FileLine* const flp = redOrp->fileline();
            m_result
                = new AstRedOr{flp, new AstOr{flp, getFourstateExpressionValue(redOrp->lhsp()),
                                              getFourstateExpressionXZ(redOrp->lhsp())}};
        }

        void visit(AstRedXor* const redXorp) override {
            // |a.xz | ^a.value
            FileLine* const flp = redXorp->fileline();
            m_result = new AstOr{
                flp, new AstRedOr{flp, getFourstateExpressionXZ(redXorp->lhsp())},
                new AstRedXor{flp, getFourstateExpressionValue(redXorp->lhsp(), false)}};
        }

        template <typename CompoarisonOp_T>
        void getFourstateExpressionArithmeticValue(CompoarisonOp_T* const biop) {
            // |(a.xz | b.xz) ? '1 : (a op b)
            FileLine* const flp = biop->fileline();
            m_result = new AstCond{
                flp,
                new AstRedOr{flp, new AstOr{flp, getFourstateExpressionXZ(biop->lhsp()),
                                            getFourstateExpressionXZ(biop->rhsp())}},
                createZeroOrOnesp(biop, true),
                new CompoarisonOp_T{
                    flp,
                    getFourstateExpressionValue(
                        biop->lhsp(), true /*must be in tmp so it always gets evaluated*/),
                    getFourstateExpressionValue(
                        biop->rhsp(), true /*must be in tmp so it always gets evaluated*/)}};
        }

        void visit(AstAdd* const addp) override { getFourstateExpressionArithmeticValue(addp); }
        void visit(AstSub* const subp) override { getFourstateExpressionArithmeticValue(subp); }
        void visit(AstMul* const mulp) override { getFourstateExpressionArithmeticValue(mulp); }
        void visit(AstMulS* const mulsp) override { getFourstateExpressionArithmeticValue(mulsp); }

        template <typename CompoarisonOp_T>
        void getFourstateExpressionDivValue(CompoarisonOp_T* const biop) {
            // |(a.xz | b.xz) | ~|b.value ? '1 : (a op b)
            FileLine* const flp = biop->fileline();
            m_result = new AstCond{
                flp,
                new AstOr{
                    flp,
                    new AstRedOr{flp, new AstOr{flp, getFourstateExpressionXZ(biop->lhsp()),
                                                getFourstateExpressionXZ(biop->rhsp())}},
                    new AstNot{flp, new AstRedOr{flp, getFourstateExpressionValue(biop->rhsp())}}},
                createZeroOrOnesp(biop, true),
                new CompoarisonOp_T{
                    flp,
                    getFourstateExpressionValue(
                        biop->lhsp(), true /*must be in tmp so it always gets evaluated*/),
                    getFourstateExpressionValue(
                        biop->rhsp(), true /*must be in tmp so it always gets evaluated*/)}};
        }

        void visit(AstDiv* const divp) override { getFourstateExpressionDivValue(divp); }
        void visit(AstDivS* const divsp) override { getFourstateExpressionDivValue(divsp); }
        void visit(AstModDiv* const moddivp) override { getFourstateExpressionDivValue(moddivp); }
        void visit(AstModDivS* const moddivsp) override {
            getFourstateExpressionDivValue(moddivsp);
        }

        void visit(AstConcat* const concatp) override {
            // {a.value, b.value}
            m_result = new AstConcat{concatp->fileline(),
                                     getFourstateExpressionValue(concatp->lhsp(), false),
                                     getFourstateExpressionValue(concatp->rhsp(), false)};
        }

        void visit(AstReplicate* const replicatep) override {
            // {count{src.value}}
            // IEEE 1800-2023 11.4.12.1 Replication operator:
            // 'A replication operator (also called a multiple concatenation) is expressed by a
            // concatenation preceded by a non-negative, non-x, and non-z constant expression,
            // called a multiplier'...
            // Because of that `replicatep->countp()` is just cloned
            m_result = new AstReplicate{replicatep->fileline(),
                                        getFourstateExpressionValue(replicatep->srcp(), false),
                                        replicatep->countp()->cloneTree(false)};
            m_result->dtypeSetBitUnsized(replicatep->width(), replicatep->dtypep()->widthMin(),
                                         replicatep->dtypep()->numeric());
        }

        void visit(AstNodeVarRef* const varRefp) override {
            noTmp();
            if (needsSplitting(varRefp->varp()->dtypep())) {
                m_fourstateVisitor.splitVar(varRefp->varp());
                AstNodeVarRef* const newp = varRefp->cloneTree(false);
                if (!newp->name().empty()) newp->name(newp->name() + VALUE_SUFFIX);
                newp->varp(getSplittedValue(varRefp->varp()));
                newp->dtypeSetBitSized(varRefp->varp()->width(),
                                       varRefp->varp()->dtypep()->numeric());
                m_result = newp;
            } else {
                AstNodeVarRef* const newp = varRefp->cloneTree(false);
                varRefp->dtypeSetBitSized(varRefp->width(), varRefp->dtypep()->numeric());
                m_result = newp;
            }
        }

        void visit(AstNodeExpr* const nodep) override {
            nodep->v3warn(E_UNSUPPORTED, "Unsupported: Operator "
                                             << nodep->typeName()
                                             << " not supported in the four-state mode");
            // Workaround to avoid Internal errors
            m_result = new AstConst{nodep->fileline(), AstConst::BitFalse{}};
        }

        void visit(AstNode* const nodep) override {
            nodep->v3fatalSrc("This node shall be unreachable in this visitor");
        }

        AstNodeExpr* getCache(const AstNodeExpr* const keyp) override {
            return getExprValuep(keyp);
        }
        void setCache(AstNodeExpr* keyp, AstNodeExpr* const valuep) override {
            setExprValuep(keyp, valuep);
        }

    public:
        using FourstateExpressionVisitor::FourstateExpressionVisitor;
        ~FourstateExpressionValueVisitor() override = default;

        AstNodeExpr* getFourstateExpressionValue(AstNodeExpr* const exprp,
                                                 bool putIntoTmp = true) override {
            if (!isFourstate(exprp)) {
                AstStmtExpr* const holderp
                    = new AstStmtExpr{exprp->fileline(), exprp->cloneTree(false)};
                m_fourstateVisitor.iterateChildren(holderp);
                AstNodeExpr* const resultp = holderp->exprp()->unlinkFrBack();
                holderp->deleteTree();
                return resultp;
            }
            return get(exprp, putIntoTmp);
        }
    };

    // Visitor used to get an expression with a value of an xz part of a four-state expression
    // This can be thought as a function - but a Visitor was used to be able to use vtable, create
    // some enclosing namespace and benefit from inheritance
    class FourstateExpressionXZVisitor final : public FourstateExpressionVisitor {

        void visit(AstAnd* const andp) override {
            // (a.value & b.xz) | (b.value & a.xz) | (a.xz & b.xz)
            FileLine* const flp = andp->fileline();
            m_result
                = new AstOr{flp,
                            new AstOr{flp,
                                      new AstAnd{flp, getFourstateExpressionValue(andp->lhsp()),
                                                 getFourstateExpressionXZ(andp->rhsp())},
                                      new AstAnd{flp, getFourstateExpressionValue(andp->rhsp()),
                                                 getFourstateExpressionXZ(andp->lhsp())}},
                            new AstAnd{flp, getFourstateExpressionXZ(andp->lhsp()),
                                       getFourstateExpressionXZ(andp->rhsp())}};
        }

        void visit(AstOr* const orp) override {
            // (a.xz & b.xz) | (a.xz & ~b.value) | (b.xz & ~a.value)
            FileLine* const flp = orp->fileline();
            m_result = new AstOr{
                flp,
                new AstOr{flp,
                          new AstAnd{flp, getFourstateExpressionXZ(orp->lhsp()),
                                     getFourstateExpressionXZ(orp->rhsp())},
                          new AstAnd{flp, getFourstateExpressionXZ(orp->lhsp()),
                                     new AstNot{flp, getFourstateExpressionValue(orp->rhsp())}}},
                new AstAnd{flp, getFourstateExpressionXZ(orp->rhsp()),
                           new AstNot{flp, getFourstateExpressionValue(orp->lhsp())}}};
        }

        void visit(AstXor* const xorp) override {
            // a.xz | b.xz
            FileLine* const flp = xorp->fileline();
            m_result = new AstOr{flp, getFourstateExpressionXZ(xorp->lhsp()),
                                 getFourstateExpressionXZ(xorp->rhsp())};
        }

        void visit(AstNot* const notp) override {
            // a.xz
            m_result = getFourstateExpressionXZ(notp->lhsp());
        }

        void visitCompare(AstNodeBiop* const cmpp) {
            // |(a.xz | b.xz)
            enforceTmp();
            FileLine* const flp = cmpp->fileline();
            m_result = new AstRedOr{flp, new AstOr{flp, getFourstateExpressionXZ(cmpp->lhsp()),
                                                   getFourstateExpressionXZ(cmpp->rhsp())}};
        }

        void visit(AstEq* const eqp) override { visitCompare(eqp); }
        void visit(AstNeq* const neqp) override { visitCompare(neqp); }
        void visit(AstGt* const gtp) override { visitCompare(gtp); }
        void visit(AstGte* const gtep) override { visitCompare(gtep); }
        void visit(AstLt* const ltp) override { visitCompare(ltp); }
        void visit(AstLte* const ltep) override { visitCompare(ltep); }

        void visit(AstGtS* const gtp) override { visitCompare(gtp); }
        void visit(AstGteS* const gtep) override { visitCompare(gtep); }
        void visit(AstLtS* const ltp) override { visitCompare(ltp); }
        void visit(AstLteS* const ltep) override { visitCompare(ltep); }

        void visit(AstEqWild* const eqWildp) override {
            // |(a.xz & ~b.xz)
            enforceTmp();
            FileLine* const flp = eqWildp->fileline();
            m_result = new AstRedOr{
                flp, new AstAnd{flp, getFourstateExpressionXZ(eqWildp->lhsp(), false),
                                new AstNot{flp, getFourstateExpressionXZ(eqWildp->rhsp())}}};
        }

        void visit(AstNeqWild* const neqWildp) override {
            // |(a.xz & ~b.xz)
            enforceTmp();
            FileLine* const flp = neqWildp->fileline();
            m_result = new AstRedOr{
                flp, new AstAnd{flp, getFourstateExpressionXZ(neqWildp->lhsp(), false),
                                new AstNot{flp, getFourstateExpressionXZ(neqWildp->rhsp())}}};
        }

        void visit(AstShiftL* const shiftlp) override {
            // |b.xz ? '1 : (a.xz << b.value)
            FileLine* const flp = shiftlp->fileline();
            m_result
                = new AstCond{flp, new AstRedOr{flp, getFourstateExpressionXZ(shiftlp->rhsp())},
                              createZeroOrOnesp(shiftlp->lhsp(), true),
                              new AstShiftL{flp, getFourstateExpressionXZ(shiftlp->lhsp(), false),
                                            getFourstateExpressionValue(shiftlp->rhsp())}};
        }

        void visit(AstShiftR* const shiftrp) override {
            // |b.xz ? '1 : (a.xz >> b.value)
            FileLine* const flp = shiftrp->fileline();
            m_result
                = new AstCond{flp, new AstRedOr{flp, getFourstateExpressionXZ(shiftrp->rhsp())},
                              createZeroOrOnesp(shiftrp->lhsp(), true),
                              new AstShiftR{flp, getFourstateExpressionXZ(shiftrp->lhsp(), false),
                                            getFourstateExpressionValue(shiftrp->rhsp())}};
        }

        void visit(AstExtend* const extendp) override {
            FileLine* const flp = extendp->fileline();
            m_result = new AstExtend{flp, getFourstateExpressionXZ(extendp->lhsp(), false),
                                     extendp->width()};
        }

        void visit(AstExtendS* const extendsp) override {
            FileLine* const flp = extendsp->fileline();
            m_result = new AstExtendS{flp, getFourstateExpressionXZ(extendsp->lhsp(), false),
                                      extendsp->width()};
        }

        void visit(AstCReset* const cresetp) override {
            m_result = cresetp->cloneTree(false);
            m_result->dtypeSetBitSized(cresetp->width(), cresetp->dtypep()->numeric());
        }

        void visit(AstConst* const constp) override {
            noTmp();
            AstConst* const newp = constp->cloneTree(false);
            newp->num().opBitsXZ(constp->num());
            newp->dtypeSetBitSized(newp->width(), newp->dtypep()->numeric());
            m_result = newp;
        }

        void visit(AstRedAnd* const redAndp) override {
            // &(a.value | a.xz) & |a.xz
            FileLine* const flp = redAndp->fileline();
            m_result = new AstAnd{flp, getFourstateExpressionValue(redAndp),
                                  new AstRedOr{flp, getFourstateExpressionXZ(redAndp->lhsp())}};
        }

        void visit(AstRedOr* const redOrp) override {
            // |a.xz & ~|(a.value & ~a.xz)
            FileLine* const flp = redOrp->fileline();
            m_result = new AstAnd{
                flp, new AstRedOr{flp, getFourstateExpressionXZ(redOrp->lhsp())},
                new AstNot{
                    flp,
                    new AstRedOr{flp, new AstAnd{flp, getFourstateExpressionValue(redOrp->lhsp()),
                                                 new AstNot{flp, getFourstateExpressionXZ(
                                                                     redOrp->lhsp())}}}}};
        }

        void visit(AstRedXor* const redXorp) override {
            // |a.xz
            m_result
                = new AstRedOr{redXorp->fileline(), getFourstateExpressionXZ(redXorp->lhsp())};
        }

        void getFourstateExpressionArithmeticXZ(AstNodeBiop* const biop) {
            // |(a.xz | b.xz) ? '1 : '0
            FileLine* const flp = biop->fileline();
            m_result = new AstCond{
                flp,
                new AstRedOr{flp, new AstOr{flp, getFourstateExpressionXZ(biop->lhsp()),
                                            getFourstateExpressionXZ(biop->rhsp())}},
                createZeroOrOnesp(biop, true), createZeroOrOnesp(biop)};
        }

        void visit(AstAdd* const addp) override { getFourstateExpressionArithmeticXZ(addp); }
        void visit(AstSub* const subp) override { getFourstateExpressionArithmeticXZ(subp); }
        void visit(AstMul* const mulp) override { getFourstateExpressionArithmeticXZ(mulp); }
        void visit(AstMulS* const mulsp) override { getFourstateExpressionArithmeticXZ(mulsp); }

        void getFourstateExpressionDivValue(AstNodeBiop* const biop) {
            // |(a.xz | b.xz) | ~|b.value ? '1 : '0
            FileLine* const flp = biop->fileline();
            m_result = new AstCond{
                flp,
                new AstOr{
                    flp,
                    new AstRedOr{flp, new AstOr{flp, getFourstateExpressionXZ(biop->lhsp()),
                                                getFourstateExpressionXZ(biop->rhsp())}},
                    new AstNot{flp, new AstRedOr{flp, getFourstateExpressionValue(biop->rhsp())}}},
                createZeroOrOnesp(biop, true), createZeroOrOnesp(biop, false)};
        }

        void visit(AstDiv* const divp) override { getFourstateExpressionDivValue(divp); }
        void visit(AstDivS* const divsp) override { getFourstateExpressionDivValue(divsp); }
        void visit(AstModDiv* const moddivp) override { getFourstateExpressionDivValue(moddivp); }
        void visit(AstModDivS* const moddivsp) override {
            getFourstateExpressionDivValue(moddivsp);
        }

        void visit(AstConcat* const concatp) override {
            // {a.xz, b.xz}
            m_result = new AstConcat{concatp->fileline(),
                                     getFourstateExpressionXZ(concatp->lhsp(), false),
                                     getFourstateExpressionXZ(concatp->rhsp(), false)};
        }

        void visit(AstReplicate* const replicatep) override {
            // {count{src.value}}
            // IEEE 1800-2023 11.4.12.1 Replication operator:
            // 'A replication operator (also called a multiple concatenation) is expressed by a
            // concatenation preceded by a non-negative, non-x, and non-z constant expression,
            // called a multiplier'...
            // Because of that `replicatep->countp()` is just cloned
            m_result = new AstReplicate{replicatep->fileline(),
                                        getFourstateExpressionXZ(replicatep->srcp(), false),
                                        replicatep->countp()->cloneTree(false)};
            m_result->dtypeSetBitUnsized(replicatep->width(), replicatep->dtypep()->widthMin(),
                                         replicatep->dtypep()->numeric());
        }

        void visit(AstNodeFTaskRef* const funcp) override {
            fourstateExpressionFuncRefHandler(funcp);
            noTmp();
            m_result = getExprXZp(funcp)->cloneTree(false);
        }

        void visit(AstCond* const condp) override {
            fourstateExpressionCondHandler(condp);
            noTmp();
            m_result = getExprXZp(condp)->cloneTree(false);
        }

        void visit(AstLogAnd* const logAndp) override {
            fourstateExpressionLogAndHandler(logAndp);
            noTmp();
            m_result = getExprXZp(logAndp)->cloneTree(false);
        }

        void visit(AstLogOr* const logOrp) override {
            fourstateExpressionLogOrHandler(logOrp);
            noTmp();
            m_result = getExprXZp(logOrp)->cloneTree(false);
        }

        void visit(AstSel* const selp) override {
            m_result = m_fourstateVisitor.getFourstateExpressionSelHandler(
                selp, getFourstateExpressionXZ(selp->fromp(), false), false);
        }

        void visit(AstNodeVarRef* const varRefp) override {
            noTmp();
            if (needsSplitting(varRefp->varp()->dtypep())) {
                m_fourstateVisitor.splitVar(varRefp->varp());
                AstNodeVarRef* const newp = varRefp->cloneTree(false);
                if (!newp->name().empty()) newp->name(newp->name() + XZ_SUFFIX);
                newp->varp(getSplittedXZ(varRefp->varp()));
                newp->dtypeSetBitSized(varRefp->varp()->width(),
                                       varRefp->varp()->dtypep()->numeric());
                m_result = newp;
            } else {
                AstConst* const newp = new AstConst{varRefp->fileline(), AstConst::WidthedValue{},
                                                    varRefp->width(), 0};
                m_result = newp;
            }
        }

        void visit(AstNodeExpr* const nodep) override {
            nodep->v3warn(E_UNSUPPORTED, "Unsupported: Operator "
                                             << nodep->typeName()
                                             << " not supported in the four-state mode");
            // Workaround to avoid Internal errors
            m_result = new AstConst{nodep->fileline(), AstConst::BitFalse{}};
        }

        void visit(AstNode* const nodep) override {
            nodep->v3fatalSrc("This node shall be unreachable in this visitor");
        }

        AstNodeExpr* getCache(const AstNodeExpr* const keyp) override { return getExprXZp(keyp); }
        void setCache(AstNodeExpr* keyp, AstNodeExpr* const valuep) override {
            setExprXZp(keyp, valuep);
        }

    public:
        using FourstateExpressionVisitor::FourstateExpressionVisitor;
        ~FourstateExpressionXZVisitor() override = default;

        AstNodeExpr* getFourstateExpressionXZ(AstNodeExpr* const exprp,
                                              bool putIntoTmp = true) override {
            if (!isFourstate(exprp)) return createZeroOrOnesp(exprp);
            return get(exprp, putIntoTmp);
        }
    };

    FourstateExpressionValueVisitor
        m_fourstateGeneratorValueVisitor;  // Generator of four-state expressions (value part)
    FourstateExpressionXZVisitor
        m_fourstateGeneratorXZVisitor;  // Generator of four-state expressions (xz part)

    AstNodeExpr* getFourstateExpressionValue(AstNodeExpr* const exprp, bool putIntoTmp = false) {
        if (AstCReset* const cresetp = VN_CAST(exprp, CReset)) {
            // This is here instead in the visitor because CReset shall never be nested into
            // the expression and also it is a very special case
            AstCReset* const resultp = cresetp->cloneTree(false);
            resultp->dtypeSetBitSized(cresetp->width(), cresetp->dtypep()->numeric());
            FourstateLogicTypePropagator{resultp};
            return resultp;
        }
        AstNodeExpr* const result
            = m_fourstateGeneratorValueVisitor.getFourstateExpressionValue(exprp, putIntoTmp);
        FourstateLogicTypePropagator{result};
        return result;
    }

    AstNodeExpr* getFourstateExpressionXZ(AstNodeExpr* const exprp, bool putIntoTmp = false) {
        if (AstCReset* const cresetp = VN_CAST(exprp, CReset)) {
            // This is here instead in the visitor because CReset shall never be nested into
            // the expression and also it is a very special case
            AstCReset* const result = cresetp->cloneTree(false);
            result->dtypeSetBitSized(cresetp->width(), cresetp->dtypep()->numeric());
            FourstateLogicTypePropagator{result};
            return result;
        }
        AstNodeExpr* const result
            = m_fourstateGeneratorXZVisitor.getFourstateExpressionXZ(exprp, putIntoTmp);
        FourstateLogicTypePropagator{result};
        return result;
    }

    AstNodeExpr* getTruthExpr(AstNodeExpr* const exprp) {
        UASSERT_OBJ(isFourstate(exprp), exprp,
                    "This function is ment to be called on four-state expressions");
        // a.value && !a.xz
        FileLine* const flp = exprp->fileline();
        AstLogAnd* const result
            = new AstLogAnd{flp, getFourstateExpressionValue(exprp),
                            new AstLogNot{flp, getFourstateExpressionXZ(exprp)}};
        setFourstate(result, false);
        setFourstate(result->rhsp(), false);
        return result;
    }

    AstNodeExpr* getTwoStateCast(AstNodeExpr* const exprp) {
        UASSERT_OBJ(isFourstate(exprp), exprp,
                    "This function is ment to be called on four-state expressions");
        // (a.value & (~a.xz))
        FileLine* const flp = exprp->fileline();
        AstAnd* const result = new AstAnd{flp, getFourstateExpressionValue(exprp),
                                          new AstNot{flp, getFourstateExpressionXZ(exprp)}};
        setFourstate(result, false);
        setFourstate(result->rhsp(), false);
        return result;
    }

    void visit(AstNodeAssign* const nodep) override {
        VL_RESTORER(m_currentStmtp);
        m_currentStmtp = nodep;
        TmpVarsReleaser tmpVarsReleaser{*this};
        if (isFourstate(nodep->lhsp())) {
            AstNodeVarRef* const lhsVarRefp = VN_CAST(nodep->lhsp(), NodeVarRef);
            if (VL_UNLIKELY(!lhsVarRefp)) {
                nodep->v3warn(
                    E_UNSUPPORTED,
                    "Fourstate LHS other than a simple variable reference is not supported");
                return;
            }
            AstNodeAssign* const assignXZp = nodep->cloneTree(false);
            {
                assignXZp->lhsp()->unlinkFrBack()->deleteTree();
                assignXZp->rhsp()->unlinkFrBack()->deleteTree();
                AstNodeExpr* const newLhsp = getFourstateExpressionXZ(lhsVarRefp);
                assignXZp->lhsp(newLhsp);
                assignXZp->rhsp(getFourstateExpressionXZ(nodep->rhsp()));
                assignXZp->dtypeFrom(newLhsp);
                nodep->addNextHere(assignXZp);
            }
            {
                AstNodeExpr* const newRhsp = getFourstateExpressionValue(nodep->rhsp());
                AstNodeExpr* const newLhsp = getFourstateExpressionValue(lhsVarRefp);
                pushDeletep(nodep->lhsp()->unlinkFrBack());
                pushDeletep(nodep->rhsp()->unlinkFrBack());
                nodep->lhsp(newLhsp);
                nodep->rhsp(newRhsp);
                nodep->dtypeFrom(newLhsp);
            }
            if (AstAssignW* const assignWValuep = VN_CAST(nodep, AssignW)) {
                assignWConflictResolution(lhsVarRefp->varp(), assignWValuep,
                                          VN_AS(assignXZp, AssignW));
                if (const AstNode* const timingControlp = assignWValuep->timingControlp()) {
                    timingControlp->v3warn(
                        E_UNSUPPORTED,
                        "Continuous assignment delays are unsupported with --fourstate");
                }
            }
        } else if (isFourstate(nodep->rhsp())) {
            AstNodeExpr* const newRhsp = getTwoStateCast(nodep->rhsp());
            pushDeletep(nodep->rhsp()->unlinkFrBack());
            nodep->rhsp(newRhsp);
        }
        iterateChildren(nodep);
    }

    void visit(AstStmtExpr* const nodep) override {
        VL_RESTORER(m_currentStmtp);
        m_currentStmtp = nodep;
        TmpVarsReleaser tmpVarsReleaser{*this};
        auto isFourState = [nodep]() -> bool {
            if (AstNodeFTaskRef* const taskRefp = VN_CAST(nodep->exprp(), NodeFTaskRef)) {
                return isFourstate(taskRefp) && !isFTaskRefHandled(taskRefp);
            }
            return isFourstate(nodep->exprp());
        };
        if (isFourState()) {
            AstNodeExpr* const exprp = nodep->exprp()->unlinkFrBack();
            nodep->exprp(getFourstateExpressionValue(exprp));
            AstNodeExpr* const newXzp = getFourstateExpressionXZ(exprp);
            iterateChildren(newXzp);
            AstStmtExpr* const newStmtExprp = new AstStmtExpr{nodep->fileline(), newXzp};
            nodep->addNextHere(newStmtExprp);
            exprp->deleteTree();
        }
        iterateChildren(nodep);
    }

    void visit(AstLoopTest* const nodep) override {
        VL_RESTORER(m_currentStmtp);
        m_currentStmtp = nodep;
        TmpVarsReleaser tmpVarsReleaser{*this};
        if (isFourstate(nodep->condp())) {
            AstNodeExpr* const condp = nodep->condp()->unlinkFrBack();
            nodep->condp(getTruthExpr(condp));
            condp->deleteTree();
        }
        iterateChildren(nodep);
    }

    void visit(AstNodeIf* const nodep) override {
        VL_RESTORER(m_currentStmtp);
        m_currentStmtp = nodep;
        if (isFourstate(nodep->condp())) {
            AstNodeExpr* const condp = nodep->condp()->unlinkFrBack();
            nodep->condp(getTruthExpr(condp));
            condp->deleteTree();
        }
        {
            TmpVarsReleaser tmpVarsReleaser{*this};
            iterateAndNextNull(nodep->condp());
        }
        iterateAndNextNull(nodep->thensp());
        iterateAndNextNull(nodep->elsesp());
    }

    void visit(AstCase* const nodep) override {
        VL_RESTORER(m_currentStmtp);
        m_currentStmtp = nodep;
        if (isFourstate(nodep->exprp())) {
            nodep->v3warn(E_UNSUPPORTED, "All case statements with four-state value as an "
                                         "expression are unsupported with --fourstate");
        } else {
            iterate(nodep->exprp());
        }
        iterateAndNextNull(nodep->itemsp());
        iterateAndNextNull(nodep->notParallelp());
    }

    void visit(AstCaseItem* const nodep) override {
        for (AstNodeExpr* condp = nodep->condsp(); condp;
             condp = VN_AS(condp->nextp(), NodeExpr)) {
            if (isFourstate(condp)) {
                nodep->v3warn(E_UNSUPPORTED,
                              "Four-state case items values are unsupported with --fourstate");
            } else {
                iterate(condp);
            }
        }
        iterateAndNextNull(nodep->stmtsp());
    }

    void visit(AstSenItem* const nodep) override {
        if (!VN_IS(nodep->sensp(), FourstateExpr) && isFourstate(nodep->sensp())) {
            AstNodeExpr* const sensp = nodep->sensp()->unlinkFrBack();
            nodep->sensp(new AstFourstateExpr{nodep->fileline(),
                                              getFourstateExpressionValue(sensp),
                                              getFourstateExpressionXZ(sensp)});
            sensp->deleteTree();
        }
        iterateChildren(nodep);
    }

    void visit(AstDisplay* const nodep) override {
        VL_RESTORER(m_currentStmtp);
        m_currentStmtp = nodep;
        if (nodep->filep() && isFourstate(nodep->filep())) {
            nodep->filep()->v3warn(
                LOGICCAST,
                "Some features are not supported with four-state values - cast it to two-state "
                "logic or suppress this warning and it will be done implicitly");
            AstNodeExpr* const newp = getTwoStateCast(nodep->filep());
            nodep->filep()->unlinkFrBack()->deleteTree();
            nodep->filep(newp);
        }
        iterateChildren(nodep);
    }

    void visit(AstFClose* const nodep) override {
        VL_RESTORER(m_currentStmtp);
        m_currentStmtp = nodep;
        if (isFourstate(nodep->filep())) {
            nodep->filep()->v3warn(
                LOGICCAST,
                "Some features are not supported with four-state values - cast it to two-state "
                "logic or suppress this warning and it will be done implicitly");
            AstNodeExpr* const newp = getTwoStateCast(nodep->filep());
            nodep->filep()->unlinkFrBack()->deleteTree();
            nodep->filep(newp);
        }
        iterateChildren(nodep);
    }

    void visit(AstFFlush* const nodep) override {
        VL_RESTORER(m_currentStmtp);
        m_currentStmtp = nodep;
        if (nodep->filep() && isFourstate(nodep->filep())) {
            nodep->filep()->v3warn(
                LOGICCAST,
                "Some features are not supported with four-state values - cast it to two-state "
                "logic or suppress this warning and it will be done implicitly");
            AstNodeExpr* const newp = getTwoStateCast(nodep->filep());
            nodep->filep()->unlinkFrBack()->deleteTree();
            nodep->filep(newp);
        }
        iterateChildren(nodep);
    }

    void cArgsHandler(AstNode* nodep) {
        for (; nodep; nodep = nodep->nextp()) {
            if (AstNodeExpr* const exprp = VN_CAST(nodep, NodeExpr)) {
                if (isFourstate(exprp)) {
                    exprp->v3warn(
                        LOGICCAST,
                        "Some features are not supported with four-state values - cast it to "
                        "two-state "
                        "logic or suppress this warning and it will be done implicitly");
                    AstNodeExpr* const newp = getTwoStateCast(exprp);
                    exprp->replaceWith(newp);
                    exprp->deleteTree();
                    nodep = newp;
                }
            }
        }
    }

    void visit(AstCStmtUser* const nodep) override {
        VL_RESTORER(m_currentStmtp);
        m_currentStmtp = nodep;
        cArgsHandler(nodep->nodesp());
    }

    void visit(AstCExprUser* const nodep) override { cArgsHandler(nodep->nodesp()); }
    void visit(AstCExpr* const nodep) override { cArgsHandler(nodep->nodesp()); }

    void visit(AstSFormatF* const nodep) override {
        for (AstNodeExpr* exprp = nodep->exprsp(); exprp;
             exprp = VN_AS(exprp->nextp(), NodeExpr)) {
            if (isFourstate(exprp)) {
                exprp->v3warn(
                    LOGICCAST,
                    "Some features are not supported with four-state values - cast it to "
                    "two-state logic or suppress this warning and it will be done implicitly");
                if (AstSFormatArg* const sformatArgp = VN_CAST(exprp, SFormatArg)) {
                    AstNodeExpr* const currentExprp = sformatArgp->exprp();
                    currentExprp->replaceWith(getTwoStateCast(currentExprp));
                    currentExprp->deleteTree();
                    setFourstate(exprp, isFourstate(sformatArgp->exprp()));
                } else {
                    AstNodeExpr* const newp = getTwoStateCast(exprp);
                    exprp->replaceWith(newp);
                    exprp->deleteTree();
                    exprp = newp;
                }
            }
        }
        iterateChildren(nodep);
    }

    void visit(AstPin* const nodep) override {
        AstVar* const varp = nodep->modVarp();
        if (!(varp->fourstateComplementp() || varp->isFourstateComplement())) {
            if (AstNodeExpr* const exprp = VN_CAST(nodep->exprp(), NodeExpr)) {
                if (VL_UNLIKELY(!(VN_IS(exprp, NodeVarRef) || VN_IS(exprp, Const)))) {
                    // The issue lays in need for precalculations, potential side effects and lack
                    // of arguments order evaluation guarantees. The idea to support it is to do
                    // something like:
                    //   Pin(foo())
                    // will turn into:
                    //   func helper()
                    //     if (called) return;
                    //     called = true;
                    //     foo(tmpValue, tmpXZ)
                    //   Pin((helper(), tmpValue), (helper(), tmpXZ))
                    exprp->v3warn(E_UNSUPPORTED,
                                  "Cells with pins that are not a variable reference or a "
                                  "constant are not supported with  --fourstate");
                    return;
                } else if (needsSplitting(varp->dtypep())) {
                    AstPin* const newp
                        = new AstPin{nodep->fileline(), nodep->pinNum(),
                                     nodep->name().empty() ? "" : nodep->name() + XZ_SUFFIX,
                                     getFourstateExpressionXZ(exprp)};
                    nodep->addNextHere(newp);
                    AstNodeExpr* const oldp = exprp->unlinkFrBack();
                    nodep->exprp(getFourstateExpressionValue(oldp));
                    oldp->deleteTree();
                    splitVar(varp);  // Ensure that variable is splitted
                    nodep->modVarp(getSplittedValue(varp));
                    newp->modVarp(getSplittedXZ(varp));
                } else if (isFourstate(exprp)) {
                    AstNodeExpr* const oldp = exprp->unlinkFrBack();
                    nodep->exprp(getTwoStateCast(oldp));
                    oldp->deleteTree();
                }
            } else if (!nodep->exprp() && needsSplitting(varp->dtypep())) {
                AstPin* const newp
                    = new AstPin{nodep->fileline(), nodep->pinNum(),
                                 nodep->name().empty() ? "" : nodep->name() + XZ_SUFFIX, nullptr};
                nodep->addNextHere(newp);
                splitVar(varp);  // Ensure that variable is splitted
                nodep->modVarp(getSplittedValue(varp));
                newp->modVarp(getSplittedXZ(varp));
            }
        }
        iterateChildren(nodep);
    }

    void visit(AstNodeFTaskRef* const nodep) override {
        if (!isFTaskRefHandled(nodep)) {
            setFTaskRefHandled(nodep);
            size_t currentArgIdx = 0;
            const FTaskPortsHelper& fTaskPortsHelper = getFTaskPortHelper(nodep->taskp());
            for (AstArg* argp = nodep->argsp(); argp; argp = VN_AS(argp->nextp(), Arg)) {
                AstVar* const varp = fTaskPortsHelper.getArgPortVar(argp->name(), currentArgIdx);
                ++currentArgIdx;
                if (needsSplitting(varp->dtypep())) {
                    AstArg* const newp = new AstArg{
                        argp->fileline(), argp->name().empty() ? "" : (varp->name() + XZ_SUFFIX),
                        getFourstateExpressionXZ(argp->exprp())};
                    argp->addNextHere(newp);
                    AstNodeExpr* const oldp = argp->exprp()->unlinkFrBack();
                    argp->exprp(getFourstateExpressionValue(oldp));
                    oldp->deleteTree();
                    if (!argp->name().empty()) argp->name(argp->name() + VALUE_SUFFIX);
                    argp = VN_AS(argp->nextp(), Arg);
                } else if (isFourstate(argp->exprp())) {
                    AstNodeExpr* const oldp = argp->exprp()->unlinkFrBack();
                    argp->exprp(getTwoStateCast(oldp));
                    oldp->deleteTree();
                }
            }
        }
        iterateChildren(nodep);
    }

    void visit(AstCastWrap* const nodep) override {
        if (!isFourstate(nodep) && isFourstate(nodep->lhsp())) {
            AstNodeExpr* const lhsp = nodep->lhsp()->unlinkFrBack();
            nodep->lhsp(getTwoStateCast(lhsp));
            lhsp->deleteTree();
        }
        iterateChildren(nodep);
    }

    void visit(AstEqCase* const nodep) override {
        FileLine* const flp = nodep->fileline();
        AstNodeExpr* newp;
        if (isFourstate(nodep->lhsp()) && isFourstate(nodep->rhsp())) {
            newp = new AstAnd{flp,
                              new AstEq{flp, getFourstateExpressionXZ(nodep->lhsp()),
                                        getFourstateExpressionXZ(nodep->rhsp())},
                              new AstEq{flp, getFourstateExpressionValue(nodep->lhsp()),
                                        getFourstateExpressionValue(nodep->rhsp())}};
        } else if (isFourstate(nodep->lhsp()) || isFourstate(nodep->rhsp())) {
            AstNodeExpr* const fourstateHsp
                = isFourstate(nodep->lhsp()) ? nodep->lhsp() : nodep->rhsp();
            AstNodeExpr* const twostateHsp = isFourstate(nodep->lhsp())
                                                 ? nodep->rhsp()->unlinkFrBack()
                                                 : nodep->lhsp()->unlinkFrBack();
            newp = new AstAnd{
                flp, new AstNot{flp, getFourstateExpressionXZ(fourstateHsp)},
                new AstEq{flp, getFourstateExpressionValue(fourstateHsp), twostateHsp}};
        } else {
            newp = new AstEq{flp, nodep->lhsp()->unlinkFrBack(), nodep->rhsp()->unlinkFrBack()};
        }
        { FourstateLogicTypePropagator{newp}; }
        VNRelinker relinker;
        nodep->unlinkFrBack(&relinker);
        relinker.relink(newp);
        nodep->deleteTree();
    }

    void visit(AstNeqCase* const nodep) override {
        FileLine* const flp = nodep->fileline();
        AstNodeExpr* newp;
        if (isFourstate(nodep->lhsp()) && isFourstate(nodep->rhsp())) {
            newp = new AstRedOr{
                flp, new AstOr{flp,
                               new AstXor{flp, getFourstateExpressionValue(nodep->lhsp()),
                                          getFourstateExpressionValue(nodep->rhsp())},
                               new AstXor{flp, getFourstateExpressionXZ(nodep->lhsp()),
                                          getFourstateExpressionXZ(nodep->rhsp())}}};
        } else if (isFourstate(nodep->lhsp()) || isFourstate(nodep->rhsp())) {
            AstNodeExpr* const fourstateHsp
                = isFourstate(nodep->lhsp()) ? nodep->lhsp() : nodep->rhsp();
            AstNodeExpr* const twostateHsp = isFourstate(nodep->lhsp())
                                                 ? nodep->rhsp()->unlinkFrBack()
                                                 : nodep->lhsp()->unlinkFrBack();
            newp = new AstRedOr{
                flp, new AstOr{
                         flp, getFourstateExpressionXZ(fourstateHsp),
                         new AstXor{flp, getFourstateExpressionValue(fourstateHsp), twostateHsp}}};
        } else {
            newp = new AstNeq{flp, nodep->lhsp()->unlinkFrBack(), nodep->rhsp()->unlinkFrBack()};
        }
        { FourstateLogicTypePropagator{newp}; }
        VNRelinker relinker;
        nodep->unlinkFrBack(&relinker);
        relinker.relink(newp);
        nodep->deleteTree();
    }

    void visit(AstSel* const nodep) override {
        UASSERT_OBJ(!isFourstate(nodep), nodep,
                    "This visitor shall never be reached for four-state AstSel");
        if (!isSelpHandled(nodep)) {
            setSelpHandled(nodep);
            AstNodeExpr* const newp
                = getFourstateExpressionSelHandler(nodep, nodep->fromp()->cloneTree(false), true);
            { FourstateLogicTypePropagator{newp}; }
            VNRelinker relinker;
            nodep->unlinkFrBack(&relinker);
            relinker.relink(newp);
            nodep->deleteTree();
        } else {
            iterateChildren(nodep);
        }
    }

    void visit(AstLogOr* const nodep) override {
        if (!hasFourstateInSubtree(nodep->rhsp())) {
            iterateChildren(nodep);
            return;
        }
        UASSERT_OBJ(!isFourstate(nodep), nodep,
                    "This shall be reached only by two-state expressions");
        FileLine* const flp = nodep->fileline();
        AstVar* resultVarp = createTmp(nodep);
        addPrecalculation(new AstAssign{flp, new AstVarRef{flp, resultVarp, VAccess::WRITE},
                                        new AstRedOr{flp, nodep->lhsp()->unlinkFrBack()}});
        addPrecalculation(
            new AstIf{flp, new AstNot{flp, new AstVarRef{flp, resultVarp, VAccess::READ}},
                      new AstAssign{flp, new AstVarRef{flp, resultVarp, VAccess::WRITE},
                                    new AstRedOr{flp, nodep->rhsp()->unlinkFrBack()}}});
        AstVarRef* const newp = new AstVarRef{flp, resultVarp, VAccess::READ};
        setFourstate(newp, false);
        VNRelinker relinker;
        nodep->unlinkFrBack(&relinker);
        relinker.relink(newp);
        nodep->deleteTree();
    }

    void visit(AstLogAnd* const nodep) override {
        if (!hasFourstateInSubtree(nodep->rhsp())) {
            iterateChildren(nodep);
            return;
        }
        UASSERT_OBJ(!isFourstate(nodep), nodep,
                    "This shall be reached only by two-state expressions");
        FileLine* const flp = nodep->fileline();
        AstVar* resultVarp = createTmp(nodep);
        addPrecalculation(new AstAssign{flp, new AstVarRef{flp, resultVarp, VAccess::WRITE},
                                        new AstRedOr{flp, nodep->lhsp()->unlinkFrBack()}});
        addPrecalculation(
            new AstIf{flp, new AstVarRef{flp, resultVarp, VAccess::READ},
                      new AstAssign{flp, new AstVarRef{flp, resultVarp, VAccess::WRITE},
                                    new AstRedOr{flp, nodep->rhsp()->unlinkFrBack()}}});
        AstVarRef* const newp = new AstVarRef{flp, resultVarp, VAccess::READ};
        setFourstate(newp, false);
        VNRelinker relinker;
        nodep->unlinkFrBack(&relinker);
        relinker.relink(newp);
        nodep->deleteTree();
    }

    void visit(AstCond* const nodep) override {
        UASSERT_OBJ(!isFourstate(nodep), nodep,
                    "This shall be reached only by two-state expressions");
        if (!hasFourstateInSubtree(nodep->thenp()) && !hasFourstateInSubtree(nodep->elsep())) {
            iterateChildren(nodep);
            return;
        }
        FileLine* const flp = nodep->fileline();
        AstVar* resultVarp = createTmp(nodep);
        addPrecalculation(
            new AstIf{flp, nodep->condp()->unlinkFrBack(),
                      new AstAssign{flp, new AstVarRef{flp, resultVarp, VAccess::WRITE},
                                    nodep->thenp()->unlinkFrBack()},
                      new AstAssign{flp, new AstVarRef{flp, resultVarp, VAccess::WRITE},
                                    nodep->elsep()->unlinkFrBack()}});
        AstVarRef* const newp = new AstVarRef{flp, resultVarp, VAccess::READ};
        setFourstate(newp, false);
        VNRelinker relinker;
        nodep->unlinkFrBack(&relinker);
        relinker.relink(newp);
        nodep->deleteTree();
    }

    void visit(AstCvtPackedToArray* const) override {
        // Skip this tree since this expr is not supported anyway
    }
    void visit(AstTestPlusArgs* const) override {
        // Skip this tree since this expr is not supported anyway
    }
    void visit(AstValuePlusArgs* const) override {
        // Skip this tree since this expr is not supported anyway
    }
    void visit(AstFOpenMcd* const) override {
        // Skip this tree since this expr is not supported anyway
    }
    void visit(AstCMethodHard* const) override {
        // Skip this tree since this expr is not supported anyway
    }
    void visit(AstConsPackUOrStruct* const) override {
        // Skip this tree since this expr is not supported anyway
    }

    void visit(AstNodeFTask* const nodep) override {
        VL_RESTORER(m_currentTmpSpotp);
        VL_RESTORER(m_tmpUnusedVarps);
        VL_RESTORER(m_tmpFuncLocal);
        m_tmpFuncLocal = true;
        m_currentTmpSpotp = nodep->stmtsp();
        TmpVarsReleaser releaser{*this};
        // Make sure FTasks use only local variables - prevents using tmp
        // which may be used by a caller
        for (auto& it : m_tmpUnusedVarps) it.clear();
        iterateChildren(nodep);
    }

    void visit(AstVar* const nodep) override {
        if (VL_UNLIKELY(!isDTypepSupported(nodep->dtypep()->skipRefp()).first)) {
            nodep->v3warn(E_UNSUPPORTED,
                          "Variables of type: " << nodep->dtypep()->prettyDTypeNameQ()
                                                << " are unsupported with --fourstate");
        } else if (needsSplitting(nodep->dtypep())) {
            splitVar(nodep);
        }
        iterateChildren(nodep);
    }

    void visit(AstPull* const nodep) override {
        nodep->v3warn(E_UNSUPPORTED, "Pullups and pulldowns are unsupported with --fourstate");
    }

    void visit(AstModportVarRef* const nodep) override {
        if ((nodep->exprp() && isFourstate(nodep->exprp()))
            || (nodep->varp() && needsSplitting(nodep->varp()->dtypep()))) {
            nodep->v3warn(E_UNSUPPORTED, "modports are not supported with --fourstate");
        } else {
            iterateChildren(nodep);
        }
    }

    void visit(AstNodeModule* const nodep) override {
        VL_RESTORER(m_currentTmpSpotp);
        VL_RESTORER(m_tmpUnusedVarps);
        m_currentTmpSpotp = nodep->stmtsp();
        iterateChildren(nodep);
    }

    void visit(AstNodeStmt* const nodep) override {
        VL_RESTORER(m_currentStmtp);
        TmpVarsReleaser tmpVarsReleaser{*this};
        m_currentStmtp = nodep;
        iterateChildren(nodep);
    }

    void visit(AstNode* const nodep) override { iterateChildren(nodep); }

public:
    explicit FourstateVisitor(AstNetlist* const netlistp)
        : m_tmpNames{"__VfourstateTmp"}
        , m_fourstateGeneratorValueVisitor{*this}
        , m_fourstateGeneratorXZVisitor{*this} {
        { FourstateLogicTypePropagator{netlistp}; }
        iterate(netlistp);
        triorTriandReduce(m_assignWToTriand, triandReducer);
        triorTriandReduce(m_assignWToTrior, triorReducer);
        triorTriandReduce(m_assignWToWire, triReducer);
        V3Error::abortIfErrors();
        { FourstateLogicTypePropagator{netlistp}; }
        netlistp->foreach([](const AstNodeExpr* const nodep) {
            if (VN_IS(nodep, NodeFTaskRef)) {
                // Changing it in type propagador is unnecessary since those will be 100% handled
                return;
            }
            if (isFourstate(nodep)) {
                nodep->v3warn(E_UNSUPPORTED, "This four-state expression has not been handled");
            }
        });
        V3Error::abortIfErrors();
        for (AstVar* const varp : m_varpsToRemove) varp->unlinkFrBack()->deleteTree();
    }
    ~FourstateVisitor() override = default;
};

void V3Fourstate::fourstateAll(AstNetlist* netlistp) {
    UINFO(2, __FUNCTION__ << ":");
    { FourstateVisitor{netlistp}; }
    v3Global.setFourstateHandled();
    V3Global::dumpCheckGlobalTree("fourstate", 0, dumpTreeEitherLevel() >= 6);
}
