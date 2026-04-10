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

namespace {
struct FourStatePair final {
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
    T, std::enable_if_t<std::is_same<decltype(std::declval<T>()(std::declval<FourStatePair>(),
                                                                std::declval<FourStatePair>())),
                                     FourStatePair>::value>>
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
        m_fourstateInSubtree = static_cast<bool>(static_cast<char>(foreach(nodep->op1p()))
                                                 | static_cast<char>(foreach(nodep->op2p()))
                                                 | static_cast<char>(foreach(nodep->op3p()))
                                                 | static_cast<char>(foreach(nodep->op4p())));
    }

    void visit(AstConst* const nodep) override {
        iterateChildrenSeparately(nodep);
        setFourstate(nodep, nodep->dtypep()->isFourstate(), m_fourstateInSubtree);
        m_fourstateInSubtree |= isFourstate(nodep);
    }

    void visit(AstNodeVarRef* const nodep) override {
        iterateChildrenSeparately(nodep);
        setFourstate(nodep, nodep->varp()->dtypep()->isFourstate(), m_fourstateInSubtree);
        m_fourstateInSubtree |= isFourstate(nodep);
    }

    void visit(AstNodeFTaskRef* const nodep) override {
        iterateChildrenSeparately(nodep);
        setFourstate(nodep,
                     nodep->taskp()->fvarp() && nodep->taskp()->fvarp()->dtypep()->isFourstate(),
                     m_fourstateInSubtree);
        m_fourstateInSubtree |= isFourstate(nodep);
    }

    void visit(AstNodeUniop* const nodep) override {
        iterateChildrenSeparately(nodep);
        setFourstate(nodep, isFourstate(nodep->lhsp()), m_fourstateInSubtree);
    }

    void visit(AstCastWrap* const nodep) override {
        iterateChildrenSeparately(nodep);
        setFourstate(nodep, nodep->dtypep()->isFourstate(), m_fourstateInSubtree);
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

    void visit(AstCMethodHard* const nodep) override {
        iterateChildrenSeparately(nodep);
        setFourstate(nodep, false, m_fourstateInSubtree);
    }

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
        setFourstate(nodep, nodep->varp()->dtypep()->isFourstate(), m_fourstateInSubtree);
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

    void visit(AstLambdaArgRef* const nodep) override {
        iterateChildrenSeparately(nodep);
        setFourstate(nodep, nodep->dtypep()->isFourstate(), m_fourstateInSubtree);
    }

    void visit(AstTestPlusArgs* const nodep) override {
        iterateChildrenSeparately(nodep);
        setFourstate(nodep, false, m_fourstateInSubtree);
    }

    void visit(AstValuePlusArgs* const nodep) override {
        iterateChildrenSeparately(nodep);
        setFourstate(nodep, false, m_fourstateInSubtree);
    }

    void visit(AstCvtArrayToPacked* const nodep) override {
        iterateChildrenSeparately(nodep);
        setFourstate(nodep, nodep->fromp()->dtypep()->skipRefp()->isFourstate(),
                     m_fourstateInSubtree);
    }

    void visit(AstSScanF* const nodep) override {
        iterateChildrenSeparately(nodep);
        setFourstate(nodep, false, m_fourstateInSubtree);
    }

    void visit(AstFScanF* const nodep) override {
        iterateChildrenSeparately(nodep);
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
    // AstVar*::user1p      ->  AstVar*.        Where is value part of splitted variable - xz
    //                                          shall be nexp() of user1p
    // AstNodeExpr::user1p  ->  AstNodeExpr*.   Expression evaluating value component
    // AstNodeExpr::user2p  ->  AstNodeExpr*.   Expression evaluating xz component
    // AstNode::user3       ->  bool.           Whether visited
    // AstNodeExpr::user4   ->  LogicType.      Expression logic type (whether it is four
    //                                          or two state)

    V3UniqueNames m_tmpNames;  // Unique names generator for temporary variables

    AstVar* m_currentTmpSpotp = nullptr;  // Node after which put AstVar* for temporary variable
    bool m_tmpFuncLocal
        = false;  // Whether temporary variables shall be created as function locals
    AstNodeStmt* m_currentStmtp = nullptr;  // Current statement
    AstNode* m_currentFTaskArgp = nullptr;  // Current argument variable of FTaskRef - if not
                                            // variable it is meaningless
    AstNode* m_currentArgVarp = nullptr;  // Current FTaskRef Argument Variable
    std::vector<AstVar*> m_varpsToRemove;  // Vars to unlink and remove in destructor

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

    static FourStatePair triReducer(const FourStatePair& a, const FourStatePair& b) {
        FileLine* const flp = a.valuep->fileline();
        FourStatePair result;
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
    static FourStatePair triandReducer(const FourStatePair& a, const FourStatePair& b) {
        FileLine* const flp = a.valuep->fileline();
        FourStatePair result;
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
    static FourStatePair triorReducer(const FourStatePair& a, const FourStatePair& b) {
        FileLine* const flp = a.valuep->fileline();
        FourStatePair result;
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
    static FourStatePair buildTree(std::vector<FourStatePair> exprps, Reducer_T&& reducer) {
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
            std::vector<FourStatePair> exprps;
            exprps.reserve(assignps.size());
            for (const auto& assignp : assignps) {
                exprps.push_back({assignp.first->rhsp()->unlinkFrBack(),
                                  assignp.second->rhsp()->unlinkFrBack()});
            }
            FourStatePair result = buildTree(std::move(exprps), reducer);
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
        default:
            assignwValuep->v3fatalSrc(
                "Unexpected variable type on lhs of assign: " << varp->varType().ascii());
            break;
        }
    }

    AstVar* createPlaceholderVarp(FileLine* const flp) {
        AstVar* const newp
            = new AstVar{flp, VVarType::BLOCKTEMP, "__VplaceHolder", VFlagBitPacked{}, 1};
        m_varpsToRemove.push_back(newp);
        return newp;
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
        m_currentTmpSpotp->addNextHere(varp);
        varp->funcLocal(m_tmpFuncLocal);
        varp->noSubst(true);
        m_tmpVarpsInUse.push_back(varp);
        return varp;
    }

    void splitVar(AstVar* const varp) {
        UASSERT_OBJ(varp->dtypep()->isFourstate(), varp,
                    "Split shall be called only on four-state variables");
        if (varp->user1p()) return;
        m_varpsToRemove.push_back(varp);
        if (AstNodeFTask* const ftaskp = VN_CAST(varp->backp(), NodeFTask)) {
            AstVar* portEndp;
            if (ftaskp->fvarp() == varp) {
                if (!ftaskp->stmtsp()) {
                    ftaskp->addStmtsp(portEndp = createPlaceholderVarp(ftaskp->fileline()));
                } else if (AstVar* const portp = VN_CAST(ftaskp->stmtsp(), Var)) {
                    if (portp->varType() != VVarType::PORT) {
                        portp->addHereThisAsNext(portEndp
                                                 = createPlaceholderVarp(ftaskp->fileline()));
                    } else {
                        portEndp = portp;
                        AstVar* iter;
                        while ((iter = VN_CAST(portEndp->nextp(), Var))
                               && iter->varType() == VVarType::PORT) {
                            portEndp = iter;
                        }
                    }
                } else {
                    ftaskp->stmtsp()->addHereThisAsNext(
                        portEndp = createPlaceholderVarp(ftaskp->fileline()));
                }
                AstVar* const returnValuep
                    = new AstVar{varp->fileline(), VVarType::PORT, varp->name() + "__Vvalue",
                                 VFlagBitPacked{}, varp->width()};
                AstVar* const returnXzp
                    = new AstVar{varp->fileline(), VVarType::PORT, varp->name() + "__Vxz",
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
                portEndp->addNextHere(returnXzp);
                portEndp->addNextHere(returnValuep);
                varp->user1p(returnValuep);
                returnValuep->fourStateComplement(returnXzp);
                ftaskp->dtypeSetVoid();
                return;
            }
        }
        AstVar* const newXzp = varp->cloneTree(false);
        newXzp->name(newXzp->name() + "__Vxz");
        newXzp->fourstateOriginalDTypeKwd(varp->dtypep()->basicp()->keyword());
        newXzp->dtypeSetBitUnsized(varp->width(), varp->widthMin(), varp->dtypep()->numeric());
        if (AstNodeExpr* const valuep = VN_CAST(newXzp->valuep(), NodeExpr)) {
            valuep->unlinkFrBack();
            newXzp->valuep(getFourStateExpressionXZ(valuep));
            valuep->deleteTree();
        }
        varp->addNextHere(newXzp);
        AstVar* const newValuep = varp->cloneTree(false);
        newValuep->name(newValuep->name() + "__Vvalue");
        newValuep->trace(varp->isTrace());
        newValuep->fourstateOriginalDTypeKwd(varp->dtypep()->basicp()->keyword());
        newValuep->dtypeSetBitUnsized(varp->width(), varp->widthMin(), varp->dtypep()->numeric());
        if (AstNodeExpr* const valuep = VN_CAST(newValuep->valuep(), NodeExpr)) {
            valuep->unlinkFrBack();
            newValuep->valuep(getFourStateExpressionValue(valuep));
            valuep->deleteTree();
        }
        newValuep->fourStateComplement(newXzp);
        varp->addNextHere(newValuep);
        varp->user1p(newValuep);
    }

    static AstVar* getSplittedValue(AstVar* const varp) {
        UASSERT_OBJ(varp->dtypep()->isFourstate(), varp,
                    "Split shall be called only on four-state variables");
        UASSERT_OBJ(varp->user1p(), varp, "Variable shall be split first");
        return VN_AS(varp->user1p(), Var);
    }

    static AstVar* getSplittedXZ(AstVar* const varp) {
        return getSplittedValue(varp)->fourStateComplement();
    }

    void addPrecalculation(AstNodeStmt* const nodep) {
        FourstateLogicTypePropagator{nodep};
        m_currentStmtp->addHereThisAsNext(nodep);
    }

    AstNodeExpr* getFourStateExpressionSelHandler(AstSel* const selp, AstNodeExpr* const valueExpr,
                                                  const bool defaultsToZero) {
        FileLine* const flp = selp->fileline();
        AstNodeExpr* lsbp = selp->lsbp();
        V3Number maxmsb{flp, lsbp->width(),
                        static_cast<uint32_t>(selp->fromp()->dtypep()->width() - 1)};
        if (isStaticallyNGte(maxmsb, lsbp)) {
            if (!selp->fromp()->isPure()) {
                addPrecalculation(new AstStmtExpr{flp, valueExpr});
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
        newp->user3(1);
        newp->fromp(valueExpr);
        if (isStaticallyGte(maxmsb, lsbp)) {
            newp->lsbp(lsbp->cloneTree(false));
            return newp;
        }
        AstConst* const maxmsbConstp = new AstConst{flp, maxmsb};
        AstNodeExpr* conditionp;
        if (isFourstate(lsbp)) {
            conditionp
                = new AstOr{flp, getFourStateExpressionXZ(lsbp, isFourstate(selp)),
                            new AstLt{flp, maxmsbConstp, getFourStateExpressionValue(lsbp, true)}};
            lsbp = getFourStateExpressionValue(lsbp, true);
        } else {
            if (!VN_IS(lsbp, NodeVarRef) && !VN_IS(lsbp, Const)) {
                AstVar* const lsbTmpp = createTmp(lsbp);
                addPrecalculation(new AstAssign{flp, new AstVarRef{flp, lsbTmpp, VAccess::WRITE},
                                                lsbp->cloneTree(false)});
                lsbp = new AstVarRef{flp, lsbTmpp, VAccess::READ};
            } else {
                lsbp = lsbp->cloneTree(false);
            }
            conditionp = new AstLt{flp, maxmsbConstp, lsbp->cloneTree(false)};
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

        void getFourStateExpressionFuncRefHandler(AstNodeFTaskRef* const funcp) {
            // Its ok to use this instead of output since we only need width which is the same
            AstVar* const functionReturnVarp = VN_AS(VN_AS(funcp->taskp(), Func)->fvarp(), Var);
            AstVar* const resultValuep = m_fourstateVisitor.createTmp(functionReturnVarp);
            AstVar* const resultXzp = m_fourstateVisitor.createTmp(functionReturnVarp);
            AstNodeFTaskRef* const newCallp = funcp->cloneTree(false);
            if (newCallp->argsp()) newCallp->argsp()->unlinkFrBackWithNext()->deleteTree();
            FileLine* const flp = funcp->fileline();
            AstNode* varStmtp = funcp->taskp()->stmtsp();
            for (AstArg* argp = funcp->argsp(); argp; argp = VN_AS(argp->nextp(), Arg)) {
                const AstVar* const varp = VN_AS(varStmtp, Var);
                if (varp->dtypep()->isFourstate() || varp->fourStateComplement()) {
                    newCallp->addArgsp(
                        new AstArg{flp, "", getFourStateExpressionValue(argp->exprp(), false)});
                    newCallp->addArgsp(
                        new AstArg{flp, "", getFourStateExpressionXZ(argp->exprp(), false)});
                    if (varp->fourStateComplement()) varStmtp = varStmtp->nextp();
                } else if (isFourstate(argp->exprp())) {
                    newCallp->addArgsp(
                        new AstArg{flp, "", m_fourstateVisitor.getTwoStateCast(argp->exprp())});
                } else {
                    newCallp->addArgsp(argp->cloneTree(false));
                }
                varStmtp = varStmtp->nextp();
            }
            AstVarRef* const resultValueRefp = new AstVarRef{flp, resultValuep, VAccess::WRITE};
            AstVarRef* const resultXzRefp = new AstVarRef{flp, resultXzp, VAccess::WRITE};
            setFourstate(resultValueRefp, false);
            setFourstate(resultXzRefp, false);
            newCallp->addArgsp(new AstArg{flp, "", resultValueRefp});
            newCallp->addArgsp(new AstArg{flp, "", resultXzRefp});
            AstStmtExpr* const newStmtExprp = new AstStmtExpr{flp, newCallp};
            newStmtExprp->user3(1);
            addPrecalculation(newStmtExprp);
            AstVarRef* const varRefValuep = new AstVarRef{flp, resultValuep, VAccess::READ};
            AstVarRef* const varRefXzp = new AstVarRef{flp, resultXzp, VAccess::READ};
            pushDeletep(varRefValuep);
            pushDeletep(varRefXzp);
            funcp->user1p(varRefValuep);
            funcp->user2p(varRefXzp);
        }

        void getFourStateExpressionCondHandler(AstCond* const condp) {
            FileLine* const flp = condp->fileline();
            AstVar* const resultValueTmpVarp = m_fourstateVisitor.createTmp(condp->thenp());
            AstVar* const resultXZTmpVarp = m_fourstateVisitor.createTmp(condp->thenp());
            AstIf* ifp = new AstIf{flp, isFourstate(condp->condp())
                                            ? getFourStateExpressionXZ(condp->condp())
                                            : condp->condp()->cloneTree(false)};
            // Those must be here so expr is always evaluated fully in the right place
            AstIf* twoStateIfp = ifp;
            if (isFourstate(condp->condp())) {
                // Condition is X/Z
                AstNodeExpr* conditionValuep = getFourStateExpressionValue(condp->condp());
                AstNodeExpr* const thenCopyp = condp->thenp()->cloneTree(false);
                AstNodeExpr* const elseCopyp = condp->elsep()->cloneTree(false);
                StatementPlaceHolder thenPlaceholder{m_fourstateVisitor, flp};
                ifp->addThensp(thenPlaceholder.stmtp());
                TmpVarsReleaser tmpVarsReleaser{m_fourstateVisitor};
                addPrecalculation(
                    new AstAssign{flp, new AstVarRef{flp, resultValueTmpVarp, VAccess::WRITE},
                                  getFourStateExpressionValue(thenCopyp, false)});
                addPrecalculation(
                    new AstAssign{flp, new AstVarRef{flp, resultXZTmpVarp, VAccess::WRITE},
                                  getFourStateExpressionXZ(thenCopyp, false)});
                AstIf* const thenifp = new AstIf{
                    flp, new AstOr{
                             flp,
                             new AstXor{flp, new AstVarRef{flp, resultValueTmpVarp, VAccess::READ},
                                        getFourStateExpressionValue(elseCopyp, false)},
                             new AstXor{flp, new AstVarRef{flp, resultXZTmpVarp, VAccess::READ},
                                        getFourStateExpressionXZ(elseCopyp, false)}}};
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
                                      getFourStateExpressionValue(condp->thenp(), false)});
                    addPrecalculation(
                        new AstAssign{flp, new AstVarRef{flp, resultXZTmpVarp, VAccess::WRITE},
                                      getFourStateExpressionXZ(condp->thenp(), false)});
                }
                {
                    // Condition is 0
                    StatementPlaceHolder elsePlaceholder{m_fourstateVisitor, flp};
                    twoStateIfp->addElsesp(elsePlaceholder.stmtp());
                    TmpVarsReleaser tmpVarsReleaser{m_fourstateVisitor};
                    addPrecalculation(
                        new AstAssign{flp, new AstVarRef{flp, resultValueTmpVarp, VAccess::WRITE},
                                      getFourStateExpressionValue(condp->elsep(), false)});
                    addPrecalculation(
                        new AstAssign{flp, new AstVarRef{flp, resultXZTmpVarp, VAccess::WRITE},
                                      getFourStateExpressionXZ(condp->elsep(), false)});
                }
            }
            addPrecalculation(ifp);
            AstVarRef* const resultValueTmpVarRefp
                = new AstVarRef{flp, resultValueTmpVarp, VAccess::READ};
            AstVarRef* const resultXZTmpVarRefp
                = new AstVarRef{flp, resultXZTmpVarp, VAccess::READ};
            pushDeletep(resultValueTmpVarRefp);
            pushDeletep(resultXZTmpVarRefp);
            condp->user1p(resultValueTmpVarRefp);
            condp->user2p(resultXZTmpVarRefp);
        }

        void getFourStateExpressionLogAndHandler(AstLogAnd* const logAndp) {
            FileLine* const flp = logAndp->fileline();
            AstVar* const resultValueTmpVarp = m_fourstateVisitor.createTmp(logAndp);
            AstVar* const resultXZTmpVarp = m_fourstateVisitor.createTmp(logAndp);
            addPrecalculation(new AstAssign{flp,
                                            new AstVarRef{flp, resultXZTmpVarp, VAccess::WRITE},
                                            getFourStateExpressionXZ(logAndp->lhsp(), false)});
            addPrecalculation(
                new AstAssign{flp, new AstVarRef{flp, resultValueTmpVarp, VAccess::WRITE},
                              new AstOr{flp, new AstVarRef{flp, resultXZTmpVarp, VAccess::READ},
                                        getFourStateExpressionValue(logAndp->lhsp(), false)}});
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
                    new AstOr{flp, getFourStateExpressionValue(logAndp->rhsp(), false),
                              getFourStateExpressionXZ(logAndp->rhsp())}});
                addPrecalculation(new AstAssign{
                    flp, new AstVarRef{flp, resultXZTmpVarp, VAccess::WRITE},
                    new AstLogAnd{flp, new AstVarRef{flp, resultValueTmpVarp, VAccess::READ},
                                  new AstOr{flp,
                                            new AstVarRef{flp, resultXZTmpVarp, VAccess::READ},
                                            getFourStateExpressionXZ(logAndp->rhsp())}}});
            }
            AstVarRef* const resultValueTmpVarRefp
                = new AstVarRef{flp, resultValueTmpVarp, VAccess::READ};
            AstVarRef* const resultXZTmpVarRefp
                = new AstVarRef{flp, resultXZTmpVarp, VAccess::READ};
            pushDeletep(resultValueTmpVarRefp);
            pushDeletep(resultXZTmpVarRefp);
            logAndp->user1p(resultValueTmpVarRefp);
            logAndp->user2p(resultXZTmpVarRefp);
        }

        void getFourStateExpressionLogOrHandler(AstLogOr* const logOrp) {
            FileLine* const flp = logOrp->fileline();
            AstVar* const resultValueTmpVarp = m_fourstateVisitor.createTmp(logOrp);
            AstVar* const resultXZTmpVarp = m_fourstateVisitor.createTmp(logOrp);
            addPrecalculation(new AstAssign{flp,
                                            new AstVarRef{flp, resultXZTmpVarp, VAccess::WRITE},
                                            getFourStateExpressionXZ(logOrp->lhsp(), false)});
            addPrecalculation(new AstAssign{flp,
                                            new AstVarRef{flp, resultValueTmpVarp, VAccess::WRITE},
                                            getFourStateExpressionValue(logOrp->lhsp(), false)});
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
                    new AstOr{flp, getFourStateExpressionValue(logOrp->rhsp()),
                              new AstOr{flp, getFourStateExpressionXZ(logOrp->rhsp()),
                                        new AstVarRef{flp, resultXZTmpVarp, VAccess::READ}}}});
                addPrecalculation(new AstAssign{
                    flp, new AstVarRef{flp, resultXZTmpVarp, VAccess::WRITE},
                    new AstLogAnd{
                        flp, new AstVarRef{flp, resultValueTmpVarp, VAccess::READ},
                        new AstOr{flp,
                                  new AstNot{flp, getFourStateExpressionValue(logOrp->rhsp())},
                                  getFourStateExpressionXZ(logOrp->rhsp())}}});
            }
            AstVarRef* const resultValueTmpVarRefp
                = new AstVarRef{flp, resultValueTmpVarp, VAccess::READ};
            AstVarRef* const resultXZTmpVarRefp
                = new AstVarRef{flp, resultXZTmpVarp, VAccess::READ};
            pushDeletep(resultValueTmpVarRefp);
            pushDeletep(resultXZTmpVarRefp);
            logOrp->user1p(resultValueTmpVarRefp);
            logOrp->user2p(resultXZTmpVarRefp);
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

        virtual AstNodeExpr* getFourStateExpressionValue(AstNodeExpr* const exprp,
                                                         bool putIntoTmp = true) {
            return m_fourstateVisitor.m_fourstateGeneratorValueVisitor.getFourStateExpressionValue(
                exprp, putIntoTmp);
        }

        virtual AstNodeExpr* getFourStateExpressionXZ(AstNodeExpr* const exprp,
                                                      const bool putIntoTmp = true) {
            return m_fourstateVisitor.m_fourstateGeneratorXZVisitor.getFourStateExpressionXZ(
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
                                  new AstOr{flp, getFourStateExpressionValue(andp->lhsp()),
                                            getFourStateExpressionXZ(andp->lhsp())},
                                  new AstOr{flp, getFourStateExpressionValue(andp->rhsp()),
                                            getFourStateExpressionXZ(andp->rhsp())}};
        }

        void visit(AstOr* const orp) override {
            // a.value | b.value | a.xz | b.xz
            FileLine* const flp = orp->fileline();
            m_result = new AstOr{flp,
                                 new AstOr{flp, getFourStateExpressionValue(orp->lhsp()),
                                           getFourStateExpressionValue(orp->rhsp())},
                                 new AstOr{flp, getFourStateExpressionXZ(orp->lhsp()),
                                           getFourStateExpressionXZ(orp->rhsp())}};
        }

        void visit(AstXor* const xorp) override {
            // (a.value ^ b.value) | a.xz | b.xz
            FileLine* const flp = xorp->fileline();
            m_result = new AstOr{flp,
                                 new AstXor{flp, getFourStateExpressionValue(xorp->lhsp(), false),
                                            getFourStateExpressionValue(xorp->rhsp(), false)},
                                 getFourStateExpressionXZ(xorp)};
        }

        void visit(AstNot* const notp) override {
            // ~a.value | a.xz
            FileLine* const flp = notp->fileline();
            m_result = new AstOr{flp, new AstNot{flp, getFourStateExpressionValue(notp->lhsp())},
                                 getFourStateExpressionXZ(notp->lhsp())};
        }

        void visit(AstEq* const eqp) override {
            // (a.xz | b.xz != 0) | (a.value == b.value )
            FileLine* const flp = eqp->fileline();
            m_result = new AstOr{flp, getFourStateExpressionXZ(eqp),
                                 new AstEq{flp, getFourStateExpressionValue(eqp->lhsp()),
                                           getFourStateExpressionValue(eqp->rhsp())}};
        }

        void visit(AstNeq* const neqp) override {
            // (a.xz | b.xz != 0) | (a.value != b.value )
            FileLine* const flp = neqp->fileline();
            m_result = new AstOr{flp, getFourStateExpressionXZ(neqp),
                                 new AstNeq{flp, getFourStateExpressionValue(neqp->lhsp()),
                                            getFourStateExpressionValue(neqp->rhsp())}};
        }

        void visit(AstExtend* const extendp) override {
            FileLine* const flp = extendp->fileline();
            m_result = new AstExtend{flp, getFourStateExpressionValue(extendp->lhsp(), false)};
        }

        void visit(AstExtendS* const extendsp) override {
            FileLine* const flp = extendsp->fileline();
            m_result = new AstExtendS{flp, getFourStateExpressionValue(extendsp->lhsp(), false)};
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
            getFourStateExpressionFuncRefHandler(funcp);
            noTmp();
            m_result = VN_AS(funcp->user1p(), NodeExpr)->cloneTree(false);
        }

        void visit(AstCond* const condp) override {
            getFourStateExpressionCondHandler(condp);
            noTmp();
            m_result = VN_AS(condp->user1p(), NodeExpr)->cloneTree(false);
        }

        void visit(AstLogAnd* const logAndp) override {
            getFourStateExpressionLogAndHandler(logAndp);
            noTmp();
            m_result = VN_AS(logAndp->user1p(), NodeExpr)->cloneTree(false);
        }

        void visit(AstLogOr* const logOrp) override {
            getFourStateExpressionLogOrHandler(logOrp);
            noTmp();
            m_result = VN_AS(logOrp->user1p(), NodeExpr)->cloneTree(false);
        }

        void visit(AstSel* const selp) override {
            m_result = m_fourstateVisitor.getFourStateExpressionSelHandler(
                selp, getFourStateExpressionValue(selp->fromp(), false), false);
        }

        void visit(AstRedOr* const redOrp) override {
            // |(a.value | a.xz)
            enforceTmp();
            FileLine* const flp = redOrp->fileline();
            m_result
                = new AstRedOr{flp, new AstOr{flp, getFourStateExpressionValue(redOrp->lhsp()),
                                              getFourStateExpressionXZ(redOrp->lhsp())}};
        }

        void getFourStateExpressionArithmeticValue(AstNodeBiop* const biop) {
            // (a.xz | b.xz) ? '1 : (a op b)
            FileLine* const flp = biop->fileline();
            AstNodeBiop* const newp = biop->cloneTree(false);
            newp->dtypeSetBitSized(biop->width(), biop->dtypep()->numeric());
            newp->lhsp()->unlinkFrBack()->deleteTree();
            newp->rhsp()->unlinkFrBack()->deleteTree();
            newp->lhsp(getFourStateExpressionValue(biop->lhsp(), false));
            newp->rhsp(getFourStateExpressionValue(biop->rhsp(), false));
            m_result = new AstCond{
                flp,
                new AstRedOr{flp, new AstOr{flp, getFourStateExpressionXZ(biop->lhsp()),
                                            getFourStateExpressionXZ(biop->rhsp())}},
                createZeroOrOnesp(biop, true), newp};
        }

        void visit(AstAdd* const addp) override { getFourStateExpressionArithmeticValue(addp); }
        void visit(AstSub* const subp) override { getFourStateExpressionArithmeticValue(subp); }
        void visit(AstMul* const mulp) override { getFourStateExpressionArithmeticValue(mulp); }

        void visit(AstNodeVarRef* const varRefp) override {
            noTmp();
            if (varRefp->varp()->dtypep()->isFourstate()) {
                m_fourstateVisitor.splitVar(varRefp->varp());
                AstNodeVarRef* const newp = varRefp->cloneTree(false);
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
            return VN_AS(keyp->user1p(), NodeExpr);
        }
        void setCache(AstNodeExpr* keyp, AstNodeExpr* const valuep) override {
            keyp->user1p(valuep);
        }

    public:
        using FourstateExpressionVisitor::FourstateExpressionVisitor;
        ~FourstateExpressionValueVisitor() override = default;

        AstNodeExpr* getFourStateExpressionValue(AstNodeExpr* const exprp,
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
                                      new AstAnd{flp, getFourStateExpressionValue(andp->lhsp()),
                                                 getFourStateExpressionXZ(andp->rhsp())},
                                      new AstAnd{flp, getFourStateExpressionValue(andp->rhsp()),
                                                 getFourStateExpressionXZ(andp->lhsp())}},
                            new AstAnd{flp, getFourStateExpressionXZ(andp->lhsp()),
                                       getFourStateExpressionXZ(andp->rhsp())}};
        }

        void visit(AstOr* const orp) override {
            // (a.xz & b.xz) | (a.xz & ~b.value) | (b.xz & ~a.value)
            FileLine* const flp = orp->fileline();
            m_result = new AstOr{
                flp,
                new AstOr{flp,
                          new AstAnd{flp, getFourStateExpressionXZ(orp->lhsp()),
                                     getFourStateExpressionXZ(orp->rhsp())},
                          new AstAnd{flp, getFourStateExpressionXZ(orp->lhsp()),
                                     new AstNot{flp, getFourStateExpressionValue(orp->rhsp())}}},
                new AstAnd{flp, getFourStateExpressionXZ(orp->rhsp()),
                           new AstNot{flp, getFourStateExpressionValue(orp->lhsp())}}};
        }

        void visit(AstXor* const xorp) override {
            // a.xz | b.xz
            FileLine* const flp = xorp->fileline();
            m_result = new AstOr{flp, getFourStateExpressionXZ(xorp->lhsp()),
                                 getFourStateExpressionXZ(xorp->rhsp())};
        }

        void visit(AstNot* const notp) override {
            // a.xz
            m_result = getFourStateExpressionXZ(notp->lhsp());
        }

        void visit(AstEq* const eqp) override {
            // a.xz | b.xz != 0
            enforceTmp();
            FileLine* const flp = eqp->fileline();
            m_result = new AstNeq{flp,
                                  new AstOr{flp, getFourStateExpressionXZ(eqp->lhsp()),
                                            getFourStateExpressionXZ(eqp->rhsp())},
                                  new AstConst{flp, AstConst::BitFalse{}}};
        }

        void visit(AstNeq* const neqp) override {
            // a.xz | b.xz != 0
            enforceTmp();
            FileLine* const flp = neqp->fileline();
            m_result = new AstNeq{flp,
                                  new AstOr{flp, getFourStateExpressionXZ(neqp->lhsp()),
                                            getFourStateExpressionXZ(neqp->rhsp())},
                                  new AstConst{flp, AstConst::BitFalse{}}};
        }

        void visit(AstExtend* const extendp) override {
            FileLine* const flp = extendp->fileline();
            m_result = new AstExtend{flp, getFourStateExpressionXZ(extendp->lhsp(), false)};
        }

        void visit(AstExtendS* const extendsp) override {
            FileLine* const flp = extendsp->fileline();
            m_result = new AstExtendS{flp, getFourStateExpressionXZ(extendsp->lhsp(), false)};
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

        void visit(AstRedOr* const redOrp) override {
            // |a.xz & ~|(a.value | a.xz)
            FileLine* const flp = redOrp->fileline();
            m_result = new AstAnd{flp, new AstRedOr{flp, getFourStateExpressionXZ(redOrp->lhsp())},
                                  new AstNot{flp, getFourStateExpressionValue(redOrp)}};
        }

        void getFourStateExpressionArithmeticXZ(AstNodeBiop* const biop) {
            // (a.xz | b.xz) ? '1 : '0
            FileLine* const flp = biop->fileline();
            m_result = new AstCond{
                flp,
                new AstRedOr{flp, new AstOr{flp, getFourStateExpressionXZ(biop->lhsp()),
                                            getFourStateExpressionXZ(biop->rhsp())}},
                createZeroOrOnesp(biop, true), createZeroOrOnesp(biop)};
        }

        void visit(AstAdd* const addp) override { getFourStateExpressionArithmeticXZ(addp); }
        void visit(AstSub* const subp) override { getFourStateExpressionArithmeticXZ(subp); }
        void visit(AstMul* const mulp) override { getFourStateExpressionArithmeticXZ(mulp); }

        void visit(AstNodeFTaskRef* const funcp) override {
            getFourStateExpressionFuncRefHandler(funcp);
            noTmp();
            m_result = VN_AS(funcp->user2p(), NodeExpr)->cloneTree(false);
        }

        void visit(AstCond* const condp) override {
            getFourStateExpressionCondHandler(condp);
            noTmp();
            m_result = VN_AS(condp->user2p(), NodeExpr)->cloneTree(false);
        }

        void visit(AstLogAnd* const logAndp) override {
            getFourStateExpressionLogAndHandler(logAndp);
            noTmp();
            m_result = VN_AS(logAndp->user2p(), NodeExpr)->cloneTree(false);
        }

        void visit(AstLogOr* const logOrp) override {
            getFourStateExpressionLogOrHandler(logOrp);
            noTmp();
            m_result = VN_AS(logOrp->user2p(), NodeExpr)->cloneTree(false);
        }

        void visit(AstSel* const selp) override {
            m_result = m_fourstateVisitor.getFourStateExpressionSelHandler(
                selp, getFourStateExpressionXZ(selp->fromp(), false), false);
        }

        void visit(AstNodeVarRef* const varRefp) override {
            noTmp();
            if (varRefp->varp()->dtypep()->isFourstate()) {
                m_fourstateVisitor.splitVar(varRefp->varp());
                AstNodeVarRef* const newp = varRefp->cloneTree(false);
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

        AstNodeExpr* getCache(const AstNodeExpr* const keyp) override {
            return VN_AS(keyp->user2p(), NodeExpr);
        }
        void setCache(AstNodeExpr* keyp, AstNodeExpr* const valuep) override {
            keyp->user2p(valuep);
        }

    public:
        using FourstateExpressionVisitor::FourstateExpressionVisitor;
        ~FourstateExpressionXZVisitor() override = default;

        AstNodeExpr* getFourStateExpressionXZ(AstNodeExpr* const exprp,
                                              bool putIntoTmp = true) override {
            if (!isFourstate(exprp)) return createZeroOrOnesp(exprp);
            return get(exprp, putIntoTmp);
        }
    };

    FourstateExpressionValueVisitor
        m_fourstateGeneratorValueVisitor;  // Generator of four-state expressions (value part)
    FourstateExpressionXZVisitor
        m_fourstateGeneratorXZVisitor;  // Generator of four-state expressions (xz part)

    AstNodeExpr* getFourStateExpressionValue(AstNodeExpr* const exprp, bool putIntoTmp = false) {
        if (AstCReset* const cresetp = VN_CAST(exprp, CReset)) {
            // This is here instead in the visitor because CReset shall never be nested into
            // the expression and also it is a very special case
            AstCReset* const resultp = cresetp->cloneTree(false);
            resultp->dtypeSetBitSized(cresetp->width(), cresetp->dtypep()->numeric());
            FourstateLogicTypePropagator{resultp};
            return resultp;
        }
        AstNodeExpr* const result
            = m_fourstateGeneratorValueVisitor.getFourStateExpressionValue(exprp, putIntoTmp);
        FourstateLogicTypePropagator{result};
        return result;
    }

    AstNodeExpr* getFourStateExpressionXZ(AstNodeExpr* const exprp, bool putIntoTmp = false) {
        if (AstCReset* const cresetp = VN_CAST(exprp, CReset)) {
            // This is here instead in the visitor because CReset shall never be nested into
            // the expression and also it is a very special case
            AstCReset* const result = cresetp->cloneTree(false);
            result->dtypeSetBitSized(cresetp->width(), cresetp->dtypep()->numeric());
            FourstateLogicTypePropagator{result};
            return result;
        }
        AstNodeExpr* const result
            = m_fourstateGeneratorXZVisitor.getFourStateExpressionXZ(exprp, putIntoTmp);
        FourstateLogicTypePropagator{result};
        return result;
    }

    AstNodeExpr* getTruthExpr(AstNodeExpr* const exprp) {
        UASSERT_OBJ(isFourstate(exprp), exprp,
                    "This function is ment to be called on four-state expressions");
        // a.value && !a.xz
        FileLine* const flp = exprp->fileline();
        AstLogAnd* const result
            = new AstLogAnd{flp, getFourStateExpressionValue(exprp),
                            new AstLogNot{flp, getFourStateExpressionXZ(exprp)}};
        setFourstate(result, false);
        setFourstate(result->rhsp(), false);
        return result;
    }

    AstNodeExpr* getTwoStateCast(AstNodeExpr* const exprp) {
        UASSERT_OBJ(isFourstate(exprp), exprp,
                    "This function is ment to be called on four-state expressions");
        // (a.value & (~a.xz))
        FileLine* const flp = exprp->fileline();
        AstAnd* const result = new AstAnd{flp, getFourStateExpressionValue(exprp),
                                          new AstNot{flp, getFourStateExpressionXZ(exprp)}};
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
                AstNodeExpr* const newLhsp = getFourStateExpressionXZ(lhsVarRefp);
                assignXZp->lhsp(newLhsp);
                assignXZp->rhsp(getFourStateExpressionXZ(nodep->rhsp()));
                assignXZp->dtypeFrom(newLhsp);
                nodep->addNextHere(assignXZp);
            }
            {
                AstNodeExpr* const newRhsp = getFourStateExpressionValue(nodep->rhsp());
                AstNodeExpr* const newLhsp = getFourStateExpressionValue(lhsVarRefp);
                pushDeletep(nodep->lhsp()->unlinkFrBack());
                pushDeletep(nodep->rhsp()->unlinkFrBack());
                nodep->lhsp(newLhsp);
                nodep->rhsp(newRhsp);
                nodep->dtypeFrom(newLhsp);
            }
            if (AstAssignW* const assignWValuep = VN_CAST(nodep, AssignW)) {
                assignWConflictResolution(lhsVarRefp->varp(), assignWValuep,
                                          VN_AS(assignXZp, AssignW));
            }
        } else if (isFourstate(nodep->rhsp())) {
            AstNodeExpr* const newRhsp = getTwoStateCast(nodep->rhsp());
            pushDeletep(nodep->rhsp()->unlinkFrBack());
            nodep->rhsp(newRhsp);
        }
        iterateChildren(nodep);
    }

    void visit(AstStmtExpr* const nodep) override {
        if (nodep->user3SetOnce()) return;
        VL_RESTORER(m_currentStmtp);
        m_currentStmtp = nodep;
        TmpVarsReleaser tmpVarsReleaser{*this};
        auto isFourState = [nodep]() -> bool {
            if (isFourstate(nodep->exprp())) return true;
            if (AstNodeFTaskRef* const taskRefp = VN_CAST(nodep->exprp(), NodeFTaskRef)) {
                AstNodeDType* const dtypep = taskRefp->taskp()->dtypep();
                return dtypep && dtypep->isFourstate();
            }
            return false;
        };
        if (isFourState()) {
            AstNodeExpr* const exprp = nodep->exprp()->unlinkFrBack();
            nodep->exprp(getFourStateExpressionValue(exprp));
            AstNodeExpr* const newXzp = getFourStateExpressionXZ(exprp);
            iterateChildren(newXzp);
            AstStmtExpr* const newStmtExprp = new AstStmtExpr{nodep->fileline(), newXzp};
            newStmtExprp->user3(1);
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

    void visit(AstSenItem* const nodep) override {
        if (isFourstate(nodep->sensp())) {
            AstNodeExpr* const sensp = nodep->sensp()->unlinkFrBack();
            nodep->sensp(new AstFourstateExpr{nodep->fileline(),
                                              getFourStateExpressionValue(sensp),
                                              getFourStateExpressionXZ(sensp)});
            sensp->deleteTree();
        }
    }

    void visit(AstSFormatF* const nodep) override {
        for (AstNodeExpr* exprp = nodep->exprsp(); exprp;
             exprp = VN_AS(exprp->nextp(), NodeExpr)) {
            if (isFourstate(exprp)) {
                exprp->v3warn(LOGICCAST,
                              "Using four-state values in formatting strings is not supported yet "
                              "- all four-state values will be implicitly casted to two-state");
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

    void visit(AstCell* const nodep) override {
        VL_RESTORER(m_currentArgVarp);
        m_currentArgVarp = nodep->modp()->stmtsp();
        iterateChildren(nodep);
    }

    void visit(AstPin* const nodep) override {
        AstVar* const varp = VN_CAST(m_currentArgVarp, Var);
        UASSERT_OBJ(varp, nodep, "Cell has no more arguments?");
        if (AstNodeExpr* const exprp = VN_CAST(nodep->exprp(), NodeExpr)) {
            if (varp->dtypep()->isFourstate()) {
                AstPin* const newp = new AstPin{nodep->fileline(), nodep->pinNum(), "",
                                                getFourStateExpressionXZ(exprp)};
                nodep->addNextHere(newp);
                AstNodeExpr* const oldp = exprp->unlinkFrBack();
                nodep->exprp(getFourStateExpressionValue(oldp));
                oldp->deleteTree();
                splitVar(varp);  // Ensure that variable is splitted
                UASSERT_OBJ(m_currentArgVarp->nextp() && m_currentArgVarp->nextp()->nextp(), varp,
                            "Varp was not split correctly");
                m_currentArgVarp = m_currentArgVarp->nextp();
                nodep->modVarp(VN_AS(m_currentArgVarp, Var));
                newp->modVarp(VN_AS(m_currentArgVarp->nextp(), Var));
            } else if (isFourstate(exprp)) {
                AstNodeExpr* const oldp = exprp->unlinkFrBack();
                nodep->exprp(getTwoStateCast(oldp));
                oldp->deleteTree();
            }
        }
        m_currentArgVarp = m_currentArgVarp->nextp();
        iterateChildren(nodep);
    }

    void visit(AstNodeFTaskRef* const nodep) override {
        VL_RESTORER(m_currentFTaskArgp);
        m_currentFTaskArgp = nodep->taskp()->stmtsp();
        iterateChildren(nodep);
    }

    void visit(AstArg* const nodep) override {
        AstVar* const varp = VN_CAST(m_currentFTaskArgp, Var);
        UASSERT_OBJ(varp, nodep, "FTask has no more arguments?");
        if (varp->dtypep()->isFourstate()) {
            nodep->addNextHere(
                new AstArg{nodep->fileline(), "", getFourStateExpressionXZ(nodep->exprp())});
            AstNodeExpr* const oldp = nodep->exprp()->unlinkFrBack();
            nodep->exprp(getFourStateExpressionValue(oldp));
            oldp->deleteTree();
            splitVar(varp);  // Ensure that variable is splitted
            UASSERT_OBJ(m_currentFTaskArgp->nextp() && m_currentFTaskArgp->nextp()->nextp(), varp,
                        "Varp was not split correctly");
            m_currentFTaskArgp = m_currentFTaskArgp->nextp();
        } else if (isFourstate(nodep->exprp())) {
            AstNodeExpr* const oldp = nodep->exprp()->unlinkFrBack();
            nodep->exprp(getTwoStateCast(oldp));
            oldp->deleteTree();
        }
        m_currentFTaskArgp = m_currentFTaskArgp->nextp();
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
                              new AstEq{flp, getFourStateExpressionXZ(nodep->lhsp()),
                                        getFourStateExpressionXZ(nodep->rhsp())},
                              new AstEq{flp, getFourStateExpressionValue(nodep->lhsp()),
                                        getFourStateExpressionValue(nodep->rhsp())}};
        } else if (isFourstate(nodep->lhsp()) || isFourstate(nodep->rhsp())) {
            AstNodeExpr* const fourstateHsp
                = isFourstate(nodep->lhsp()) ? nodep->lhsp() : nodep->rhsp();
            AstNodeExpr* const twostateHsp = isFourstate(nodep->lhsp())
                                                 ? nodep->rhsp()->unlinkFrBack()
                                                 : nodep->lhsp()->unlinkFrBack();
            newp = new AstAnd{
                flp, new AstNot{flp, getFourStateExpressionXZ(fourstateHsp)},
                new AstEq{flp, getFourStateExpressionValue(fourstateHsp), twostateHsp}};
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
                               new AstXor{flp, getFourStateExpressionValue(nodep->lhsp()),
                                          getFourStateExpressionValue(nodep->rhsp())},
                               new AstXor{flp, getFourStateExpressionXZ(nodep->lhsp()),
                                          getFourStateExpressionXZ(nodep->rhsp())}}};
        } else if (isFourstate(nodep->lhsp()) || isFourstate(nodep->rhsp())) {
            AstNodeExpr* const fourstateHsp
                = isFourstate(nodep->lhsp()) ? nodep->lhsp() : nodep->rhsp();
            AstNodeExpr* const twostateHsp = isFourstate(nodep->lhsp())
                                                 ? nodep->rhsp()->unlinkFrBack()
                                                 : nodep->lhsp()->unlinkFrBack();
            newp = new AstRedOr{
                flp, new AstOr{
                         flp, getFourStateExpressionXZ(fourstateHsp),
                         new AstXor{flp, getFourStateExpressionValue(fourstateHsp), twostateHsp}}};
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
        if (nodep->user3SetOnce()) return;
        AstNodeExpr* const newp
            = getFourStateExpressionSelHandler(nodep, nodep->fromp()->cloneTree(false), true);
        { FourstateLogicTypePropagator{newp}; }
        VNRelinker relinker;
        nodep->unlinkFrBack(&relinker);
        relinker.relink(newp);
        nodep->deleteTree();
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

    void visit(AstNodeFTask* const nodep) override {
        VL_RESTORER(m_currentTmpSpotp);
        VL_RESTORER(m_tmpUnusedVarps);
        VL_RESTORER(m_tmpFuncLocal);
        m_tmpFuncLocal = true;
        m_currentTmpSpotp = createPlaceholderVarp(nodep->fileline());
        if (AstNode* stmtp = nodep->stmtsp()) {
            while (VN_IS(stmtp->nextp(), Var)) stmtp = stmtp->nextp();
            stmtp->addNextHere(m_currentTmpSpotp);
        } else {
            nodep->addStmtsp(m_currentTmpSpotp);
        }
        TmpVarsReleaser releaser{*this};
        // Make sure FTasks use only local variables - prevents using tmp
        // which may be used by a caller
        for (auto& it : m_tmpUnusedVarps) it.clear();
        iterateChildren(nodep);
    }

    void visit(AstVar* const nodep) override {
        if (nodep->dtypep()->isFourstate()) splitVar(nodep);
        iterateChildren(nodep);
    }

    void visit(AstNodeModule* const nodep) override {
        VL_RESTORER(m_currentTmpSpotp);
        VL_RESTORER(m_tmpUnusedVarps);
        m_currentTmpSpotp = createPlaceholderVarp(nodep->fileline());
        if (AstNode* stmtp = nodep->stmtsp()) {
            stmtp->addHereThisAsNext(m_currentTmpSpotp);
        } else {
            nodep->addStmtsp(m_currentTmpSpotp);
        }
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
        : m_tmpNames{"__VfourStateTmp"}
        , m_fourstateGeneratorValueVisitor{*this}
        , m_fourstateGeneratorXZVisitor{*this} {
        { FourstateLogicTypePropagator{netlistp}; }
        iterate(netlistp);
        triorTriandReduce(m_assignWToTriand, triandReducer);
        triorTriandReduce(m_assignWToTrior, triorReducer);
        triorTriandReduce(m_assignWToWire, triReducer);
    }
    ~FourstateVisitor() override {
        V3Error::abortIfErrors();
        for (AstVar* const varp : m_varpsToRemove) varp->unlinkFrBack()->deleteTree();
    }
};

void V3Fourstate::fourstateAll(AstNetlist* netlistp) {
    UINFO(2, __FUNCTION__ << ":");
    { FourstateVisitor{netlistp}; }
    v3Global.setFourstateHandled();
    V3Global::dumpCheckGlobalTree("fourstate", 0, dumpTreeEitherLevel() >= 6);
}
