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
 *  - Short-circuiting
 *  - Statements - cases etc.
 *  - split asswignw into multiple statements
 */

struct FourStatePair final {
    AstNodeExpr* value;
    AstNodeExpr* xz;
};

namespace {
enum LogicType : char {
    UNINITIALIZED = 0,
    TWO_STATE,
    FOUR_STATE,
};

static void setLogicType(AstNodeExpr* const exprp, const LogicType logic) {
    exprp->user4(static_cast<int>(logic));
}

static void setFourstate(AstNodeExpr* const exprp, bool fourstate = true) {
    setLogicType(exprp, fourstate ? FOUR_STATE : TWO_STATE);
}

static LogicType getLogicType(const AstNodeExpr* const exprp) {
    return static_cast<LogicType>(exprp->user4());
}

static bool isFourstate(const AstNodeExpr* const exprp) {
    const LogicType logic = getLogicType(exprp);
    UASSERT_OBJ(logic != UNINITIALIZED, exprp, "Expression logic type is unevaluated");
    return logic == FOUR_STATE;
}

template <typename T, typename = void>
struct ReducerTrait final : std::false_type {};
template <typename T>
struct ReducerTrait<
    T, std::enable_if_t<std::is_same<decltype(std::declval<T>()(std::declval<FourStatePair>(),
                                                                std::declval<FourStatePair>())),
                                     FourStatePair>::value>>
    final : std::true_type {};
}  // namespace

class FourstateLogicTypePropagator final : public VNVisitor {
    void visit(AstConst* const nodep) override {
        iterateChildren(nodep);
        setFourstate(nodep, nodep->dtypep()->isFourstate());
    }

    void visit(AstNodeVarRef* const nodep) override {
        iterateChildren(nodep);
        setFourstate(nodep, nodep->varp()->dtypep()->isFourstate());
    }

    void visit(AstNodeFTaskRef* const nodep) override {
        iterateChildren(nodep);
        setFourstate(nodep,
                     nodep->taskp()->fvarp() && nodep->taskp()->fvarp()->dtypep()->isFourstate());
    }

    void visit(AstNodeUniop* const nodep) override {
        iterateChildren(nodep);
        setFourstate(nodep, isFourstate(nodep->lhsp()));
    }

    void visit(AstCastWrap* const nodep) override {
        iterateChildren(nodep);
        setFourstate(nodep, nodep->dtypep()->isFourstate());
    }

    void visit(AstNodeBiop* const nodep) override {
        iterateChildren(nodep);
        setFourstate(nodep, isFourstate(nodep->lhsp()) || isFourstate(nodep->rhsp()));
    }

    void visit(AstEqCase* const nodep) override {
        iterateChildren(nodep);
        setFourstate(nodep, true);
    }

    void visit(AstNeqCase* const nodep) override {
        iterateChildren(nodep);
        setFourstate(nodep, true);
    }

    void visit(AstDiv* nodep) override {
        iterateChildren(nodep);
        if (AstConst* const constp = VN_CAST(nodep->rhsp(), Const)) {
            setFourstate(nodep, isFourstate(nodep->lhsp()) || constp->num().isEqZero()
                                    || constp->num().isAnyXZ());
        } else {
            setFourstate(nodep);
        }
    }

    void visit(AstNodeTriop* const nodep) override {
        iterateChildren(nodep);
        setFourstate(nodep, isFourstate(nodep->lhsp()) || isFourstate(nodep->rhsp())
                                || isFourstate(nodep->thsp()));
    }

    void visit(AstCond* const nodep) override {
        iterateChildren(nodep);
        setFourstate(nodep, isFourstate(nodep->condp()) || isFourstate(nodep->thenp())
                                || isFourstate(nodep->elsep()));
    }

    void visit(AstCReset* const nodep) override {
        iterateChildren(nodep);
        setFourstate(nodep, false);
    }

    void visit(AstSFormatArg* const nodep) override {
        iterateChildren(nodep);
        setFourstate(nodep, isFourstate(nodep->exprp()));
        if (isFourstate(nodep)) {
            nodep->v3fatalSrc("Unsuppored: four-state expression in formating string");
        }
    }

    void visit(AstNodeExpr* const nodep) override {
        iterateChildren(nodep);
        if (nodep->dtypep()->isIntegralOrPacked()) {
            nodep->v3warn(E_UNSUPPORTED,
                          "Unsupported: Operator not supported in the four-state mode");
            setLogicType(nodep, TWO_STATE);  // Set an arbitraty logic type
        }
    }

    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    FourstateLogicTypePropagator(AstNode* const nodep) { iterate(nodep); }
    ~FourstateLogicTypePropagator() override = default;
};

class FourstateVisitor final : public VNVisitor {
    const VNUser1InUse m_user1InUse;
    const VNUser2InUse m_user2InUse;
    const VNUser4InUse m_user4InUse;
    // Node status
    // AstVar*::user1p      ->  AstVar*.        Where is value part of splitted variable - xz shall
    //                                          be nexp() of user1p
    // AstNodeExpr::user1p  ->  AstNodeExpr*.   Expression evaluating value component
    // AstStmtExpr::user1   ->  bool.           Whether visited
    // AstNodeExpr::user2p  ->  AstNodeExpr*.   Expression evaluating xz component
    // AstNodeExpr::user4   ->  LogicType.      Expression logic type (whether it is four
    //                                          or two state)

    V3UniqueNames m_tmpNames;

    AstVar* m_currentTmpSpotp = nullptr;  // Node after which put AstVar* for temporary variable
    bool m_tmpFuncLocal = false;
    AstNodeStmt* m_currentStmtp = nullptr;  // Current statement
    AstNode* m_currentFTaskArgp
        = nullptr;  // Current argument variable of FTaskRef - if not variable it is meaningless
    AstNode* m_currentPinp = nullptr;  // Current Pin of a Cell
    std::vector<AstVar*> m_varpsToRemove;  // Vars to unlink and remove in destructor

    // array - whether numeric
    // map - width
    std::array<std::map<int, std::vector<AstVar*>>, 2> m_tmpVarps;
    std::vector<AstVar*> m_tmpVarpsInUse;

    // Original AstVar* and pair of assignments <value, xz>
    using NetToAssignwps
        = std::map<const AstVar*, std::vector<std::pair<AstAssignW*, AstAssignW*>>>;
    NetToAssignwps m_assignWToTrior;
    NetToAssignwps m_assignWToTriand;
    NetToAssignwps m_assignWToWire;

    static FourStatePair triReducer(const FourStatePair& a, const FourStatePair& b) {
        FileLine* const flp = a.value->fileline();
        FourStatePair result;
        {
            // a.value | b.value
            result.value = new AstOr{flp, a.value, b.value};
        }
        {
            // (a.value & a.xz) | (b.value & b.xz) | (a.xz & b.xz) | (a.value & ~b.value & ~b.xz) |
            // (b.value & ~a.value & ~a.xz)
            result.xz = new AstOr{
                flp,
                new AstOr{flp,
                          new AstOr{flp, new AstAnd{flp, a.value->cloneTree(false), a.xz},
                                    new AstAnd{flp, b.value->cloneTree(false), b.xz}},
                          new AstAnd{flp, a.xz->cloneTree(false), b.xz->cloneTree(false)}},
                new AstOr{flp,
                          new AstAnd{flp,
                                     new AstAnd{flp, a.value->cloneTree(false),
                                                new AstNot{flp, b.value->cloneTree(false)}},
                                     new AstNot{flp, b.xz->cloneTree(false)}},
                          new AstAnd{flp,
                                     new AstAnd{flp, b.value->cloneTree(false),
                                                new AstNot{flp, a.value->cloneTree(false)}},
                                     new AstNot{flp, a.xz->cloneTree(false)}}}};
        }
        return result;
    }
    static FourStatePair triandReducer(const FourStatePair& a, const FourStatePair& b) {
        FileLine* const flp = a.value->fileline();
        FourStatePair result;
        {
            // (a.value & b.xz) | (b.value & a.xz) | (a.value & b.value)
            result.value = new AstOr{
                flp,
                new AstOr{flp, new AstAnd{flp, a.value, b.xz}, new AstAnd{flp, b.value, a.xz}},
                new AstAnd{flp, a.value->cloneTree(false), b.value->cloneTree(false)}};
        }
        {
            // (a.xz & b.xz) | (a.value & b.value & a.xz) | (a.value & b.value & b.xz)
            result.xz = new AstOr{
                flp,
                new AstOr{flp, new AstAnd{flp, a.xz->cloneTree(false), b.xz->cloneTree(false)},
                          new AstAnd{flp,
                                     new AstAnd{flp, a.value->cloneTree(false),
                                                b.value->cloneTree(false)},
                                     b.xz->cloneTree(false)}},
                new AstAnd{flp,
                           new AstAnd{flp, a.value->cloneTree(false), b.value->cloneTree(false)},
                           b.xz->cloneTree(false)}};
        }
        return result;
    }
    static FourStatePair triorReducer(const FourStatePair& a, const FourStatePair& b) {
        FileLine* const flp = a.value->fileline();
        FourStatePair result;
        {
            // a.value | b.value
            result.value = new AstOr{flp, a.value, b.value};
        }
        {
            // (a.value | b.xz) & (b.value | a.xz) & (a.xz | ~a.value) & (b.xz | ~b.value)
            result.xz
                = new AstAnd{flp,
                             new AstAnd{flp, new AstOr{flp, a.value->cloneTree(false), b.xz},
                                        new AstOr{flp, b.value->cloneTree(false), a.xz}},
                             new AstAnd{flp,
                                        new AstOr{flp, a.xz->cloneTree(false),
                                                  new AstNot{flp, a.value->cloneTree(false)}},
                                        new AstOr{flp, b.xz->cloneTree(false),
                                                  new AstNot{flp, b.value->cloneTree(false)}}}};
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
            assignps[0].first->rhsp(result.value);
            assignps[0].second->rhsp(result.xz);
            for (size_t i = 1; i < assignps.size(); ++i) {
                assignps[i].first->unlinkFrBack()->deleteTree();
                assignps[i].second->unlinkFrBack()->deleteTree();
            }
        }
    }

    static AstConst* createConst(const AstNodeExpr* const exprp, const bool ones = false) {
        AstConst* const resultp
            = new AstConst{exprp->fileline(), AstConst::WidthedValue{}, exprp->width(), 0};
        resultp->dtypeSetBitUnsized(exprp->width(), exprp->widthMin(), exprp->dtypep()->numeric());
        if (ones) resultp->num().setAllBits1();
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
        case VVarType::WIRE: m_assignWToWire[varp].emplace_back(assignwValuep, assignwXzp); break;
        default:
            assignwValuep->v3fatalSrc(
                "Unexpected variable type on lhs of assign: " << varp->varType().ascii());
            break;
        }
    }

    AstVar* createPlaceHolderVar(FileLine* const flp) {
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
                m_visitor.m_tmpVarps[varp->dtypep()->numeric().isSigned() ? 1 : 0][varp->width()]
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
        auto& pool = m_tmpVarps[dtypep->numeric().isSigned() ? 1 : 0];
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
                    ftaskp->addStmtsp(portEndp = createPlaceHolderVar(ftaskp->fileline()));
                } else if (AstVar* const portp = VN_CAST(ftaskp->stmtsp(), Var)) {
                    if (portp->varType() != VVarType::PORT) {
                        portp->addHereThisAsNext(portEndp
                                                 = createPlaceHolderVar(ftaskp->fileline()));
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
                        portEndp = createPlaceHolderVar(ftaskp->fileline()));
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

    class FourstateExpressionVisitor VL_NOT_FINAL : public VNVisitor {
    protected:
        FourstateVisitor& m_fourstateVisitor;
        AstNodeExpr* m_result = nullptr;

    private:
        bool m_noTmp = false;

        virtual AstNodeExpr* getCache(const AstNodeExpr* keyp) = 0;
        virtual void setCache(AstNodeExpr* keyp, AstNodeExpr* valuep) = 0;

    protected:
        void noTmp() { m_noTmp = true; }

        void addPrecalculation(AstNodeStmt* const nodep) {
            FourstateLogicTypePropagator{nodep};
            m_fourstateVisitor.iterate(nodep);
            m_fourstateVisitor.m_currentStmtp->addHereThisAsNext(nodep);
        }

        void getFourStateExpressionFuncRefHandler(AstNodeFTaskRef* const funcp) {
            // Its ok to use this instead of output since we only need width which is the same
            AstVar* const functionReturnVarp = VN_AS(VN_AS(funcp->taskp(), Func)->fvarp(), Var);
            AstVar* const resultValuep = m_fourstateVisitor.createTmp(functionReturnVarp);
            AstVar* const resultXzp = m_fourstateVisitor.createTmp(functionReturnVarp);
            AstNodeFTaskRef* const newCallp = funcp->cloneTree(false);
            newCallp->argsp()->unlinkFrBackWithNext()->deleteTree();
            FileLine* const flp = funcp->fileline();
            for (AstArg* argp = funcp->argsp(); argp; argp = VN_AS(argp->nextp(), Arg)) {
                if (argp->exprp()->dtypep()->isFourstate()) {
                    newCallp->addArgsp(
                        new AstArg{flp, "", getFourStateExpressionValue(argp->exprp(), false)});
                    newCallp->addArgsp(
                        new AstArg{flp, "", getFourStateExpressionXZ(argp->exprp(), false)});
                } else {
                    newCallp->addArgsp(argp->cloneTree(false));
                }
            }
            AstVarRef* const resultValueRefp = new AstVarRef{flp, resultValuep, VAccess::WRITE};
            AstVarRef* const resultXzRefp = new AstVarRef{flp, resultXzp, VAccess::WRITE};
            setFourstate(resultValueRefp, false);
            setFourstate(resultXzRefp, false);
            newCallp->addArgsp(new AstArg{flp, "", resultValueRefp});
            newCallp->addArgsp(new AstArg{flp, "", resultXzRefp});
            AstStmtExpr* const newStmtExprp = new AstStmtExpr{flp, newCallp};
            newStmtExprp->user1(1);
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
            if (!isFourstate(condp->condp())) {
                AstNodeVarRef* condVarRefp;
                if (AstNodeVarRef* const varRefp = VN_CAST(condp->condp(), NodeVarRef)) {
                    condVarRefp = varRefp->cloneTree(true);
                } else {
                    AstVar* const condTmpVarp = m_fourstateVisitor.createTmp(condp->condp());
                    AstVarRef* const condTmpVarRefp
                        = new AstVarRef{flp, condTmpVarp, VAccess::WRITE};
                    setFourstate(condTmpVarRefp, false);
                    addPrecalculation(
                        new AstAssign{flp, condTmpVarRefp, condp->condp()->cloneTree(false)});
                    condVarRefp = new AstVarRef{flp, condTmpVarp, VAccess::READ};
                }
                AstCond* const valuep
                    = new AstCond{flp, condVarRefp->cloneTree(false),
                                  getFourStateExpressionValue(condp->thenp(), false),
                                  getFourStateExpressionValue(condp->elsep(), false)};

                AstCond* const xzp = new AstCond{flp, condVarRefp,
                                                 getFourStateExpressionXZ(condp->thenp(), false),
                                                 getFourStateExpressionXZ(condp->elsep(), false)};
                pushDeletep(valuep);
                pushDeletep(xzp);
                condp->user1p(valuep);
                condp->user2p(xzp);
                return;
            }
            AstVar* const resultValueTmpVarp = m_fourstateVisitor.createTmp(condp->thenp());
            AstVar* const resultXZTmpVarp = m_fourstateVisitor.createTmp(condp->thenp());
            // Those must be here so expr is always evaluated fully in the right place
            AstNodeExpr* resultExprValuep = getFourStateExpressionValue(condp->condp());
            AstNodeExpr* resultExprXZp = getFourStateExpressionXZ(condp->condp());
            AstIf* const ifp = new AstIf{flp, resultExprXZp};
            {
                // Condition is X/Z
                StatementPlaceHolder thenPlaceholder{m_fourstateVisitor, flp};
                ifp->addThensp(thenPlaceholder.stmtp());
                TmpVarsReleaser tmpVarsReleaser{m_fourstateVisitor};
                addPrecalculation(
                    new AstAssign{flp, new AstVarRef{flp, resultValueTmpVarp, VAccess::WRITE},
                                  getFourStateExpressionValue(condp->thenp(), false)});
                addPrecalculation(
                    new AstAssign{flp, new AstVarRef{flp, resultXZTmpVarp, VAccess::WRITE},
                                  getFourStateExpressionXZ(condp->thenp(), false)});
                AstIf* const thenifp = new AstIf{
                    flp, new AstOr{
                             flp,
                             new AstXor{flp, new AstVarRef{flp, resultValueTmpVarp, VAccess::READ},
                                        getFourStateExpressionValue(condp->elsep(), false)},
                             new AstXor{flp, new AstVarRef{flp, resultXZTmpVarp, VAccess::READ},
                                        getFourStateExpressionXZ(condp->elsep(), false)}}};
                ifp->addThensp(thenifp);
                thenifp->addThensp(
                    new AstAssign{flp, new AstVarRef{flp, resultValueTmpVarp, VAccess::WRITE},
                                  createConst(condp->thenp(), true)});
                thenifp->addThensp(
                    new AstAssign{flp, new AstVarRef{flp, resultXZTmpVarp, VAccess::WRITE},
                                  createConst(condp->thenp(), true)});
            }
            {
                // Condition is 1/0
                AstIf* elseifp = new AstIf{flp, resultExprValuep};
                ifp->addElsesp(elseifp);
                {
                    // Condition is 1
                    StatementPlaceHolder thenPlaceholder{m_fourstateVisitor, flp};
                    elseifp->addThensp(thenPlaceholder.stmtp());
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
                    elseifp->addElsesp(elsePlaceholder.stmtp());
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
            m_noTmp = false;
            iterate(exprp);
            UASSERT_OBJ(m_result, exprp,
                        "Result shall always be returned - even if it is just a place holder");
            if (putIntoTmp && !m_noTmp) {
                FileLine* const flp = exprp->fileline();
                AstVar* const varp = m_fourstateVisitor.createTmp(exprp);
                AstVarRef* const varRefp = new AstVarRef{flp, varp, VAccess::WRITE};
                AstAssign* const assignp = new AstAssign{flp, varRefp, m_result};
                FourstateLogicTypePropagator{assignp};
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

        void visit(AstEqCase* const eqCasep) override {
            // (a.xz == b.xz) & (a.value == b.value)
            FileLine* const flp = eqCasep->fileline();
            m_result = new AstLogAnd{flp,
                                     new AstEq{flp, getFourStateExpressionXZ(eqCasep->lhsp()),
                                               getFourStateExpressionXZ(eqCasep->rhsp())},
                                     new AstEq{flp, getFourStateExpressionValue(eqCasep->lhsp()),
                                               getFourStateExpressionValue(eqCasep->rhsp())}};
        }

        void visit(AstNeqCase* const neqp) override {
            // |((a.value ^ b.value) | (a.xz ^ b.xz))
            FileLine* const flp = neqp->fileline();
            m_result = new AstRedOr{
                flp, new AstOr{flp,
                               new AstXor{flp, getFourStateExpressionValue(neqp->lhsp()),
                                          getFourStateExpressionValue(neqp->rhsp())},
                               new AstXor{flp, getFourStateExpressionXZ(neqp->lhsp()),
                                          getFourStateExpressionXZ(neqp->rhsp())}}};
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
                createConst(biop, true), newp};
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
            nodep->v3warn(E_UNSUPPORTED,
                          "Unsupported: Operator not supported in the four-state mode");
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
            if (!isFourstate(exprp)) return exprp->cloneTree(false);
            return get(exprp, putIntoTmp);
        }
    };

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
            FileLine* const flp = eqp->fileline();
            m_result = new AstNeq{flp,
                                  new AstOr{flp, getFourStateExpressionXZ(eqp->lhsp()),
                                            getFourStateExpressionXZ(eqp->rhsp())},
                                  new AstConst{flp, AstConst::BitFalse{}}};
        }

        void visit(AstNeq* const neqp) override {
            // a.xz | b.xz != 0
            FileLine* const flp = neqp->fileline();
            m_result = new AstNeq{flp,
                                  new AstOr{flp, getFourStateExpressionXZ(neqp->lhsp()),
                                            getFourStateExpressionXZ(neqp->rhsp())},
                                  new AstConst{flp, AstConst::BitFalse{}}};
        }

        void visit(AstEqCase* const eqp) override {
            // 0
            FileLine* const flp = eqp->fileline();
            m_result = new AstConst{flp, AstConst::BitFalse{}};
        }

        void visit(AstNeqCase* const neqp) override {
            // 0
            FileLine* const flp = neqp->fileline();
            m_result = new AstConst{flp, AstConst::BitFalse{}};
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

        void getFourStateExpressionArithmeticXZ(AstNodeBiop* const biop) {
            // (a.xz | b.xz) ? '1 : '0
            FileLine* const flp = biop->fileline();
            m_result = new AstCond{
                flp,
                new AstRedOr{flp, new AstOr{flp, getFourStateExpressionXZ(biop->lhsp()),
                                            getFourStateExpressionXZ(biop->rhsp())}},
                createConst(biop, true), createConst(biop)};
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
            nodep->v3warn(E_UNSUPPORTED,
                          "Unsupported: Operator not supported in the four-state mode");
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
            if (!isFourstate(exprp)) return createConst(exprp);
            return get(exprp, putIntoTmp);
        }
    };

    FourstateExpressionValueVisitor m_fourstateGeneratorValueVisitor;
    FourstateExpressionXZVisitor m_fourstateGeneratorXZVisitor;

    AstNodeExpr* getFourStateExpressionValue(AstNodeExpr* const exprp) {
        if (AstCReset* const cresetp = VN_CAST(exprp, CReset)) {
            // This is here instead in the visitor because CReset shall never be nested into
            // the expression and also it is a very special case
            AstCReset* const result = cresetp->cloneTree(false);
            result->dtypeSetBitSized(cresetp->width(), cresetp->dtypep()->numeric());
            FourstateLogicTypePropagator{result};
            return result;
        }
        AstNodeExpr* const result
            = m_fourstateGeneratorValueVisitor.getFourStateExpressionValue(exprp, false);
        FourstateLogicTypePropagator{result};
        return result;
    }

    AstNodeExpr* getFourStateExpressionXZ(AstNodeExpr* const exprp) {
        if (AstCReset* const cresetp = VN_CAST(exprp, CReset)) {
            // This is here instead in the visitor because CReset shall never be nested into
            // the expression and also it is a very special case
            AstCReset* const result = cresetp->cloneTree(false);
            result->dtypeSetBitSized(cresetp->width(), cresetp->dtypep()->numeric());
            FourstateLogicTypePropagator{result};
            return result;
        }
        AstNodeExpr* const result
            = m_fourstateGeneratorXZVisitor.getFourStateExpressionXZ(exprp, false);
        FourstateLogicTypePropagator{result};
        return result;
    }

    AstNodeExpr* getTruthExpr(AstNodeExpr* const exprp) {
        UASSERT_OBJ(isFourstate(exprp), exprp,
                    "This function is ment to be called on four-state expressions");
        // a.value && !a.xz
        FileLine* const flp = exprp->fileline();
        AstNodeExpr* const result
            = new AstLogAnd{flp, getFourStateExpressionValue(exprp),
                            new AstLogNot{flp, getFourStateExpressionXZ(exprp)}};
        FourstateLogicTypePropagator{result};
        return result;
    }

    AstNodeExpr* getTwoStateCast(AstNodeExpr* const exprp) {
        UASSERT_OBJ(isFourstate(exprp), exprp,
                    "This function is ment to be called on four-state expressions");
        // (a.value & (~a.xz))
        FileLine* const flp = exprp->fileline();
        AstNodeExpr* const result = new AstAnd{flp, getFourStateExpressionValue(exprp),
                                               new AstNot{flp, getFourStateExpressionXZ(exprp)}};
        FourstateLogicTypePropagator{result};
        return result;
    }

    void visit(AstNodeAssign* const nodep) override {
        VL_RESTORER(m_currentStmtp);
        m_currentStmtp = nodep;
        TmpVarsReleaser tmpVarsReleaser{*this};
        if (isFourstate(nodep->lhsp())) {
            AstNodeVarRef* const lhsVarRefp = VN_CAST(nodep->lhsp(), NodeVarRef);
            if (VL_UNLIKELY(!lhsVarRefp)) {
                nodep->v3warn(E_UNSUPPORTED,
                              "Fourstate LHS different than variable reference in assignment is "
                              "unsupported in four-state mode");
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
        } else {
            UASSERT_OBJ(!nodep->rhsp()->dtypep()->isFourstate(), nodep,
                        "Verilator makes rhsp == lhsp");
        }
        iterateChildren(nodep);
    }

    void visit(AstStmtExpr* const nodep) override {
        if (nodep->user1SetOnce()) return;
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
            newStmtExprp->user1(1);
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

    void visit(AstCell* const nodep) override {
        VL_RESTORER(m_currentPinp);
        m_currentPinp = nodep->modp()->stmtsp();
        iterateChildren(nodep);
    }

    void visit(AstPin* const nodep) override {
        AstVar* const varp = VN_CAST(m_currentPinp, Var);
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
                UASSERT_OBJ(m_currentPinp->nextp() && m_currentPinp->nextp()->nextp(), varp,
                            "Varp was not split correctly");
                m_currentPinp = m_currentPinp->nextp();
                nodep->modVarp(VN_AS(m_currentPinp, Var));
                newp->modVarp(VN_AS(m_currentPinp->nextp(), Var));
            } else if (isFourstate(exprp)) {
                AstNodeExpr* const oldp = exprp->unlinkFrBack();
                nodep->exprp(getTwoStateCast(oldp));
                oldp->deleteTree();
            }
        }
        m_currentPinp = m_currentPinp->nextp();
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
        VNRelinker relinker;
        nodep->unlinkFrBack(&relinker);
        relinker.relink(getTruthExpr(nodep));
        nodep->deleteTree();
    }

    void visit(AstNeqCase* const nodep) override {
        VNRelinker relinker;
        nodep->unlinkFrBack(&relinker);
        relinker.relink(getTruthExpr(nodep));
        nodep->deleteTree();
    }

    void visit(AstNodeFTask* const nodep) override {
        VL_RESTORER(m_currentTmpSpotp);
        VL_RESTORER(m_tmpVarps);
        VL_RESTORER(m_tmpFuncLocal);
        m_tmpFuncLocal = true;
        m_currentTmpSpotp = createPlaceHolderVar(nodep->fileline());
        if (AstNode* stmtp = nodep->stmtsp()) {
            while (VN_IS(stmtp->nextp(), Var)) stmtp = stmtp->nextp();
            stmtp->addNextHere(m_currentTmpSpotp);
        } else {
            nodep->addStmtsp(m_currentTmpSpotp);
        }
        iterateChildren(nodep);
    }

    void visit(AstVar* const nodep) override {
        if (nodep->dtypep()->isFourstate()) splitVar(nodep);
        iterateChildren(nodep);
    }

    void visit(AstNodeModule* const nodep) override {
        VL_RESTORER(m_currentTmpSpotp);
        VL_RESTORER(m_tmpVarps);
        m_currentTmpSpotp = createPlaceHolderVar(nodep->fileline());
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
