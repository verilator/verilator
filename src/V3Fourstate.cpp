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

template <typename T, typename = void>
struct ReducerTrait final : std::false_type {};
template <typename T>
struct ReducerTrait<
    T, std::enable_if_t<std::is_same<decltype(std::declval<T>()(std::declval<FourStatePair>(),
                                                                std::declval<FourStatePair>())),
                                     FourStatePair>::value>>
    final : std::true_type {};

class FourstateVisitor final : public VNVisitor {
    const VNUser1InUse m_user1InUse;
    const VNUser2InUse m_user2InUse;
    // Node status
    // AstVar*::user1p      ->  AstVar*.        Where is value part of splitted variable - xz shall
    //                                          be nexp() of user1p
    // AstNodeExpr::user1p  ->  AstNodeExpr*.   Expression evaluating value component
    // AstStmtExpr::user1   ->  bool.           Whether visited
    // AstNodeExpr::user2p  ->  AstNodeExpr*.   Expression evaluating xz component

    V3UniqueNames m_tmpNames;

    AstVar* m_currentTmpSpotp = nullptr;  // Node after which put AstVar* for temporary variable
    bool m_tmpFuncLocal = false;
    AstNodeStmt* m_currentStmtp = nullptr;  // Current statement
    AstNode* m_currentFTaskArgp
        = nullptr;  // Current argument variable of FTaskRef - if not variable it is meaningless
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

    struct TmpVarsReleaser final {
        FourstateVisitor& visitor;
        ~TmpVarsReleaser() {
            for (AstVar* const varp : visitor.m_tmpVarpsInUse) {
                visitor.m_tmpVarps[varp->dtypep()->numeric().isSigned() ? 1 : 0][varp->width()]
                    .push_back(varp);
            }
            visitor.m_tmpVarpsInUse.clear();
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
            newXzp->valuep(getFourStateExpressionXZ(valuep, false));
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
            newValuep->valuep(getFourStateExpressionValue(valuep, false));
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

    AstNodeExpr* getFourStateExpressionAndValue(AstAnd* const andp) {
        // (a.value | a.xz) & (b.value | b.xz)
        FileLine* const flp = andp->fileline();
        return new AstAnd{flp,
                          new AstOr{flp, getFourStateExpressionValue(andp->lhsp()),
                                    getFourStateExpressionXZ(andp->lhsp())},
                          new AstOr{flp, getFourStateExpressionValue(andp->rhsp()),
                                    getFourStateExpressionXZ(andp->rhsp())}};
    }

    AstNodeExpr* getFourStateExpressionAndXZ(AstAnd* const andp) {
        // (a.value & b.xz) | (b.value & a.xz) | (a.xz & b.xz)
        FileLine* const flp = andp->fileline();
        return new AstOr{flp,
                         new AstOr{flp,
                                   new AstAnd{flp, getFourStateExpressionValue(andp->lhsp()),
                                              getFourStateExpressionXZ(andp->rhsp())},
                                   new AstAnd{flp, getFourStateExpressionValue(andp->rhsp()),
                                              getFourStateExpressionXZ(andp->lhsp())}},
                         new AstAnd{flp, getFourStateExpressionXZ(andp->lhsp()),
                                    getFourStateExpressionXZ(andp->rhsp())}};
    }

    AstNodeExpr* getFourStateExpressionOrValue(AstOr* const orp) {
        // a.value | b.value | a.xz | b.xz
        FileLine* const flp = orp->fileline();
        return new AstOr{flp,
                         new AstOr{flp, getFourStateExpressionValue(orp->lhsp()),
                                   getFourStateExpressionValue(orp->rhsp())},
                         new AstOr{flp, getFourStateExpressionXZ(orp->lhsp()),
                                   getFourStateExpressionXZ(orp->rhsp())}};
    }

    AstNodeExpr* getFourStateExpressionOrXZ(AstOr* const orp) {
        // (a.xz & b.xz) | (a.xz & ~b.value) | (b.xz & ~a.value)
        FileLine* const flp = orp->fileline();
        return new AstOr{
            flp,
            new AstOr{flp,
                      new AstAnd{flp, getFourStateExpressionXZ(orp->lhsp()),
                                 getFourStateExpressionXZ(orp->rhsp())},
                      new AstAnd{flp, getFourStateExpressionXZ(orp->lhsp()),
                                 new AstNot{flp, getFourStateExpressionValue(orp->rhsp())}}},
            new AstAnd{flp, getFourStateExpressionXZ(orp->rhsp()),
                       new AstNot{flp, getFourStateExpressionValue(orp->lhsp())}}};
    }

    AstNodeExpr* getFourStateExpressionXorValue(AstXor* const xorp) {
        // (a.value ^ b.value) | a.xz | b.xz
        FileLine* const flp = xorp->fileline();
        return new AstOr{flp,
                         new AstXor{flp, getFourStateExpressionValue(xorp->lhsp(), false),
                                    getFourStateExpressionValue(xorp->rhsp(), false)},
                         getFourStateExpressionXorXZ(xorp)};
    }

    AstNodeExpr* getFourStateExpressionXorXZ(AstXor* const xorp) {
        // a.xz | b.xz
        FileLine* const flp = xorp->fileline();
        return new AstOr{flp, getFourStateExpressionXZ(xorp->lhsp()),
                         getFourStateExpressionXZ(xorp->rhsp())};
    }

    AstNodeExpr* getFourStateExpressionNotValue(AstNot* const notp) {
        // ~a.value | a.xz
        FileLine* const flp = notp->fileline();
        return new AstOr{flp, new AstNot{flp, getFourStateExpressionValue(notp->lhsp())},
                         getFourStateExpressionXZ(notp->lhsp())};
    }

    AstNodeExpr* getFourStateExpressionNotXZ(AstNot* const notp) {
        // a.xz
        return getFourStateExpressionXZ(notp->lhsp());
    }

    AstNodeExpr* getFourStateExpressionEqValue(AstEq* const eqp) {
        // (a.xz | b.xz != 0) | (a.value == b.value )
        FileLine* const flp = eqp->fileline();
        return new AstOr{flp, getFourStateExpressionEqXZ(eqp),
                         new AstEq{flp, getFourStateExpressionValue(eqp->lhsp()),
                                   getFourStateExpressionValue(eqp->rhsp())}};
    }

    AstNodeExpr* getFourStateExpressionEqXZ(AstEq* const eqp) {
        // a.xz | b.xz != 0
        FileLine* const flp = eqp->fileline();
        return new AstNeq{flp,
                          new AstOr{flp, getFourStateExpressionXZ(eqp->lhsp()),
                                    getFourStateExpressionXZ(eqp->rhsp())},
                          new AstConst{flp, AstConst::BitFalse{}}};
    }

    AstNodeExpr* getFourStateExpressionNeqValue(AstNeq* const neqp) {
        // (a.xz | b.xz != 0) | (a.value != b.value )
        FileLine* const flp = neqp->fileline();
        return new AstOr{flp, getFourStateExpressionNeqXZ(neqp),
                         new AstNeq{flp, getFourStateExpressionValue(neqp->lhsp()),
                                    getFourStateExpressionValue(neqp->rhsp())}};
    }

    AstNodeExpr* getFourStateExpressionNeqXZ(AstNeq* const neqp) {
        // a.xz | b.xz != 0
        FileLine* const flp = neqp->fileline();
        return new AstNeq{flp,
                          new AstOr{flp, getFourStateExpressionXZ(neqp->lhsp()),
                                    getFourStateExpressionXZ(neqp->rhsp())},
                          new AstConst{flp, AstConst::BitFalse{}}};
    }

    AstNodeExpr* getFourStateExpressionEqCaseValue(AstEqCase* const eqCasep) {
        // (a.xz == b.xz) & (a.value == b.value)
        FileLine* const flp = eqCasep->fileline();
        return new AstLogAnd{flp,
                             new AstEq{flp, getFourStateExpressionXZ(eqCasep->lhsp()),
                                       getFourStateExpressionXZ(eqCasep->rhsp())},
                             new AstEq{flp, getFourStateExpressionValue(eqCasep->lhsp()),
                                       getFourStateExpressionValue(eqCasep->rhsp())}};
    }

    AstNodeExpr* getFourStateExpressionEqCaseXZ(AstEqCase* const eqp) {
        // 0
        FileLine* const flp = eqp->fileline();
        return new AstConst{flp, AstConst::BitFalse{}};
    }

    AstNodeExpr* getFourStateExpressionNeqCaseValue(AstNeqCase* const neqp) {
        // |((a.value ^ b.value) | (a.xz ^ b.xz))
        FileLine* const flp = neqp->fileline();
        return new AstRedOr{flp,
                            new AstOr{flp,
                                      new AstXor{flp, getFourStateExpressionValue(neqp->lhsp()),
                                                 getFourStateExpressionValue(neqp->rhsp())},
                                      new AstXor{flp, getFourStateExpressionXZ(neqp->lhsp()),
                                                 getFourStateExpressionXZ(neqp->rhsp())}}};
    }

    AstNodeExpr* getFourStateExpressionNeqCaseXZ(AstNeqCase* const neqp) {
        // 0
        FileLine* const flp = neqp->fileline();
        return new AstConst{flp, AstConst::BitFalse{}};
    }

    AstNodeExpr* getFourStateExpressionExtendValue(AstExtend* const extendp) {
        FileLine* const flp = extendp->fileline();
        return new AstExtend{flp, getFourStateExpressionValue(extendp->lhsp(), false)};
    }

    AstNodeExpr* getFourStateExpressionExtendXZ(AstExtend* const extendp) {
        FileLine* const flp = extendp->fileline();
        return new AstExtend{flp, getFourStateExpressionXZ(extendp->lhsp(), false)};
    }

    AstNodeExpr* getFourStateExpressionExtendSValue(AstExtendS* const extendsp) {
        FileLine* const flp = extendsp->fileline();
        return new AstExtendS{flp, getFourStateExpressionValue(extendsp->lhsp(), false)};
    }

    AstNodeExpr* getFourStateExpressionExtendSXZ(AstExtendS* const extendsp) {
        FileLine* const flp = extendsp->fileline();
        return new AstExtendS{flp, getFourStateExpressionXZ(extendsp->lhsp(), false)};
    }

    void getFourStateExpressionFuncRefHandler(AstNodeFTaskRef* const funcp) {
        // Its ok to use this instead of output since we only need width which is the same
        AstVar* const functionReturnVarp = VN_AS(VN_AS(funcp->taskp(), Func)->fvarp(), Var);
        AstVar* const resultValuep = createTmp(functionReturnVarp);
        AstVar* const resultXzp = createTmp(functionReturnVarp);
        AstNodeFTaskRef* const newCallp = funcp->cloneTree(false);
        newCallp->argsp()->unlinkFrBackWithNext()->deleteTree();
        FileLine* const flp = funcp->fileline();
        for (AstArg* argp = funcp->argsp(); argp; argp = VN_AS(argp->nextp(), Arg)) {
            if (argp->exprp()->dtypep()->isFourstate()) {
                newCallp->addArgsp(
                    new AstArg{flp, "", getFourStateExpressionValue(argp->exprp())});
                newCallp->addArgsp(new AstArg{flp, "", getFourStateExpressionXZ(argp->exprp())});
            } else {
                newCallp->addArgsp(argp->cloneTree(false));
            }
        }
        newCallp->addArgsp(new AstArg{flp, "", new AstVarRef{flp, resultValuep, VAccess::WRITE}});
        newCallp->addArgsp(new AstArg{flp, "", new AstVarRef{flp, resultXzp, VAccess::WRITE}});
        AstStmtExpr* const newStmtExprp = new AstStmtExpr{flp, newCallp};
        newStmtExprp->user1(1);
        m_currentStmtp->addHereThisAsNext(newStmtExprp);
        AstVarRef* const varRefValuep = new AstVarRef{flp, resultValuep, VAccess::READ};
        AstVarRef* const varRefXzp = new AstVarRef{flp, resultXzp, VAccess::READ};
        pushDeletep(varRefValuep);
        pushDeletep(varRefXzp);
        funcp->user1p(varRefValuep);
        funcp->user2p(varRefXzp);
    }

    AstNodeExpr* getFourStateExpressionValue(AstNodeExpr* const exprp, bool putIntoTmp = true) {
        // VN_AS is expected to be here (instead of VN_CAST)
        if (AstNodeExpr* result = VN_AS(exprp->user1p(), NodeExpr)) {
            return result->cloneTree(false);
        }
        AstNodeExpr* result;
        if (AstNodeVarRef* const varRefp = VN_CAST(exprp, NodeVarRef)) {
            putIntoTmp = false;
            if (varRefp->varp()->dtypep()->isFourstate()) {
                splitVar(varRefp->varp());
                AstNodeVarRef* const newp = varRefp->cloneTree(false);
                newp->varp(getSplittedValue(varRefp->varp()));
                newp->dtypeSetBitSized(varRefp->varp()->width(),
                                       varRefp->varp()->dtypep()->numeric());
                result = newp;
            } else {
                AstNodeVarRef* const newp = varRefp->cloneTree(false);
                varRefp->dtypeSetBitSized(varRefp->width(), varRefp->dtypep()->numeric());
                result = newp;
            }
        } else if (AstConst* const constp = VN_CAST(exprp, Const)) {
            putIntoTmp = false;
            AstConst* const newp = constp->cloneTree(false);
            newp->num().opBitsOneX(constp->num());
            newp->dtypeSetBitUnsized(newp->width(), newp->dtypep()->widthMin(),
                                     newp->dtypep()->numeric());
            result = newp;
        } else if (AstAnd* const andp = VN_CAST(exprp, And)) {
            result = getFourStateExpressionAndValue(andp);
        } else if (AstOr* const orp = VN_CAST(exprp, Or)) {
            result = getFourStateExpressionOrValue(orp);
        } else if (AstXor* const xorp = VN_CAST(exprp, Xor)) {
            result = getFourStateExpressionXorValue(xorp);
        } else if (AstNot* const notp = VN_CAST(exprp, Not)) {
            result = getFourStateExpressionNotValue(notp);
        } else if (AstEq* const eqp = VN_CAST(exprp, Eq)) {
            result = getFourStateExpressionEqValue(eqp);
        } else if (AstNeq* const neqp = VN_CAST(exprp, Neq)) {
            result = getFourStateExpressionNeqValue(neqp);
        } else if (AstEqCase* const eqCasep = VN_CAST(exprp, EqCase)) {
            result = getFourStateExpressionEqCaseValue(eqCasep);
        } else if (AstNeqCase* const neqCasep = VN_CAST(exprp, NeqCase)) {
            result = getFourStateExpressionNeqCaseValue(neqCasep);
        } else if (AstExtend* const extendp = VN_CAST(exprp, Extend)) {
            result = getFourStateExpressionExtendValue(extendp);
        } else if (AstExtendS* const extendsp = VN_CAST(exprp, ExtendS)) {
            result = getFourStateExpressionExtendSValue(extendsp);
        } else if (AstNodeFTaskRef* const funcp = VN_CAST(exprp, NodeFTaskRef)) {
            // Everything is handled by the function
            getFourStateExpressionFuncRefHandler(funcp);
            return VN_AS(exprp->user1p(), NodeExpr)->cloneTree(false);
        } else if (AstCReset* const cresetp = VN_CAST(exprp, CReset)) {
            result = cresetp->cloneTree(false);
        } else {
            exprp->v3warn(E_UNSUPPORTED,
                          "Unsupported: Operator not supported in the four-state mode");
            // Workaround to avaoid Internal errors
            result = new AstConst{exprp->fileline(), AstConst::BitFalse{}};
        }
        if (putIntoTmp) {
            FileLine* const flp = exprp->fileline();
            AstVar* const varp = createTmp(exprp);
            m_currentStmtp->addHereThisAsNext(
                new AstAssign{flp, new AstVarRef{flp, varp, VAccess::WRITE}, result});
            result = new AstVarRef{flp, varp, VAccess::READ};
        }
        exprp->user1p(result);
        return result;
    }

    AstNodeExpr* getFourStateExpressionXZ(AstNodeExpr* const exprp, bool putIntoTmp = true) {
        // VN_AS is expected to be here (instead of VN_CAST)
        if (AstNodeExpr* result = VN_AS(exprp->user2p(), NodeExpr)) {
            return result->cloneTree(false);
        }
        AstNodeExpr* result;
        if (AstNodeVarRef* const varRefp = VN_CAST(exprp, NodeVarRef)) {
            putIntoTmp = false;
            if (varRefp->varp()->dtypep()->isFourstate()) {
                splitVar(varRefp->varp());
                AstNodeVarRef* const newp = varRefp->cloneTree(false);
                newp->varp(getSplittedXZ(varRefp->varp()));
                newp->dtypeSetBitSized(varRefp->varp()->width(),
                                       varRefp->varp()->dtypep()->numeric());
                result = newp;
            } else {
                AstConst* const newp = new AstConst{varRefp->fileline(), AstConst::WidthedValue{},
                                                    varRefp->width(), 0};
                result = newp;
            }
        } else if (AstConst* const constp = VN_CAST(exprp, Const)) {
            putIntoTmp = false;
            AstConst* const newp = constp->cloneTree(false);
            newp->num().opBitsXZ(constp->num());
            newp->dtypeSetBitSized(newp->width(), newp->dtypep()->numeric());
            result = newp;
        } else if (AstAnd* const andp = VN_CAST(exprp, And)) {
            result = getFourStateExpressionAndXZ(andp);
        } else if (AstOr* const orp = VN_CAST(exprp, Or)) {
            result = getFourStateExpressionOrXZ(orp);
        } else if (AstXor* const xorp = VN_CAST(exprp, Xor)) {
            result = getFourStateExpressionXorXZ(xorp);
        } else if (AstNot* const notp = VN_CAST(exprp, Not)) {
            result = getFourStateExpressionNotXZ(notp);
        } else if (AstEq* const eqp = VN_CAST(exprp, Eq)) {
            result = getFourStateExpressionEqXZ(eqp);
        } else if (AstNeq* const neqp = VN_CAST(exprp, Neq)) {
            result = getFourStateExpressionNeqXZ(neqp);
        } else if (AstEqCase* const eqCasep = VN_CAST(exprp, EqCase)) {
            result = getFourStateExpressionEqCaseXZ(eqCasep);
        } else if (AstNeqCase* const neqCasep = VN_CAST(exprp, NeqCase)) {
            result = getFourStateExpressionNeqCaseXZ(neqCasep);
        } else if (AstExtend* const extendp = VN_CAST(exprp, Extend)) {
            result = getFourStateExpressionExtendXZ(extendp);
        } else if (AstExtendS* const extendsp = VN_CAST(exprp, ExtendS)) {
            result = getFourStateExpressionExtendSXZ(extendsp);
        } else if (AstNodeFTaskRef* const funcp = VN_CAST(exprp, NodeFTaskRef)) {
            // Everything is handled by the function
            getFourStateExpressionFuncRefHandler(funcp);
            return VN_AS(exprp->user2p(), NodeExpr)->cloneTree(false);
        } else if (AstCReset* const cresetp = VN_CAST(exprp, CReset)) {
            result = cresetp->cloneTree(false);
        } else {
            exprp->v3warn(E_UNSUPPORTED,
                          "Unsupported: Operator not supported in the four-state mode");
            // Workaround to avaoid Internal errors
            result = new AstConst{exprp->fileline(), AstConst::BitFalse{}};
        }
        if (putIntoTmp) {
            FileLine* const flp = exprp->fileline();
            AstVar* const varp = createTmp(exprp);
            m_currentStmtp->addHereThisAsNext(
                new AstAssign{flp, new AstVarRef{flp, varp, VAccess::WRITE}, result});
            result = new AstVarRef{flp, varp, VAccess::READ};
        }
        exprp->user2p(result);
        return result;
    }

    AstNodeExpr* getTruthExpr(AstNodeExpr* const exprp) {
        // a.value && !a.xz
        FileLine* const flp = exprp->fileline();
        return new AstLogAnd{flp, getFourStateExpressionValue(exprp, false),
                             new AstLogNot{flp, getFourStateExpressionXZ(exprp, false)}};
    }

    AstNodeExpr* getTwoStateCast(AstNodeExpr* const exprp) {
        // (a.value & (~a.xz))
        FileLine* const flp = exprp->fileline();
        return new AstAnd{flp, getFourStateExpressionValue(exprp, false),
                          new AstNot{flp, getFourStateExpressionXZ(exprp, false)}};
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

    void visit(AstNodeAssign* const nodep) override {
        VL_RESTORER(m_currentStmtp);
        TmpVarsReleaser tmpVarsReleaser{*this};
        m_currentStmtp = nodep;
        if (nodep->dtypep()->isFourstate()) {
            AstNodeVarRef* const lhsVarRefp = VN_CAST(nodep->lhsp(), NodeVarRef);
            if (VL_UNLIKELY(!lhsVarRefp)) {
                nodep->v3warn(E_UNSUPPORTED,
                              "LHS different than variable reference in assignment is "
                              "unsupported in four-state mode");
                return;
            }
            AstNodeAssign* const assignXZp = nodep->cloneTree(false);
            {
                assignXZp->lhsp()->unlinkFrBack()->deleteTree();
                assignXZp->rhsp()->unlinkFrBack()->deleteTree();
                AstNodeExpr* const newLhsp = getFourStateExpressionXZ(lhsVarRefp, false);
                assignXZp->lhsp(newLhsp);
                assignXZp->rhsp(getFourStateExpressionXZ(nodep->rhsp(), false));
                assignXZp->dtypeFrom(newLhsp);
                nodep->addNextHere(assignXZp);
            }
            {
                AstNodeExpr* const newRhsp = getFourStateExpressionValue(nodep->rhsp(), false);
                AstNodeExpr* const newLhsp = getFourStateExpressionValue(lhsVarRefp, false);
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
        }
        iterateChildren(nodep);
    }

    void visit(AstStmtExpr* const nodep) override {
        if (nodep->user1SetOnce()) return;
        VL_RESTORER(m_currentStmtp);
        TmpVarsReleaser tmpVarsReleaser{*this};
        m_currentStmtp = nodep;
        auto isFourState = [nodep]() -> bool {
            if (nodep->exprp()->dtypep()->isFourstate()) return true;
            if (AstNodeFTaskRef* const taskRefp = VN_CAST(nodep->exprp(), NodeFTaskRef)) {
                AstNodeDType* const dtypep = taskRefp->taskp()->dtypep();
                return dtypep && dtypep->isFourstate();
            }
            return false;
        };
        if (isFourState()) {
            AstNodeExpr* const exprp = nodep->exprp()->unlinkFrBack();
            nodep->exprp(getFourStateExpressionValue(exprp, false));
            AstNodeExpr* const newXzp = getFourStateExpressionXZ(exprp, false);
            iterateChildren(newXzp);
            AstStmtExpr* const newStmtExprp = new AstStmtExpr{nodep->fileline(), newXzp};
            newStmtExprp->user1(1);
            nodep->addNextHere(newStmtExprp);
            exprp->deleteTree();
        }
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
        TmpVarsReleaser tmpVarsReleaser{*this};
        if (varp->dtypep()->isFourstate()) {
            nodep->addNextHere(new AstArg{nodep->fileline(), "",
                                          getFourStateExpressionXZ(nodep->exprp(), false)});
            AstNodeExpr* const oldp = nodep->exprp()->unlinkFrBack();
            nodep->exprp(getFourStateExpressionValue(oldp, false));
            oldp->deleteTree();
            splitVar(varp);  // Ensure that variable is splitted
            UASSERT_OBJ(m_currentFTaskArgp->nextp() && m_currentFTaskArgp->nextp()->nextp(), varp,
                        "Varp was not split correctly");
            m_currentFTaskArgp = m_currentFTaskArgp->nextp();
        }
        m_currentFTaskArgp = m_currentFTaskArgp->nextp();
        iterateChildren(nodep);
    }

    void visit(AstCond* const nodep) override {
        if (nodep->condp()->dtypep()->isFourstate()) {
            AstNodeExpr* const condp = nodep->condp()->unlinkFrBack();
            nodep->condp(getTruthExpr(condp));
            condp->deleteTree();
        }
        iterateChildren(nodep);
    }

    void visit(AstEqCase* const nodep) override {
        VNRelinker relinker;
        nodep->unlinkFrBack(&relinker);
        if (!nodep->lhsp()->dtypep()->isFourstate() && !nodep->rhsp()->dtypep()->isFourstate()) {
            AstEq* const newp = new AstEq{nodep->fileline(), nodep->lhsp()->unlinkFrBack(),
                                          nodep->rhsp()->unlinkFrBack()};
            relinker.relink(newp);
            iterateChildren(newp);
        } else {
            relinker.relink(getFourStateExpressionValue(nodep, false));
        }
        nodep->deleteTree();
    }

    void visit(AstNeqCase* const nodep) override {
        VNRelinker relinker;
        nodep->unlinkFrBack(&relinker);
        if (!nodep->lhsp()->dtypep()->isFourstate() && !nodep->rhsp()->dtypep()->isFourstate()) {
            AstNeq* const newp = new AstNeq{nodep->fileline(), nodep->lhsp()->unlinkFrBack(),
                                            nodep->rhsp()->unlinkFrBack()};
            relinker.relink(newp);
            iterateChildren(newp);
        } else {
            relinker.relink(getFourStateExpressionValue(nodep, false));
        }
        nodep->deleteTree();
    }

    void visit(AstEq* const nodep) override {
        if (nodep->lhsp()->dtypep()->isFourstate() || nodep->rhsp()->dtypep()->isFourstate()) {
            VNRelinker relinker;
            nodep->unlinkFrBack(&relinker);
            relinker.relink(getTruthExpr(nodep));
            nodep->deleteTree();
        } else {
            iterateChildren(nodep);
        }
    }

    void visit(AstNeq* const nodep) override {
        if (nodep->lhsp()->dtypep()->isFourstate() || nodep->rhsp()->dtypep()->isFourstate()) {
            VNRelinker relinker;
            nodep->unlinkFrBack(&relinker);
            relinker.relink(getTruthExpr(nodep));
            nodep->deleteTree();
        } else {
            iterateChildren(nodep);
        }
    }

    void handleTwoStateSubExprOperand(AstNodeExpr* const exprp) {
        if (exprp->dtypep()->isFourstate()) {
            VNRelinker relinker;
            AstNodeExpr* oldp = exprp->unlinkFrBack(&relinker);
            relinker.relink(getTwoStateCast(oldp));
            oldp->deleteTree();
        } else {
            iterate(exprp);
        }
    }

    void visit(AstNodeUniop* const nodep) override {
        UASSERT_OBJ(!nodep->dtypep()->isFourstate(), nodep,
                    "This visitor shall only be reached for two-state expressions");
        handleTwoStateSubExprOperand(nodep->lhsp());
    }

    void visit(AstNodeBiop* const nodep) override {
        UASSERT_OBJ(!nodep->dtypep()->isFourstate(), nodep,
                    "This visitor shall only be reached for two-state expressions");
        handleTwoStateSubExprOperand(nodep->lhsp());
        handleTwoStateSubExprOperand(nodep->rhsp());
    }

    void visit(AstNodeTriop* const nodep) override {
        UASSERT_OBJ(!nodep->dtypep()->isFourstate(), nodep,
                    "This visitor shall only be reached for two-state expressions");
        handleTwoStateSubExprOperand(nodep->lhsp());
        handleTwoStateSubExprOperand(nodep->rhsp());
        handleTwoStateSubExprOperand(nodep->thsp());
    }

    void visit(AstNodeIf* const nodep) override {
        VL_RESTORER(m_currentStmtp);
        m_currentStmtp = nodep;
        {
            TmpVarsReleaser tmpVarsReleaser{*this};
            if (nodep->condp()->dtypep()->isFourstate()) {
                AstNodeExpr* const condp = nodep->condp()->unlinkFrBack();
                nodep->condp(getTruthExpr(condp));
                condp->deleteTree();
            }
            iterateAndNextNull(nodep->condp());
        }
        iterateAndNextNull(nodep->thensp());
        iterateAndNextNull(nodep->elsesp());
    }

    void visit(AstLoopTest* const nodep) override {
        VL_RESTORER(m_currentStmtp);
        m_currentStmtp = nodep;
        if (nodep->condp()->dtypep()->isFourstate()) {
            AstNodeExpr* const condp = nodep->condp()->unlinkFrBack();
            nodep->condp(getTruthExpr(condp));
            condp->deleteTree();
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
        : m_tmpNames{"__VfourStateTmp"} {
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

void V3Fourstate::fourstateAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ":");
    { FourstateVisitor{nodep}; }
    V3Global::dumpCheckGlobalTree("fourstate", 0, dumpTreeEitherLevel() >= 6);
}
