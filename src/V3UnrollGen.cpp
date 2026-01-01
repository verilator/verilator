// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Generate loop unrolling
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2026 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
//
// Unroll AstLoopStmts
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Const.h"
#include "V3Simulate.h"
#include "V3Unroll.h"

VL_DEFINE_DEBUG_FUNCTIONS;
//######################################################################
// Unroll AstGenFor

class UnrollGenVisitor final : public VNVisitor {
    // STATE - across all visitors
    AstVar* m_forVarp = nullptr;  // Iterator variable
    const AstNode* m_ignoreIncp = nullptr;  // Increment node to ignore
    bool m_varModeCheck = false;  // Just checking RHS assignments
    bool m_varAssignHit = false;  // Assign var hit
    bool m_forkHit = false;  // Fork hit
    std::string m_beginName;  // What name to give begin iterations

    // METHODS
    void replaceVarRef(AstNode* bodyp, AstNode* varValuep) {
        // Replace all occurances of loop variable in bodyp and next
        bodyp->foreachAndNext([this, varValuep](AstVarRef* refp) {
            if (refp->varp() == m_forVarp && refp->access().isReadOnly()) {
                AstNode* const newconstp = varValuep->cloneTree(false);
                refp->replaceWith(newconstp);
                VL_DO_DANGLING(pushDeletep(refp), refp);
            }
        });
    }

    bool cantUnroll(AstNode* nodep, const char* reason) const {
        UINFO(4, "   Can't Unroll: " << reason << " :" << nodep);
        nodep->v3warn(E_UNSUPPORTED, "Unsupported: Can't unroll generate for; " << reason);
        return false;
    }

    bool forUnrollCheck(
        AstGenFor* const nodep,
        AstNode* const initp,  // Maybe under nodep (no nextp), or standalone (ignore nextp)
        AstNodeExpr* condp,
        AstNode* const incp,  // Maybe under nodep or in bodysp
        AstNode* bodysp) {
        // To keep the IF levels low, we return as each test fails.
        UINFO(4, " FOR Check " << nodep);
        if (initp) UINFO(6, "    Init " << initp);
        if (condp) UINFO(6, "    Cond " << condp);
        if (incp) UINFO(6, "    Inc  " << incp);

        // Initial value check
        AstAssign* const initAssp = VN_CAST(initp, Assign);
        if (!initAssp) return cantUnroll(nodep, "no initial assignment");
        UASSERT_OBJ(!(initp->nextp() && initp->nextp() != nodep), nodep,
                    "initial assignment shouldn't be a list");
        if (!VN_IS(initAssp->lhsp(), VarRef)) {
            return cantUnroll(nodep, "no initial assignment to simple variable");
        }
        //
        // Condition check
        UASSERT_OBJ(!condp->nextp(), nodep, "conditional shouldn't be a list");
        //
        // Assignment of next value check
        const AstAssign* const incAssp = VN_CAST(incp, Assign);
        if (!incAssp) return cantUnroll(nodep, "no increment assignment");
        if (incAssp->nextp()) return cantUnroll(nodep, "multiple increments");

        m_forVarp = VN_AS(initAssp->lhsp(), VarRef)->varp();
        if (!m_forVarp->isGenVar()) {
            nodep->v3error("Non-genvar used in generate for: " << m_forVarp->prettyNameQ());
        }
        V3Const::constifyParamsEdit(initAssp->rhsp());  // rhsp may change

        // This check shouldn't be needed when using V3Simulate
        // however, for repeat loops, the loop variable is auto-generated
        // and the initp statements will reference a variable outside of the initp scope
        // alas, failing to simulate.
        const AstConst* const constInitp = VN_CAST(initAssp->rhsp(), Const);
        if (!constInitp) return cantUnroll(nodep, "non-constant initializer");

        //
        // Now, make sure there's no assignment to this variable in the loop
        m_varModeCheck = true;
        m_varAssignHit = false;
        m_forkHit = false;
        m_ignoreIncp = incp;
        iterateAndNextNull(bodysp);
        iterateAndNextNull(incp);
        m_varModeCheck = false;
        m_ignoreIncp = nullptr;
        if (m_varAssignHit) return cantUnroll(nodep, "genvar assigned *inside* loop");

        if (m_forkHit) return cantUnroll(nodep, "fork inside loop");

        //
        UINFO(8, "   Loop Variable: " << m_forVarp);
        UINFOTREE(9, nodep, "", "for");

        // Finally, we can do it
        if (!forUnroller(nodep, initAssp, condp, incp, bodysp)) {
            return cantUnroll(nodep, "Unable to unroll loop");
        }
        VL_DANGLING(nodep);
        // Cleanup
        return true;
    }

    bool simulateTree(AstNodeExpr* nodep, const V3Number* loopValue, const AstNode* dtypep,
                      V3Number& outNum) {
        AstNode* clonep = nodep->cloneTree(true);
        UASSERT_OBJ(clonep, nodep, "Failed to clone tree");
        if (loopValue) {
            AstConst* varValuep = new AstConst{nodep->fileline(), *loopValue};
            // Iteration requires a back, so put under temporary node
            AstBegin* tempp = new AstBegin{nodep->fileline(), "[EditWrapper]", clonep, false};
            replaceVarRef(tempp->stmtsp(), varValuep);
            clonep = tempp->stmtsp()->unlinkFrBackWithNext();
            VL_DO_CLEAR(tempp->deleteTree(), tempp = nullptr);
            VL_DO_DANGLING(pushDeletep(varValuep), varValuep);
        }
        SimulateVisitor simvis;
        simvis.mainParamEmulate(clonep);
        if (!simvis.optimizable()) {
            UINFO(4, "Unable to simulate");
            UINFOTREE(9, nodep, "", "_simtree");
            VL_DO_DANGLING(clonep->deleteTree(), clonep);
            return false;
        }
        // Fetch the result
        const V3Number* resp = simvis.fetchNumberNull(clonep);
        if (!resp) {
            UINFO(3, "No number returned from simulation");
            VL_DO_DANGLING(clonep->deleteTree(), clonep);
            return false;
        }
        // Patch up datatype
        if (dtypep) {
            AstConst new_con{clonep->fileline(), *resp};
            new_con.dtypeFrom(dtypep);
            outNum = new_con.num();
            outNum.isSigned(dtypep->isSigned());
            VL_DO_DANGLING(clonep->deleteTree(), clonep);
            return true;
        }
        outNum = *resp;
        VL_DO_DANGLING(clonep->deleteTree(), clonep);
        return true;
    }

    bool forUnroller(AstGenFor* nodep, AstAssign* initp, AstNodeExpr* condp, AstNode* incp,
                     AstNode* bodysp) {
        UINFO(9, "forUnroller " << nodep);
        V3Number loopValue{nodep};
        if (!simulateTree(initp->rhsp(), nullptr, initp, loopValue)) {  //
            return false;
        }
        AstNode* stmtsp = nullptr;
        if (initp) {
            initp->unlinkFrBack();  // Always a single statement; nextp() may be nodep
            // Don't add to list, we do it once, and setting loop index isn't
            // needed if we have > 1 loop, as we're constant propagating it
            pushDeletep(initp);  // Always cloned below.
        }
        if (bodysp) {
            bodysp->unlinkFrBackWithNext();
            stmtsp = AstNode::addNext(stmtsp, bodysp);  // Maybe null if no body
        }
        // Mark variable to disable some later warnings
        m_forVarp->usedLoopIdx(true);

        AstNode* newbodysp = nullptr;
        if (stmtsp) {
            pushDeletep(stmtsp);  // Always cloned below.
            size_t iterCount = 0;
            const size_t iterLimit = v3Global.opt.unrollLimit();
            while (true) {
                UINFO(8, "      Looping " << loopValue);
                V3Number res{nodep};
                if (!simulateTree(condp, &loopValue, nullptr, res)) {
                    nodep->v3error("Loop unrolling failed.");
                    return false;
                }
                if (!res.isEqOne()) {
                    break;  // Done with the loop
                } else {
                    if (++iterCount > iterLimit) {
                        nodep->v3error("Unrolling generate loop took too long; probably this is "
                                       "an infinite loop, otherwise set '--unroll-limit' above "
                                       << iterLimit);
                        break;
                    }

                    // Replace iterator values with constant
                    AstNode* oneloopp = stmtsp->cloneTree(true);
                    AstConst* varValuep = new AstConst{nodep->fileline(), loopValue};
                    if (oneloopp) {
                        // Iteration requires a back, so put under temporary node
                        AstBegin* const tempp
                            = new AstBegin{oneloopp->fileline(), "[EditWrapper]", oneloopp, false};
                        replaceVarRef(tempp->stmtsp(), varValuep);
                        oneloopp = tempp->stmtsp()->unlinkFrBackWithNext();
                        VL_DO_DANGLING(tempp->deleteTree(), tempp);
                    }
                    const string index = AstNode::encodeNumber(varValuep->toSInt());
                    const string nname = m_beginName + "__BRA__" + index + "__KET__";
                    oneloopp = new AstGenBlock{oneloopp->fileline(), nname, oneloopp, false};
                    VL_DO_DANGLING(pushDeletep(varValuep), varValuep);
                    if (newbodysp) {
                        newbodysp->addNext(oneloopp);
                    } else {
                        newbodysp = oneloopp;
                    }

                    // loopValue += valInc
                    const AstAssign* const incpass = VN_AS(incp, Assign);
                    V3Number newLoopValue{nodep};
                    if (!simulateTree(incpass->rhsp(), &loopValue, incpass, newLoopValue)) {
                        nodep->v3error("Loop unrolling failed");
                        return false;
                    }
                    loopValue.opAssign(newLoopValue);
                }
            }
        }
        if (!newbodysp) {  // initp might have effects after the loop
            if (initp) {  // GENFOR(ASSIGN(...)) need to move under a new Initial
                newbodysp = new AstInitial{initp->fileline(), initp->cloneTree(true)};
            } else {
                newbodysp = initp ? initp->cloneTree(true) : nullptr;
            }
        }
        // Replace the FOR()
        if (newbodysp) {
            nodep->replaceWith(newbodysp);
        } else {
            nodep->unlinkFrBack();
        }
        if (newbodysp) UINFOTREE(9, newbodysp, "", "_new");
        return true;
    }

    // VISITORS
    void visit(AstVarRef* nodep) override {
        if (m_varModeCheck && nodep->varp() == m_forVarp && nodep->access().isWriteOrRW()) {
            UINFO(8, "   Itervar assigned to: " << nodep);
            m_varAssignHit = true;
        }
    }

    void visit(AstNode* nodep) override {
        if (m_varModeCheck && nodep == m_ignoreIncp) {
            // Ignore subtree that is the increment
        } else {
            iterateChildren(nodep);
        }
    }

public:
    // CONSTRUCTORS
    UnrollGenVisitor() = default;

    void unroll(AstGenFor* nodep, const std::string& beginName) {
        m_forVarp = nullptr;  // Iterator variable
        m_ignoreIncp = nullptr;  // Increment node to ignore
        m_varModeCheck = false;  // Just checking RHS assignments
        m_varAssignHit = false;  // Assign var hit
        m_forkHit = false;  // Fork hit
        m_beginName = beginName;

        // Constify before unroll call, as it may change what is underneath.
        if (nodep->initsp()) V3Const::constifyEdit(nodep->initsp());  // initsp may change
        if (nodep->condp()) V3Const::constifyEdit(nodep->condp());  // condp may change
        if (nodep->incsp()) V3Const::constifyEdit(nodep->incsp());  // incsp may change
        if (nodep->condp()->isZero()) {
            // We don't need to do any loops.  Remove the GenFor,
            // Genvar's don't care about any initial assignments.
            //
            // Note normal For's can't do exactly this deletion, as
            // we'd need to initialize the variable to the initial
            // condition, but they'll become while's which can be
            // deleted by V3Const.
            VL_DO_DANGLING(pushDeletep(nodep->unlinkFrBack()), nodep);
        } else if (forUnrollCheck(nodep, nodep->initsp(), nodep->condp(), nodep->incsp(),
                                  nodep->itemsp())) {
            VL_DO_DANGLING(pushDeletep(nodep), nodep);  // Did replacement
        } else {
            nodep->v3error("For loop doesn't have genvar index, or is malformed");
            // We will die, do it gracefully
            VL_DO_DANGLING(pushDeletep(nodep->unlinkFrBack()), nodep);
        }
    }
};

//######################################################################
// GenForUnroller members

GenForUnroller::GenForUnroller()
    : m_unrollerp{new UnrollGenVisitor{}} {}
GenForUnroller::~GenForUnroller() { VL_DO_DANGLING(delete m_unrollerp, m_unrollerp); }
void GenForUnroller::unroll(AstGenFor* nodep, const std::string& beginName) {
    m_unrollerp->unroll(nodep, beginName);
}
