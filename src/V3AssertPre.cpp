// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Collect and print statistics
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2005-2022 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
//  Pre steps:
//      Attach clocks to each assertion
//      Substitute property references by property body (IEEE Std 1800-2012, section 16.12.1).
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3AssertPre.h"

#include "V3Ast.h"
#include "V3Global.h"
#include "V3Task.h"

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// Assert class functions

class AssertPreVisitor final : public VNVisitor {
    // Removes clocks and other pre-optimizations
    // Eventually inlines calls to sequences, properties, etc.
    // We're not parsing the tree, or anything more complicated.
private:
    // NODE STATE/TYPES
    // STATE
    // Reset each module:
    AstSenItem* m_seniDefaultp = nullptr;  // Default sensitivity (from AstDefClock)
    // Reset each assertion:
    AstSenItem* m_senip = nullptr;  // Last sensitivity
    // Reset each always:
    AstSenItem* m_seniAlwaysp = nullptr;  // Last sensitivity in always
    // Reset each assertion:
    AstNodeExpr* m_disablep = nullptr;  // Last disable

    // METHODS

    AstSenTree* newSenTree(AstNode* nodep) {
        // Create sentree based on clocked or default clock
        // Return nullptr for always
        AstSenTree* newp = nullptr;
        AstSenItem* senip = m_senip;
        if (!senip) senip = m_seniDefaultp;
        if (!senip) senip = m_seniAlwaysp;
        if (!senip) {
            nodep->v3warn(E_UNSUPPORTED, "Unsupported: Unclocked assertion");
            newp = new AstSenTree(nodep->fileline(), nullptr);
        } else {
            newp = new AstSenTree(nodep->fileline(), senip->cloneTree(true));
        }
        return newp;
    }
    void clearAssertInfo() {
        m_senip = nullptr;
        m_disablep = nullptr;
    }
    AstPropSpec* getPropertyExprp(const AstProperty* const propp) {
        // The only statements possible in AstProperty are AstPropSpec (body)
        // and AstVar (arguments).
        AstNode* propExprp = propp->stmtsp();
        while (VN_IS(propExprp, Var)) propExprp = propExprp->nextp();
        return VN_CAST(propExprp, PropSpec);
    }
    void replaceVarRefsWithExprRecurse(AstNode* const nodep, const AstVar* varp,
                                       AstNode* const exprp) {
        if (!nodep) return;
        if (const AstVarRef* varrefp = VN_CAST(nodep, VarRef)) {
            if (varp == varrefp->varp()) nodep->replaceWith(exprp->cloneTree(false));
        }
        replaceVarRefsWithExprRecurse(nodep->op1p(), varp, exprp);
        replaceVarRefsWithExprRecurse(nodep->op2p(), varp, exprp);
        replaceVarRefsWithExprRecurse(nodep->op3p(), varp, exprp);
        replaceVarRefsWithExprRecurse(nodep->op4p(), varp, exprp);
    }
    AstPropSpec* substitutePropertyCall(AstPropSpec* nodep) {
        if (AstFuncRef* const funcrefp = VN_CAST(nodep->propp(), FuncRef)) {
            if (AstProperty* const propp = VN_CAST(funcrefp->taskp(), Property)) {
                AstPropSpec* propExprp = getPropertyExprp(propp);
                // Substitute inner property call befory copying in order to not doing the same for
                // each call of outer property call.
                propExprp = substitutePropertyCall(propExprp);
                // Clone subtree after substitution. It is needed, because property might be called
                // multiple times with different arguments.
                propExprp = propExprp->cloneTree(false);
                // Substitute formal arguments with actual arguments
                const V3TaskConnects tconnects = V3Task::taskConnects(funcrefp, propp->stmtsp());
                for (const auto& tconnect : tconnects) {
                    const AstVar* const portp = tconnect.first;
                    AstArg* const argp = tconnect.second;
                    AstNode* const pinp = argp->exprp()->unlinkFrBack();
                    replaceVarRefsWithExprRecurse(propExprp, portp, pinp);
                }
                // Handle case with 2 disable iff statement (IEEE 1800-2017 16.12.1)
                if (nodep->disablep() && propExprp->disablep()) {
                    nodep->v3error("disable iff expression before property call and in its "
                                   "body is not legal");
                    pushDeletep(propExprp->disablep()->unlinkFrBack());
                }
                // If disable iff is in outer property, move it to inner
                if (nodep->disablep()) {
                    AstNodeExpr* const disablep = nodep->disablep()->unlinkFrBack();
                    propExprp->disablep(disablep);
                }

                if (nodep->sensesp() && propExprp->sensesp()) {
                    nodep->v3warn(E_UNSUPPORTED,
                                  "Unsupported: Clock event before property call and in its body");
                    pushDeletep(propExprp->sensesp()->unlinkFrBack());
                }
                // If clock event is in outer property, move it to inner
                if (nodep->sensesp()) {
                    AstSenItem* const sensesp = nodep->sensesp();
                    sensesp->unlinkFrBack();
                    propExprp->sensesp(sensesp);
                }

                // Now substitute property reference with property body
                nodep->replaceWith(propExprp);
                return propExprp;
            }
        }
        return nodep;
    }

    // VISITORS
    //========== Statements
    void visit(AstClocking* nodep) override {
        UINFO(8, "   CLOCKING" << nodep << endl);
        // Store the new default clock, reset on new module
        m_seniDefaultp = nodep->sensesp();
        // Trash it, keeping children
        if (nodep->bodysp()) {
            nodep->replaceWith(nodep->bodysp()->unlinkFrBack());
        } else {
            nodep->unlinkFrBack();
        }
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }
    void visit(AstAlways* nodep) override {
        iterateAndNextNull(nodep->sensesp());
        if (nodep->sensesp()) m_seniAlwaysp = nodep->sensesp()->sensesp();
        iterateAndNextNull(nodep->stmtsp());
        m_seniAlwaysp = nullptr;
    }

    void visit(AstNodeCoverOrAssert* nodep) override {
        if (nodep->sentreep()) return;  // Already processed
        clearAssertInfo();
        // Find Clocking's buried under nodep->exprsp
        iterateChildren(nodep);
        if (!nodep->immediate()) nodep->sentreep(newSenTree(nodep));
        clearAssertInfo();
    }
    void visit(AstFell* nodep) override {
        if (nodep->sentreep()) return;  // Already processed
        iterateChildren(nodep);
        FileLine* const fl = nodep->fileline();
        AstNodeExpr* exprp = nodep->exprp()->unlinkFrBack();
        if (exprp->width() > 1) exprp = new AstSel(fl, exprp, 0, 1);
        AstNodeExpr* const past = new AstPast(fl, exprp, nullptr);
        past->dtypeFrom(exprp);
        exprp = new AstAnd(fl, past, new AstNot(fl, exprp->cloneTree(false)));
        exprp->dtypeSetBit();
        nodep->replaceWith(exprp);
        nodep->sentreep(newSenTree(nodep));
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }
    void visit(AstPast* nodep) override {
        if (nodep->sentreep()) return;  // Already processed
        iterateChildren(nodep);
        nodep->sentreep(newSenTree(nodep));
    }
    void visit(AstRose* nodep) override {
        if (nodep->sentreep()) return;  // Already processed
        iterateChildren(nodep);
        FileLine* const fl = nodep->fileline();
        AstNodeExpr* exprp = nodep->exprp()->unlinkFrBack();
        if (exprp->width() > 1) exprp = new AstSel(fl, exprp, 0, 1);
        AstNodeExpr* const past = new AstPast(fl, exprp, nullptr);
        past->dtypeFrom(exprp);
        exprp = new AstAnd(fl, new AstNot(fl, past), exprp->cloneTree(false));
        exprp->dtypeSetBit();
        nodep->replaceWith(exprp);
        nodep->sentreep(newSenTree(nodep));
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }
    void visit(AstStable* nodep) override {
        if (nodep->sentreep()) return;  // Already processed
        iterateChildren(nodep);
        FileLine* const fl = nodep->fileline();
        AstNodeExpr* exprp = nodep->exprp()->unlinkFrBack();
        AstNodeExpr* const past = new AstPast(fl, exprp, nullptr);
        past->dtypeFrom(exprp);
        exprp = new AstEq(fl, past, exprp->cloneTree(false));
        exprp->dtypeSetBit();
        nodep->replaceWith(exprp);
        nodep->sentreep(newSenTree(nodep));
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }

    void visit(AstImplication* nodep) override {
        if (nodep->sentreep()) return;  // Already processed

        FileLine* const fl = nodep->fileline();
        AstNodeExpr* const rhsp = nodep->rhsp()->unlinkFrBack();
        AstNodeExpr* lhsp = nodep->lhsp()->unlinkFrBack();

        if (m_disablep) lhsp = new AstAnd(fl, new AstNot(fl, m_disablep), lhsp);

        AstNodeExpr* const past = new AstPast(fl, lhsp, nullptr);
        past->dtypeFrom(lhsp);
        AstNodeExpr* const exprp = new AstOr(fl, new AstNot(fl, past), rhsp);
        exprp->dtypeSetBit();
        nodep->replaceWith(exprp);
        nodep->sentreep(newSenTree(nodep));
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }

    void visit(AstPropSpec* nodep) override {
        nodep = substitutePropertyCall(nodep);
        // No need to iterate the body, once replace will get iterated
        iterateAndNextNull(nodep->sensesp());
        if (m_senip)
            nodep->v3warn(E_UNSUPPORTED, "Unsupported: Only one PSL clock allowed per assertion");
        // Block is the new expression to evaluate
        AstNodeExpr* blockp = VN_AS(nodep->propp()->unlinkFrBack(), NodeExpr);
        if (AstNodeExpr* const disablep = nodep->disablep()) {
            m_disablep = disablep->cloneTree(false);
            if (VN_IS(nodep->backp(), Cover)) {
                blockp = new AstAnd(disablep->fileline(),
                                    new AstNot(disablep->fileline(), disablep->unlinkFrBack()),
                                    blockp);
            } else {
                blockp = new AstOr(disablep->fileline(), disablep->unlinkFrBack(), blockp);
            }
        }
        // Unlink and just keep a pointer to it, convert to sentree as needed
        m_senip = nodep->sensesp();
        nodep->replaceWith(blockp);
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }
    void visit(AstNodeModule* nodep) override {
        iterateChildren(nodep);
        // Reset defaults
        m_seniDefaultp = nullptr;
    }
    void visit(AstProperty* nodep) override {
        // The body will be visited when will be substituted in place of property reference
        // (AstFuncRef)
        VL_DO_DANGLING(pushDeletep(nodep->unlinkFrBack()), nodep);
    }
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit AssertPreVisitor(AstNetlist* nodep) {
        clearAssertInfo();
        // Process
        iterate(nodep);
    }
    ~AssertPreVisitor() override = default;
};

//######################################################################
// Top Assert class

void V3AssertPre::assertPreAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    { AssertPreVisitor{nodep}; }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("assertpre", 0, dumpTree() >= 3);
}
