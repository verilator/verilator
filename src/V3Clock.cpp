// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Clocking POS/NEGEDGE insertion
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2020 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
// V3Clock's Transformations:
//
// Top Scope:
//   Check created ACTIVEs
//      Compress adjacent ACTIVEs with same sensitivity list
//      Form master _eval function
//              Add around the SENTREE a (IF POSEDGE(..))
//                      Add a __Vlast_{clock} for the comparison
//                      Set the __Vlast_{clock} at the end of the block
//              Replace UNTILSTABLEs with loops until specified signals become const.
//   Create global calling function for any per-scope functions.  (For FINALs).
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3Global.h"
#include "V3Clock.h"
#include "V3Ast.h"
#include "V3EmitCBase.h"

#include <algorithm>
#include <cstdarg>

//######################################################################
// Clock state, as a visitor of each AstNode

class ClockVisitor : public AstNVisitor {
private:
    // NODE STATE
    // Cleared each Module:
    //  AstVarScope::user1p()   -> AstVarScope*.  Temporary signal that was created.
    AstUser1InUse       m_inuser1;

    // TYPES
    enum { DOUBLE_OR_RATE = 10 };  // How many | per ||, Determined experimentally as best

    // STATE
    AstNodeModule*      m_modp;         // Current module
    AstTopScope*        m_topScopep;    // Current top scope
    AstScope*           m_scopep;       // Current scope
    AstCFunc*           m_evalFuncp;    // Top eval function we are creating
    AstCFunc*           m_initFuncp;    // Top initial function we are creating
    AstCFunc*           m_finalFuncp;   // Top final function we are creating
    AstCFunc*           m_settleFuncp;  // Top settlement function we are creating
    AstSenTree*         m_lastSenp;     // Last sensitivity match, so we can detect duplicates.
    AstIf*              m_lastIfp;      // Last sensitivity if active to add more under
    AstMTaskBody*       m_mtaskBodyp;   // Current mtask body

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    AstVarScope* getCreateLastClk(AstVarScope* vscp) {
        if (vscp->user1p()) return static_cast<AstVarScope*>(vscp->user1p());
        AstVar* varp = vscp->varp();
        if (!varp->width1()) varp->v3error("Unsupported: Clock edge on non-single bit signal: "
                                           <<varp->prettyNameQ());
        string newvarname = (string("__Vclklast__")
                             +vscp->scopep()->nameDotless()+"__"+varp->name());
        AstVar* newvarp = new AstVar(vscp->fileline(),
                                     AstVarType::MODULETEMP, newvarname, VFlagLogicPacked(), 1);
        newvarp->noReset(true);  // Reset by below assign
        m_modp->addStmtp(newvarp);
        AstVarScope* newvscp = new AstVarScope(vscp->fileline(), m_scopep, newvarp);
        vscp->user1p(newvscp);
        m_scopep->addVarp(newvscp);
        // Add init
        AstNode* fromp = new AstVarRef(newvarp->fileline(), vscp, false);
        if (v3Global.opt.xInitialEdge()) fromp = new AstNot(fromp->fileline(), fromp);
        AstNode* newinitp = new AstAssign(vscp->fileline(),
                                          new AstVarRef(newvarp->fileline(), newvscp, true),
                                          fromp);
        addToInitial(newinitp);
        // At bottom, assign them
        AstAssign* finalp
            = new AstAssign(vscp->fileline(),
                            new AstVarRef(vscp->fileline(), newvscp, true),
                            new AstVarRef(vscp->fileline(), vscp, false));
        m_evalFuncp->addFinalsp(finalp);
        //
        UINFO(4,"New Last: "<<newvscp<<endl);
        return newvscp;
    }
    AstNode* createSenItemEquation(AstSenItem* nodep) {
        // We know the var is clean, and one bit, so we use binary ops
        // for speed instead of logical ops.
        // POSEDGE:  var & ~var_last
        // NEGEDGE:  ~var & var_last
        // BOTHEDGE:  var ^ var_last
        // HIGHEDGE:  var
        // LOWEDGE:  ~var
        AstNode* newp = NULL;
        if (nodep->edgeType()==VEdgeType::ET_ILLEGAL) {
            if (!v3Global.opt.bboxUnsup()) {
                nodep->v3error("Unsupported: Complicated event expression in sensitive activity list");
            }
            return NULL;
        }
        AstVarScope* clkvscp = nodep->varrefp()->varScopep();
        if (nodep->edgeType() == VEdgeType::ET_POSEDGE) {
            AstVarScope* lastVscp = getCreateLastClk(clkvscp);
            newp = new AstAnd(nodep->fileline(),
                              new AstVarRef(nodep->fileline(),
                                            nodep->varrefp()->varScopep(), false),
                              new AstNot(nodep->fileline(),
                                         new AstVarRef(nodep->fileline(),
                                                       lastVscp, false)));
        } else if (nodep->edgeType() == VEdgeType::ET_NEGEDGE) {
            AstVarScope* lastVscp = getCreateLastClk(clkvscp);
            newp = new AstAnd(nodep->fileline(),
                              new AstNot(nodep->fileline(),
                                         new AstVarRef(nodep->fileline(),
                                                       nodep->varrefp()->varScopep(), false)),
                              new AstVarRef(nodep->fileline(), lastVscp, false));
        } else if (nodep->edgeType() == VEdgeType::ET_BOTHEDGE) {
            AstVarScope* lastVscp = getCreateLastClk(clkvscp);
            newp = new AstXor(nodep->fileline(),
                              new AstVarRef(nodep->fileline(),
                                            nodep->varrefp()->varScopep(), false),
                              new AstVarRef(nodep->fileline(), lastVscp, false));
        } else if (nodep->edgeType() == VEdgeType::ET_HIGHEDGE) {
            newp = new AstVarRef(nodep->fileline(),
                                 clkvscp, false);
        } else if (nodep->edgeType() == VEdgeType::ET_LOWEDGE) {
            newp = new AstNot(nodep->fileline(),
                              new AstVarRef(nodep->fileline(),
                                            clkvscp, false));
        } else {
            nodep->v3fatalSrc("Bad edge type");
        }
        return newp;
    }
    AstNode* createSenGateEquation(AstSenGate* nodep) {
        AstNode* newp = new AstAnd(nodep->fileline(),
                                   createSenseEquation(nodep->sensesp()),
                                   nodep->rhsp()->cloneTree(true));
        return newp;
    }
    AstNode* createSenseEquation(AstNodeSenItem* nodesp) {
        // Nodep may be a list of elements; we need to walk it
        AstNode* senEqnp = NULL;
        for (AstNodeSenItem* senp = nodesp; senp; senp = VN_CAST(senp->nextp(), NodeSenItem)) {
            AstNode* senOnep = NULL;
            if (AstSenItem* itemp = VN_CAST(senp, SenItem)) {
                senOnep = createSenItemEquation(itemp);
            } else if (AstSenGate* itemp = VN_CAST(senp, SenGate)) {
                senOnep = createSenGateEquation(itemp);
            } else {
                senp->v3fatalSrc("Strange node under sentree");
            }
            if (senEqnp) {
                // Add new OR to the sensitivity list equation
                senEqnp = new AstOr(senp->fileline(), senEqnp, senOnep);
            } else {
                senEqnp = senOnep;
            }
        }
        return senEqnp;
    }
    AstIf* makeActiveIf(AstSenTree* sensesp) {
        AstNode* senEqnp = createSenseEquation(sensesp->sensesp());
        UASSERT_OBJ(senEqnp, sensesp, "No sense equation, shouldn't be in sequent activation.");
        AstIf* newifp = new AstIf(sensesp->fileline(), senEqnp, NULL, NULL);
        return newifp;
    }
    void clearLastSen() {
        m_lastSenp = NULL;
        m_lastIfp = NULL;
    }

    // VISITORS
    virtual void visit(AstTopScope* nodep) VL_OVERRIDE {
        UINFO(4," TOPSCOPE   "<<nodep<<endl);
        m_topScopep = nodep;
        m_scopep = nodep->scopep();
        UASSERT_OBJ(m_scopep, nodep,
                    "No scope found on top level, perhaps you have no statements?");
        //VV*****  We reset all user1p()
        AstNode::user1ClearTree();
        // Make top functions
        {
            AstCFunc* funcp = new AstCFunc(nodep->fileline(), "_eval", m_scopep);
            funcp->argTypes(EmitCBaseVisitor::symClassVar());
            funcp->dontCombine(true);
            funcp->symProlog(true);
            funcp->isStatic(true);
            funcp->entryPoint(true);
            m_scopep->addActivep(funcp);
            m_evalFuncp = funcp;
        }
        {
            AstCFunc* funcp = new AstCFunc(nodep->fileline(), "_eval_initial", m_scopep);
            funcp->argTypes(EmitCBaseVisitor::symClassVar());
            funcp->dontCombine(true);
            funcp->slow(true);
            funcp->symProlog(true);
            funcp->isStatic(true);
            funcp->entryPoint(true);
            m_scopep->addActivep(funcp);
            m_initFuncp = funcp;
        }
        {
            AstCFunc* funcp = new AstCFunc(nodep->fileline(), "final", m_scopep);
            funcp->skipDecl(true);
            funcp->dontCombine(true);
            funcp->slow(true);
            funcp->isStatic(false);
            funcp->entryPoint(true);
            funcp->protect(false);
            funcp->addInitsp(new AstCStmt
                             (nodep->fileline(),
                              EmitCBaseVisitor::symClassVar()+" = this->__VlSymsp;\n"));
            funcp->addInitsp(new AstCStmt(nodep->fileline(),
                                          EmitCBaseVisitor::symTopAssign()+"\n"));
            m_scopep->addActivep(funcp);
            m_finalFuncp = funcp;
        }
        {
            AstCFunc* funcp = new AstCFunc(nodep->fileline(), "_eval_settle", m_scopep);
            funcp->argTypes(EmitCBaseVisitor::symClassVar());
            funcp->dontCombine(true);
            funcp->slow(true);
            funcp->isStatic(true);
            funcp->symProlog(true);
            funcp->entryPoint(true);
            m_scopep->addActivep(funcp);
            m_settleFuncp = funcp;
        }
        // Process the activates
        iterateChildren(nodep);
        // Done, clear so we can detect errors
        UINFO(4," TOPSCOPEDONE "<<nodep<<endl);
        clearLastSen();
        m_topScopep = NULL;
        m_scopep = NULL;
    }
    virtual void visit(AstNodeModule* nodep) VL_OVERRIDE {
        //UINFO(4," MOD   "<<nodep<<endl);
        AstNodeModule* origModp = m_modp;
        {
            m_modp = nodep;
            iterateChildren(nodep);
        }
        m_modp = origModp;
    }
    virtual void visit(AstScope* nodep) VL_OVERRIDE {
        //UINFO(4," SCOPE   "<<nodep<<endl);
        m_scopep = nodep;
        iterateChildren(nodep);
        if (AstNode* movep = nodep->finalClksp()) {
            UASSERT_OBJ(m_topScopep, nodep, "Final clocks under non-top scope");
            movep->unlinkFrBackWithNext();
            m_evalFuncp->addFinalsp(movep);
        }
        m_scopep = NULL;
    }
    virtual void visit(AstAlways* nodep) VL_OVERRIDE {
        AstNode* cmtp = new AstComment(nodep->fileline(), nodep->typeName(), true);
        nodep->replaceWith(cmtp);
        if (AstNode* stmtsp = nodep->bodysp()) {
            stmtsp->unlinkFrBackWithNext();
            cmtp->addNextHere(stmtsp);
        }
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
    }
    virtual void visit(AstAlwaysPost* nodep) VL_OVERRIDE {
        AstNode* cmtp = new AstComment(nodep->fileline(), nodep->typeName(), true);
        nodep->replaceWith(cmtp);
        if (AstNode* stmtsp = nodep->bodysp()) {
            stmtsp->unlinkFrBackWithNext();
            cmtp->addNextHere(stmtsp);
        }
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
    }
    virtual void visit(AstCoverToggle* nodep) VL_OVERRIDE {
        //nodep->dumpTree(cout, "ct:");
        //COVERTOGGLE(INC, ORIG, CHANGE) ->
        //   IF(ORIG ^ CHANGE) { INC; CHANGE = ORIG; }
        AstNode* incp = nodep->incp()->unlinkFrBack();
        AstNode* origp = nodep->origp()->unlinkFrBack();
        AstNode* changep = nodep->changep()->unlinkFrBack();
        AstIf* newp = new AstIf(nodep->fileline(),
                                new AstXor(nodep->fileline(),
                                           origp,
                                           changep),
                                incp, NULL);
        // We could add another IF to detect posedges, and only increment if so.
        // It's another whole branch though versus a potential memory miss.
        // We'll go with the miss.
        newp->addIfsp(new AstAssign(nodep->fileline(),
                                    changep->cloneTree(false),
                                    origp->cloneTree(false)));
        nodep->replaceWith(newp); VL_DO_DANGLING(nodep->deleteTree(), nodep);
    }
    virtual void visit(AstInitial* nodep) VL_OVERRIDE {
        AstNode* cmtp = new AstComment(nodep->fileline(), nodep->typeName(), true);
        nodep->replaceWith(cmtp);
        if (AstNode* stmtsp = nodep->bodysp()) {
            stmtsp->unlinkFrBackWithNext();
            cmtp->addNextHere(stmtsp);
        }
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
    }
    virtual void visit(AstCFunc* nodep) VL_OVERRIDE {
        iterateChildren(nodep);
        // Link to global function
        if (nodep->formCallTree()) {
            UINFO(4, "    formCallTree "<<nodep<<endl);
            AstCCall* callp = new AstCCall(nodep->fileline(), nodep);
            callp->argTypes("vlSymsp");
            m_finalFuncp->addStmtsp(callp);
        }
    }
    virtual void visit(AstSenTree* nodep) VL_OVERRIDE {
        // Delete it later; Actives still pointing to it
        nodep->unlinkFrBack();
        pushDeletep(nodep);
    }
    void addToEvalLoop(AstNode* stmtsp) {
       m_evalFuncp->addStmtsp(stmtsp);  // add to top level function
    }
    void addToSettleLoop(AstNode* stmtsp) {
       m_settleFuncp->addStmtsp(stmtsp);  // add to top level function
    }
    void addToInitial(AstNode* stmtsp) {
       m_initFuncp->addStmtsp(stmtsp);  // add to top level function
    }
    virtual void visit(AstActive* nodep) VL_OVERRIDE {
        // Careful if adding variables here, ACTIVES can be under other ACTIVES
        // Need to save and restore any member state in AstUntilStable block
        if (!m_topScopep || !nodep->stmtsp()) {
            // Not at the top or empty block...
            // Only empty blocks should be leftover on the non-top.  Killem.
            UASSERT_OBJ(!nodep->stmtsp(), nodep, "Non-empty lower active");
            VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
        } else if (m_mtaskBodyp) {
            UINFO(4,"  TR ACTIVE  "<<nodep<<endl);
            AstNode* stmtsp = nodep->stmtsp()->unlinkFrBackWithNext();
            if (nodep->hasClocked()) {
                UASSERT_OBJ(!nodep->hasInitial(), nodep,
                            "Initial block should not have clock sensitivity");
                if (m_lastSenp && nodep->sensesp()->sameTree(m_lastSenp)) {
                    UINFO(4,"    sameSenseTree\n");
                } else {
                    clearLastSen();
                    m_lastSenp = nodep->sensesp();
                    // Make a new if statement
                    m_lastIfp = makeActiveIf(m_lastSenp);
                    m_mtaskBodyp->addStmtsp(m_lastIfp);
                }
                // Move statements to if
                m_lastIfp->addIfsp(stmtsp);
            } else if (nodep->hasInitial() || nodep->hasSettle()) {
                nodep->v3fatalSrc("MTask should not include initial/settle logic.");
            } else {
                // Combo logic. Move statements to mtask func.
                clearLastSen();
                m_mtaskBodyp->addStmtsp(stmtsp);
            }
            VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
        } else {
            UINFO(4,"  ACTIVE  "<<nodep<<endl);
            AstNode* stmtsp = nodep->stmtsp()->unlinkFrBackWithNext();
            if (nodep->hasClocked()) {
                // Remember the latest sensitivity so we can compare it next time
                UASSERT_OBJ(!nodep->hasInitial(), nodep,
                            "Initial block should not have clock sensitivity");
                if (m_lastSenp && nodep->sensesp()->sameTree(m_lastSenp)) {
                    UINFO(4,"    sameSenseTree\n");
                } else {
                    clearLastSen();
                    m_lastSenp = nodep->sensesp();
                    // Make a new if statement
                    m_lastIfp = makeActiveIf(m_lastSenp);
                    addToEvalLoop(m_lastIfp);
                }
                // Move statements to if
                m_lastIfp->addIfsp(stmtsp);
            } else if (nodep->hasInitial()) {
                // Don't need to: clearLastSen();, as we're adding it to different cfunc
                // Move statements to function
                addToInitial(stmtsp);
            } else if (nodep->hasSettle()) {
                // Don't need to: clearLastSen();, as we're adding it to different cfunc
                // Move statements to function
                addToSettleLoop(stmtsp);
            } else {
                // Combo
                clearLastSen();
                // Move statements to function
                addToEvalLoop(stmtsp);
            }
            VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
        }
    }
    virtual void visit(AstExecGraph* nodep) VL_OVERRIDE {
        for (m_mtaskBodyp = VN_CAST(nodep->op1p(), MTaskBody);
             m_mtaskBodyp;
             m_mtaskBodyp = VN_CAST(m_mtaskBodyp->nextp(), MTaskBody)) {
            clearLastSen();
            iterate(m_mtaskBodyp);
        }
        clearLastSen();
        // Move the ExecGraph into _eval. Its location marks the
        // spot where the graph will execute, relative to other
        // (serial) logic in the cycle.
        nodep->unlinkFrBack();
        addToEvalLoop(nodep);
    }

    //--------------------
    // Default: Just iterate
    virtual void visit(AstNode* nodep) VL_OVERRIDE {
        iterateChildren(nodep);
    }

public:
    // CONSTRUCTORS
    explicit ClockVisitor(AstNetlist* nodep) {
        m_modp = NULL;
        m_evalFuncp = NULL;
        m_initFuncp = NULL;
        m_finalFuncp = NULL;
        m_settleFuncp = NULL;
        m_topScopep = NULL;
        m_lastSenp = NULL;
        m_lastIfp = NULL;
        m_scopep = NULL;
        m_mtaskBodyp = NULL;
        //
        iterate(nodep);
        // Allow downstream modules to find _eval()
        // easily without iterating through the tree.
        nodep->evalp(m_evalFuncp);
    }
    virtual ~ClockVisitor() {}
};

//######################################################################
// Clock class functions

void V3Clock::clockAll(AstNetlist* nodep) {
    UINFO(2,__FUNCTION__<<": "<<endl);
    {
        ClockVisitor visitor (nodep);
    }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("clock", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}
