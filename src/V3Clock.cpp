// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Clocking POS/NEGEDGE insertion
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2022 by Wilson Snyder. This program is free software; you
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

#include "V3Clock.h"

#include "V3Ast.h"
#include "V3Global.h"

#include <algorithm>

//######################################################################
// Convert every WRITE AstVarRef to a READ ref

class ConvertWriteRefsToRead final : public VNVisitor {
private:
    // MEMBERS
    AstNode* m_result = nullptr;

    // CONSTRUCTORS
    explicit ConvertWriteRefsToRead(AstNode* nodep) {
        m_result = iterateSubtreeReturnEdits(nodep);
    }

    // VISITORS
    void visit(AstVarRef* nodep) override {
        UASSERT_OBJ(!nodep->access().isRW(), nodep, "Cannot handle a READWRITE reference");
        if (nodep->access().isWriteOnly()) {
            nodep->replaceWith(
                new AstVarRef(nodep->fileline(), nodep->varScopep(), VAccess::READ));
        }
    }

    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    static AstNode* main(AstNode* nodep) { return ConvertWriteRefsToRead(nodep).m_result; }
};

//######################################################################
// Clock state, as a visitor of each AstNode

class ClockVisitor final : public VNVisitor {
private:
    // NODE STATE
    // Cleared each Module:
    //  AstVarScope::user1p()   -> AstVarScope*.  Temporary signal that was created.
    const VNUser1InUse m_inuser1;

    // STATE
    AstNodeModule* m_modp = nullptr;  // Current module
    const AstTopScope* m_topScopep = nullptr;  // Current top scope
    AstScope* m_scopep = nullptr;  // Current scope
    AstCFunc* m_evalFuncp = nullptr;  // Top eval function we are creating
    AstCFunc* m_initFuncp = nullptr;  // Top initial function we are creating
    AstCFunc* m_finalFuncp = nullptr;  // Top final function we are creating
    AstCFunc* m_settleFuncp = nullptr;  // Top settlement function we are creating
    AstSenTree* m_lastSenp = nullptr;  // Last sensitivity match, so we can detect duplicates.
    AstIf* m_lastIfp = nullptr;  // Last sensitivity if active to add more under
    AstMTaskBody* m_mtaskBodyp = nullptr;  // Current mtask body

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    AstVarScope* getCreateLastClk(AstVarScope* vscp) {
        if (vscp->user1p()) return static_cast<AstVarScope*>(vscp->user1p());
        const AstVar* const varp = vscp->varp();
        if (!varp->width1()) {
            varp->v3warn(E_UNSUPPORTED, "Unsupported: Clock edge on non-single bit signal: "
                                            << varp->prettyNameQ());
        }
        const string newvarname
            = (string("__Vclklast__") + vscp->scopep()->nameDotless() + "__" + varp->name());
        AstVar* const newvarp = new AstVar(vscp->fileline(), VVarType::MODULETEMP, newvarname,
                                           VFlagLogicPacked(), 1);
        newvarp->noReset(true);  // Reset by below assign
        m_modp->addStmtp(newvarp);
        AstVarScope* const newvscp = new AstVarScope(vscp->fileline(), m_scopep, newvarp);
        vscp->user1p(newvscp);
        m_scopep->addVarp(newvscp);
        // Add init
        AstNode* fromp = new AstVarRef(newvarp->fileline(), vscp, VAccess::READ);
        if (v3Global.opt.xInitialEdge()) fromp = new AstNot(fromp->fileline(), fromp);
        AstNode* const newinitp = new AstAssign(
            vscp->fileline(), new AstVarRef(newvarp->fileline(), newvscp, VAccess::WRITE), fromp);
        addToInitial(newinitp);
        // At bottom, assign them
        AstAssign* const finalp = new AstAssign(
            vscp->fileline(), new AstVarRef(vscp->fileline(), newvscp, VAccess::WRITE),
            new AstVarRef(vscp->fileline(), vscp, VAccess::READ));
        m_evalFuncp->addFinalsp(finalp);
        //
        UINFO(4, "New Last: " << newvscp << endl);
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
        // ANYEDGE:   var ^ var_last
        AstNode* newp = nullptr;
        if (nodep->edgeType() == VEdgeType::ET_ILLEGAL) {
            nodep->v3warn(E_UNSUPPORTED,
                          "Unsupported: Complicated event expression in sensitive activity list");
            return nullptr;
        }
        UASSERT_OBJ(nodep->varrefp(), nodep, "No clock found on sense item");
        AstVarScope* const clkvscp = nodep->varrefp()->varScopep();
        if (nodep->edgeType() == VEdgeType::ET_POSEDGE) {
            AstVarScope* const lastVscp = getCreateLastClk(clkvscp);
            newp = new AstAnd(
                nodep->fileline(),
                new AstVarRef(nodep->fileline(), nodep->varrefp()->varScopep(), VAccess::READ),
                new AstNot(nodep->fileline(),
                           new AstVarRef(nodep->fileline(), lastVscp, VAccess::READ)));
        } else if (nodep->edgeType() == VEdgeType::ET_NEGEDGE) {
            AstVarScope* const lastVscp = getCreateLastClk(clkvscp);
            newp = new AstAnd(
                nodep->fileline(),
                new AstNot(nodep->fileline(),
                           new AstVarRef(nodep->fileline(), nodep->varrefp()->varScopep(),
                                         VAccess::READ)),
                new AstVarRef(nodep->fileline(), lastVscp, VAccess::READ));
        } else if (nodep->edgeType() == VEdgeType::ET_BOTHEDGE) {
            AstVarScope* const lastVscp = getCreateLastClk(clkvscp);
            newp = new AstXor(
                nodep->fileline(),
                new AstVarRef(nodep->fileline(), nodep->varrefp()->varScopep(), VAccess::READ),
                new AstVarRef(nodep->fileline(), lastVscp, VAccess::READ));
        } else if (nodep->edgeType() == VEdgeType::ET_HIGHEDGE) {
            newp = new AstVarRef(nodep->fileline(), clkvscp, VAccess::READ);
        } else if (nodep->edgeType() == VEdgeType::ET_LOWEDGE) {
            newp = new AstNot(nodep->fileline(),
                              new AstVarRef(nodep->fileline(), clkvscp, VAccess::READ));
        } else {
            nodep->v3fatalSrc("Bad edge type");
        }
        return newp;
    }
    AstNode* createSenseEquation(AstSenItem* nodesp) {
        // Nodep may be a list of elements; we need to walk it
        AstNode* senEqnp = nullptr;
        for (AstSenItem* senp = nodesp; senp; senp = VN_AS(senp->nextp(), SenItem)) {
            AstNode* const senOnep = createSenItemEquation(senp);
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
        AstNode* const senEqnp = createSenseEquation(sensesp->sensesp());
        UASSERT_OBJ(senEqnp, sensesp, "No sense equation, shouldn't be in sequent activation.");
        AstIf* const newifp = new AstIf(sensesp->fileline(), senEqnp);
        return newifp;
    }
    void clearLastSen() {
        m_lastSenp = nullptr;
        m_lastIfp = nullptr;
    }
    AstCFunc* makeTopFunction(const string& name, bool slow = false) {
        AstCFunc* const funcp = new AstCFunc{m_topScopep->fileline(), name, m_topScopep->scopep()};
        funcp->dontCombine(true);
        funcp->isStatic(false);
        funcp->isLoose(true);
        funcp->entryPoint(true);
        funcp->slow(slow);
        funcp->isConst(false);
        funcp->declPrivate(true);
        m_topScopep->scopep()->addActivep(funcp);
        return funcp;
    }
    void splitCheck(AstCFunc* ofuncp) {
        if (!v3Global.opt.outputSplitCFuncs() || !ofuncp->stmtsp()) return;
        if (ofuncp->nodeCount() < v3Global.opt.outputSplitCFuncs()) return;

        int funcnum = 0;
        int func_stmts = 0;
        AstCFunc* funcp = nullptr;

        // Unlink all statements, then add item by item to new sub-functions
        AstBegin* const tempp = new AstBegin{ofuncp->fileline(), "[EditWrapper]",
                                             ofuncp->stmtsp()->unlinkFrBackWithNext()};
        if (ofuncp->finalsp()) tempp->addStmtsp(ofuncp->finalsp()->unlinkFrBackWithNext());
        while (tempp->stmtsp()) {
            AstNode* const itemp = tempp->stmtsp()->unlinkFrBack();
            const int stmts = itemp->nodeCount();
            if (!funcp || (func_stmts + stmts) > v3Global.opt.outputSplitCFuncs()) {
                // Make a new function
                funcp
                    = new AstCFunc{ofuncp->fileline(), ofuncp->name() + "__" + cvtToStr(funcnum++),
                                   m_topScopep->scopep()};
                funcp->dontCombine(true);
                funcp->isStatic(false);
                funcp->isLoose(true);
                funcp->slow(ofuncp->slow());
                m_topScopep->scopep()->addActivep(funcp);
                //
                AstCCall* const callp = new AstCCall{funcp->fileline(), funcp};
                ofuncp->addStmtsp(callp);
                func_stmts = 0;
            }
            funcp->addStmtsp(itemp);
            func_stmts += stmts;
        }
        VL_DO_DANGLING(tempp->deleteTree(), tempp);
    }

    // VISITORS
    virtual void visit(AstTopScope* nodep) override {
        UINFO(4, " TOPSCOPE   " << nodep << endl);
        m_topScopep = nodep;
        m_scopep = nodep->scopep();
        UASSERT_OBJ(m_scopep, nodep,
                    "No scope found on top level, perhaps you have no statements?");
        // VV*****  We reset all user1p()
        AstNode::user1ClearTree();
        // Make top functions
        m_evalFuncp = makeTopFunction("_eval");
        m_initFuncp = makeTopFunction("_eval_initial", /* slow: */ true);
        m_settleFuncp = makeTopFunction("_eval_settle", /* slow: */ true);
        m_finalFuncp = makeTopFunction("_final", /* slow: */ true);
        // Process the activates
        iterateChildren(nodep);
        UINFO(4, " TOPSCOPE iter done " << nodep << endl);
        // Clear the DPI export trigger flag at the end of eval
        if (AstVarScope* const dpiExportTriggerp = v3Global.rootp()->dpiExportTriggerp()) {
            FileLine* const fl = dpiExportTriggerp->fileline();
            AstAssign* const assignp
                = new AstAssign{fl, new AstVarRef{fl, dpiExportTriggerp, VAccess::WRITE},
                                new AstConst{fl, AstConst::BitFalse{}}};
            m_evalFuncp->addFinalsp(assignp);
        }
        // Split large functions
        splitCheck(m_evalFuncp);
        splitCheck(m_initFuncp);
        splitCheck(m_finalFuncp);
        splitCheck(m_settleFuncp);
        // Done, clear so we can detect errors
        UINFO(4, " TOPSCOPEDONE " << nodep << endl);
        clearLastSen();
        m_topScopep = nullptr;
        m_scopep = nullptr;
    }
    virtual void visit(AstNodeModule* nodep) override {
        // UINFO(4, " MOD   " << nodep << endl);
        VL_RESTORER(m_modp);
        {
            m_modp = nodep;
            iterateChildren(nodep);
        }
    }
    virtual void visit(AstScope* nodep) override {
        // UINFO(4, " SCOPE   " << nodep << endl);
        m_scopep = nodep;
        iterateChildren(nodep);
        if (AstNode* const movep = nodep->finalClksp()) {
            UASSERT_OBJ(m_topScopep, nodep, "Final clocks under non-top scope");
            movep->unlinkFrBackWithNext();
            m_evalFuncp->addFinalsp(movep);
        }
        m_scopep = nullptr;
    }
    virtual void visit(AstNodeProcedure* nodep) override {
        if (AstNode* const stmtsp = nodep->bodysp()) {
            stmtsp->unlinkFrBackWithNext();
            nodep->addNextHere(stmtsp);
        }
        VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
    }
    virtual void visit(AstCoverToggle* nodep) override {
        // nodep->dumpTree(cout, "ct:");
        // COVERTOGGLE(INC, ORIG, CHANGE) ->
        //   IF(ORIG ^ CHANGE) { INC; CHANGE = ORIG; }
        AstNode* const incp = nodep->incp()->unlinkFrBack();
        AstNode* const origp = nodep->origp()->unlinkFrBack();
        AstNode* const changeWrp = nodep->changep()->unlinkFrBack();
        AstNode* const changeRdp = ConvertWriteRefsToRead::main(changeWrp->cloneTree(false));
        AstIf* const newp
            = new AstIf(nodep->fileline(), new AstXor(nodep->fileline(), origp, changeRdp), incp);
        // We could add another IF to detect posedges, and only increment if so.
        // It's another whole branch though versus a potential memory miss.
        // We'll go with the miss.
        newp->addIfsp(new AstAssign(nodep->fileline(), changeWrp, origp->cloneTree(false)));
        nodep->replaceWith(newp);
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
    }
    virtual void visit(AstCFunc* nodep) override {
        iterateChildren(nodep);
        // Link to global function
        if (nodep->isFinal()) {
            UINFO(4, "    isFinal " << nodep << endl);
            AstCCall* const callp = new AstCCall(nodep->fileline(), nodep);
            m_finalFuncp->addStmtsp(callp);
        }
    }
    virtual void visit(AstSenTree* nodep) override {
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
    virtual void visit(AstActive* nodep) override {
        // Careful if adding variables here, ACTIVES can be under other ACTIVES
        // Need to save and restore any member state in AstUntilStable block
        if (!m_topScopep || !nodep->stmtsp()) {
            // Not at the top or empty block...
            // Only empty blocks should be leftover on the non-top.  Killem.
            UASSERT_OBJ(!nodep->stmtsp(), nodep, "Non-empty lower active");
            VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
        } else if (m_mtaskBodyp) {
            UINFO(4, "  TR ACTIVE  " << nodep << endl);
            AstNode* const stmtsp = nodep->stmtsp()->unlinkFrBackWithNext();
            if (nodep->hasClocked()) {
                UASSERT_OBJ(!nodep->hasInitial(), nodep,
                            "Initial block should not have clock sensitivity");
                if (m_lastSenp && nodep->sensesp()->sameTree(m_lastSenp)) {
                    UINFO(4, "    sameSenseTree\n");
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
            UINFO(4, "  ACTIVE  " << nodep << endl);
            AstNode* const stmtsp = nodep->stmtsp()->unlinkFrBackWithNext();
            if (nodep->hasClocked()) {
                // Remember the latest sensitivity so we can compare it next time
                UASSERT_OBJ(!nodep->hasInitial(), nodep,
                            "Initial block should not have clock sensitivity");
                if (m_lastSenp && nodep->sensesp()->sameTree(m_lastSenp)) {
                    UINFO(4, "    sameSenseTree\n");
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
    virtual void visit(AstExecGraph* nodep) override {
        VL_RESTORER(m_mtaskBodyp);
        for (m_mtaskBodyp = nodep->mTaskBodiesp(); m_mtaskBodyp;
             m_mtaskBodyp = VN_AS(m_mtaskBodyp->nextp(), MTaskBody)) {
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
    virtual void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit ClockVisitor(AstNetlist* nodep) {
        iterate(nodep);
        // Allow downstream modules to find _eval()
        // easily without iterating through the tree.
        nodep->evalp(m_evalFuncp);
    }
    virtual ~ClockVisitor() override = default;
};

//######################################################################
// Clock class functions

void V3Clock::clockAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    { ClockVisitor{nodep}; }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("clock", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}
