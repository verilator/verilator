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

#include "V3Global.h"
#include "V3Clock.h"
#include "V3Ast.h"
#include "V3Sched.h"

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
    AstScope* m_scopep = nullptr;  // Current scope
    AstCFunc* const m_initp;  // Top initial function (already created)
    AstEval* const m_evalp;  // Top eval function (already created)
    AstSenTree* m_lastSenp = nullptr;  // Last sensitivity match, so we can detect duplicates.
    AstIf* m_lastIfp = nullptr;  // Last sensitivity if active to add more under

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
        m_initp->addStmtsp(newinitp);
        // At bottom, assign them
        AstAssign* const finalp = new AstAssign(
            vscp->fileline(), new AstVarRef(vscp->fileline(), newvscp, VAccess::WRITE),
            new AstVarRef(vscp->fileline(), vscp, VAccess::READ));
        m_evalp->addFinalp(finalp);
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
        AstIf* const newifp = new AstIf(sensesp->fileline(), senEqnp, nullptr, nullptr);
        return newifp;
    }
    void clearLastSen() {
        m_lastSenp = nullptr;
        m_lastIfp = nullptr;
    }
    // VISITORS
    virtual void visit(AstTopScope* nodep) override {
        UINFO(4, " TOPSCOPE   " << nodep << endl);
        m_scopep = nodep->scopep();
        UASSERT_OBJ(m_scopep, nodep,
                    "No scope found on top level, perhaps you have no statements?");
        // VV*****  We reset all user1p()
        AstNode::user1ClearTree();
        // Process the activates
        iterateChildren(nodep);
        UINFO(4, " TOPSCOPE iter done " << nodep << endl);
        // Clear the DPI export trigger flag at the end of eval
        if (AstVarScope* const dpiExportTriggerp = v3Global.rootp()->dpiExportTriggerp()) {
            FileLine* const fl = dpiExportTriggerp->fileline();
            AstAssign* const assignp
                = new AstAssign{fl, new AstVarRef{fl, dpiExportTriggerp, VAccess::WRITE},
                                new AstConst{fl, AstConst::BitFalse{}}};
            m_evalp->addFinalp(assignp);
        }
        // Done, clear so we can detect errors
        UINFO(4, " TOPSCOPEDONE " << nodep << endl);
        clearLastSen();
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
        if (AstNodeStmt* const stmtp = nodep->finalClksp()) {
            stmtp->unlinkFrBackWithNext();
            m_evalp->addFinalp(stmtp);
        }
        m_scopep = nullptr;
    }
    virtual void visit(AstCoverToggle* nodep) override {
        // nodep->dumpTree(cout, "ct:");
        // COVERTOGGLE(INC, ORIG, CHANGE) ->
        //   IF(ORIG ^ CHANGE) { INC; CHANGE = ORIG; }
        AstNode* const incp = nodep->incp()->unlinkFrBack();
        AstNode* const origp = nodep->origp()->unlinkFrBack();
        AstNode* const changeWrp = nodep->changep()->unlinkFrBack();
        AstNode* const changeRdp = ConvertWriteRefsToRead::main(changeWrp->cloneTree(false));
        AstIf* const newp = new AstIf(
            nodep->fileline(), new AstXor(nodep->fileline(), origp, changeRdp), incp, nullptr);
        // We could add another IF to detect posedges, and only increment if so.
        // It's another whole branch though versus a potential memory miss.
        // We'll go with the miss.
        newp->addIfsp(new AstAssign(nodep->fileline(), changeWrp, origp->cloneTree(false)));
        nodep->replaceWith(newp);
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
    }
    virtual void visit(AstSenTree* nodep) override {
        // Delete it later; Actives still pointing to it
        nodep->unlinkFrBack();
        pushDeletep(nodep);
    }
    virtual void visit(AstActive* nodep) override {
        // Careful if adding variables here, ACTIVES can be under other ACTIVES
        // Need to save and restore any member state in AstUntilStable block
        VNRelinker relinker;
        nodep->unlinkFrBack(&relinker);
        UASSERT_OBJ(nodep->stmtsp(), nodep, "Should not have been created if empty");
        AstNode* const stmtsp = nodep->stmtsp()->unlinkFrBackWithNext();
        if (nodep->hasClocked()) {
            // Create 'if' statement, if needed
            if (!m_lastSenp || !nodep->sensesp()->sameTree(m_lastSenp)) {
                clearLastSen();
                m_lastSenp = nodep->sensesp();
                // Make a new if statement
                m_lastIfp = makeActiveIf(m_lastSenp);
                relinker.relink(m_lastIfp);
            }
            // Move statements to if
            m_lastIfp->addIfsp(stmtsp);
        } else if (nodep->hasCombo()) {
            clearLastSen();
            // Move statements to body
            relinker.relink(stmtsp);
        } else {
            nodep->v3fatalSrc("Should have been removed by V3Sched::schedule");
        }
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
    }
    virtual void visit(AstExecGraph* nodep) override {
        for (AstMTaskBody* mtaskBodyp = VN_AS(nodep->op1p(), MTaskBody); mtaskBodyp;
             mtaskBodyp = VN_AS(mtaskBodyp->nextp(), MTaskBody)) {
            clearLastSen();
            iterate(mtaskBodyp);
        }
        clearLastSen();
    }

    //--------------------
    virtual void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit ClockVisitor(AstNetlist* netlistp)
        : m_initp{netlistp->initp()}
        , m_evalp{netlistp->evalp()} {
        iterate(netlistp);
        // Split large functions
        V3Sched::splitCheck(m_initp);
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
