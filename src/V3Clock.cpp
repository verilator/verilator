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
    // STATE
    AstSenTree* m_lastSenp = nullptr;  // Last sensitivity match, so we can detect duplicates.
    AstIf* m_lastIfp = nullptr;  // Last sensitivity if active to add more under

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    AstNode* createSenseEquation(AstSenItem* nodesp) {
        AstNode* senEqnp = nullptr;
        for (AstSenItem* senp = nodesp; senp; senp = VN_AS(senp->nextp(), SenItem)) {
            UASSERT_OBJ(senp->edgeType() == VEdgeType::ET_TRUE, senp, "Should have been lowered");
            AstNode* const senOnep = senp->sensp()->cloneTree(false);
            senEqnp = senEqnp ? new AstOr{senp->fileline(), senEqnp, senOnep} : senOnep;
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
    // VISITORS
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
    virtual void visit(AstSenTree* nodep) override {
        nodep->unlinkFrBack();
        pushDeletep(nodep);  // Delete it later, AstActives still pointing to it
    }
    virtual void visit(AstActive* nodep) override {
        UASSERT_OBJ(nodep->hasClocked(), nodep, "Should have been converted by V3Sched");
        UASSERT_OBJ(nodep->stmtsp(), nodep, "Should not have been created if empty");

        VNRelinker relinker;
        nodep->unlinkFrBack(&relinker);
        AstNode* const stmtsp = nodep->stmtsp()->unlinkFrBackWithNext();

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

        // Dispose of the AstActive
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
    }
    virtual void visit(AstExecGraph* nodep) override {
        for (AstMTaskBody* mtaskBodyp = nodep->mTaskBodiesp(); mtaskBodyp;
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
    explicit ClockVisitor(AstNetlist* netlistp) { iterate(netlistp); }
    virtual ~ClockVisitor() override = default;
};

//######################################################################
// Clock class functions

void V3Clock::clockAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    { ClockVisitor{nodep}; }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("clock", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}
