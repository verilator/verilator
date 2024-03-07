// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Clocking POS/NEGEDGE insertion
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2024 by Wilson Snyder. This program is free software; you
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

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Clock.h"

#include "V3Sched.h"

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// Convert every WRITE AstVarRef to a READ ref

class ConvertWriteRefsToRead final : public VNVisitor {
    // MEMBERS
    AstNodeExpr* m_result = nullptr;

    // CONSTRUCTORS
    explicit ConvertWriteRefsToRead(AstNodeExpr* nodep) {
        m_result = VN_AS(iterateSubtreeReturnEdits(nodep), NodeExpr);
    }

    // VISITORS
    void visit(AstVarRef* nodep) override {
        UASSERT_OBJ(!nodep->access().isRW(), nodep, "Cannot handle a READWRITE reference");
        if (nodep->access().isWriteOnly()) {
            nodep->replaceWith(
                new AstVarRef{nodep->fileline(), nodep->varScopep(), VAccess::READ});
        }
    }

    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    static AstNodeExpr* main(AstNodeExpr* nodep) { return ConvertWriteRefsToRead{nodep}.m_result; }
};

//######################################################################
// Clock state, as a visitor of each AstNode

class ClockVisitor final : public VNVisitor {
    // NODE STATE
    // ???
    const VNUser1InUse m_user1InUse;
    // STATE
    AstCFunc* m_evalp = nullptr;  // The '_eval' function
    AstScope* m_scopep = nullptr;  // Current scope
    AstSenTree* m_lastSenp = nullptr;  // Last sensitivity match, so we can detect duplicates.
    AstIf* m_lastIfp = nullptr;  // Last sensitivity if active to add more under
    bool m_inSampled = false;  // True inside a sampled expression

    // METHODS

    AstNodeExpr* createSenseEquation(AstSenItem* nodesp) {
        AstNodeExpr* senEqnp = nullptr;
        for (AstSenItem* senp = nodesp; senp; senp = VN_AS(senp->nextp(), SenItem)) {
            UASSERT_OBJ(senp->edgeType() == VEdgeType::ET_TRUE, senp, "Should have been lowered");
            AstNodeExpr* const senOnep = senp->sensp()->cloneTree(false);
            senEqnp = senEqnp ? new AstOr{senp->fileline(), senEqnp, senOnep} : senOnep;
        }
        return senEqnp;
    }
    AstVarScope* createSampledVar(AstVarScope* vscp) {
        if (vscp->user1p()) return VN_AS(vscp->user1p(), VarScope);
        const AstVar* const varp = vscp->varp();
        const string newvarname
            = string{"__Vsampled__"} + vscp->scopep()->nameDotless() + "__" + varp->name();
        FileLine* const flp = vscp->fileline();
        AstVar* const newvarp = new AstVar{flp, VVarType::MODULETEMP, newvarname, varp->dtypep()};
        newvarp->noReset(true);  // Reset by below assign
        m_scopep->modp()->addStmtsp(newvarp);
        AstVarScope* const newvscp = new AstVarScope{flp, m_scopep, newvarp};
        vscp->user1p(newvscp);
        m_scopep->addVarsp(newvscp);
        // At the top of _eval, assign them
        AstAssign* const finalp = new AstAssign{flp, new AstVarRef{flp, newvscp, VAccess::WRITE},
                                                new AstVarRef{flp, vscp, VAccess::READ}};
        m_evalp->addInitsp(finalp);
        UINFO(4, "New Sampled: " << newvscp << endl);
        return newvscp;
    }
    AstIf* makeActiveIf(AstSenTree* sensesp) {
        AstNodeExpr* const senEqnp = createSenseEquation(sensesp->sensesp());
        UASSERT_OBJ(senEqnp, sensesp, "No sense equation, shouldn't be in sequent activation.");
        AstIf* const newifp = new AstIf{sensesp->fileline(), senEqnp};
        return newifp;
    }
    void clearLastSen() {
        m_lastSenp = nullptr;
        m_lastIfp = nullptr;
    }
    // VISITORS
    void visit(AstCoverToggle* nodep) override {
        // nodep->dumpTree("-  ct: ");
        // COVERTOGGLE(INC, ORIG, CHANGE) ->
        //   IF(ORIG ^ CHANGE) { INC; CHANGE = ORIG; }
        AstNode* const incp = nodep->incp()->unlinkFrBack();
        AstNodeExpr* const origp = nodep->origp()->unlinkFrBack();
        AstNodeExpr* const changeWrp = nodep->changep()->unlinkFrBack();
        AstNodeExpr* const changeRdp = ConvertWriteRefsToRead::main(changeWrp->cloneTree(false));
        AstNodeExpr* comparedp = nullptr;
        // Xor will optimize better than Eq, when CoverToggle has bit selects,
        // but can only use Xor with non-opaque types
        if (const AstBasicDType* const bdtypep
            = VN_CAST(origp->dtypep()->skipRefp(), BasicDType)) {
            if (!bdtypep->isOpaque()) comparedp = new AstXor{nodep->fileline(), origp, changeRdp};
        }
        if (!comparedp) comparedp = AstEq::newTyped(nodep->fileline(), origp, changeRdp);
        AstIf* const newp = new AstIf{nodep->fileline(), comparedp, incp};
        // We could add another IF to detect posedges, and only increment if so.
        // It's another whole branch though versus a potential memory miss.
        // We'll go with the miss.
        newp->addThensp(new AstAssign{nodep->fileline(), changeWrp, origp->cloneTree(false)});
        nodep->replaceWith(newp);
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
    }
    void visit(AstSenTree* nodep) override {
        nodep->unlinkFrBack();
        pushDeletep(nodep);  // Delete it later, AstActives still pointing to it
    }
    void visit(AstActive* nodep) override {
        UASSERT_OBJ(nodep->hasClocked(), nodep, "Should have been converted by V3Sched");
        UASSERT_OBJ(nodep->stmtsp(), nodep, "Should not have been created if empty");

        AstNode* const stmtsp = nodep->stmtsp()->unlinkFrBackWithNext();

        // Create 'if' statement, if needed
        if (!m_lastSenp || !nodep->sensesp()->sameTree(m_lastSenp)) {
            VNRelinker relinker;
            nodep->unlinkFrBack(&relinker);
            clearLastSen();
            m_lastSenp = nodep->sensesp();
            // Make a new if statement
            m_lastIfp = makeActiveIf(m_lastSenp);
            relinker.relink(m_lastIfp);
        } else {
            nodep->unlinkFrBack();
        }

        // Move statements to if
        m_lastIfp->addThensp(stmtsp);

        // Dispose of the AstActive
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
    }
    void visit(AstExecGraph* nodep) override {
        for (AstMTaskBody* mtaskBodyp = nodep->mTaskBodiesp(); mtaskBodyp;
             mtaskBodyp = VN_AS(mtaskBodyp->nextp(), MTaskBody)) {
            clearLastSen();
            iterate(mtaskBodyp);
        }
        clearLastSen();
    }

    //========== Create sampled values
    void visit(AstScope* nodep) override {
        VL_RESTORER(m_scopep);
        {
            m_scopep = nodep;
            iterateChildren(nodep);
        }
    }
    void visit(AstSampled* nodep) override {
        VL_RESTORER(m_inSampled);
        {
            m_inSampled = true;
            iterateChildren(nodep);
            nodep->replaceWith(nodep->exprp()->unlinkFrBack());
            VL_DO_DANGLING(pushDeletep(nodep), nodep);
        }
    }
    void visit(AstVarRef* nodep) override {
        iterateChildren(nodep);
        if (m_inSampled && !nodep->user1SetOnce()) {
            UASSERT_OBJ(nodep->access().isReadOnly(), nodep, "Should have failed in V3Access");
            AstVarScope* const varscp = nodep->varScopep();
            AstVarScope* const lastscp = createSampledVar(varscp);
            AstNode* const newp = new AstVarRef{nodep->fileline(), lastscp, VAccess::READ};
            newp->user1SetOnce();  // Don't sample this one
            nodep->replaceWith(newp);
            VL_DO_DANGLING(pushDeletep(nodep), nodep);
        }
    }

    //--------------------
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit ClockVisitor(AstNetlist* netlistp) {
        m_evalp = netlistp->evalp();
        iterate(netlistp);
    }
    ~ClockVisitor() override = default;
};

//######################################################################
// Clock class functions

void V3Clock::clockAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    { ClockVisitor{nodep}; }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("clock", 0, dumpTreeEitherLevel() >= 3);
}
