// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Post scheduling transformations
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
// V3Clock's Transformations:
//
//  This pass is historic and does some arbitray post scheduling rewrites
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Clock.h"

#include "V3Const.h"
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
            VL_DO_DANGLING(pushDeletep(nodep), nodep);
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

    // STATE
    AstCFunc* m_sampleCFuncp = nullptr;  // The CFunc to populate with sampled value assignments

    // VISITORS
    void visit(AstCoverToggle* nodep) override {
        // UINFOTREE(1, nodep, "", "ct");
        // COVERTOGGLE(INC, ORIG, CHANGE) ->
        //   IF(ORIG ^ CHANGE) { INC; CHANGE = ORIG; }
        AstCoverInc* const incp = nodep->incp()->unlinkFrBack();
        AstNodeExpr* const origp = nodep->origp()->unlinkFrBack();
        AstNodeExpr* const changeWrp = nodep->changep()->unlinkFrBack();
        AstNodeExpr* const changeRdp = ConvertWriteRefsToRead::main(changeWrp->cloneTree(false));
        AstNodeExpr* comparedp = nullptr;
        incp->toggleExprp(origp->cloneTree(false));
        incp->toggleCovExprp(changeRdp->cloneTree(false));
        // Xor will optimize better than Eq, when CoverToggle has bit selects,
        // but can only use Xor with non-opaque types
        if (const AstBasicDType* const bdtypep
            = VN_CAST(origp->dtypep()->skipRefp(), BasicDType)) {
            if (!bdtypep->isOpaque()) comparedp = new AstXor{nodep->fileline(), origp, changeRdp};
        }
        if (!comparedp) comparedp = AstNeq::newTyped(nodep->fileline(), origp, changeRdp);
        AstIf* const newp = new AstIf{nodep->fileline(), comparedp, incp};
        // We could add another IF to detect posedges, and only increment if so.
        // It's another whole branch though versus a potential memory miss.
        // We'll go with the miss.
        newp->addThensp(new AstAssign{nodep->fileline(), changeWrp, origp->cloneTree(false)});
        nodep->replaceWith(newp);
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
    }
    void visit(AstSenTree* nodep) override {
        pushDeletep(nodep->unlinkFrBack());  // No longer needed
    }

    //========== Move sampled assignments
    void visit(AstVarScope* nodep) override {
        AstVar* const varp = nodep->varp();
        if (!varp->valuep()) return;
        if (!VString::startsWith(varp->name(), "__Vsampled")) return;

        // Create the containing function on first encounter
        if (!m_sampleCFuncp) {
            m_sampleCFuncp = V3Sched::util::makeSubFunction(v3Global.rootp(), "_sample", false);
        }

        FileLine* const flp = nodep->fileline();
        AstNodeExpr* const rhsp = VN_AS(varp->valuep()->unlinkFrBack(), NodeExpr);
        AstVarRef* const lhsp = new AstVarRef{flp, nodep, VAccess::WRITE};
        m_sampleCFuncp->addStmtsp(new AstAssign{flp, lhsp, rhsp});
        varp->direction(VDirection::NONE);  // Restore defaults
        varp->primaryIO(false);
    }

    //--------------------
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit ClockVisitor(AstNetlist* netlistp) {
        iterate(netlistp);
        // If we need a sample function, call it at the begining of eval
        if (m_sampleCFuncp) {
            V3Sched::util::splitCheck(m_sampleCFuncp);
            AstCCall* const callp = new AstCCall{m_sampleCFuncp->fileline(), m_sampleCFuncp};
            callp->dtypeSetVoid();
            netlistp->evalp()->stmtsp()->addHereThisAsNext(callp->makeStmt());
        }
    }
    ~ClockVisitor() override = default;
};

//######################################################################
// Clock class functions

void V3Clock::clockAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ":");
    { ClockVisitor{nodep}; }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("clock", 0, dumpTreeEitherLevel() >= 3);
}
