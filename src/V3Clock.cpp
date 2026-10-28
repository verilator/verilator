// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Post scheduling transformations
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2003-2026 Wilson Snyder
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

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// Convert every WRITE AstVarRef to a READ ref

class ConvertWriteRefsToRead final : public VNVisitor {
    // MEMBERS
    AstNodeExpr* m_result = nullptr;  // Converted expression

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
        FileLine* const flp = nodep->fileline();
        // Xor will optimize better than Eq, when CoverToggle has bit selects,
        // but can only use Xor with non-opaque types
        if (const AstBasicDType* const bdtypep
            = VN_CAST(origp->dtypep()->skipRefp(), BasicDType)) {
            if (!bdtypep->isOpaque()) {
                AstNodeExpr* const zp = new AstConst{flp, AstConst::DTyped{}, origp->dtypep()};
                comparedp = new AstNeq{flp, zp, new AstXor{flp, origp, changeRdp}};
            }
        }
        if (!comparedp) comparedp = AstNeq::newTyped(flp, origp, changeRdp);
        AstIf* const newp = new AstIf{flp, comparedp, incp};
        // We could add another IF to detect posedges, and only increment if so.
        // It's another whole branch though versus a potential memory miss.
        // We'll go with the miss.
        newp->addThensp(new AstAssign{flp, changeWrp, origp->cloneTree(false)});
        nodep->replaceWith(newp);
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
    }
    void visit(AstSenTree* nodep) override {
        VL_DO_DANGLING(pushDeletep(nodep->unlinkFrBack()), nodep);  // No longer needed
    }

    //--------------------
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit ClockVisitor(AstNetlist* netlistp) { iterate(netlistp); }
    ~ClockVisitor() override = default;
};

//######################################################################
// Clock class functions

void V3Clock::clockAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ":");
    { ClockVisitor{nodep}; }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("clock", 0, dumpTreeEitherLevel() >= 3);
}
