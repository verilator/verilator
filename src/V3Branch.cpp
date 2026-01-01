// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Branch prediction
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
// BRANCH TRANSFORMATIONS:
//      At each IF/(IF else).
//         Count underneath $display/$stop statements.
//         If more on if than else, this branch is unlikely, or vice-versa.
//      At each FTASKREF,
//         Count calls into the function
//      Then, if FTASK is called only once, add inline attribute
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Branch.h"

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// Branch state, as a visitor of each AstNode

class BranchVisitor final : public VNVisitorConst {
    // STATE - for current visit position (use VL_RESTORER)
    int m_unlikely = 0;  // Excuses for branch likely not taken

    // VISITORS
    void visit(AstNodeIf* nodep) override {
        UINFO(4, " IF: " << nodep);
        VL_RESTORER(m_unlikely);
        // Do then
        m_unlikely = 0;
        iterateAndNextConstNull(nodep->thensp());
        const int thenUnlikely = m_unlikely;
        // Do else
        m_unlikely = 0;
        iterateAndNextConstNull(nodep->elsesp());
        const int elseUnlikely = m_unlikely;
        // Compute
        if (elseUnlikely > thenUnlikely) {
            nodep->branchPred(VBranchPred::BP_LIKELY);
        } else if (elseUnlikely < thenUnlikely) {
            nodep->branchPred(VBranchPred::BP_UNLIKELY);
        }  // else leave unknown
    }

    void visit(AstNode* nodep) override {
        if (nodep->isUnlikely()) {
            UINFO(4, "  UNLIKELY: " << nodep);
            ++m_unlikely;
        }
        iterateChildrenConst(nodep);
    }

public:
    // CONSTRUCTORS
    explicit BranchVisitor(AstNetlist* nodep) { iterateChildrenConst(nodep); }
    ~BranchVisitor() override = default;
};

//######################################################################
// Branch class functions

void V3Branch::branchAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ":");
    { BranchVisitor{nodep}; }
    V3Global::dumpCheckGlobalTree("branch", 0, dumpTreeEitherLevel() >= 3);
}
