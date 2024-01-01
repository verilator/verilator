// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Branch prediction
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
    // NODE STATE
    // Entire netlist:
    //  AstFTask::user1()       -> int.  Number of references
    const VNUser1InUse m_inuser1;

    // STATE - across all visitors
    std::vector<AstCFunc*> m_cfuncsp;  // List of all tasks

    // STATE - for current visit position (use VL_RESTORER)
    int m_likely = false;  // Excuses for branch likely taken
    int m_unlikely = false;  // Excuses for branch likely not taken

    // METHODS

    void reset() {
        m_likely = false;
        m_unlikely = false;
    }
    void checkUnlikely(AstNode* nodep) {
        if (nodep->isUnlikely()) {
            UINFO(4, "  UNLIKELY: " << nodep << endl);
            m_unlikely++;
        }
    }

    // VISITORS
    void visit(AstNodeIf* nodep) override {
        UINFO(4, " IF: " << nodep << endl);
        VL_RESTORER(m_likely);
        VL_RESTORER(m_unlikely);
        {
            // Do if
            reset();
            iterateAndNextConstNull(nodep->thensp());
            const int ifLikely = m_likely;
            const int ifUnlikely = m_unlikely;
            // Do else
            reset();
            iterateAndNextConstNull(nodep->elsesp());
            const int elseLikely = m_likely;
            const int elseUnlikely = m_unlikely;
            // Compute
            const int likeness = ifLikely - ifUnlikely - (elseLikely - elseUnlikely);
            if (likeness > 0) {
                nodep->branchPred(VBranchPred::BP_LIKELY);
            } else if (likeness < 0) {
                nodep->branchPred(VBranchPred::BP_UNLIKELY);
            }  // else leave unknown
        }
    }
    void visit(AstNodeCCall* nodep) override {
        checkUnlikely(nodep);
        nodep->funcp()->user1Inc();
        iterateChildrenConst(nodep);
    }
    void visit(AstCFunc* nodep) override {
        checkUnlikely(nodep);
        m_cfuncsp.push_back(nodep);
        iterateChildrenConst(nodep);
    }
    void visit(AstNode* nodep) override {
        checkUnlikely(nodep);
        iterateChildrenConst(nodep);
    }

    // METHODS
    void calc_tasks() {
        for (AstCFunc* nodep : m_cfuncsp) {
            if (!nodep->dontInline()) nodep->isInline(true);
        }
    }

public:
    // CONSTRUCTORS
    explicit BranchVisitor(AstNetlist* nodep) {
        reset();
        iterateChildrenConst(nodep);
        calc_tasks();
    }
    ~BranchVisitor() override = default;
};

//######################################################################
// Branch class functions

void V3Branch::branchAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    { BranchVisitor{nodep}; }
}
