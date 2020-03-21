// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Branch prediction
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
// BRANCH TRANSFORMATIONS:
//      At each IF/(IF else).
//         Count underneath $display/$stop statements.
//         If more on if than else, this branch is unlikely, or vice-versa.
//      At each FTASKREF,
//         Count calls into the function
//      Then, if FTASK is called only once, add inline attribute
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3Global.h"
#include "V3Branch.h"
#include "V3Ast.h"

#include <cstdarg>
#include <map>

//######################################################################
// Branch state, as a visitor of each AstNode

class BranchVisitor : public AstNVisitor {
private:
    // NODE STATE
    // Entire netlist:
    //  AstFTask::user1()       -> int.  Number of references
    AstUser1InUse       m_inuser1;

    // TYPES
    typedef std::vector<AstCFunc*> CFuncVec;

    // STATE
    int         m_likely;       // Excuses for branch likely taken
    int         m_unlikely;     // Excuses for branch likely not taken
    CFuncVec    m_cfuncsp;      // List of all tasks

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    void reset() {
        m_likely = false;
        m_unlikely = false;
    }
    void checkUnlikely(AstNode* nodep) {
        if (nodep->isUnlikely()) {
            UINFO(4,"  UNLIKELY: "<<nodep<<endl);
            m_unlikely++;
        }
    }

    // VISITORS
    virtual void visit(AstNodeIf* nodep) VL_OVERRIDE {
        UINFO(4," IF: "<<nodep<<endl);
        int lastLikely = m_likely;
        int lastUnlikely = m_unlikely;
        {
            // Do if
            reset();
            iterateAndNextNull(nodep->ifsp());
            int ifLikely = m_likely;
            int ifUnlikely = m_unlikely;
            // Do else
            reset();
            iterateAndNextNull(nodep->elsesp());
            int elseLikely = m_likely;
            int elseUnlikely = m_unlikely;
            // Compute
            int likeness = ifLikely - ifUnlikely - (elseLikely - elseUnlikely);
            if (likeness > 0) {
                nodep->branchPred(VBranchPred::BP_LIKELY);
            } else if (likeness < 0) {
                nodep->branchPred(VBranchPred::BP_UNLIKELY);
            }  // else leave unknown
        }
        m_likely = lastLikely;
        m_unlikely = lastUnlikely;
    }
    virtual void visit(AstNodeCCall* nodep) VL_OVERRIDE {
        checkUnlikely(nodep);
        nodep->funcp()->user1Inc();
        iterateChildren(nodep);
    }
    virtual void visit(AstCFunc* nodep) VL_OVERRIDE {
        checkUnlikely(nodep);
        m_cfuncsp.push_back(nodep);
        iterateChildren(nodep);
    }
    virtual void visit(AstNode* nodep) VL_OVERRIDE {
        checkUnlikely(nodep);
        iterateChildren(nodep);
    }

    // METHODS
    void calc_tasks() {
        for (CFuncVec::iterator it=m_cfuncsp.begin(); it!=m_cfuncsp.end(); ++it) {
            AstCFunc* nodep = *it;
            if (!nodep->dontInline()) {
                nodep->isInline(true);
            }
        }
    }

public:
    // CONSTRUCTORS
    explicit BranchVisitor(AstNetlist* nodep) {
        reset();
        iterateChildren(nodep);
        calc_tasks();
    }
    virtual ~BranchVisitor() {}
};

//######################################################################
// Branch class functions

void V3Branch::branchAll(AstNetlist* nodep) {
    UINFO(2,__FUNCTION__<<": "<<endl);
    BranchVisitor visitor (nodep);
}
