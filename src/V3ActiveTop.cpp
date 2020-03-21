// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Break always into sensitivity active domains
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
// V3Active's Transformations:
//
// Note this can be called multiple times.
//   Across all ACTIVES
//      SenTrees are now under each ACTIVE statement, we want them global:
//          Find SenTree in under global TopScope, or create it there
//          Move SenTree the global SenTree
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3Global.h"
#include "V3ActiveTop.h"
#include "V3Ast.h"
#include "V3SenTree.h"
#include "V3Const.h"

//######################################################################
// Active class functions

class ActiveTopVisitor : public AstNVisitor {
private:
    // NODE STATE
    //  Entire netlist
    //   AstNode::user()                bool. True if processed
    //  Each call to V3Const::constify
    //   AstNode::user4()               Used by V3Const::constify, called below
    AstUser1InUse       m_inuser1;

    // STATE
    AstTopScope*        m_topscopep;    // Top scope for adding sentrees under
    SenTreeFinder       m_finder;       // Find global sentree's and add them

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    // VISITORS
    virtual void visit(AstTopScope* nodep) VL_OVERRIDE {
        m_topscopep = nodep;
        m_finder.main(m_topscopep);
        iterateChildren(nodep);
        m_topscopep = NULL;
    }
    virtual void visit(AstNodeModule* nodep) VL_OVERRIDE {
        // Create required actives and add to module
        // We can start ordering at a module, or a scope
        UINFO(4," MOD   "<<nodep<<endl);
        iterateChildren(nodep);
    }
    virtual void visit(AstActive* nodep) VL_OVERRIDE {
        UINFO(4,"   ACTIVE "<<nodep<<endl);
        V3Const::constifyExpensiveEdit(nodep);  // Remove duplicate clocks and such; sensesp() may change!
        AstSenTree* sensesp = nodep->sensesp();
        UASSERT_OBJ(sensesp, nodep, "NULL");
        if (sensesp->sensesp()
            && VN_IS(sensesp->sensesp(), SenItem)
            && VN_CAST(sensesp->sensesp(), SenItem)->isNever()) {
            // Never executing.  Kill it.
            UASSERT_OBJ(!sensesp->sensesp()->nextp(), nodep,
                        "Never senitem should be alone, else the never should be eliminated.");
            VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
            return;
        }
        // Copy combo tree to settlement tree with duplicated statements
        if (sensesp->hasCombo()) {
            AstSenTree* newsentreep
                = new AstSenTree(nodep->fileline(),
                                 new AstSenItem(nodep->fileline(), AstSenItem::Settle()));
            AstActive* newp = new AstActive(nodep->fileline(),"settle", newsentreep);
            newp->sensesStorep(newsentreep);
            if (nodep->stmtsp()) newp->addStmtsp(nodep->stmtsp()->cloneTree(true));
            nodep->addNextHere(newp);
        }
        // Move the SENTREE for each active up to the global level.
        // This way we'll easily see what clock domains are identical
        AstSenTree* wantp = m_finder.getSenTree(nodep->fileline(), sensesp);
        UINFO(4,"   lookdone\n");
        if (wantp != sensesp) {
            // Move the active's contents to the other active
            UINFO(4,"   merge active "<<sensesp<<" into "<<wantp<<endl);
            if (nodep->sensesStorep()) {
                UASSERT_OBJ(sensesp == nodep->sensesStorep(), nodep,
                            "sensesStore should have been deleted earlier if different");
                sensesp->unlinkFrBack();
                // There may be other references to same sense tree,
                // we'll be removing all references when we get to them,
                // but don't dangle our pointer yet!
                pushDeletep(sensesp);
            }
            nodep->sensesp(wantp);
        }
        // No need to do statements under it, they're already moved.
        //iterateChildren(nodep);
    }
    virtual void visit(AstInitial* nodep) VL_OVERRIDE {  // LCOV_EXCL_LINE
        nodep->v3fatalSrc("Node should have been under ACTIVE");
    }
    virtual void visit(AstAssignAlias* nodep) VL_OVERRIDE {  // LCOV_EXCL_LINE
        nodep->v3fatalSrc("Node should have been under ACTIVE");
    }
    virtual void visit(AstAssignW* nodep) VL_OVERRIDE {  // LCOV_EXCL_LINE
        nodep->v3fatalSrc("Node should have been under ACTIVE");
    }
    virtual void visit(AstAlways* nodep) VL_OVERRIDE {  // LCOV_EXCL_LINE
        nodep->v3fatalSrc("Node should have been under ACTIVE");
    }
    virtual void visit(AstAlwaysPublic* nodep) VL_OVERRIDE {  // LCOV_EXCL_LINE
        nodep->v3fatalSrc("Node should have been under ACTIVE");
    }
    virtual void visit(AstFinal* nodep) VL_OVERRIDE {  // LCOV_EXCL_LINE
        nodep->v3fatalSrc("Node should have been deleted");
    }
    // Empty visitors, speed things up
    virtual void visit(AstNodeMath* nodep) VL_OVERRIDE {}
    virtual void visit(AstVarScope* nodep) VL_OVERRIDE {}
    //--------------------
    virtual void visit(AstNode* nodep) VL_OVERRIDE {
        iterateChildren(nodep);
    }
public:
    // CONSTRUCTORS
    explicit ActiveTopVisitor(AstNetlist* nodep) {
        m_topscopep = NULL;
        iterate(nodep);
    }
    virtual ~ActiveTopVisitor() {}
};

//######################################################################
// Active class functions

void V3ActiveTop::activeTopAll(AstNetlist* nodep) {
    UINFO(2,__FUNCTION__<<": "<<endl);
    {
        ActiveTopVisitor visitor (nodep);
    }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("activetop", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}
