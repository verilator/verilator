// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Break always into sensitivity active domains
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

#include "V3ActiveTop.h"

#include "V3Ast.h"
#include "V3Const.h"
#include "V3Global.h"
#include "V3SenTree.h"

//######################################################################
// Active class functions

class ActiveTopVisitor final : public VNVisitor {
private:
    // NODE STATE
    //  Entire netlist
    //   AstNode::user()                bool. True if processed
    //  Each call to V3Const::constify
    //   AstNode::user4()               Used by V3Const::constify, called below
    const VNUser1InUse m_inuser1;

    // STATE
    SenTreeFinder m_finder;  // Find global sentree's / add them under the AstTopScope

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    // VISITORS
    virtual void visit(AstNodeModule* nodep) override {
        // Create required actives and add to module
        // We can start ordering at a module, or a scope
        UINFO(4, " MOD   " << nodep << endl);
        iterateChildren(nodep);
    }
    virtual void visit(AstActive* nodep) override {
        UINFO(4, "   ACTIVE " << nodep << endl);
        // Remove duplicate clocks and such; sensesp() may change!
        V3Const::constifyExpensiveEdit(nodep);
        AstSenTree* const sensesp = nodep->sensesp();
        UASSERT_OBJ(sensesp, nodep, "nullptr");
        if (sensesp->sensesp() && sensesp->sensesp()->isNever()) {
            // Never executing.  Kill it.
            UASSERT_OBJ(!sensesp->sensesp()->nextp(), nodep,
                        "Never senitem should be alone, else the never should be eliminated.");
            VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
            return;
        }
        // Copy combo tree to settlement tree with duplicated statements
        if (sensesp->hasCombo()) {
            AstSenTree* const newsentreep = new AstSenTree(
                nodep->fileline(), new AstSenItem(nodep->fileline(), AstSenItem::Settle()));
            AstActive* const newp = new AstActive(nodep->fileline(), "settle", newsentreep);
            newp->sensesStorep(newsentreep);
            if (nodep->stmtsp()) newp->addStmtsp(nodep->stmtsp()->cloneTree(true));
            nodep->addNextHere(newp);
        }
        // Move the SENTREE for each active up to the global level.
        // This way we'll easily see what clock domains are identical
        AstSenTree* const wantp = m_finder.getSenTree(sensesp);
        UINFO(4, "   lookdone\n");
        if (wantp != sensesp) {
            // Move the active's contents to the other active
            UINFO(4, "   merge active " << sensesp << " into " << wantp << endl);
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
        // iterateChildren(nodep);
    }
    virtual void visit(AstNodeProcedure* nodep) override {  // LCOV_EXCL_LINE
        nodep->v3fatalSrc("Node should have been under ACTIVE");
    }
    virtual void visit(AstAssignAlias* nodep) override {  // LCOV_EXCL_LINE
        nodep->v3fatalSrc("Node should have been under ACTIVE");
    }
    virtual void visit(AstAssignW* nodep) override {  // LCOV_EXCL_LINE
        nodep->v3fatalSrc("Node should have been under ACTIVE");
    }
    virtual void visit(AstAlwaysPublic* nodep) override {  // LCOV_EXCL_LINE
        nodep->v3fatalSrc("Node should have been under ACTIVE");
    }
    //--------------------
    virtual void visit(AstNodeMath*) override {}  // Accelerate
    virtual void visit(AstVarScope*) override {}  // Accelerate
    virtual void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit ActiveTopVisitor(AstNetlist* nodep) { iterate(nodep); }
    virtual ~ActiveTopVisitor() override = default;
};

//######################################################################
// Active class functions

void V3ActiveTop::activeTopAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    { ActiveTopVisitor{nodep}; }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("activetop", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}
