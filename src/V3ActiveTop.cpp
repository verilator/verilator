// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Break always into sensitivity active domains
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
// V3Active's Transformations:
//
// Note this can be called multiple times.
//   Across all ACTIVES
//      SenTrees are now under each ACTIVE statement, we want them global:
//          Find SenTree in under global TopScope, or create it there
//          Move SenTree the global SenTree
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3ActiveTop.h"

#include "V3Const.h"
#include "V3SenTree.h"

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// Active class functions

class ActiveTopVisitor final : public VNVisitor {
    // STATE
    SenTreeFinder m_finder;  // Find global sentree's / add them under the AstTopScope

    // METHODS

    static bool isInitial(AstNode* nodep) {
        const VNUser1InUse user1InUse;
        // Return true if no variables that read.
        return nodep->forall([&](const AstVarRef* refp) -> bool {
            AstVarScope* const vscp = refp->varScopep();
            // Note: Use same heuristic as ordering does to ignore written variables
            // TODO: Use live variable analysis.
            if (refp->access().isWriteOnly()) {
                vscp->user1(true);
                return true;
            }
            // Read or ReadWrite: OK if written before
            return vscp->user1();
        });
    }

    // VISITORS
    void visit(AstNodeModule* nodep) override {
        // Create required actives and add to module
        // We can start ordering at a module, or a scope
        UINFO(4, " MOD   " << nodep << endl);
        iterateChildren(nodep);
    }
    void visit(AstActive* nodep) override {
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

        // If this is combinational logic that does not read any variables, then it really is an
        // initial block in disguise, so move such logic under an Initial AstActive, V3Order would
        // prune these otherwise.
        // TODO: we should warn for these if they were 'always @*' as some (including strictly
        //       compliant) simulators will never execute these.
        if (nodep->sensesp()->hasCombo()) {
            FileLine* const flp = nodep->fileline();
            AstActive* initialp = nullptr;
            for (AstNode *logicp = nodep->stmtsp(), *nextp; logicp; logicp = nextp) {
                nextp = logicp->nextp();
                if (!isInitial(logicp)) continue;
                if (!initialp) initialp = new AstActive{flp, "", m_finder.getInitial()};
                initialp->addStmtsp(logicp->unlinkFrBack());
            }
            if (initialp) nodep->addHereThisAsNext(initialp);
        }
    }
    void visit(AstNodeProcedure* nodep) override {  // LCOV_EXCL_LINE
        nodep->v3fatalSrc("Node should have been under ACTIVE");
    }
    void visit(AstAssignAlias* nodep) override {  // LCOV_EXCL_LINE
        nodep->v3fatalSrc("Node should have been under ACTIVE");
    }
    void visit(AstAssignW* nodep) override {  // LCOV_EXCL_LINE
        nodep->v3fatalSrc("Node should have been under ACTIVE");
    }
    void visit(AstAlwaysPublic* nodep) override {  // LCOV_EXCL_LINE
        nodep->v3fatalSrc("Node should have been under ACTIVE");
    }
    //--------------------
    void visit(AstNodeExpr*) override {}  // Accelerate
    void visit(AstVarScope*) override {}  // Accelerate
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit ActiveTopVisitor(AstNetlist* nodep) { iterate(nodep); }
    ~ActiveTopVisitor() override = default;
};

//######################################################################
// Active class functions

void V3ActiveTop::activeTopAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    { ActiveTopVisitor{nodep}; }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("activetop", 0, dumpTreeLevel() >= 3);
}
