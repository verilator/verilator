// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Replace increments/decrements with new variables
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
// V3LinkInc's Transformations:
//
//      prepost_stmt_visit
//        PREADD/PRESUB
//          Create a temporary __VIncrementX variable, assign the value of
//          the current variable value to it, substitute the current
//          variable with the temporary one in the statement.
//          Increment/decrement the original variable with by the given
//          value.
//        POSTADD/POSTSUB
//          Increment/decrement the current variable by the given value.
//          Create a temporary __VIncrementX variable, assign the value of
//          of the current variable (after the operation) to it. Substitute
//          The original variable with the temporary one in the statement.
//      prepost_non_stmt_visit
//        PREADD/PRESUB/POSTADD/POSTSUB
//          Increment/decrement the current variable by the given value.
//          The order (pre/post) doesn't matter outside statements thus
//          the pre/post operations are treated equally and there is no
//          need for a temporary variable.
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3Global.h"
#include "V3LinkInc.h"
#include "V3Ast.h"

#include <algorithm>

//######################################################################

class LinkIncVisitor : public AstNVisitor {
private:
    // TYPES
    enum InsertMode {
        IM_BEFORE,  // Pointing at statement ref is in, insert before this
        IM_AFTER,  // Pointing at last inserted stmt, insert after
        IM_WHILE_PRECOND  // Pointing to for loop, add to body end
    };

    // STATE
    int m_modIncrementsNum;  // Var name counter
    InsertMode m_insMode;  // How to insert
    AstNode* m_insStmtp;  // Where to insert statement
    bool m_unsupportedHere;  // Used to detect where it's not supported yet

private:
    void insertBeforeStmt(AstNode* nodep, AstNode* newp) {
        // Return node that must be visited, if any
        // See also AstNode::addBeforeStmt; this predates that function
        if (debug() >= 9) newp->dumpTree(cout, "-newstmt:");
        UASSERT_OBJ(m_insStmtp, nodep, "Function not underneath a statement");
        if (m_insMode == IM_BEFORE) {
            // Add the whole thing before insertAt
            if (debug() >= 9) newp->dumpTree(cout, "-newfunc:");
            m_insStmtp->addHereThisAsNext(newp);
        } else if (m_insMode == IM_AFTER) {
            m_insStmtp->addNextHere(newp);
        } else if (m_insMode == IM_WHILE_PRECOND) {
            AstWhile* whilep = VN_CAST(m_insStmtp, While);
            UASSERT_OBJ(whilep, nodep, "Insert should be under WHILE");
            whilep->addPrecondsp(newp);
        } else {
            nodep->v3fatalSrc("Unknown InsertMode");
        }
        m_insMode = IM_AFTER;
        m_insStmtp = newp;
    }

    // VISITORS
    virtual void visit(AstNodeModule* nodep) VL_OVERRIDE {
        // Reset increments count
        m_modIncrementsNum = 0;
        iterateChildren(nodep);
    }
    virtual void visit(AstWhile* nodep) VL_OVERRIDE {
        // Special, as statements need to be put in different places
        // Preconditions insert first just before themselves (the normal
        // rule for other statement types)
        m_insStmtp = NULL;  // First thing should be new statement
        iterateAndNextNull(nodep->precondsp());
        // Conditions insert first at end of precondsp.
        m_insMode = IM_WHILE_PRECOND;
        m_insStmtp = nodep;
        iterateAndNextNull(nodep->condp());
        // Body insert just before themselves
        m_insStmtp = NULL;  // First thing should be new statement
        iterateAndNextNull(nodep->bodysp());
        iterateAndNextNull(nodep->incsp());
        // Done the loop
        m_insStmtp = NULL;  // Next thing should be new statement
    }
    virtual void visit(AstNodeFor* nodep) VL_OVERRIDE {  // LCOV_EXCL_LINE
        nodep->v3fatalSrc(
            "For statements should have been converted to while statements in V3Begin.cpp");
    }
    virtual void visit(AstNodeStmt* nodep) VL_OVERRIDE {
        if (!nodep->isStatement()) {
            iterateChildren(nodep);
            return;
        }
        m_insMode = IM_BEFORE;
        m_insStmtp = nodep;
        iterateChildren(nodep);
        m_insStmtp = NULL;  // Next thing should be new statement
    }
    virtual void visit(AstNodeBlock* nodep) VL_OVERRIDE {
        AstNode* insStmtp_prev = m_insStmtp;
        {
            m_insStmtp = NULL;
            iterateChildren(nodep);
        }
        m_insStmtp = insStmtp_prev;
    }
    void unsupported_visit(AstNode* nodep) {
        m_unsupportedHere = true;
        UINFO(9, "Marking unsupported " << nodep << endl);
        iterateChildren(nodep);
        m_unsupportedHere = false;
    }
    virtual void visit(AstLogAnd* nodep) VL_OVERRIDE { unsupported_visit(nodep); }
    virtual void visit(AstLogOr* nodep) VL_OVERRIDE { unsupported_visit(nodep); }
    virtual void visit(AstLogEq* nodep) VL_OVERRIDE { unsupported_visit(nodep); }
    virtual void visit(AstLogIf* nodep) VL_OVERRIDE { unsupported_visit(nodep); }
    virtual void visit(AstNodeCond* nodep) VL_OVERRIDE { unsupported_visit(nodep); }
    void prepost_visit(AstNodeTriop* nodep) {
        // Check if we are underneath a statement
        if (!m_insStmtp) {
            prepost_non_stmt_visit(nodep);
        } else {
            prepost_stmt_visit(nodep);
        }
    }
    void prepost_non_stmt_visit(AstNodeTriop* nodep) {
        iterateChildren(nodep);

        AstConst* constp = VN_CAST(nodep->lhsp(), Const);
        UASSERT_OBJ(nodep, constp, "Expecting CONST");
        AstConst* newconstp = constp->cloneTree(true);

        AstNode* storetop = nodep->thsp();
        AstNode* valuep = nodep->rhsp();

        storetop->unlinkFrBack();
        valuep->unlinkFrBack();

        AstAssign* assignp;
        if (VN_IS(nodep, PreSub) || VN_IS(nodep, PostSub)) {
            assignp = new AstAssign(nodep->fileline(), storetop,
                                    new AstSub(nodep->fileline(), valuep, newconstp));
        } else {
            assignp = new AstAssign(nodep->fileline(), storetop,
                                    new AstAdd(nodep->fileline(), valuep, newconstp));
        }
        nodep->replaceWith(assignp);
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
    }
    void prepost_stmt_visit(AstNodeTriop* nodep) {
        iterateChildren(nodep);

        AstNodeVarRef* varrefp;
        if (m_unsupportedHere || !(varrefp = VN_CAST(nodep->rhsp(), VarRef))) {
            nodep->v3error("Unsupported: Incrementation in this context.");
            return;
        }

        AstConst* constp = VN_CAST(nodep->lhsp(), Const);
        UASSERT_OBJ(nodep, constp, "Expecting CONST");
        AstNode* backp = nodep->backp();
        AstConst* newconstp = constp->cloneTree(true);

        // Prepare a temporary variable
        FileLine* fl = backp->fileline();
        string name = string("__Vincrement") + cvtToStr(++m_modIncrementsNum);
        AstVar* varp = new AstVar(fl, AstVarType::BLOCKTEMP, name, varrefp->varp()->subDTypep());

        // Declare the variable
        insertBeforeStmt(nodep, varp);

        // Define what operation will we be doing
        AstNode* operp;
        if (VN_IS(nodep, PostSub) || VN_IS(nodep, PreSub)) {
            operp = new AstSub(fl, new AstVarRef(fl, varrefp->varp(), false), newconstp);
        } else {
            operp = new AstAdd(fl, new AstVarRef(fl, varrefp->varp(), false), newconstp);
        }

        if (VN_IS(nodep, PreAdd) || VN_IS(nodep, PreSub)) {
            // PreAdd/PreSub operations
            // Immediately after declaration - increment it by one
            m_insStmtp->addHereThisAsNext(new AstAssign(fl, new AstVarRef(fl, varp, true), operp));
            // Immediately after incrementing - assign it to the original variable
            m_insStmtp->addHereThisAsNext(new AstAssign(
                fl, new AstVarRef(fl, varrefp->varp(), true), new AstVarRef(fl, varp, false)));
        } else {
            // PostAdd/PostSub operations
            // assign the original variable to the temporary one
            m_insStmtp->addHereThisAsNext(new AstAssign(
                fl, new AstVarRef(fl, varp, true), new AstVarRef(fl, varrefp->varp(), false)));
            // Increment the original variable by one
            m_insStmtp->addHereThisAsNext(
                new AstAssign(fl, new AstVarRef(fl, varrefp->varp(), true), operp));
        }

        // Replace the node with the temporary
        nodep->replaceWith(new AstVarRef(varrefp->fileline(), varp, true));
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
    }
    virtual void visit(AstPreAdd* nodep) VL_OVERRIDE { prepost_visit(nodep); }
    virtual void visit(AstPostAdd* nodep) VL_OVERRIDE { prepost_visit(nodep); }
    virtual void visit(AstPreSub* nodep) VL_OVERRIDE { prepost_visit(nodep); }
    virtual void visit(AstPostSub* nodep) VL_OVERRIDE { prepost_visit(nodep); }
    virtual void visit(AstGenFor* nodep) VL_OVERRIDE { iterateChildren(nodep); }
    virtual void visit(AstNode* nodep) VL_OVERRIDE { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit LinkIncVisitor(AstNetlist* nodep) {
        m_modIncrementsNum = 0;
        m_insMode = IM_BEFORE;
        m_insStmtp = NULL;
        m_unsupportedHere = false;
        iterate(nodep);
    }
    virtual ~LinkIncVisitor() {}
};

//######################################################################
// Task class functions

void V3LinkInc::linkIncrements(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    { LinkIncVisitor bvisitor(nodep); }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("linkInc", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}
