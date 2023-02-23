// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Replace increments/decrements with new variables
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2023 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
// V3LinkInc's Transformations:
//
//      prepost_expr_visit
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
//      prepost_stmt_visit
//        PREADD/PRESUB/POSTADD/POSTSUB
//          Increment/decrement the current variable by the given value.
//          The order (pre/post) doesn't matter outside statements thus
//          the pre/post operations are treated equally and there is no
//          need for a temporary variable.
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3LinkInc.h"

#include "V3Ast.h"
#include "V3Global.h"

#include <algorithm>

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################

class LinkIncVisitor final : public VNVisitor {
private:
    // TYPES
    enum InsertMode : uint8_t {
        IM_BEFORE,  // Pointing at statement ref is in, insert before this
        IM_AFTER,  // Pointing at last inserted stmt, insert after
        IM_WHILE_PRECOND  // Pointing to for loop, add to body end
    };

    // STATE
    AstNodeFTask* m_ftaskp = nullptr;  // Function or task we're inside
    int m_modIncrementsNum = 0;  // Var name counter
    InsertMode m_insMode = IM_BEFORE;  // How to insert
    AstNode* m_insStmtp = nullptr;  // Where to insert statement
    bool m_unsupportedHere = false;  // Used to detect where it's not supported yet

    // METHODS
    void insertBeforeStmt(AstNode* nodep, AstNode* newp) {
        // Return node that must be visited, if any
        // See also AstNode::addBeforeStmt; this predates that function
        if (debug() >= 9) newp->dumpTree("-  newstmt: ");
        UASSERT_OBJ(m_insStmtp, nodep, "Function not underneath a statement");
        if (m_insMode == IM_BEFORE) {
            // Add the whole thing before insertAt
            if (debug() >= 9) newp->dumpTree("-  newfunc: ");
            m_insStmtp->addHereThisAsNext(newp);
        } else if (m_insMode == IM_AFTER) {
            m_insStmtp->addNextHere(newp);
        } else if (m_insMode == IM_WHILE_PRECOND) {
            AstWhile* const whilep = VN_AS(m_insStmtp, While);
            UASSERT_OBJ(whilep, nodep, "Insert should be under WHILE");
            whilep->addPrecondsp(newp);
        } else {
            nodep->v3fatalSrc("Unknown InsertMode");
        }
    }

    // VISITORS
    void visit(AstNodeModule* nodep) override {
        VL_RESTORER(m_modIncrementsNum);
        m_modIncrementsNum = 0;
        iterateChildren(nodep);
    }
    void visit(AstNodeFTask* nodep) override {
        VL_RESTORER(m_ftaskp);
        m_ftaskp = nodep;
        iterateChildren(nodep);
    }
    void visit(AstWhile* nodep) override {
        // Special, as statements need to be put in different places
        // Preconditions insert first just before themselves (the normal
        // rule for other statement types)
        m_insStmtp = nullptr;  // First thing should be new statement
        iterateAndNextNull(nodep->precondsp());
        // Conditions insert first at end of precondsp.
        m_insMode = IM_WHILE_PRECOND;
        m_insStmtp = nodep;
        iterateAndNextNull(nodep->condp());
        // Body insert just before themselves
        m_insStmtp = nullptr;  // First thing should be new statement
        iterateAndNextNull(nodep->stmtsp());
        iterateAndNextNull(nodep->incsp());
        // Done the loop
        m_insStmtp = nullptr;  // Next thing should be new statement
    }
    void visit(AstForeach* nodep) override {
        // Special, as statements need to be put in different places
        // Body insert just before themselves
        m_insStmtp = nullptr;  // First thing should be new statement
        iterateChildren(nodep);
        // Done the loop
        m_insStmtp = nullptr;  // Next thing should be new statement
    }
    void visit(AstJumpBlock* nodep) override {
        // Special, as statements need to be put in different places
        // Body insert just before themselves
        m_insStmtp = nullptr;  // First thing should be new statement
        iterateChildren(nodep);
        // Done the loop
        m_insStmtp = nullptr;  // Next thing should be new statement
    }
    void visit(AstNodeIf* nodep) override {
        m_insStmtp = nodep;
        iterateAndNextNull(nodep->condp());
        m_insStmtp = nullptr;
        iterateAndNextNull(nodep->thensp());
        iterateAndNextNull(nodep->elsesp());
        m_insStmtp = nullptr;
    }
    void visit(AstCaseItem* nodep) override {
        m_insMode = IM_BEFORE;
        {
            VL_RESTORER(m_unsupportedHere);
            m_unsupportedHere = true;
            iterateAndNextNull(nodep->condsp());
        }
        m_insStmtp = nullptr;  // Next thing should be new statement
        iterateAndNextNull(nodep->stmtsp());
    }
    void visit(AstNodeFor* nodep) override {  // LCOV_EXCL_LINE
        nodep->v3fatalSrc(
            "For statements should have been converted to while statements in V3Begin.cpp");
    }
    void visit(AstDelay* nodep) override {
        m_insStmtp = nodep;
        iterateAndNextNull(nodep->lhsp());
        m_insStmtp = nullptr;
        iterateAndNextNull(nodep->stmtsp());
        m_insStmtp = nullptr;
    }
    void visit(AstEventControl* nodep) override {
        m_insStmtp = nullptr;
        iterateAndNextNull(nodep->stmtsp());
        m_insStmtp = nullptr;
    }
    void visit(AstWait* nodep) override {
        m_insStmtp = nodep;
        iterateAndNextNull(nodep->condp());
        m_insStmtp = nullptr;
        iterateAndNextNull(nodep->stmtsp());
        m_insStmtp = nullptr;
    }
    void visit(AstNodeStmt* nodep) override {
        m_insMode = IM_BEFORE;
        m_insStmtp = nodep;
        iterateChildren(nodep);
        m_insStmtp = nullptr;  // Next thing should be new statement
    }
    void unsupported_visit(AstNode* nodep) {
        VL_RESTORER(m_unsupportedHere);
        m_unsupportedHere = true;
        UINFO(9, "Marking unsupported " << nodep << endl);
        iterateChildren(nodep);
    }
    void visit(AstLogAnd* nodep) override { unsupported_visit(nodep); }
    void visit(AstLogOr* nodep) override { unsupported_visit(nodep); }
    void visit(AstLogEq* nodep) override { unsupported_visit(nodep); }
    void visit(AstLogIf* nodep) override { unsupported_visit(nodep); }
    void visit(AstNodeCond* nodep) override { unsupported_visit(nodep); }
    void visit(AstPropSpec* nodep) override { unsupported_visit(nodep); }
    void prepost_visit(AstNodeTriop* nodep) {
        // Check if we are underneath a statement
        if (!m_insStmtp) {
            prepost_stmt_visit(nodep);
        } else {
            prepost_expr_visit(nodep);
        }
    }
    void prepost_stmt_visit(AstNodeTriop* nodep) {
        iterateChildren(nodep);

        // Currently we can't reference the target, so we just copy the AST both for read and
        // write, but doing so would double any side-effects, so as a safety measure all
        // statements which could have side-effects are banned at the moment.
        if (!nodep->rhsp()->isTreePureRecurse()) {
            nodep->rhsp()->v3warn(E_UNSUPPORTED,
                                  "Unsupported: Inc/Dec of expression with side-effects");
            return;
        }

        AstConst* const constp = VN_AS(nodep->lhsp(), Const);
        UASSERT_OBJ(nodep, constp, "Expecting CONST");
        AstConst* const newconstp = constp->cloneTree(true);

        AstNodeExpr* const storeTop = nodep->thsp()->unlinkFrBack();
        AstNodeExpr* const valuep = nodep->rhsp()->unlinkFrBack();

        AstAssign* assignp;
        if (VN_IS(nodep, PreSub) || VN_IS(nodep, PostSub)) {
            assignp = new AstAssign{nodep->fileline(), storeTop,
                                    new AstSub{nodep->fileline(), valuep, newconstp}};
        } else {
            assignp = new AstAssign{nodep->fileline(), storeTop,
                                    new AstAdd{nodep->fileline(), valuep, newconstp}};
        }
        nodep->replaceWith(assignp);
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
    }
    void prepost_expr_visit(AstNodeTriop* nodep) {
        iterateChildren(nodep);

        // Currently we can't reference the target, so we just copy the AST both for read and
        // write, but doing so would double any side-effects, so as a safety measure all
        // statements which could have side-effects are banned at the moment.
        if (!nodep->rhsp()->isTreePureRecurse()) {
            nodep->rhsp()->v3warn(E_UNSUPPORTED,
                                  "Unsupported: Inc/Dec of expression with side-effects");
            return;
        }

        const AstNodeVarRef* varrefp = nullptr;
        if (m_unsupportedHere || !(varrefp = VN_CAST(nodep->rhsp(), VarRef))) {
            nodep->v3warn(E_UNSUPPORTED, "Unsupported: Incrementation in this context.");
            return;
        }

        AstConst* const constp = VN_AS(nodep->lhsp(), Const);
        UASSERT_OBJ(nodep, constp, "Expecting CONST");
        const AstNode* const backp = nodep->backp();
        AstConst* const newconstp = constp->cloneTree(true);

        // Prepare a temporary variable
        FileLine* const fl = backp->fileline();
        const string name = string("__Vincrement") + cvtToStr(++m_modIncrementsNum);
        AstVar* const varp = new AstVar{fl, VVarType::BLOCKTEMP, name, VFlagChildDType{},
                                        varrefp->varp()->subDTypep()->cloneTree(true)};
        if (m_ftaskp) varp->funcLocal(true);

        // Declare the variable
        insertBeforeStmt(nodep, varp);

        // Define what operation will we be doing
        AstNodeExpr* operp;
        if (VN_IS(nodep, PostSub) || VN_IS(nodep, PreSub)) {
            operp = new AstSub{fl, new AstVarRef{fl, varrefp->varp(), VAccess::READ}, newconstp};
        } else {
            operp = new AstAdd{fl, new AstVarRef{fl, varrefp->varp(), VAccess::READ}, newconstp};
        }

        if (VN_IS(nodep, PreAdd) || VN_IS(nodep, PreSub)) {
            // PreAdd/PreSub operations
            // Immediately after declaration - increment it by one
            varp->addNextHere(new AstAssign{fl, new AstVarRef{fl, varrefp->varp(), VAccess::WRITE},
                                            new AstVarRef{fl, varp, VAccess::READ}});
            // Immediately after incrementing - assign it to the original variable
            varp->addNextHere(new AstAssign{fl, new AstVarRef{fl, varp, VAccess::WRITE}, operp});
        } else {
            // PostAdd/PostSub operations
            // assign the original variable to the temporary one
            varp->addNextHere(
                new AstAssign{fl, new AstVarRef{fl, varrefp->varp(), VAccess::WRITE}, operp});
            // Increment the original variable by one
            varp->addNextHere(new AstAssign{fl, new AstVarRef{fl, varp, VAccess::WRITE},
                                            new AstVarRef{fl, varrefp->varp(), VAccess::READ}});
        }

        // Replace the node with the temporary
        nodep->replaceWith(new AstVarRef{varrefp->fileline(), varp, VAccess::READ});
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
    }
    void visit(AstPreAdd* nodep) override { prepost_visit(nodep); }
    void visit(AstPostAdd* nodep) override { prepost_visit(nodep); }
    void visit(AstPreSub* nodep) override { prepost_visit(nodep); }
    void visit(AstPostSub* nodep) override { prepost_visit(nodep); }
    void visit(AstGenFor* nodep) override { iterateChildren(nodep); }
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit LinkIncVisitor(AstNetlist* nodep) { iterate(nodep); }
    ~LinkIncVisitor() override = default;
};

//######################################################################
// Task class functions

void V3LinkInc::linkIncrements(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    { LinkIncVisitor{nodep}; }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("linkinc", 0, dumpTree() >= 3);
}
