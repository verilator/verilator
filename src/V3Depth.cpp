// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Prevent very deep expressions
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
// V3Depth's Transformations:
//
// Each module:
//      For each wide OP, assign a temporary variable.
//      For each deep expression, assign expression to temporary.
// Each CFunc:
//      Any statements that need "this" are marked non-static
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3Depth.h"

#include "V3Ast.h"
#include "V3Global.h"
#include "V3UniqueNames.h"

#include <algorithm>

//######################################################################

class DepthVisitor final : public VNVisitor {
private:
    // NODE STATE

    // STATE
    AstCFunc* m_cfuncp = nullptr;  // Current block
    AstMTaskBody* m_mtaskbodyp = nullptr;  // Current mtaskbody
    AstNode* m_stmtp = nullptr;  // Current statement
    int m_depth = 0;  // How deep in an expression
    int m_maxdepth = 0;  // Maximum depth in an expression
    V3UniqueNames m_tempNames;  // For generating unique temporary variable names

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    void createDeepTemp(AstNode* nodep) {
        UINFO(6, "  Deep  " << nodep << endl);
        // if (debug() >= 9) nodep->dumpTree(cout, "deep:");
        AstVar* const varp = new AstVar{nodep->fileline(), VVarType::STMTTEMP,
                                        m_tempNames.get(nodep), nodep->dtypep()};
        if (m_cfuncp) {
            m_cfuncp->addInitsp(varp);
        } else if (m_mtaskbodyp) {
            m_mtaskbodyp->addStmtsFirstp(varp);
        } else {
            nodep->v3fatalSrc("Deep expression not under a function");
        }
        // Replace node tree with reference to var
        AstVarRef* const newp = new AstVarRef{nodep->fileline(), varp, VAccess::READ};
        nodep->replaceWith(newp);
        // Put assignment before the referencing statement
        AstAssign* const assp = new AstAssign{
            nodep->fileline(), new AstVarRef{nodep->fileline(), varp, VAccess::WRITE}, nodep};
        m_stmtp->addHereThisAsNext(assp);
    }

    // VISITORS
    virtual void visit(AstCFunc* nodep) override {
        VL_RESTORER(m_cfuncp);
        VL_RESTORER(m_mtaskbodyp);
        {
            m_cfuncp = nodep;
            m_mtaskbodyp = nullptr;
            m_depth = 0;
            m_maxdepth = 0;
            m_tempNames.reset();
            iterateChildren(nodep);
        }
    }
    virtual void visit(AstMTaskBody* nodep) override {
        VL_RESTORER(m_cfuncp);
        VL_RESTORER(m_mtaskbodyp);
        {
            m_cfuncp = nullptr;
            m_mtaskbodyp = nodep;
            m_depth = 0;
            m_maxdepth = 0;
            // We don't reset the names, as must share across tasks
            iterateChildren(nodep);
        }
    }
    void visitStmt(AstNodeStmt* nodep) {
        VL_RESTORER(m_stmtp);
        {
            m_stmtp = nodep;
            m_depth = 0;
            m_maxdepth = 0;
            iterateChildren(nodep);
        }
    }
    virtual void visit(AstNodeStmt* nodep) override {
        if (!nodep->isStatement()) {
            iterateChildren(nodep);
        } else {
            visitStmt(nodep);
        }
    }
    // Operators
    virtual void visit(AstNodeTermop* nodep) override {}
    virtual void visit(AstNodeMath* nodep) override {
        // We have some operator defines that use 2 parens, so += 2.
        {
            VL_RESTORER(m_depth);
            m_depth += 2;
            if (m_depth > m_maxdepth) m_maxdepth = m_depth;
            iterateChildren(nodep);
        }
        if (m_stmtp && (v3Global.opt.compLimitParens() >= 1)  // Else compiler doesn't need it
            && (m_maxdepth - m_depth) > v3Global.opt.compLimitParens()
            && !VN_IS(nodep->backp(), NodeStmt)  // Not much point if we're about to use it
        ) {
            m_maxdepth = m_depth;
            createDeepTemp(nodep);
        }
    }

    //--------------------
    // Marking of non-static functions (because they might need "this")
    // (Here instead of new visitor after V3Descope just to avoid another visitor)
    void needNonStaticFunc(AstNode* nodep) {
        UASSERT_OBJ(m_cfuncp, nodep, "Non-static accessor not under a function");
        if (m_cfuncp->isStatic()) {
            UINFO(5, "Mark non-public due to " << nodep << endl);
            m_cfuncp->isStatic(false);
        }
    }
    virtual void visit(AstUCFunc* nodep) override {
        needNonStaticFunc(nodep);
        iterateChildren(nodep);
    }
    virtual void visit(AstUCStmt* nodep) override {
        needNonStaticFunc(nodep);
        visitStmt(nodep);
    }

    //--------------------
    // Default: Just iterate
    virtual void visit(AstVar*) override {}  // Don't hit varrefs under vars
    virtual void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit DepthVisitor(AstNetlist* nodep)
        : m_tempNames{"__Vdeeptemp"} {
        iterate(nodep);
    }
    virtual ~DepthVisitor() override = default;
};

//######################################################################
// Depth class functions

void V3Depth::depthAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    { DepthVisitor{nodep}; }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("depth", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 6);
}
