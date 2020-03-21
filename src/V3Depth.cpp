// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Prevent very deep expressions
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

#include "V3Global.h"
#include "V3Depth.h"
#include "V3Ast.h"

#include <algorithm>
#include <cstdarg>

//######################################################################

class DepthVisitor : public AstNVisitor {
private:
    // NODE STATE

    // STATE
    AstNodeModule*      m_modp;         // Current module
    AstCFunc*           m_funcp;        // Current block
    AstNode*            m_stmtp;        // Current statement
    int                 m_depth;        // How deep in an expression
    int                 m_maxdepth;     // Maximum depth in an expression

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    void createDeepTemp(AstNode* nodep) {
        UINFO(6,"  Deep  "<<nodep<<endl);
        //if (debug()>=9) nodep->dumpTree(cout, "deep:");

        string newvarname = (string("__Vdeeptemp")+cvtToStr(m_modp->varNumGetInc()));
        AstVar* varp = new AstVar(nodep->fileline(), AstVarType::STMTTEMP, newvarname,
                                  // Width, not widthMin, as we may be in
                                  // middle of BITSEL expression which though
                                  // it's one bit wide, needs the mask in the
                                  // upper bits.  (Someday we'll have a valid
                                  // bitmask instead of widths....)
                                  // See t_func_crc for an example test that requires this
                                  VFlagLogicPacked(), nodep->width());
        UASSERT_OBJ(m_funcp, nodep, "Deep expression not under a function");
        m_funcp->addInitsp(varp);
        // Replace node tree with reference to var
        AstVarRef* newp = new AstVarRef(nodep->fileline(), varp, false);
        nodep->replaceWith(newp);
        // Put assignment before the referencing statement
        AstAssign* assp = new AstAssign(nodep->fileline(),
                                        new AstVarRef(nodep->fileline(), varp, true),
                                        nodep);
        AstNRelinker linker2;
        m_stmtp->unlinkFrBack(&linker2);
        assp->addNext(m_stmtp);
        linker2.relink(assp);
    }

    // VISITORS
    virtual void visit(AstNodeModule* nodep) VL_OVERRIDE {
        UINFO(4," MOD   "<<nodep<<endl);
        AstNodeModule* origModp = m_modp;
        {
            m_modp = nodep;
            m_funcp = NULL;
            iterateChildren(nodep);
        }
        m_modp = origModp;
    }
    virtual void visit(AstCFunc* nodep) VL_OVERRIDE {
        m_funcp = nodep;
        m_depth = 0;
        m_maxdepth = 0;
        iterateChildren(nodep);
        m_funcp = NULL;
    }
    void visitStmt(AstNodeStmt* nodep) {
        m_depth = 0;
        m_maxdepth = 0;
        m_stmtp = nodep;
        iterateChildren(nodep);
        m_stmtp = NULL;
    }
    virtual void visit(AstNodeStmt* nodep) VL_OVERRIDE {
        if (!nodep->isStatement()) {
            iterateChildren(nodep);
        } else {
            visitStmt(nodep);
        }
    }
    // Operators
    virtual void visit(AstNodeTermop* nodep) VL_OVERRIDE {
    }
    virtual void visit(AstNodeMath* nodep) VL_OVERRIDE {
        // We have some operator defines that use 2 parens, so += 2.
        m_depth += 2;
        if (m_depth>m_maxdepth) m_maxdepth = m_depth;
        iterateChildren(nodep);
        m_depth -= 2;

        if (m_stmtp
            && (v3Global.opt.compLimitParens() >= 1)  // Else compiler doesn't need it
            && (m_maxdepth-m_depth) > v3Global.opt.compLimitParens()
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
        UASSERT_OBJ(m_funcp, nodep, "Non-static accessor not under a function");
        if (m_funcp->isStatic().trueUnknown()) {
            UINFO(5,"Mark non-public due to "<<nodep<<endl);
            m_funcp->isStatic(false);
        }
    }
    virtual void visit(AstUCFunc* nodep) VL_OVERRIDE {
        needNonStaticFunc(nodep);
        iterateChildren(nodep);
    }
    virtual void visit(AstUCStmt* nodep) VL_OVERRIDE {
        needNonStaticFunc(nodep);
        visitStmt(nodep);
    }

    //--------------------
    // Default: Just iterate
    virtual void visit(AstVar* nodep) VL_OVERRIDE {}  // Don't hit varrefs under vars
    virtual void visit(AstNode* nodep) VL_OVERRIDE {
        iterateChildren(nodep);
    }

public:
    // CONSTRUCTORS
    explicit DepthVisitor(AstNetlist* nodep) {
        m_modp = NULL;
        m_funcp = NULL;
        m_stmtp = NULL;
        m_depth = 0;
        m_maxdepth = 0;
        //
        iterate(nodep);
    }
    virtual ~DepthVisitor() {}
};

//######################################################################
// Depth class functions

void V3Depth::depthAll(AstNetlist* nodep) {
    UINFO(2,__FUNCTION__<<": "<<endl);
    {
        DepthVisitor visitor (nodep);
    }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("depth", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 6);
}
