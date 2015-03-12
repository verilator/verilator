// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Prevent very deep expressions
//
// Code available from: http://www.veripool.org/verilator
//
//*************************************************************************
//
// Copyright 2003-2015 by Wilson Snyder.  This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
//
// Verilator is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
//*************************************************************************
// V3Depth's Transformations:
//
// Each module:
//	For each wide OP, assign a temporary variable.
//	For each deep expression, assign expression to temporary.
// Each CFunc:
//	Any statements that need "this" are marked non-static
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"
#include <cstdio>
#include <cstdarg>
#include <unistd.h>
#include <algorithm>

#include "V3Global.h"
#include "V3Depth.h"
#include "V3Ast.h"

//######################################################################

class DepthVisitor : public AstNVisitor {
private:
    // NODE STATE

    // STATE
    AstNodeModule*	m_modp;		// Current module
    AstCFunc*		m_funcp;	// Current block
    AstNode*		m_stmtp;	// Current statement
    int			m_depth;	// How deep in an expression
    int			m_maxdepth;	// Maximum depth in an expression

    // METHODS
    static int debug() {
	static int level = -1;
	if (VL_UNLIKELY(level < 0)) level = v3Global.opt.debugSrcLevel(__FILE__);
	return level;
    }

    void createDeepTemp(AstNode* nodep) {
	UINFO(6,"  Deep  "<<nodep<<endl);
	//if (debug()>=9) nodep->dumpTree(cout,"deep:");

	string newvarname = ((string)"__Vdeeptemp"+cvtToStr(m_modp->varNumGetInc()));
	AstVar* varp = new AstVar (nodep->fileline(), AstVarType::STMTTEMP, newvarname,
				   // Width, not widthMin, as we may be in middle of BITSEL expression which
				   // though it's one bit wide, needs the mask in the upper bits.
				   // (Someday we'll have a valid bitmask instead of widths....)
				   // See t_func_crc for an example test that requires this
				   VFlagLogicPacked(), nodep->width());
	if (!m_funcp) nodep->v3fatalSrc("Deep expression not under a function");
	m_funcp->addInitsp(varp);
	// Replace node tree with reference to var
	AstVarRef* newp = new AstVarRef (nodep->fileline(), varp, false);
	nodep->replaceWith(newp);
	// Put assignment before the referencing statement
	AstAssign* assp = new AstAssign (nodep->fileline(),
					 new AstVarRef(nodep->fileline(), varp, true),
					 nodep);
	AstNRelinker linker2;
	m_stmtp->unlinkFrBack(&linker2);
	assp->addNext(m_stmtp);
	linker2.relink(assp);
    }

    // VISITORS
    virtual void visit(AstNodeModule* nodep, AstNUser*) {
	UINFO(4," MOD   "<<nodep<<endl);
	m_modp = nodep;
	m_funcp = NULL;
	nodep->iterateChildren(*this);
	m_modp = NULL;
    }
    virtual void visit(AstCFunc* nodep, AstNUser*) {
	m_funcp = nodep;
	m_depth = 0;
	m_maxdepth = 0;
	nodep->iterateChildren(*this);
	m_funcp = NULL;
    }
    void visitStmt(AstNodeStmt* nodep) {
	m_depth = 0;
	m_maxdepth = 0;
	m_stmtp = nodep;
	nodep->iterateChildren(*this);
	m_stmtp = NULL;
    }
    virtual void visit(AstNodeStmt* nodep, AstNUser*) {
	visitStmt(nodep);
    }
    // Operators
    virtual void visit(AstNodeTermop* nodep, AstNUser*) {
    }
    virtual void visit(AstNodeMath* nodep, AstNUser*) {
	// We have some operator defines that use 2 parens, so += 2.
	m_depth += 2;
	if (m_depth>m_maxdepth) m_maxdepth=m_depth;
	nodep->iterateChildren(*this);
	m_depth -= 2;

	if (m_stmtp
	    && (v3Global.opt.compLimitParens() >= 1)	// Else compiler doesn't need it
	    && (m_maxdepth-m_depth) > v3Global.opt.compLimitParens()
	    && !nodep->backp()->castNodeStmt()  // Not much point if we're about to use it
	    ) {
	    m_maxdepth = m_depth;
	    createDeepTemp(nodep);
	}
    }

    //--------------------
    // Marking of non-static functions (because they might need "this")
    // (Here just to avoid another iteration)
    void needNonStaticFunc(AstNode* nodep) {
	if (!m_funcp) nodep->v3fatalSrc("Non-static accessor not under a function");
	if (m_funcp->isStatic()) {
	    UINFO(5,"Mark non-public due to "<<nodep<<endl);
	    m_funcp->isStatic(false);
	}
    }
    virtual void visit(AstUCFunc* nodep, AstNUser*) {
	needNonStaticFunc(nodep);
	nodep->iterateChildren(*this);
    }
    virtual void visit(AstUCStmt* nodep, AstNUser*) {
	needNonStaticFunc(nodep);
	visitStmt(nodep);
    }

    //--------------------
    // Default: Just iterate
    virtual void visit(AstVar* nodep, AstNUser*) {}	// Don't hit varrefs under vars
    virtual void visit(AstNode* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
    }

public:
    // CONSTUCTORS
    DepthVisitor(AstNetlist* nodep) {
	m_modp=NULL;
	m_funcp=NULL;
	m_stmtp=NULL;
	m_depth=0;
	m_maxdepth=0;
	//
	nodep->accept(*this);
    }
    virtual ~DepthVisitor() {}
};

//######################################################################
// Depth class functions

void V3Depth::depthAll(AstNetlist* nodep) {
    UINFO(2,__FUNCTION__<<": "<<endl);
    DepthVisitor visitor (nodep);
    V3Global::dumpCheckGlobalTree("depth.tree", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 6);
}
