// $Id$
//*************************************************************************
// DESCRIPTION: Verilator: Prevent very deep expressions
//
// Code available from: http://www.veripool.com/verilator
//
// AUTHORS: Wilson Snyder with Paul Wasson, Duane Gabli
//
//*************************************************************************
//
// Copyright 2003-2006 by Wilson Snyder.  This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// General Public License or the Perl Artistic License.
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
//
//*************************************************************************

#include "config.h"
#include <stdio.h>
#include <stdarg.h>
#include <unistd.h>
#include <algorithm>

#include "V3Global.h"
#include "V3Depth.h"
#include "V3Ast.h"

//######################################################################
// Depth state, as a visitor of each AstNode

class DepthVisitor : public AstNVisitor {
private:
    // NODE STATE

    // STATE
    AstModule*		m_modp;		// Current module
    AstCFunc*		m_funcp;	// Current block
    AstNode*		m_stmtp;	// Current statement
    int			m_depth;	// How deep in an expression
    int			m_maxdepth;	// Maximum depth in an expression

    //int debug() { return 9; }

    // MSVC++ has a limit of 100 parenthesis.  We have some operator
    // defines that use 2 parens.  Thus we can't have a expression deeper
    // then 50 operators.  We'll add some margin though.
    enum en { MAX_EXPR_DEPTH = 40 };	// Expressions deeper then this need temp

    // METHODS
    void createDeepTemp(AstNode* nodep) {
	UINFO(6,"  Deep  "<<nodep<<endl);
	//if (debug()>=9) nodep->dumpTree(cout,"deep:");

	string newvarname = ((string)"__Vdeeptemp__"+cvtToStr(m_modp->varNumGetInc()));
	AstVar* varp = new AstVar (nodep->fileline(), AstVarType::STMTTEMP, newvarname,
				   // Width, not widthMin, as we may be in middle of BITSEL expression which
				   // though it's one bit wide, needs the mask in the upper bits.
				   // (Someday we'll have a valid bitmask instead of widths....)
				   new AstRange(nodep->fileline(), nodep->width()-1, 0));
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
    virtual void visit(AstModule* nodep, AstNUser*) {
	UINFO(4," MOD   "<<nodep<<endl);
	m_modp = nodep;
	m_funcp = NULL;
	nodep->iterateChildren(*this);
    }
    virtual void visit(AstCFunc* nodep, AstNUser*) {
	m_funcp = nodep;
	m_depth = 0;
	m_maxdepth = 0;
	nodep->iterateChildren(*this);
    }
    virtual void visit(AstNodeStmt* nodep, AstNUser*) {
	m_depth = 0;
	m_maxdepth = 0;
	m_stmtp = nodep;
	nodep->iterateChildren(*this);
	m_stmtp = NULL;
    }
    // Operators
    virtual void visit(AstNodeTermop* nodep, AstNUser*) {
    }
    virtual void visit(AstNodeMath* nodep, AstNUser*) {
	m_depth++;
	if (m_depth>m_maxdepth) m_maxdepth=m_depth;
	nodep->iterateChildren(*this); 
	m_depth--;

	if ((m_maxdepth-m_depth) > MAX_EXPR_DEPTH
	    && m_stmtp
	    && !nodep->backp()->castNodeStmt()  // Not much point if we're about to use it
	    ) {
	    m_maxdepth = m_depth;
	    createDeepTemp(nodep);
	}
    }

    //--------------------
    // Default: Just iterate
    virtual void visit(AstVar* nodep, AstNUser*) {}	// Don't hit varrefs under vars
    virtual void visit(AstNode* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
    }

public:
    // CONSTUCTORS
    DepthVisitor(AstNode* nodep) {
	m_modp=NULL;
	m_funcp=NULL;
	m_stmtp=NULL;
	m_depth=0;
	m_maxdepth=0;
	//
	AstNode::userClearTree();	// userp() used on entire tree
	nodep->accept(*this);
    }
    virtual ~DepthVisitor() {}
};

//----------------------------------------------------------------------
// Top loop

//######################################################################
// Depth class functions

void V3Depth::depthAll(AstNetlist* nodep) {
    UINFO(2,__FUNCTION__<<": "<<endl);
    // We must do it in bottom-up module
    DepthVisitor visitor (nodep);
}
