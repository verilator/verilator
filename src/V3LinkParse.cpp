//*************************************************************************
// DESCRIPTION: Verilator: Parse module/signal name references
//
// Code available from: http://www.veripool.org/verilator
//
// AUTHORS: Wilson Snyder with Paul Wasson, Duane Gabli
//
//*************************************************************************
//
// Copyright 2003-2009 by Wilson Snyder.  This program is free software; you can
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
// LinkParse TRANSFORMATIONS:
//	Top-down traversal
//	    Replace ParseRef with VarRef, VarXRef, FuncRef or TaskRef
//	    TASKREF(PARSEREF(DOT(TEXTa,TEXTb))) -> TASKREF(a,b)
//	    PARSEREF(TEXTa) -> VARREF(a)
//	    PARSEREF(DOT(TEXTa,TEXTb)) -> VARXREF("a","b")
//	    PARSEREF(DOT(DOT(TEXTa,TEXTb),TEXTc)) -> VARXREF("a.b","c")
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"
#include <cstdio>
#include <cstdarg>
#include <unistd.h>
#include <map>
#include <algorithm>
#include <vector>

#include "V3Global.h"
#include "V3LinkParse.h"
#include "V3Ast.h"

//######################################################################
// Link state, as a visitor of each AstNode

class LinkParseVisitor : public AstNVisitor {
private:
    // NODE STATE
    // Cleared on netlist
    //  AstNode::user()		-> bool.  True if processed
    AstUser1InUse	m_inuser1;

    // STATE
    string	m_dotText;	// Dotted module text we are building for a dotted node, passed up
    bool	m_inModDot;	// We're inside module part of dotted name
    AstParseRefExp m_exp;	// Type of data we're looking for
    AstText*	m_baseTextp;	// Lowest TEXT node that needs replacement with varref

    // METHODS
    static int debug() {
	static int level = -1;
	if (VL_UNLIKELY(level < 0)) level = v3Global.opt.debugSrcLevel(__FILE__);
	return level;
    }

    void checkExpected(AstNode* nodep) {
	if (m_exp != AstParseRefExp::NONE) {
	    nodep->v3fatalSrc("Tree syntax error: Not expecting "<<nodep->type()<<" under a "<<nodep->backp()->type());
	    m_exp = AstParseRefExp::NONE;
	}
    }

    // VISITs
    virtual void visit(AstNodeFTaskRef* nodep, AstNUser*) {
	if (!nodep->user1()) {
	    nodep->user1(true);   // Process only once.
	    UINFO(5,"   "<<nodep<<endl);
	    checkExpected(nodep);
	    // Due to a need to get the arguments, the ParseRefs are under here,
	    // rather than the NodeFTaskRef under the ParseRef.
	    if (nodep->namep()) {
		m_exp = AstParseRefExp::FUNC;
		nodep->namep()->accept(*this);  // No next, we don't want to do the edit
		m_exp = AstParseRefExp::NONE;
		if (!m_baseTextp) nodep->v3fatalSrc("No TEXT found to indicate function name");
		nodep->name(m_baseTextp->text());
		nodep->dotted(m_dotText);
		nodep->namep()->unlinkFrBack()->deleteTree(); m_baseTextp=NULL;
	    }
	    nodep->iterateChildren(*this);
	}
    }
    virtual void visit(AstParseRef* nodep, AstNUser*) {
	// VarRef: Parse its reference
	UINFO(5,"   "<<nodep<<endl);
	// May be a varref inside a select, etc, so save state and recurse
	string		oldText = m_dotText;
	bool		oldDot = m_inModDot;
	AstParseRefExp  oldExp = m_exp;
	AstText*	oldBasep = m_baseTextp;
	{
	    // Replace the parsed item with its child IE the selection tree down to the varref itself
	    // Do this before iterating, so we don't have to process the edited tree twice
	    AstNode* lhsp = nodep->lhsp()->unlinkFrBack();
	    nodep->replaceWith(lhsp);

	    // Process lower nodes
	    m_dotText = "";
	    m_baseTextp = NULL;
	    if (m_exp == AstParseRefExp::FUNC) {
		lhsp->accept(*this);
		// Return m_dotText to invoker
	    } else if (nodep->expect() == AstParseRefExp::VAR_MEM
		       || nodep->expect() == AstParseRefExp::VAR_ANY) {
		m_exp = nodep->expect();
		lhsp->accept(*this);
		m_exp = AstParseRefExp::NONE;
		if (!m_baseTextp) nodep->v3fatalSrc("No TEXT found to indicate function name");
		if (m_dotText == "") {
		    AstNode* newp = new AstVarRef(nodep->fileline(), m_baseTextp->text(), false);  // lvalue'ness computed later
		    m_baseTextp->replaceWith(newp); m_baseTextp->deleteTree(); m_baseTextp=NULL;
		} else {
		    AstNode* newp = new AstVarXRef(nodep->fileline(), m_baseTextp->text(), m_dotText, false);  // lvalue'ness computed later
		    m_baseTextp->replaceWith(newp); m_baseTextp->deleteTree(); m_baseTextp=NULL;
		}
	    } else {
		nodep->v3fatalSrc("Unknown ParseRefExp type\n");
	    }
	    nodep->deleteTree(); nodep=NULL;
	}
	if (m_exp != AstParseRefExp::FUNC) {  // Fuctions need to look at the name themself
	    m_dotText = oldText;
	    m_inModDot = oldDot;
	    m_exp = oldExp;
	    m_baseTextp = oldBasep;
	}
    }
    virtual void visit(AstDot* nodep, AstNUser*) {
	UINFO(5,"     "<<nodep<<endl);
	if (m_inModDot) { // Already under dot, so this is {modulepart} DOT {modulepart}
	    m_dotText = "";
	    nodep->lhsp()->iterateAndNext(*this);
	    string namelhs = m_dotText;

	    m_dotText = "";
	    nodep->rhsp()->iterateAndNext(*this);
	    m_dotText = namelhs + "." + m_dotText;
	} else {  // Not in ModDot, so this is {modulepart} DOT {name}
	    m_inModDot = true;
	    m_dotText = "";
	    nodep->lhsp()->iterateAndNext(*this);
	    string namelhs = m_dotText;

	    m_inModDot = false;
	    m_dotText = "";
	    nodep->rhsp()->iterateAndNext(*this);
	    m_dotText = namelhs;

	    nodep->replaceWith(nodep->rhsp()->unlinkFrBack()); nodep->deleteTree(); nodep=NULL;
	}
    }
    virtual void visit(AstSelBit* nodep, AstNUser*) {
	if (!nodep->user1()) {
	    nodep->user1(true);   // Process only once.
	    if (m_inModDot) { // Already under dot, so this is {modulepart} DOT {modulepart}
		m_dotText = "";
		nodep->lhsp()->iterateAndNext(*this);
		if (AstConst* constp = nodep->rhsp()->castConst()) {
		    string index = AstNode::encodeNumber(constp->toSInt());
		    m_dotText = m_dotText+"__BRA__"+index+"__KET__";
		} else {
		    nodep->v3error("Unsupported: Non-constant inside []'s in the cell part of a dotted reference");
		}
		// And pass up m_dotText
	    } else if (m_exp==AstParseRefExp::FUNC) {
		nodep->v3error("Syntax Error: Range selection '[]' is not allowed as part of function names");
	    } else {
		nodep->lhsp()->iterateAndNext(*this);
		AstParseRefExp lastExp = m_exp;
		AstText* lasttextp = m_baseTextp;
		{
		    m_exp = AstParseRefExp::NONE;
		    nodep->rhsp()->iterateAndNext(*this);
		}
		m_baseTextp = lasttextp;
		m_exp = lastExp;
	    }
	}
    }
    virtual void visit(AstNodePreSel* nodep, AstNUser*) {
	// Excludes simple AstSel, see above
	if (!nodep->user1()) {
	    nodep->user1(true);   // Process only once.
	    if (m_inModDot) { // Already under dot, so this is {modulepart} DOT {modulepart}
		nodep->v3error("Syntax Error: Range ':', '+:' etc are not allowed in the cell part of a dotted reference");
	    } else if (m_exp==AstParseRefExp::FUNC) {
		nodep->v3error("Syntax Error: Range ':', '+:' etc are not allowed as part of function names");
	    } else if (m_exp==AstParseRefExp::VAR_MEM) {
		nodep->v3error("Syntax Error: Range ':', '+:' etc are not allowed when expecting memory reference");
	    } else {
		nodep->lhsp()->iterateAndNext(*this);
		AstParseRefExp lastExp = m_exp;
		AstText* lasttextp = m_baseTextp;
		{
		    m_exp = AstParseRefExp::NONE;
		    nodep->rhsp()->iterateAndNext(*this);
		    nodep->thsp()->iterateAndNext(*this);
		}
		m_baseTextp = lasttextp;
		m_exp = lastExp;
	    }
	}
    }
    virtual void visit(AstText* nodep, AstNUser*) {
	if (!nodep->user1()) {
	    nodep->user1(true);   // Process only once.
	    if (m_exp != AstParseRefExp::NONE) {
		UINFO(7,"      "<<nodep<<endl);
		if (m_inModDot) {  // Dotted part, just pass up
		    m_dotText = nodep->text();
		} else {
		    if (m_baseTextp) nodep->v3fatalSrc("Multiple low-level ParseRef text's found; which one is var name?");
		    m_baseTextp = nodep;
		}
	    }
	}
    }
    virtual void visit(AstNode* nodep, AstNUser*) {
	// Default: Just iterate
	checkExpected(nodep);  // So we detect node types we forgot to list here
	nodep->iterateChildren(*this);
    }

public:
    // CONSTUCTORS
    LinkParseVisitor(AstNetlist* rootp) {
	m_inModDot = false;
	m_exp = AstParseRefExp::NONE;
	m_baseTextp = NULL;
	rootp->accept(*this);
    }
    virtual ~LinkParseVisitor() {}
};

//######################################################################
// Link class functions

void V3LinkParse::linkParse(AstNetlist* rootp) {
    UINFO(4,__FUNCTION__<<": "<<endl);
    LinkParseVisitor visitor(rootp);
}
