//*************************************************************************
// DESCRIPTION: Verilator: Parse module/signal name references
//
// Code available from: http://www.veripool.org/verilator
//
// AUTHORS: Wilson Snyder with Paul Wasson, Duane Gabli
//
//*************************************************************************
//
// Copyright 2003-2012 by Wilson Snyder.  This program is free software; you can
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
#include <set>
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
    //  AstNode::user1()	-> bool.  True if processed
    //  AstNode::user2()	-> bool.  True if fileline recomputed
    AstUser1InUse	m_inuser1;
    AstUser2InUse	m_inuser2;

    // TYPES
    typedef map <pair<void*,string>,AstTypedef*> ImplTypedefMap;
    typedef set <FileLine*> FileLineSet;

    // STATE
    string	m_dotText;	// Dotted module text we are building for a dotted node, passed up
    bool	m_inModDot;	// We're inside module part of dotted name
    AstParseRefExp m_exp;	// Type of data we're looking for
    AstText*	m_baseTextp;	// Lowest TEXT node that needs replacement with varref
    AstVar*	m_varp;		// Variable we're under
    ImplTypedefMap	m_implTypedef;	// Created typedefs for each <container,name>
    FileLineSet		m_filelines;	// Filelines that have been seen

    // METHODS
    static int debug() {
	static int level = -1;
	if (VL_UNLIKELY(level < 0)) level = v3Global.opt.debugSrcLevel(__FILE__);
	return level;
    }

    void cleanFileline(AstNode* nodep) {
	if (!nodep->user2Inc()) {  // Process once
	    // We make all filelines unique per AstNode.  This allows us to
	    // later turn off messages on a fileline when an issue is found
	    // so that messages on replicated blocks occur only once,
	    // without suppressing other token's messages as a side effect.
	    // We could have verilog.l create a new one on every token,
	    // but that's a lot more structures than only doing AST nodes.
	    if (m_filelines.find(nodep->fileline()) != m_filelines.end()) {
		nodep->fileline(new FileLine(nodep->fileline()));
	    }
	    m_filelines.insert(nodep->fileline());
	}
    }

    void checkExpected(AstNode* nodep) {
	if (m_exp != AstParseRefExp::PX_NONE) {
	    nodep->v3fatalSrc("Tree syntax error: Not expecting "<<nodep->type()<<" under a "<<nodep->backp()->type());
	    m_exp = AstParseRefExp::PX_NONE;
	}
    }

    // VISITs
    virtual void visit(AstNodeFTaskRef* nodep, AstNUser*) {
	if (!nodep->user1Inc()) {  // Process only once.
	    cleanFileline(nodep);
	    UINFO(5,"   "<<nodep<<endl);
	    checkExpected(nodep);
	    // Due to a need to get the arguments, the ParseRefs are under here,
	    // rather than the NodeFTaskRef under the ParseRef.
	    if (nodep->namep()) {
		m_exp = AstParseRefExp::PX_FUNC;
		nodep->namep()->accept(*this);  // No next, we don't want to do the edit
		m_exp = AstParseRefExp::PX_NONE;
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
	    if (m_exp == AstParseRefExp::PX_FUNC) {
		lhsp->accept(*this);
		// Return m_dotText to invoker
	    } else if (nodep->expect() == AstParseRefExp::PX_VAR_MEM
		       || nodep->expect() == AstParseRefExp::PX_VAR_ANY) {
		m_exp = nodep->expect();
		lhsp->accept(*this);
		m_exp = AstParseRefExp::PX_NONE;
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
	if (m_exp != AstParseRefExp::PX_FUNC) {  // Fuctions need to look at the name themself
	    m_dotText = oldText;
	    m_inModDot = oldDot;
	    m_exp = oldExp;
	    m_baseTextp = oldBasep;
	}
    }
    virtual void visit(AstDot* nodep, AstNUser*) {
	UINFO(5,"     "<<nodep<<endl);
	cleanFileline(nodep);
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
	if (!nodep->user1Inc()) {  // Process only once.
	    cleanFileline(nodep);
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
	    } else if (m_exp==AstParseRefExp::PX_FUNC) {
		nodep->v3error("Syntax Error: Range selection '[]' is not allowed as part of function names");
	    } else {
		nodep->lhsp()->iterateAndNext(*this);
		AstParseRefExp lastExp = m_exp;
		AstText* lasttextp = m_baseTextp;
		{
		    m_exp = AstParseRefExp::PX_NONE;
		    nodep->rhsp()->iterateAndNext(*this);
		}
		m_baseTextp = lasttextp;
		m_exp = lastExp;
	    }
	}
    }
    virtual void visit(AstNodePreSel* nodep, AstNUser*) {
	// Excludes simple AstSel, see above
	if (!nodep->user1Inc()) {  // Process only once.
	    cleanFileline(nodep);
	    if (m_inModDot) { // Already under dot, so this is {modulepart} DOT {modulepart}
		nodep->v3error("Syntax Error: Range ':', '+:' etc are not allowed in the cell part of a dotted reference");
	    } else if (m_exp==AstParseRefExp::PX_FUNC) {
		nodep->v3error("Syntax Error: Range ':', '+:' etc are not allowed as part of function names");
	    } else if (m_exp==AstParseRefExp::PX_VAR_MEM) {
		nodep->v3error("Syntax Error: Range ':', '+:' etc are not allowed when expecting memory reference");
	    } else {
		nodep->lhsp()->iterateAndNext(*this);
		AstParseRefExp lastExp = m_exp;
		AstText* lasttextp = m_baseTextp;
		{
		    m_exp = AstParseRefExp::PX_NONE;
		    nodep->rhsp()->iterateAndNext(*this);
		    nodep->thsp()->iterateAndNext(*this);
		}
		m_baseTextp = lasttextp;
		m_exp = lastExp;
	    }
	}
    }
    virtual void visit(AstText* nodep, AstNUser*) {
	if (!nodep->user1Inc()) {  // Process only once.
	    cleanFileline(nodep);
	    if (m_exp != AstParseRefExp::PX_NONE) {
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
    virtual void visit(AstEnumItem* nodep, AstNUser*) {
	// Expand ranges
	cleanFileline(nodep);
	nodep->iterateChildren(*this);
	if (nodep->rangep()) {
	    if (!nodep->rangep()->msbp()->castConst()
		|| !nodep->rangep()->lsbp()->castConst()) nodep->v3error("Enum ranges must be integral, per spec");
	    int msb = nodep->rangep()->msbConst();
	    int lsb = nodep->rangep()->lsbConst();
	    int increment = (msb > lsb) ? -1 : 1;
	    int offset_from_init = 0;
	    AstNode* addp = NULL;
	    for (int i=msb; i!=(lsb+increment); i+=increment, offset_from_init++) {
		string name = nodep->name() + cvtToStr(i);
		AstNode* valuep = NULL;
		if (nodep->valuep()) valuep = new AstAdd(nodep->fileline(), nodep->valuep()->cloneTree(true),
							 new AstConst(nodep->fileline(), AstConst::Unsized32(), offset_from_init));
		addp = addp->addNextNull(new AstEnumItem(nodep->fileline(), name, NULL, valuep));
	    }
	    nodep->replaceWith(addp);
	    nodep->deleteTree();
	}
    }

    virtual void visit(AstVar* nodep, AstNUser*) {
	cleanFileline(nodep);
	m_varp = nodep;
	nodep->iterateChildren(*this);
	m_varp = NULL;
    }

    virtual void visit(AstAttrOf* nodep, AstNUser*) {
	cleanFileline(nodep);
	nodep->iterateChildren(*this);
	if (nodep->attrType() == AstAttrType::VAR_CLOCK) {
	    if (!m_varp) nodep->v3fatalSrc("Attribute not attached to variable");
	    m_varp->attrScClocked(true);
	    nodep->unlinkFrBack()->deleteTree(); nodep=NULL;
	}
	else if (nodep->attrType() == AstAttrType::VAR_CLOCK_ENABLE) {
	    if (!m_varp) nodep->v3fatalSrc("Attribute not attached to variable");
	    m_varp->attrClockEn(true);
	    nodep->unlinkFrBack()->deleteTree(); nodep=NULL;
	}
	else if (nodep->attrType() == AstAttrType::VAR_PUBLIC) {
	    if (!m_varp) nodep->v3fatalSrc("Attribute not attached to variable");
	    m_varp->sigUserRWPublic(true); m_varp->sigModPublic(true);
	    nodep->unlinkFrBack()->deleteTree(); nodep=NULL;
	}
	else if (nodep->attrType() == AstAttrType::VAR_PUBLIC_FLAT) {
	    if (!m_varp) nodep->v3fatalSrc("Attribute not attached to variable");
	    m_varp->sigUserRWPublic(true);
	    nodep->unlinkFrBack()->deleteTree(); nodep=NULL;
	}
	else if (nodep->attrType() == AstAttrType::VAR_PUBLIC_FLAT_RD) {
	    if (!m_varp) nodep->v3fatalSrc("Attribute not attached to variable");
	    m_varp->sigUserRdPublic(true);
	    nodep->unlinkFrBack()->deleteTree(); nodep=NULL;
	}
	else if (nodep->attrType() == AstAttrType::VAR_PUBLIC_FLAT_RW) {
	    if (!m_varp) nodep->v3fatalSrc("Attribute not attached to variable");
	    m_varp->sigUserRWPublic(true);
	    nodep->unlinkFrBack()->deleteTree(); nodep=NULL;
	}
	else if (nodep->attrType() == AstAttrType::VAR_ISOLATE_ASSIGNMENTS) {
	    if (!m_varp) nodep->v3fatalSrc("Attribute not attached to variable");
	    m_varp->attrIsolateAssign(true);
	    nodep->unlinkFrBack()->deleteTree(); nodep=NULL;
	}
	else if (nodep->attrType() == AstAttrType::VAR_SFORMAT) {
	    if (!m_varp) nodep->v3fatalSrc("Attribute not attached to variable");
	    m_varp->attrSFormat(true);
	    nodep->unlinkFrBack()->deleteTree(); nodep=NULL;
	}
	else if (nodep->attrType() == AstAttrType::VAR_SC_BV) {
	    if (!m_varp) nodep->v3fatalSrc("Attribute not attached to variable");
	    m_varp->attrScBv(true);
	    nodep->unlinkFrBack()->deleteTree(); nodep=NULL;
	}
    }

    virtual void visit(AstAlwaysPublic* nodep, AstNUser*) {
	// AlwaysPublic was attached under a var, but it's a statement that should be
	// at the same level as the var
	cleanFileline(nodep);
	nodep->iterateChildren(*this);
	if (m_varp) {
	    nodep->unlinkFrBack();
	    m_varp->addNext(nodep);
	    // lvalue is true, because we know we have a verilator public_flat_rw
	    // but someday we may be more general
	    bool lvalue = m_varp->isSigUserRWPublic();
	    nodep->addStmtp(new AstVarRef(nodep->fileline(), m_varp, lvalue));
	}
    }

    virtual void visit(AstDefImplicitDType* nodep, AstNUser*) {
	cleanFileline(nodep);
	UINFO(8,"   DEFIMPLICIT "<<nodep<<endl);
	// Must remember what names we've already created, and combine duplicates
	// so that for "var enum {...} a,b" a & b will share a common typedef
	// Unique name space under each containerp() so that an addition of a new type won't change every verilated module.
	AstTypedef* defp = NULL;
	ImplTypedefMap::iterator it = m_implTypedef.find(make_pair(nodep->containerp(), nodep->name()));
	if (it != m_implTypedef.end()) {
	    defp = it->second;
	} else {
	    // Definition must be inserted right after the variable (etc) that needed it
	    // AstVar, AstTypedef, AstNodeFTask are common containers
	    AstNode* backp = nodep->backp();
	    for (; backp; backp=backp->backp()) {
		if (backp->castVar()) break;
		else if (backp->castTypedef()) break;
		else if (backp->castNodeFTask()) break;
	    }
	    if (!backp) nodep->v3fatalSrc("Implicit enum/struct type created under unexpected node type");
	    AstNodeDType* dtypep = nodep->dtypep(); dtypep->unlinkFrBack();
	    if (backp->castTypedef()) { // A typedef doesn't need us to make yet another level of typedefing
		// For typedefs just remove the AstRefDType level of abstraction
		nodep->replaceWith(dtypep);
		nodep->deleteTree(); nodep=NULL;
		return;
	    } else {
		defp = new AstTypedef(nodep->fileline(), nodep->name(), dtypep);
		m_implTypedef.insert(make_pair(make_pair(nodep->containerp(), defp->name()), defp));
		backp->addNextHere(defp);
	    }
	}
	nodep->replaceWith(new AstRefDType(nodep->fileline(), defp->name()));
	nodep->deleteTree(); nodep=NULL;
    }

    virtual void visit(AstNode* nodep, AstNUser*) {
	// Default: Just iterate
	cleanFileline(nodep);
	checkExpected(nodep);  // So we detect node types we forgot to list here
	nodep->iterateChildren(*this);
    }

public:
    // CONSTUCTORS
    LinkParseVisitor(AstNetlist* rootp) {
	m_inModDot = false;
	m_exp = AstParseRefExp::PX_NONE;
	m_baseTextp = NULL;
	m_varp = NULL;
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
