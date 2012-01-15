//*************************************************************************
// DESCRIPTION: Verilator: Add temporaries, such as for inst nodes
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
// V3Inst's Transformations:
//
// Each module:
//	Pins:
//	    Create a wire assign to interconnect to submodule
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"
#include <cstdio>
#include <cstdarg>
#include <unistd.h>
#include <algorithm>

#include "V3Global.h"
#include "V3Inst.h"
#include "V3Ast.h"
#include "V3Changed.h"

//######################################################################
// Inst state, as a visitor of each AstNode

class InstVisitor : public AstNVisitor {
private:
    // NODE STATE
    // Cleared each Cell:
    //  AstVar::user1p()	-> AstNode*.  Expression connected to given pin
    //  AstVarRef::user1p()	-> bool.  True if created senitem for parent's connected signal
    //  AstPin::user1p()	-> bool.  True if created assignment already
    AstUser1InUse	m_inuser1;

    // STATE
    AstNodeModule*	m_modp;		// Current module
    AstCell*	m_cellp;	// Current cell

    static int debug() {
	static int level = -1;
	if (VL_UNLIKELY(level < 0)) level = v3Global.opt.debugSrcLevel(__FILE__);
	return level;
    }
    //int m_debug;  int debug() { return m_debug; }

    // VISITORS
    virtual void visit(AstNodeModule* nodep, AstNUser*) {
	UINFO(4," MOD   "<<nodep<<endl);
	//if (nodep->name() == "t_chg") m_debug = 9; else m_debug=0;
	m_modp = nodep;
	nodep->iterateChildren(*this);
	m_modp = NULL;
    }
    virtual void visit(AstCell* nodep, AstNUser*) {
	UINFO(4,"  CELL   "<<nodep<<endl);
	m_cellp = nodep;
	//VV*****  We reset user1p() on each cell!!!
	AstNode::user1ClearTree();
	// Collect pin expressions, so submod->varp->user1p() points to expression it connects to
	for (AstPin* pinp = nodep->pinsp(); pinp; pinp=pinp->nextp()->castPin()) {
	    pinp->modVarp()->user1p(pinp->exprp());
	}
	nodep->iterateChildren(*this);
	m_cellp = NULL;
    }
    virtual void visit(AstPin* nodep, AstNUser*) {
	// PIN(p,expr) -> ASSIGNW(VARXREF(p),expr)    (if sub's input)
	//	      or  ASSIGNW(expr,VARXREF(p))    (if sub's output)
	UINFO(4,"   PIN  "<<nodep<<endl);
	if (debug()>=9) nodep->dumpTree(cout,"  Pin_oldb: ");
	if (nodep->modVarp()->isOutOnly() && nodep->exprp()->castConst())
	    nodep->v3error("Output port is connected to a constant pin, electrical short");
	// Use user1p on the PIN to indicate we created an assign for this pin
	if (!nodep->user1Inc()) {
	    // Simplify it
	    V3Inst::pinReconnectSimple(nodep, m_cellp, m_modp);
	    // Make a ASSIGNW (expr, pin)
	    AstNode*  exprp  = nodep->exprp()->cloneTree(false);
	    if (nodep->width() != nodep->modVarp()->width())
		nodep->v3fatalSrc("Width mismatch, should have been handled in pinReconnectSimple\n");
	    if (nodep->modVarp()->isInout()) {
		nodep->v3fatalSrc("Unsupported: Verilator is a 2-state simulator");
	    } else if (nodep->modVarp()->isOutput()) {
		AstNode* rhsp = new AstVarXRef (exprp->fileline(), nodep->modVarp(), m_cellp->name(), false);
		rhsp->widthSignedFrom(nodep);
		AstAssignW* assp = new AstAssignW (exprp->fileline(), exprp, rhsp);
		m_modp->addStmtp(assp);
	    } else if (nodep->modVarp()->isInput()) {
		// Don't bother moving constants now,
		// we'll be pushing the const down to the cell soon enough.
		AstNode* assp = new AstAssignW
		    (exprp->fileline(),
		     new AstVarXRef(exprp->fileline(), nodep->modVarp(), m_cellp->name(), true),
		     exprp);
		m_modp->addStmtp(assp);
		if (debug()>=9) assp->dumpTree(cout,"     _new: ");
	    } else {
		nodep->v3error("Assigned pin is neither input nor output");
	    }
	}

	// We're done with the pin
	nodep->unlinkFrBack()->deleteTree(); nodep=NULL;
    }

    virtual void visit(AstUdpTable* nodep, AstNUser*) {
	if (!v3Global.opt.bboxUnsup()) {
	    // If we support primitives, update V3Undriven to remove special case
	    nodep->v3error("Unsupported: Verilog 1995 UDP Tables.  Use --bbox-unsup to ignore tables.");
	}
    }

    // Save some time
    virtual void visit(AstNodeAssign*, AstNUser*) {}
    virtual void visit(AstAlways*, AstNUser*) {}

    //--------------------
    // Default: Just iterate
    virtual void visit(AstNode* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
    }
public:
    // CONSTUCTORS
    InstVisitor(AstNode* nodep) {
	m_modp=NULL;
	m_cellp=NULL;
	//
	nodep->accept(*this);
    }
    virtual ~InstVisitor() {}
};

//######################################################################

class InstDeVisitor : public AstNVisitor {
    // Find all cells with arrays, and convert to non-arrayed
private:
    // STATE
    AstRange*	m_cellRangep;	// Range for arrayed instantiations, NULL for normal instantiations
    int		m_instNum;	// Current instantiation number
    int		m_instLsb;	// Current instantiation number

    static int debug() {
	static int level = -1;
	if (VL_UNLIKELY(level < 0)) level = v3Global.opt.debugSrcLevel(__FILE__);
	return level;
    }

    // VISITORS
    virtual void visit(AstCell* nodep, AstNUser*) {
	if (nodep->rangep()) {
	    m_cellRangep = nodep->rangep();
	    UINFO(4,"  CELL   "<<nodep<<endl);
	    // Make all of the required clones
	    m_instLsb = m_cellRangep->lsbConst();
	    for (m_instNum = m_instLsb; m_instNum<=m_cellRangep->msbConst(); m_instNum++) {
		AstCell* newp = nodep->cloneTree(false);
		nodep->addNextHere(newp);
		// Remove ranging and fix name
		newp->rangep()->unlinkFrBack()->deleteTree();
		// Somewhat illogically, we need to rename the orignal name of the cell too.
		// as that is the name users expect for dotting
		// The spec says we add [x], but that won't work in C...
		newp->name(newp->name()+"__BRA__"+cvtToStr(m_instNum)+"__KET__");
		newp->origName(newp->origName()+"__BRA__"+cvtToStr(m_instNum)+"__KET__");
		// Fixup pins
		newp->pinsp()->iterateAndNext(*this);
		if (debug()==9) { newp->dumpTree(cout,"newcell: "); cout<<endl; }
	    }

	    // Done.  Delete original
	    m_cellRangep=NULL;
	    nodep->unlinkFrBack(); pushDeletep(nodep); nodep=NULL;
	}
    }
    virtual void visit(AstPin* nodep, AstNUser*) {
	// Any non-direct pins need reconnection with a part-select
	if (m_cellRangep) {
	    UINFO(4,"   PIN  "<<nodep<<endl);
	    int pinwidth = nodep->modVarp()->width();
	    int expwidth = nodep->exprp()->width();
	    if (expwidth == pinwidth) {
		// NOP: Arrayed instants: widths match so connect to each instance
	    } else if (expwidth == pinwidth*m_cellRangep->elementsConst()) {
		// Arrayed instants: one bit for each of the instants (each assign is 1 pinwidth wide)
		AstNode* exprp = nodep->exprp()->unlinkFrBack();
		bool inputPin = nodep->modVarp()->isInput();
		if (!inputPin && !exprp->castVarRef()
		    && !exprp->castSel()) {  // V3Const will collapse the SEL with the one we're about to make
		    nodep->v3error("Unsupported: Per-bit array instantiations with output connections to non-wires.");
		    // Note spec allows more complicated matches such as slices and such
		}
		exprp = new AstSel (exprp->fileline(), exprp,
				    pinwidth*(m_instNum-m_instLsb),
				    pinwidth);
		nodep->exprp(exprp);
	    } else {
		nodep->v3fatalSrc("Width mismatch; V3Width should have errored out.");
	    }
	}
    }

    // Save some time
    virtual void visit(AstNodeMath*, AstNUser*) {}
    //--------------------
    // Default: Just iterate
    virtual void visit(AstNode* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
    }
public:
    // CONSTUCTORS
    InstDeVisitor(AstNode* nodep) {
	m_cellRangep=NULL;
	m_instNum=0;
	m_instLsb=0;
	//
	nodep->accept(*this);
    }
    virtual ~InstDeVisitor() {}
};

//######################################################################
// Inst class functions

void V3Inst::pinReconnectSimple(AstPin* pinp, AstCell* cellp, AstNodeModule* modp) {
    // If a pin connection is "simple" leave it as-is
    // Else create a intermediate wire to perform the interconnect
    // Note this module calles cloneTree() via new AstVar
    AstVar* pinVarp = pinp->modVarp();
    AstVarRef* connectRefp = pinp->exprp()->castVarRef();
    AstBasicDType* pinBasicp = pinVarp->dtypep()->basicp();  // Maybe NULL
    AstBasicDType* connBasicp = NULL;
    if (connectRefp) connBasicp = connectRefp->varp()->dtypep()->basicp();
    //
    if (connectRefp
	&& connectRefp->varp()->dtypep()->sameTree(pinVarp->dtypep())
	&& !connectRefp->varp()->isSc()) { // Need the signal as a 'shell' to convert types
	// Done.  Same data type
    } else if (connBasicp
	       && pinBasicp
	       && connBasicp->width() == pinBasicp->width()
	       && connBasicp->lsb() == pinBasicp->lsb()
	       && !connectRefp->varp()->isSc()	// Need the signal as a 'shell' to convert types
	       && pinp->width() == pinVarp->width()
	       && 1) {
	// Done. One to one interconnect won't need a temporary variable.
    } else if (pinp->exprp()->castConst()) {
	// Done. Constant.
    } else {
	// Make a new temp wire
	//if (1||debug()>=9) { pinp->dumpTree(cout,"in_pin:"); }
	AstAssignW* assignp = NULL;
	AstNode* pinexprp = pinp->exprp()->unlinkFrBack();
	string newvarname = "__Vcellinp__"+cellp->name()+"__"+pinp->name();
	AstVar* newvarp = new AstVar (pinVarp->fileline(), AstVarType::MODULETEMP, newvarname, pinVarp);
	modp->addStmtp(newvarp);
	if (pinVarp->isInout()) {
	    pinVarp->v3fatalSrc("Unsupported: Inout connections to pins must be direct one-to-one connection (without any expression)");
	} else if (pinVarp->isOutput()) {
	    // See also V3Inst
	    AstNode* rhsp = new AstVarRef(pinp->fileline(), newvarp, false);
	    if (pinp->width() > rhsp->width()) {
		if (rhsp->isSigned()) {
		    rhsp = new AstExtendS(pinp->fileline(), rhsp);
		} else {
		    rhsp = new AstExtend (pinp->fileline(), rhsp);
		}
	    } else if (pinp->width() < rhsp->width()) {
		rhsp = new AstSel    (pinp->fileline(), rhsp, 0, pinp->width());
	    }
	    rhsp->widthSignedFrom(pinp);
	    assignp = new AstAssignW (pinp->fileline(), pinexprp, rhsp);
	    pinp->exprp(new AstVarRef (pinexprp->fileline(), newvarp, true));
	} else {
	    // V3 width should have range/extended to make the widths correct
	    if (pinexprp->width() != pinVarp->width()) pinp->v3fatalSrc("Input pin width mismatch");
	    assignp = new AstAssignW (pinp->fileline(),
				      new AstVarRef(pinp->fileline(), newvarp, true),
				      pinexprp);
	    pinp->exprp(new AstVarRef (pinexprp->fileline(), newvarp, false));
	}
	pinp->widthSignedFrom(pinp->exprp());
	if (assignp) modp->addStmtp(assignp);
	//if (1||debug()) { pinp->dumpTree(cout,"  out:"); }
	//if (1||debug()) { assignp->dumpTree(cout," aout:"); }
    }
}

//######################################################################
// Inst class visitor

void V3Inst::instAll(AstNetlist* nodep) {
    UINFO(2,__FUNCTION__<<": "<<endl);
    InstVisitor visitor (nodep);
}

void V3Inst::dearrayAll(AstNetlist* nodep) {
    UINFO(2,__FUNCTION__<<": "<<endl);
    InstDeVisitor visitor (nodep);
}
