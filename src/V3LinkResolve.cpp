// $Id$
//*************************************************************************
// DESCRIPTION: Verilator: Resolve module/signal name references
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
// LinkResolve TRANSFORMATIONS:
//	Top-down traversal
//	    Extracts:
//		Add SUB so that we subtract off the "base 0-start" of the array
//	    SelBit: Convert to ArraySel
//		Add SUB so that we subtract off the "base 0-start" of the array
//	    File operations
//		Convert normal var to FILE* type
//*************************************************************************

#include "config.h"
#include <stdio.h>
#include <stdarg.h>
#include <unistd.h>
#include <map>
#include <algorithm>
#include <vector>

#include "V3Global.h"
#include "V3LinkResolve.h"
#include "V3Ast.h"

//######################################################################
// Link state, as a visitor of each AstNode

class LinkResolveVisitor : public AstNVisitor {
private:
    // NODE STATE
    //  Entire netlist:
    //   AstCaseItem::user2()	// bool		  Moved default caseitems

    // STATE
    // Below state needs to be preserved between each module call.
    AstModule*	m_modp;		// Current module
    AstNodeFTask* m_ftaskp;	// Function or task we're inside
    bool	m_setRefLvalue;	// Set VarRefs to lvalues for pin assignments
    AstBegin*	m_beginLastp;	// Last begin block seen (not present one)
    int		m_beginNum;	// Begin block number, 0=none seen

    //int debug() { return 9; }

    // METHODS
    // VISITs
    virtual void visit(AstNetlist* nodep, AstNUser*) {
	AstNode::user2ClearTree();
	// And recurse...
	nodep->iterateChildren(*this);
    }

    virtual void visit(AstModule* nodep, AstNUser*) {
	// Module: Create sim table for entire module and iterate
	UINFO(8,"MODULE "<<nodep<<endl);
	m_modp = nodep;
	m_beginNum = 0;
	m_beginLastp = NULL;
	nodep->iterateChildren(*this);
	m_modp = NULL;
    }
    virtual void visit(AstBegin* nodep, AstNUser*) {
	// Rename "genblk"s to include a number if there was more then one per block
	// This is better then doing it at parse time, because if there's only one, it's named logically.
	UINFO(8,"   "<<nodep<<endl);
	++m_beginNum;
	if (m_beginNum == 2) {  // We didn't know in time to fix the first one.  Do now
	    if (!m_beginLastp) nodep->v3fatalSrc("Where was first begin?");
	    m_beginLastp->name(m_beginLastp->name()+"1");
	}
	if (m_beginNum > 1) {  // Now us
	    nodep->name(nodep->name()+cvtToStr(m_beginNum));
	}
	// Recurse
	int oldNum = m_beginNum;
	m_beginNum = 0;
	m_beginLastp = NULL;
	{
	    nodep->iterateChildren(*this);
	}
	m_beginNum = oldNum;
	m_beginLastp = nodep;  // Us, so 2nd begin can change our name
    }
    virtual void visit(AstVar* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
	if (nodep->arraysp() && nodep->isIO()) {
	    nodep->v3error("Arrayed variables may not be inputs nor outputs");
	}
	if (m_ftaskp) nodep->funcLocal(true);
	if (nodep && nodep->isSigPublic()) m_modp->modPublic(true);	// Avoid flattening if signals are exposed
    }

    virtual void visit(AstNodeVarRef* nodep, AstNUser*) {
	// VarRef: Resolve its reference
	if (nodep->varp()) {
	    nodep->varp()->usedParam(true);
	    if (nodep->lvalue() && nodep->varp()->isInput()) {
		nodep->v3error("Assigning to input variable: "<<nodep->prettyName());
	    }
	}
	if (m_setRefLvalue) {
	    nodep->lvalue(true);
	}
	nodep->iterateChildren(*this);
    }

    virtual void visit(AstNodeFTask* nodep, AstNUser*) {
	// NodeTask: Remember its name for later resolution
	// Remember the existing symbol table scope
	m_ftaskp = nodep;
	nodep->iterateChildren(*this);
	m_ftaskp = NULL;
    }

    virtual void visit(AstPin* nodep, AstNUser*) {
	if (nodep->modVarp() && nodep->modVarp()->isOutput()) {
	    // When the varref's were created, we didn't know the I/O state
	    // Now that we do, and it's from a output, we know it's a lvalue
	    m_setRefLvalue = true;
	    nodep->iterateChildren(*this);
	    m_setRefLvalue = false;
	} else {
	    nodep->iterateChildren(*this);
	}
    }

    virtual void visit(AstSel* nodep, AstNUser*) {
	nodep->lhsp()->iterateAndNext(*this);
	{   // Only set lvalues on the from
	    bool last_setRefLvalue = m_setRefLvalue;
	    m_setRefLvalue = false;
	    nodep->rhsp()->iterateAndNext(*this);
	    nodep->thsp()->iterateAndNext(*this);
	    m_setRefLvalue = last_setRefLvalue;
	}
    }
    virtual void visit(AstArraySel* nodep, AstNUser*) {
	nodep->lhsp()->iterateAndNext(*this);
	{   // Only set lvalues on the from
	    bool last_setRefLvalue = m_setRefLvalue;
	    m_setRefLvalue = false;
	    nodep->rhsp()->iterateAndNext(*this);
	    m_setRefLvalue = last_setRefLvalue;
	}
    }
    void iterateSelTriop(AstNodePreSel* nodep) {
	nodep->lhsp()->iterateAndNext(*this);
	{   // Only set lvalues on the from
	    bool last_setRefLvalue = m_setRefLvalue;
	    m_setRefLvalue = false;
	    nodep->rhsp()->iterateAndNext(*this);
	    nodep->thsp()->iterateAndNext(*this);
	    m_setRefLvalue = last_setRefLvalue;
	}
    }

    AstNode* newSubAttrOf(AstNode* underp, AstNode* fromp, AstAttrType attrType) {
	// Account for a variable's LSB in bit selections
	// Replace underp with a SUB(underp, ATTROF(varp, attrType))
	int dimension=0;
	while (fromp && !fromp->castNodeVarRef() && (fromp->castSel() || fromp->castArraySel())) {
	    if (fromp->castSel()) fromp = fromp->castSel()->fromp();
	    else fromp = fromp->castArraySel()->fromp();
	    dimension++;
	}
	AstNodeVarRef* varrefp = fromp->castNodeVarRef();
	if (!varrefp) fromp->v3fatalSrc("Bit/array selection of non-variable");
	if (!varrefp->varp()) varrefp->v3fatalSrc("Signal not linked");
	AstRange* vararrayp = varrefp->varp()->arrayp(dimension);
	AstRange* varrangep = varrefp->varp()->rangep();
	if ((attrType==AstAttrType::ARRAY_LSB
	     // SUB #'s Not needed because LSB==0? (1D only, else we'll constify it later)
	     ? (vararrayp && !vararrayp->lsbp()->isZero())
	     : (varrangep && !varrangep->lsbp()->isZero()))) {
	    AstNode* newrefp;
	    if (varrefp->castVarXRef()) {
		newrefp = new AstVarXRef(underp->fileline(),
					 varrefp->varp(), varrefp->castVarXRef()->dotted(), false);
	    } else {
		newrefp = new AstVarRef (underp->fileline(),
					 varrefp->varp(), false);
	    }
	    AstNode* newp = new AstSub (underp->fileline(),
					underp,
					new AstAttrOf(underp->fileline(),
						      attrType, newrefp, dimension));
	    return newp;
	} else {
	    return underp;
	}
    }

    void selCheckDimension(AstSel* nodep) {
	// Perform error checks on the node
	AstNode* fromp = nodep->lhsp();
	AstNode* basefromp = AstArraySel::baseFromp(fromp);
	AstNodeVarRef* varrefp = basefromp->castNodeVarRef();
	AstVar* varp = varrefp ? varrefp->varp() : NULL;
	if (fromp->castSel()
	    || (varp && !varp->rangep() && !varp->isParam())) {
	    nodep->v3error("Illegal bit select; variable already selected, or bad dimension");
	}
    }

    virtual void visit(AstSelBit* nodep, AstNUser*) {
	// Couldn't tell until link time if [#] references a bit or an array
	iterateSelTriop(nodep);
	AstNode* fromp = nodep->lhsp()->unlinkFrBack();
	AstNode* bitp = nodep->rhsp()->unlinkFrBack();
	AstNode* basefromp = AstArraySel::baseFromp(fromp);
	int dimension      = AstArraySel::dimension(fromp);
	AstNodeVarRef* varrefp = basefromp->castNodeVarRef();
	if (varrefp
	    && varrefp->varp()
	    && varrefp->varp()->arrayp(dimension)) {
	    // SELBIT(array, index) -> ARRAYSEL(array, index)
	    AstNode* newp = new AstArraySel
		(nodep->fileline(),
		 fromp,
		 newSubAttrOf(bitp, fromp, AstAttrType::ARRAY_LSB));
	    nodep->replaceWith(newp); pushDeletep(nodep); nodep=NULL;
	}
	else {
	    // SELBIT(range, index) -> SEL(array, index, 1)
	    V3Number one (nodep->fileline(),32,1); one.width(32,false);  // Unsized so width from user
	    AstSel* newp = new AstSel
		(nodep->fileline(),
		 fromp,
		 newSubAttrOf(bitp, fromp, AstAttrType::RANGE_LSB),
		 new AstConst (nodep->fileline(),one));
	    selCheckDimension(newp);
	    nodep->replaceWith(newp); pushDeletep(nodep); nodep=NULL;
	}
    }

    virtual void visit(AstSelExtract* nodep, AstNUser*) {
	// SELEXTRACT(from,msb,lsb) -> SEL(from, lsb, 1+msb-lsb)
	iterateSelTriop(nodep);
	AstNode* fromp = nodep->lhsp()->unlinkFrBack();
	AstNode* msbp = nodep->rhsp()->unlinkFrBack();
	AstNode* lsbp = nodep->thsp()->unlinkFrBack();
	AstNode* widthp;
	if (msbp->castConst() && lsbp->castConst()) {
	    // Quite common, save V3Const some effort
	    V3Number widnum (msbp->fileline(),32,msbp->castConst()->asInt() +1-lsbp->castConst()->asInt());
	    widnum.width(32,false);  // Unsized so width from user
	    widthp = new AstConst (msbp->fileline(), widnum);
	    pushDeletep(msbp);
	} else {
	    V3Number one (nodep->fileline(),32,1);  one.width(32,false);  // Unsized so width from user
	    widthp = new AstSub (lsbp->fileline(),
				 new AstAdd(msbp->fileline(),
					    new AstConst(msbp->fileline(),one),
					    msbp),
				 lsbp->cloneTree(true));
	}
	AstSel* newp = new AstSel
	    (nodep->fileline(),
	     fromp,
	     newSubAttrOf(lsbp, fromp, AstAttrType::RANGE_LSB),
	     widthp);
	selCheckDimension(newp);
	nodep->replaceWith(newp); pushDeletep(nodep); nodep=NULL;
    }
    virtual void visit(AstSelPlus* nodep, AstNUser*) {
	// SELPLUS -> SEL
	iterateSelTriop(nodep);
	AstNode* fromp = nodep->lhsp()->unlinkFrBack();
	AstNode* lsbp = nodep->rhsp()->unlinkFrBack();
	AstNode* widthp = nodep->thsp()->unlinkFrBack();
	AstSel*  newp = new AstSel
	    (nodep->fileline(),
	     fromp,
	     newSubAttrOf(lsbp, fromp, AstAttrType::RANGE_LSB),
	     widthp);
	selCheckDimension(newp);
	nodep->replaceWith(newp); pushDeletep(nodep); nodep=NULL;
    }
    virtual void visit(AstSelMinus* nodep, AstNUser*) {
	// SELMINUS(from,msb,width) -> SEL(from, msb-(width-1)-lsb#)
	iterateSelTriop(nodep);
	AstNode* fromp = nodep->lhsp()->unlinkFrBack();
	AstNode* msbp = nodep->rhsp()->unlinkFrBack();
	AstNode* widthp = nodep->thsp()->unlinkFrBack();
	V3Number one (msbp->fileline(),32,1);  one.width(32,false);  // Unsized so width from user
	AstSel*  newp = new AstSel
	    (nodep->fileline(),
	     fromp,
	     newSubAttrOf(new AstSub (msbp->fileline(),
				      msbp,
				      new AstSub (msbp->fileline(),
						  widthp->cloneTree(true),
						  new AstConst (msbp->fileline(), one))),
			  fromp, AstAttrType::RANGE_LSB),
	     widthp);
	selCheckDimension(newp);
	nodep->replaceWith(newp); pushDeletep(nodep); nodep=NULL;
    }

    virtual void visit(AstCaseItem* nodep, AstNUser*) {
	// Move default caseItems to the bottom of the list
	// That saves us from having to search each case list twice, for non-defaults and defaults
	nodep->iterateChildren(*this);
	if (!nodep->user2() && nodep->isDefault() && nodep->nextp()) {
	    nodep->user2(true);
	    AstNode* nextp = nodep->nextp();
	    nodep->unlinkFrBack();
	    nextp->addNext(nodep);
	}
    }

    virtual void visit(AstPragma* nodep, AstNUser*) {
	if (nodep->pragType() == AstPragmaType::PUBLIC_MODULE) {
	    if (!m_modp) nodep->v3fatalSrc("PUBLIC_MODULE not under a module\n");
	    m_modp->modPublic(true);
	    nodep->unlinkFrBack(); pushDeletep(nodep); nodep=NULL;
	}
	else if (nodep->pragType() == AstPragmaType::PUBLIC_TASK) {
	    if (!m_ftaskp) nodep->v3fatalSrc("PUBLIC_TASK not under a task\n");
	    m_ftaskp->taskPublic(true);
	    m_modp->modPublic(true);  // Need to get to the task...
	    nodep->unlinkFrBack(); pushDeletep(nodep); nodep=NULL;
	}
	else if (nodep->pragType() == AstPragmaType::COVERAGE_BLOCK_OFF) {
	    if (!v3Global.opt.coverageLine()) {  // No need for block statements; may optimize better without
		nodep->unlinkFrBack(); pushDeletep(nodep); nodep=NULL;
	    }
	}
	else {
	    nodep->iterateChildren(*this);
	}
    }

    void expectDescriptor(AstNode* nodep, AstNodeVarRef* filep) {
	if (!filep) nodep->v3error("Unsupported: $fopen/$fclose descriptor must be a simple variable");
	if (filep && filep->varp()) filep->varp()->attrFileDescr(true);
    }
    virtual void visit(AstFOpen* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
	expectDescriptor(nodep, nodep->filep());
    }
    virtual void visit(AstFClose* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
	expectDescriptor(nodep, nodep->filep());
    }

    virtual void visit(AstScCtor* nodep, AstNUser*) {
	// Constructor info means the module must remain public
	m_modp->modPublic(true);
	nodep->iterateChildren(*this);
    }
    virtual void visit(AstScInt* nodep, AstNUser*) {
	// Special class info means the module must remain public
	m_modp->modPublic(true);
	nodep->iterateChildren(*this);
    }

    virtual void visit(AstNode* nodep, AstNUser*) {
	// Default: Just iterate
	nodep->iterateChildren(*this);
    }

public:
    // CONSTUCTORS
    LinkResolveVisitor(AstNetlist* rootp) {
	m_ftaskp = NULL;
	m_modp = NULL;
	m_setRefLvalue = false;
	m_beginNum = 0;
	m_beginLastp = NULL;
	//
	rootp->accept(*this);
    }
    virtual ~LinkResolveVisitor() {}
};

//######################################################################
// LinkBotupVisitor
//	Recurses cells backwards, so we can pick up those things that propagate
// 	from child cells up to the top module.

class LinkBotupVisitor : public AstNVisitor {
private:
    // STATE
    AstModule*	m_modp;		// Current module
    //int debug() { return 9; }

    // VISITs
    virtual void visit(AstNetlist* nodep, AstNUser*) {
	// Iterate modules backwards, in bottom-up order.
	nodep->iterateChildrenBackwards(*this);
    }
    virtual void visit(AstModule* nodep, AstNUser*) {
	m_modp = nodep;
	nodep->iterateChildren(*this);
	m_modp = NULL;
    }
    virtual void visit(AstCell* nodep, AstNUser*) {
	// Parent module inherits child's publicity
	if (nodep->modp()->modPublic()) m_modp->modPublic(true);
	//** No iteration for speed
    }
    virtual void visit(AstNodeMath* nodep, AstNUser*) {
	// Speedup
    }
    virtual void visit(AstNode* nodep, AstNUser*) {
	// Default: Just iterate
	nodep->iterateChildren(*this);
    }
public:
    // CONSTUCTORS
    LinkBotupVisitor(AstNetlist* rootp) {
	m_modp = NULL;
	//
	rootp->accept(*this);
    }
    virtual ~LinkBotupVisitor() {}
};

//######################################################################
// Link class functions

void V3LinkResolve::linkResolve(AstNetlist* rootp) {
    UINFO(4,__FUNCTION__<<": "<<endl);
    LinkResolveVisitor visitor(rootp);
    LinkBotupVisitor visitorb(rootp);
}
