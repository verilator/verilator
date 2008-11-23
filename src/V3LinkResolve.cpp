//*************************************************************************
// DESCRIPTION: Verilator: Resolve module/signal name references
//
// Code available from: http://www.veripool.org/verilator
//
// AUTHORS: Wilson Snyder with Paul Wasson, Duane Gabli
//
//*************************************************************************
//
// Copyright 2003-2008 by Wilson Snyder.  This program is free software; you can
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
//	    SenItems: Convert pos/negedge of non-simple signals to temporaries
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
#include "V3LinkResolve.h"
#include "V3Ast.h"

//######################################################################
// Link state, as a visitor of each AstNode

class LinkResolveVisitor : public AstNVisitor {
private:
    // NODE STATE
    //  Entire netlist:
    //   AstCaseItem::user2()	// bool		  Moved default caseitems
    AstUser2InUse	m_inuse2;

    // STATE
    // Below state needs to be preserved between each module call.
    AstModule*	m_modp;		// Current module
    AstNodeFTask* m_ftaskp;	// Function or task we're inside
    AstVAssert*	m_assertp;	// Current assertion
    int		m_senitemCvtNum; // Temporary signal counter

    //int debug() { return 9; }

    // METHODS
    // VISITs
    virtual void visit(AstModule* nodep, AstNUser*) {
	// Module: Create sim table for entire module and iterate
	UINFO(8,"MODULE "<<nodep<<endl);
	m_modp = nodep;
	m_senitemCvtNum = 0;
	nodep->iterateChildren(*this);
	m_modp = NULL;
    }
    virtual void visit(AstVAssert* nodep, AstNUser*) {
	if (m_assertp) nodep->v3error("Assert not allowed under another assert");
	m_assertp = nodep;
	nodep->iterateChildren(*this);
	m_assertp = NULL;
    }

    virtual void visit(AstVar* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
	if (nodep->arraysp() && nodep->isIO()) {
	    nodep->v3error("Arrayed variables may not be inputs nor outputs");
	}
	if (m_ftaskp) nodep->funcLocal(true);
	if (nodep->isSigModPublic()) {
	    nodep->sigModPublic(false);  // We're done with this attribute
	    m_modp->modPublic(true);	// Avoid flattening if signals are exposed
	}
    }

    virtual void visit(AstNodeVarRef* nodep, AstNUser*) {
	// VarRef: Resolve its reference
	if (nodep->varp()) {
	    nodep->varp()->usedParam(true);
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

    virtual void visit(AstSenItem* nodep, AstNUser*) {
	// Remove bit selects, and bark if it's not a simple variable
	nodep->iterateChildren(*this);
	if (nodep->isClocked()) {
	    // If it's not a simple variable wrap in a temporary
	    // This is a bit unfortunate as we haven't done width resolution
	    // and any width errors will look a bit odd, but it works.
	    AstNode* sensp = nodep->sensp();
	    if (sensp
		&& !sensp->castNodeVarRef()
		&& !sensp->castConst()) {
		// Make a new temp wire
		string newvarname = "__Vsenitemexpr"+cvtToStr(++m_senitemCvtNum);
		AstVar* newvarp = new AstVar (sensp->fileline(), AstVarType::MODULETEMP, newvarname,
					      NULL,NULL);
		// We can't just add under the module, because we may be inside a generate, begin, etc.
		// We know a SenItem should be under a SenTree/Always etc, we we'll just hunt upwards
		AstNode* addwherep = nodep;  // Add to this element's next
		while (addwherep->castSenItem()
		       || addwherep->castSenTree()) {
		    addwherep = addwherep->backp();
		}
		if (!addwherep->castAlways()) {  // Assertion perhaps?
		    sensp->v3error("Unsupported: Non-single-bit pos/negedge clock statement under some complicated block");
		    addwherep = m_modp;
		}
		addwherep->addNext(newvarp);

		sensp->replaceWith(new AstVarRef (sensp->fileline(), newvarp, false));
		AstAssignW* assignp = new AstAssignW
		    (sensp->fileline(),
		     new AstVarRef(sensp->fileline(), newvarp, true),
		     sensp);
		addwherep->addNext(assignp);
	    }
	} else {  // Old V1995 sensitivity list; we'll probably mostly ignore
	    bool did=1;
	    while (did) {
		did=0;
		if (AstNodeSel* selp = nodep->sensp()->castNodeSel()) {
		    AstNode* fromp = selp->fromp()->unlinkFrBack();
		    selp->replaceWith(fromp); selp->deleteTree(); selp=NULL;
		    did=1;
		}
		// NodeSel doesn't include AstSel....
		if (AstSel* selp = nodep->sensp()->castSel()) {
		    AstNode* fromp = selp->fromp()->unlinkFrBack();
		    selp->replaceWith(fromp); selp->deleteTree(); selp=NULL;
		    did=1;
		}
	    }
	}
	if (!nodep->sensp()->castNodeVarRef()) {
	    if (debug()) nodep->dumpTree(cout,"-tree: ");
	    nodep->v3error("Unsupported: Complex statement in sensitivity list");
	}
    }

    void iterateSelTriop(AstNodePreSel* nodep) {
	nodep->iterateChildren(*this);
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
	    V3Number widnum (msbp->fileline(),32,msbp->castConst()->toSInt() +1-lsbp->castConst()->toSInt());
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

    void expectFormat(AstNode* nodep, const string& format, AstNode* argp, bool isScan) {
	// Check display arguments
	bool inPct = false;
	for (const char* inp = format.c_str(); *inp; inp++) {
	    char ch = tolower(*inp);   // Breaks with iterators...
	    if (!inPct && ch=='%') {
		inPct = true;
	    } else if (inPct) {
		inPct = false;
		switch (ch) {
		case '0': case '1': case '2': case '3': case '4':
		case '5': case '6': case '7': case '8': case '9':
		    inPct = true;
		    break;
		case '%': break;  // %% - just output a %
		case 'm':  // %m - auto insert "name"
		    if (isScan) nodep->v3error("Unsupported: %m in $fscanf");
		    break;
		default:  // Most operators, just move to next argument
		    if (!V3Number::displayedFmtLegal(ch)) {
			nodep->v3error("Unknown $display format code: %"<<ch);
		    } else {
			if (!argp) {
			    nodep->v3error("Missing arguments for $display format");
			} else {
			    argp = argp->nextp();
			}
		    }
		    break;
		} // switch
	    }
	}
	if (argp) {
	    argp->v3error("Extra arguments for $display format\n");
	}
    }

    void expectDescriptor(AstNode* nodep, AstNodeVarRef* filep) {
	if (!filep) nodep->v3error("Unsupported: $fopen/$fclose/$f* descriptor must be a simple variable");
	if (filep && filep->varp()) filep->varp()->attrFileDescr(true);
    }

    virtual void visit(AstFOpen* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
	expectDescriptor(nodep, nodep->filep()->castNodeVarRef());
    }
    virtual void visit(AstFClose* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
	expectDescriptor(nodep, nodep->filep()->castNodeVarRef());
    }
    virtual void visit(AstFEof* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
	expectDescriptor(nodep, nodep->filep()->castNodeVarRef());
    }
    virtual void visit(AstFFlush* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
	if (nodep->filep()) {
	    expectDescriptor(nodep, nodep->filep()->castNodeVarRef());
	}
    }
    virtual void visit(AstFGetC* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
	expectDescriptor(nodep, nodep->filep()->castNodeVarRef());
    }
    virtual void visit(AstFGetS* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
	expectDescriptor(nodep, nodep->filep()->castNodeVarRef());
    }
    virtual void visit(AstFScanF* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
	expectDescriptor(nodep, nodep->filep()->castNodeVarRef());
	expectFormat(nodep, nodep->text(), nodep->exprsp(), true);
    }
    virtual void visit(AstSScanF* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
	expectFormat(nodep, nodep->text(), nodep->exprsp(), true);
    }
    virtual void visit(AstDisplay* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
	if (nodep->filep()) expectDescriptor(nodep, nodep->filep()->castNodeVarRef());
	expectFormat(nodep, nodep->text(), nodep->exprsp(), false);
	if (!m_assertp
	    && (nodep->displayType() == AstDisplayType::INFO
		|| nodep->displayType() == AstDisplayType::WARNING
		|| nodep->displayType() == AstDisplayType::ERROR
		|| nodep->displayType() == AstDisplayType::FATAL)) {
	    nodep->v3error(nodep->verilogKwd()+" only allowed under a assertion.");
	}
	if (nodep->displayType().needScopeTracking()
	    || nodep->name().find("%m") != string::npos) {
	    nodep->scopeNamep(new AstScopeName(nodep->fileline()));
	}
    }

    virtual void visit(AstScCtor* nodep, AstNUser*) {
	// Constructor info means the module must remain public
	m_modp->modPublic(true);
	nodep->iterateChildren(*this);
    }
    virtual void visit(AstScDtor* nodep, AstNUser*) {
	// Destructor info means the module must remain public
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
	m_assertp = NULL;
	m_senitemCvtNum = 0;
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
