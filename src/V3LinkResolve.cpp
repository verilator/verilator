// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Resolve module/signal name references
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
    AstUser2InUse	m_inuser2;

    // STATE
    // Below state needs to be preserved between each module call.
    AstNodeModule*	m_modp;		// Current module
    AstNodeFTask* m_ftaskp;	// Function or task we're inside
    AstVAssert*	m_assertp;	// Current assertion
    int		m_senitemCvtNum; // Temporary signal counter

    // METHODS
    static int debug() {
	static int level = -1;
	if (VL_UNLIKELY(level < 0)) level = v3Global.opt.debugSrcLevel(__FILE__);
	return level;
    }

    // VISITs
    // TODO: Most of these visitors are here for historical reasons.
    // TODO: ExpectDecriptor can move to data type resolution, and the rest
    // TODO: could move to V3LinkParse to get them out of the way of elaboration
    virtual void visit(AstNodeModule* nodep, AstNUser*) {
	// Module: Create sim table for entire module and iterate
	UINFO(8,"MODULE "<<nodep<<endl);
	if (nodep->dead()) return;
	m_modp = nodep;
	m_senitemCvtNum = 0;
	nodep->iterateChildren(*this);
	m_modp = NULL;
    }
    virtual void visit(AstInitial* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
	// Initial assignments under function/tasks can just be simple assignments without the initial
	if (m_ftaskp) {
	    nodep->replaceWith(nodep->bodysp()->unlinkFrBackWithNext()); nodep=NULL;
	}
    }
    virtual void visit(AstVAssert* nodep, AstNUser*) {
	if (m_assertp) nodep->v3error("Assert not allowed under another assert");
	m_assertp = nodep;
	nodep->iterateChildren(*this);
	m_assertp = NULL;
    }

    virtual void visit(AstVar* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
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
	if (nodep->dpiExport()) {
	    nodep->scopeNamep(new AstScopeName(nodep->fileline()));
	}
    }
    virtual void visit(AstNodeFTaskRef* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
	if (nodep->taskp() && (nodep->taskp()->dpiContext() || nodep->taskp()->dpiExport())) {
	    nodep->scopeNamep(new AstScopeName(nodep->fileline()));
	}
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
					      VFlagLogicPacked(), 1);
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
		if (AstNodePreSel* selp = nodep->sensp()->castNodePreSel()) {
		    AstNode* fromp = selp->lhsp()->unlinkFrBack();
		    selp->replaceWith(fromp); selp->deleteTree(); selp=NULL;
		    did=1;
		}
	    }
	}
	if (!nodep->sensp()->castNodeVarRef()
	    && !nodep->sensp()->castEnumItemRef()) {  // V3Const will cleanup
	    if (debug()) nodep->dumpTree(cout,"-tree: ");
	    nodep->v3error("Unsupported: Complex statement in sensitivity list");
	}
    }
    virtual void visit(AstSenGate* nodep, AstNUser*) {
	nodep->v3fatalSrc("SenGates shouldn't be in tree yet");
    }

    virtual void visit(AstNodePreSel* nodep, AstNUser*) {
	if (!nodep->attrp()) {
	    nodep->iterateChildren(*this);
	    // Constification may change the fromp() to a constant, which will lose the
	    // variable we're extracting from (to determine MSB/LSB/endianness/etc.)
	    // So we replicate it in another node
	    // Note that V3Param knows not to replace AstVarRef's under AstAttrOf's
	    AstNode* basefromp = AstArraySel::baseFromp(nodep);
	    if (AstNodeVarRef* varrefp = basefromp->castNodeVarRef()) {  // Maybe varxref - so need to clone
		nodep->attrp(new AstAttrOf(nodep->fileline(), AstAttrType::VAR_BASE,
					   varrefp->cloneTree(false)));
	    } else if (AstMemberSel* fromp = basefromp->castMemberSel()) {
		nodep->attrp(new AstAttrOf(nodep->fileline(), AstAttrType::MEMBER_BASE,
					   fromp->cloneTree(false)));
	    } else if (AstEnumItemRef* fromp = basefromp->castEnumItemRef()) {
		nodep->attrp(new AstAttrOf(nodep->fileline(), AstAttrType::ENUM_BASE,
					   fromp->cloneTree(false)));
	    } else {
		if (basefromp) { UINFO(1,"    Related node: "<<basefromp<<endl); }
		nodep->v3fatalSrc("Illegal bit select; no signal/member being extracted from");
	    }
	}
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
	for (string::const_iterator it = format.begin(); it != format.end(); ++it) {
	    char ch = tolower(*it);
	    if (!inPct && ch=='%') {
		inPct = true;
	    } else if (inPct) {
		inPct = false;
		switch (tolower(ch)) {
		case '0': case '1': case '2': case '3': case '4':
		case '5': case '6': case '7': case '8': case '9':
		case '.':
		    inPct = true;
		    break;
		case '%': break;  // %% - just output a %
		case 'm':  // %m - auto insert "name"
		    if (isScan) nodep->v3error("Unsupported: %m in $fscanf");
		    break;
		default:  // Most operators, just move to next argument
		    if (!V3Number::displayedFmtLegal(ch)) {
			nodep->v3error("Unknown $display-like format code: %"<<ch);
		    } else {
			if (!argp) {
			    nodep->v3error("Missing arguments for $display-like format");
			} else {
			    argp = argp->nextp();
			}
		    }
		    break;
		} // switch
	    }
	}
	if (argp) {
	    argp->v3error("Extra arguments for $display-like format");
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
    virtual void visit(AstSFormatF* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
	expectFormat(nodep, nodep->text(), nodep->exprsp(), false);
	if ((nodep->backp()->castDisplay() && nodep->backp()->castDisplay()->displayType().needScopeTracking())
	    || nodep->formatScopeTracking()) {
	    nodep->scopeNamep(new AstScopeName(nodep->fileline()));
	}
    }
    virtual void visit(AstDisplay* nodep, AstNUser* vup) {
	nodep->iterateChildren(*this);
	if (nodep->filep()) expectDescriptor(nodep, nodep->filep()->castNodeVarRef());
	if (!m_assertp
	    && (nodep->displayType() == AstDisplayType::DT_INFO
		|| nodep->displayType() == AstDisplayType::DT_WARNING
		|| nodep->displayType() == AstDisplayType::DT_ERROR
		|| nodep->displayType() == AstDisplayType::DT_FATAL)) {
	    nodep->v3error(nodep->verilogKwd()+" only allowed under an assertion.");
	}
    }

    virtual void visit(AstUdpTable* nodep, AstNUser*) {
	UINFO(5,"UDPTABLE  "<<nodep<<endl);
	if (!v3Global.opt.bboxUnsup()) {
	    // We don't warn until V3Inst, so that UDPs that are in libraries and
	    // never used won't result in any warnings.
	} else {
	    // Massive hack, just tie off all outputs so our analysis can proceed
	    AstVar* varoutp = NULL;
	    for (AstNode* stmtp = m_modp->stmtsp(); stmtp; stmtp=stmtp->nextp()) {
		if (AstVar* varp = stmtp->castVar()) {
		    if (varp->isInput()) {
		    } else if (varp->isOutput()) {
			if (varoutp) { varp->v3error("Multiple outputs not allowed in udp modules"); }
			varoutp = varp;
			// Tie off
			m_modp->addStmtp(new AstAssignW(varp->fileline(),
							new AstVarRef(varp->fileline(), varp, true),
							new AstConst(varp->fileline(), AstConst::LogicFalse())));
		    } else {
			varp->v3error("Only inputs and outputs are allowed in udp modules");
		    }
		}
	    }
	    nodep->unlinkFrBack(); pushDeletep(nodep); nodep=NULL;
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
    AstNodeModule*	m_modp;		// Current module

    // METHODS
    static int debug() {
	static int level = -1;
	if (VL_UNLIKELY(level < 0)) level = v3Global.opt.debugSrcLevel(__FILE__);
	return level;
    }

    // VISITs
    virtual void visit(AstNetlist* nodep, AstNUser*) {
	// Iterate modules backwards, in bottom-up order.
	nodep->iterateChildrenBackwards(*this);
    }
    virtual void visit(AstNodeModule* nodep, AstNUser*) {
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
    V3Global::dumpCheckGlobalTree("linkresolve.tree", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 6);
}
