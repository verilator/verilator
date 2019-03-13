// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Resolve module/signal name references
//
// Code available from: http://www.veripool.org/verilator
//
//*************************************************************************
//
// Copyright 2003-2019 by Wilson Snyder.  This program is free software; you can
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

#include "V3Global.h"
#include "V3String.h"
#include "V3LinkResolve.h"
#include "V3Ast.h"

#include <algorithm>
#include <cstdarg>
#include <map>
#include <vector>

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
    VL_DEBUG_FUNC;  // Declare debug()

    // VISITs
    // TODO: Most of these visitors are here for historical reasons.
    // TODO: ExpectDecriptor can move to data type resolution, and the rest
    // TODO: could move to V3LinkParse to get them out of the way of elaboration
    virtual void visit(AstNodeModule* nodep) {
	// Module: Create sim table for entire module and iterate
	UINFO(8,"MODULE "<<nodep<<endl);
	if (nodep->dead()) return;
	m_modp = nodep;
	m_senitemCvtNum = 0;
        iterateChildren(nodep);
	m_modp = NULL;
    }
    virtual void visit(AstInitial* nodep) {
        iterateChildren(nodep);
	// Initial assignments under function/tasks can just be simple assignments without the initial
	if (m_ftaskp) {
	    nodep->replaceWith(nodep->bodysp()->unlinkFrBackWithNext()); VL_DANGLING(nodep);
	}
    }
    virtual void visit(AstVAssert* nodep) {
	if (m_assertp) nodep->v3error("Assert not allowed under another assert");
	m_assertp = nodep;
        iterateChildren(nodep);
	m_assertp = NULL;
    }

    virtual void visit(AstVar* nodep) {
        iterateChildren(nodep);
	if (m_ftaskp) nodep->funcLocal(true);
	if (nodep->isSigModPublic()) {
	    nodep->sigModPublic(false);  // We're done with this attribute
	    m_modp->modPublic(true);	// Avoid flattening if signals are exposed
	}
    }

    virtual void visit(AstNodeVarRef* nodep) {
	// VarRef: Resolve its reference
	if (nodep->varp()) {
	    nodep->varp()->usedParam(true);
	}
        iterateChildren(nodep);
    }

    virtual void visit(AstNodeFTask* nodep) {
	// NodeTask: Remember its name for later resolution
	// Remember the existing symbol table scope
	m_ftaskp = nodep;
        iterateChildren(nodep);
	m_ftaskp = NULL;
	if (nodep->dpiExport()) {
	    nodep->scopeNamep(new AstScopeName(nodep->fileline()));
	}
    }
    virtual void visit(AstNodeFTaskRef* nodep) {
        iterateChildren(nodep);
	if (nodep->taskp() && (nodep->taskp()->dpiContext() || nodep->taskp()->dpiExport())) {
	    nodep->scopeNamep(new AstScopeName(nodep->fileline()));
	}
    }

    virtual void visit(AstSenItem* nodep) {
	// Remove bit selects, and bark if it's not a simple variable
        iterateChildren(nodep);
	if (nodep->isClocked()) {
	    // If it's not a simple variable wrap in a temporary
	    // This is a bit unfortunate as we haven't done width resolution
	    // and any width errors will look a bit odd, but it works.
	    AstNode* sensp = nodep->sensp();
	    if (sensp
                && !VN_IS(sensp, NodeVarRef)
                && !VN_IS(sensp, Const)) {
		// Make a new temp wire
		string newvarname = "__Vsenitemexpr"+cvtToStr(++m_senitemCvtNum);
                AstVar* newvarp = new AstVar(sensp->fileline(), AstVarType::MODULETEMP, newvarname,
                                             VFlagLogicPacked(), 1);
		// We can't just add under the module, because we may be inside a generate, begin, etc.
		// We know a SenItem should be under a SenTree/Always etc, we we'll just hunt upwards
		AstNode* addwherep = nodep;  // Add to this element's next
                while (VN_IS(addwherep, SenItem)
                       || VN_IS(addwherep, SenTree)) {
		    addwherep = addwherep->backp();
		}
                if (!VN_IS(addwherep, Always)) {  // Assertion perhaps?
		    sensp->v3error("Unsupported: Non-single-bit pos/negedge clock statement under some complicated block");
		    addwherep = m_modp;
		}
		addwherep->addNext(newvarp);

                sensp->replaceWith(new AstVarRef(sensp->fileline(), newvarp, false));
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
                if (AstNodeSel* selp = VN_CAST(nodep->sensp(), NodeSel)) {
		    AstNode* fromp = selp->fromp()->unlinkFrBack();
		    selp->replaceWith(fromp); selp->deleteTree(); VL_DANGLING(selp);
		    did=1;
		}
		// NodeSel doesn't include AstSel....
                if (AstSel* selp = VN_CAST(nodep->sensp(), Sel)) {
		    AstNode* fromp = selp->fromp()->unlinkFrBack();
		    selp->replaceWith(fromp); selp->deleteTree(); VL_DANGLING(selp);
		    did=1;
		}
                if (AstNodePreSel* selp = VN_CAST(nodep->sensp(), NodePreSel)) {
		    AstNode* fromp = selp->lhsp()->unlinkFrBack();
		    selp->replaceWith(fromp); selp->deleteTree(); VL_DANGLING(selp);
		    did=1;
		}
	    }
	}
        if (!VN_IS(nodep->sensp(), NodeVarRef)
            && !VN_IS(nodep->sensp(), EnumItemRef)  // V3Const will cleanup
	    && !nodep->isIllegal()) {
	    if (debug()) nodep->dumpTree(cout,"-tree: ");
	    nodep->v3error("Unsupported: Complex statement in sensitivity list");
	}
    }
    virtual void visit(AstSenGate* nodep) {
	nodep->v3fatalSrc("SenGates shouldn't be in tree yet");
    }

    virtual void visit(AstNodePreSel* nodep) {
	if (!nodep->attrp()) {
            iterateChildren(nodep);
	    // Constification may change the fromp() to a constant, which will lose the
	    // variable we're extracting from (to determine MSB/LSB/endianness/etc.)
	    // So we replicate it in another node
	    // Note that V3Param knows not to replace AstVarRef's under AstAttrOf's
	    AstNode* basefromp = AstArraySel::baseFromp(nodep);
            if (AstNodeVarRef* varrefp = VN_CAST(basefromp, NodeVarRef)) {  // Maybe varxref - so need to clone
		nodep->attrp(new AstAttrOf(nodep->fileline(), AstAttrType::VAR_BASE,
					   varrefp->cloneTree(false)));
            } else if (AstUnlinkedRef* uvxrp = VN_CAST(basefromp, UnlinkedRef)) {  // Maybe unlinked - so need to clone
		nodep->attrp(new AstAttrOf(nodep->fileline(), AstAttrType::VAR_BASE,
					   uvxrp->cloneTree(false)));
            } else if (AstMemberSel* fromp = VN_CAST(basefromp, MemberSel)) {
		nodep->attrp(new AstAttrOf(nodep->fileline(), AstAttrType::MEMBER_BASE,
					   fromp->cloneTree(false)));
            } else if (AstEnumItemRef* fromp = VN_CAST(basefromp, EnumItemRef)) {
		nodep->attrp(new AstAttrOf(nodep->fileline(), AstAttrType::ENUM_BASE,
					   fromp->cloneTree(false)));
            } else if (VN_IS(basefromp, Replicate)) {
                // From {...}[...] syntax in IEEE 2017
                if (basefromp) { UINFO(1,"    Related node: "<<basefromp<<endl); }
                nodep->v3error("Unsupported: Select of concatenation");
		nodep = NULL;
	    } else {
		if (basefromp) { UINFO(1,"    Related node: "<<basefromp<<endl); }
		nodep->v3fatalSrc("Illegal bit select; no signal/member being extracted from");
	    }
	}
    }

    virtual void visit(AstCaseItem* nodep) {
	// Move default caseItems to the bottom of the list
	// That saves us from having to search each case list twice, for non-defaults and defaults
        iterateChildren(nodep);
	if (!nodep->user2() && nodep->isDefault() && nodep->nextp()) {
	    nodep->user2(true);
	    AstNode* nextp = nodep->nextp();
	    nodep->unlinkFrBack();
	    nextp->addNext(nodep);
	}
    }

    virtual void visit(AstPragma* nodep) {
	if (nodep->pragType() == AstPragmaType::PUBLIC_MODULE) {
	    if (!m_modp) nodep->v3fatalSrc("PUBLIC_MODULE not under a module");
	    m_modp->modPublic(true);
	    nodep->unlinkFrBack(); pushDeletep(nodep); VL_DANGLING(nodep);
	}
	else if (nodep->pragType() == AstPragmaType::PUBLIC_TASK) {
	    if (!m_ftaskp) nodep->v3fatalSrc("PUBLIC_TASK not under a task");
	    m_ftaskp->taskPublic(true);
	    m_modp->modPublic(true);  // Need to get to the task...
	    nodep->unlinkFrBack(); pushDeletep(nodep); VL_DANGLING(nodep);
	}
	else if (nodep->pragType() == AstPragmaType::COVERAGE_BLOCK_OFF) {
	    if (!v3Global.opt.coverageLine()) {  // No need for block statements; may optimize better without
		nodep->unlinkFrBack(); pushDeletep(nodep); VL_DANGLING(nodep);
	    }
	}
	else {
            iterateChildren(nodep);
	}
    }

    string expectFormat(AstNode* nodep, const string& format, AstNode* argp, bool isScan) {
	// Check display arguments, return new format string
	string newFormat;
	bool inPct = false;
        string fmt;
	for (string::const_iterator it = format.begin(); it != format.end(); ++it) {
	    char ch = *it;
	    if (!inPct && ch=='%') {
		inPct = true;
		fmt = ch;
	    } else if (inPct && (isdigit(ch) || ch=='.')) {
		fmt += ch;
	    } else if (inPct) {
		inPct = false;
		fmt += ch;
		switch (tolower(ch)) {
		case '%':  // %% - just output a %
		    break;
		case 'm':  // %m - auto insert "name"
		    if (isScan) { nodep->v3error("Unsupported: %m in $fscanf"); fmt = ""; }
		    break;
		case 'l':  // %l - auto insert "library"
		    if (isScan) { nodep->v3error("Unsupported: %l in $fscanf"); fmt = ""; }
		    if (m_modp) fmt = VString::quotePercent(m_modp->prettyName());
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
		newFormat += fmt;
	    } else {
		newFormat += ch;
	    }
	}

	if (argp && !isScan) {
	    int skipCount = 0; // number of args consume by any additional format strings
	    while (argp) {
		if (skipCount) {
		    argp = argp->nextp();
		    skipCount--;
		    continue;
		}
                AstConst *constp = VN_CAST(argp, Const);
		bool isFromString = (constp) ? constp->num().isFromString() : false;
		if (isFromString) {
		    int numchars = argp->dtypep()->width()/8;
		    string str(numchars, ' ');
		    // now scan for % operators
		    bool inpercent = false;
		    for (int i = 0; i < numchars; i++) {
			int ii = numchars - i - 1;
			char c = constp->num().dataByte(ii);
			str[i] = c;
			if (!inpercent && c == '%') {
			    inpercent = true;
			} else if (inpercent) {
			    inpercent = 0;
			    switch (c) {
			    case '0': case '1': case '2': case '3': case '4':
			    case '5': case '6': case '7': case '8': case '9':
			    case '.':
				inpercent = true;
				break;
			    case '%':
				break;
			    default:
				if (V3Number::displayedFmtLegal(c)) {
				    skipCount++;
				}
			    }
			}
		    }
		    newFormat.append(str);
		    AstNode *nextp = argp->nextp();
		    argp->unlinkFrBack(); pushDeletep(argp); VL_DANGLING(argp);
		    argp = nextp;
		} else {
		    newFormat.append("%h");
		    argp = argp->nextp();
		}
	    }
	}
	return newFormat;
    }

    void expectDescriptor(AstNode* nodep, AstNodeVarRef* filep) {
	if (!filep) nodep->v3error("Unsupported: $fopen/$fclose/$f* descriptor must be a simple variable");
	if (filep && filep->varp()) filep->varp()->attrFileDescr(true);
    }

    virtual void visit(AstFOpen* nodep) {
        iterateChildren(nodep);
        expectDescriptor(nodep, VN_CAST(nodep->filep(), NodeVarRef));
    }
    virtual void visit(AstFClose* nodep) {
        iterateChildren(nodep);
        expectDescriptor(nodep, VN_CAST(nodep->filep(), NodeVarRef));
    }
    virtual void visit(AstFEof* nodep) {
        iterateChildren(nodep);
        expectDescriptor(nodep, VN_CAST(nodep->filep(), NodeVarRef));
    }
    virtual void visit(AstFRead* nodep) {
        iterateChildren(nodep);
        expectDescriptor(nodep, VN_CAST(nodep->filep(), NodeVarRef));
    }
    virtual void visit(AstFScanF* nodep) {
        iterateChildren(nodep);
	expectFormat(nodep, nodep->text(), nodep->exprsp(), true);
    }
    virtual void visit(AstSScanF* nodep) {
        iterateChildren(nodep);
	expectFormat(nodep, nodep->text(), nodep->exprsp(), true);
    }
    virtual void visit(AstSFormatF* nodep) {
        iterateChildren(nodep);
	// Cleanup old-school displays without format arguments
	if (!nodep->hasFormat()) {
	    if (nodep->text()!="") nodep->v3fatalSrc("Non-format $sformatf should have \"\" format");
            if (VN_IS(nodep->exprsp(), Const)
                && VN_CAST(nodep->exprsp(), Const)->num().isFromString()) {
                AstConst* fmtp = VN_CAST(nodep->exprsp()->unlinkFrBack(), Const);
		nodep->text(fmtp->num().toString());
		pushDeletep(fmtp); VL_DANGLING(fmtp);
	    }
	    nodep->hasFormat(true);
	}
	string newFormat = expectFormat(nodep, nodep->text(), nodep->exprsp(), false);
	nodep->text(newFormat);
        if ((VN_IS(nodep->backp(), Display)
             && VN_CAST(nodep->backp(), Display)->displayType().needScopeTracking())
	    || nodep->formatScopeTracking()) {
	    nodep->scopeNamep(new AstScopeName(nodep->fileline()));
	}
    }
    virtual void visit(AstDisplay* nodep) {
        iterateChildren(nodep);
    }

    virtual void visit(AstUdpTable* nodep) {
	UINFO(5,"UDPTABLE  "<<nodep<<endl);
	if (!v3Global.opt.bboxUnsup()) {
	    // We don't warn until V3Inst, so that UDPs that are in libraries and
	    // never used won't result in any warnings.
	} else {
	    // Massive hack, just tie off all outputs so our analysis can proceed
	    AstVar* varoutp = NULL;
	    for (AstNode* stmtp = m_modp->stmtsp(); stmtp; stmtp=stmtp->nextp()) {
                if (AstVar* varp = VN_CAST(stmtp, Var)) {
                    if (varp->isReadOnly()) {
                    } else if (varp->isWritable()) {
                        if (varoutp) {
                            varp->v3error("Multiple outputs not allowed in udp modules");
                        }
                        varoutp = varp;
                        // Tie off
                        m_modp->addStmtp(new AstAssignW(
                                             varp->fileline(),
                                             new AstVarRef(varp->fileline(), varp, true),
                                             new AstConst(varp->fileline(), AstConst::LogicFalse())));
		    } else {
			varp->v3error("Only inputs and outputs are allowed in udp modules");
		    }
		}
	    }
	    nodep->unlinkFrBack(); pushDeletep(nodep); VL_DANGLING(nodep);
	}
    }

    virtual void visit(AstScCtor* nodep) {
	// Constructor info means the module must remain public
	m_modp->modPublic(true);
        iterateChildren(nodep);
    }
    virtual void visit(AstScDtor* nodep) {
	// Destructor info means the module must remain public
	m_modp->modPublic(true);
        iterateChildren(nodep);
    }
    virtual void visit(AstScInt* nodep) {
	// Special class info means the module must remain public
	m_modp->modPublic(true);
        iterateChildren(nodep);
    }

    virtual void visit(AstNode* nodep) {
	// Default: Just iterate
        iterateChildren(nodep);
    }

public:
    // CONSTUCTORS
    explicit LinkResolveVisitor(AstNetlist* rootp) {
	m_ftaskp = NULL;
	m_modp = NULL;
	m_assertp = NULL;
	m_senitemCvtNum = 0;
	//
        iterate(rootp);
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
    VL_DEBUG_FUNC;  // Declare debug()

    // VISITs
    virtual void visit(AstNetlist* nodep) {
	// Iterate modules backwards, in bottom-up order.
        iterateChildrenBackwards(nodep);
    }
    virtual void visit(AstNodeModule* nodep) {
	m_modp = nodep;
        iterateChildren(nodep);
	m_modp = NULL;
    }
    virtual void visit(AstCell* nodep) {
	// Parent module inherits child's publicity
	if (nodep->modp()->modPublic()) m_modp->modPublic(true);
	//** No iteration for speed
    }
    virtual void visit(AstNodeMath* nodep) {
	// Speedup
    }
    virtual void visit(AstNode* nodep) {
	// Default: Just iterate
        iterateChildren(nodep);
    }
public:
    // CONSTUCTORS
    explicit LinkBotupVisitor(AstNetlist* rootp) {
	m_modp = NULL;
	//
        iterate(rootp);
    }
    virtual ~LinkBotupVisitor() {}
};

//######################################################################
// Link class functions

void V3LinkResolve::linkResolve(AstNetlist* rootp) {
    UINFO(4,__FUNCTION__<<": "<<endl);
    {
        LinkResolveVisitor visitor(rootp);
        LinkBotupVisitor visitorb(rootp);
    }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("linkresolve", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 6);
}
