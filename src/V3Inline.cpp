// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Add temporaries, such as for inline nodes
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
// V3Inline's Transformations:
//
// Each module:
//	Look for CELL... PRAGMA INLINE_MODULE
//	    Replicate the cell's module
//	        Convert pins to wires that make assignments
//		Rename vars to include cell name
//	    Insert cell's module statements into the upper module
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"
#include <cstdio>
#include <cstdarg>
#include <unistd.h>
#include <algorithm>
#include <vector>

#include "V3Global.h"
#include "V3Inline.h"
#include "V3Inst.h"
#include "V3Stats.h"
#include "V3Ast.h"

// CONFIG
static const int INLINE_MODS_SMALLER = 100;	// If a mod is < this # nodes, can always inline it

//######################################################################
// Inline state, as a visitor of each AstNode

class InlineMarkVisitor : public AstNVisitor {
private:
    // NODE STATE
    // Output
    //  AstNodeModule::user1()	// OUTPUT: bool. User request to inline this module
    // Entire netlist (can be cleared after this visit completes)
    //  AstNodeModule::user2()	// CIL_*. Allowed to automatically inline module
    //  AstNodeModule::user3()	// int. Number of cells referencing this module
    AstUser1InUse	m_inuser1;
    AstUser2InUse	m_inuser2;
    AstUser3InUse	m_inuser3;

    enum {CIL_NOTHARD=0,	// For user2, inline not supported
	  CIL_NOTSOFT,		// For user2, don't inline unless user overrides
	  CIL_MAYBE};		// For user2, might inline

    // STATE
    AstNodeModule*	m_modp;		// Flattened cell's containing module
    int			m_stmtCnt;	// Statements in module
    V3Double0		m_statUnsup;	// Statistic tracking

    // METHODS
    static int debug() {
	static int level = -1;
	if (VL_UNLIKELY(level < 0)) level = v3Global.opt.debugSrcLevel(__FILE__);
	return level;
    }
    void cantInline(const char* reason, bool hard) {
	if (hard) {
	    if (m_modp->user2() != CIL_NOTHARD) {
		UINFO(4,"  No inline hard: "<<reason<<" "<<m_modp<<endl);
		m_modp->user2(CIL_NOTHARD);
		++m_statUnsup;
	    }
	} else {
	    if (m_modp->user2() == CIL_MAYBE) {
		UINFO(4,"  No inline soft: "<<reason<<" "<<m_modp<<endl);
		m_modp->user2(CIL_NOTSOFT);
	    }
	}
    }

    // VISITORS
    virtual void visit(AstNodeModule* nodep, AstNUser*) {
	m_stmtCnt = 0;
	m_modp = nodep;
	m_modp->user2(CIL_MAYBE);
	if (m_modp->castIface()) {
	    // Inlining an interface means we no longer have a cell handle to resolve to.
	    // If inlining moves post-scope this can perhaps be relaxed.
	    cantInline("modIface",true);
	}
	if (m_modp->modPublic()) cantInline("modPublic",false);
	//
	nodep->iterateChildren(*this);
	//
	bool userinline = nodep->user1();
	int allowed = nodep->user2();
	int refs = nodep->user3();
	// Should we automatically inline this module?
	// inlineMult = 2000 by default.  If a mod*#instances is < this # nodes, can inline it
	bool doit = ((allowed == CIL_NOTSOFT || allowed == CIL_MAYBE)
		     && (userinline
			 || ((allowed == CIL_MAYBE)
			     && (refs==1
				 || m_stmtCnt < INLINE_MODS_SMALLER
				 || v3Global.opt.inlineMult() < 1
				 || refs*m_stmtCnt < v3Global.opt.inlineMult()))));
	// Packages aren't really "under" anything so they confuse this algorithm
	if (nodep->castPackage()) doit = false;
	UINFO(4, " Inline="<<doit<<" Possible="<<allowed<<" Usr="<<userinline<<" Refs="<<refs<<" Stmts="<<m_stmtCnt
	      <<"  "<<nodep<<endl);
	nodep->user1(doit);
	m_modp = NULL;
    }
    virtual void visit(AstCell* nodep, AstNUser*) {
	nodep->modp()->user3Inc();
	nodep->iterateChildren(*this);
    }
    virtual void visit(AstPragma* nodep, AstNUser*) {
	if (nodep->pragType() == AstPragmaType::INLINE_MODULE) {
	    //UINFO(0,"PRAG MARK "<<m_modp<<endl);
	    if (!m_modp) {
		nodep->v3error("Inline pragma not under a module");
	    } else {
		m_modp->user1(1);
	    }
	    nodep->unlinkFrBack()->deleteTree(); nodep=NULL;  // Remove so don't propagate to upper cell...
	} else if (nodep->pragType() == AstPragmaType::NO_INLINE_MODULE) {
	    if (!m_modp) {
		nodep->v3error("Inline pragma not under a module");
	    } else {
		cantInline("Pragma NO_INLINE_MODULE",false);
	    }
	    nodep->unlinkFrBack()->deleteTree(); nodep=NULL;  // Remove so don't propagate to upper cell...
	} else {
	    nodep->iterateChildren(*this);
	}
    }
    virtual void visit(AstVarXRef* nodep, AstNUser*) {
	// Cleanup link until V3LinkDot can correct it
	nodep->varp(NULL);
    }
    virtual void visit(AstVar* nodep, AstNUser*) {
	// Can't look at AstIfaceRefDType directly as it is no longer underneath the module
	if (nodep->isIfaceRef()) {
	    // Unsupported: Inlining of modules with ifaces (see AstIface comment above)
	    if (m_modp) cantInline("Interfaced",true);
	}
	nodep->iterateChildren(*this);
    }
    virtual void visit(AstNodeFTaskRef* nodep, AstNUser*) {
	// Cleanup link until V3LinkDot can correct it
	if (!nodep->packagep()) nodep->taskp(NULL);
	nodep->iterateChildren(*this);
    }
    // Nop's to speed up the loop
    virtual void visit(AstAlways* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
	m_stmtCnt++;
    }
    virtual void visit(AstNodeAssign* nodep, AstNUser*) {
	// Don't count assignments, as they'll likely flatten out
	// Still need to iterate though to nullify VarXRefs
	int oldcnt = m_stmtCnt;
	nodep->iterateChildren(*this);
	m_stmtCnt = oldcnt;
    }
    //--------------------
    // Default: Just iterate
    virtual void visit(AstNode* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
	m_stmtCnt++;
    }

public:
    // CONSTUCTORS
    InlineMarkVisitor(AstNode* nodep) {
	m_modp = NULL;
	m_stmtCnt = 0;
	nodep->accept(*this);
    }
    virtual ~InlineMarkVisitor() {
	V3Stats::addStat("Optimizations, Inline unsupported", m_statUnsup);
	// Done with these, are not outputs
	AstNode::user2ClearTree();
	AstNode::user3ClearTree();
    }
};

//######################################################################
// Using clonep(), find cell cross references.
// clone() must not be called inside this visitor

class InlineCollectVisitor : public AstNVisitor {
private:
    // NODE STATE
    //  Output:
    //   AstCell::user4p()	// AstCell* of the created clone

    static int debug() {
	static int level = -1;
	if (VL_UNLIKELY(level < 0)) level = v3Global.opt.debugSrcLevel(__FILE__);
	return level;
    }

    // VISITORS
    virtual void visit(AstCell* nodep, AstNUser*) {
	nodep->user4p(nodep->clonep());
    }
    // Accelerate
    virtual void visit(AstNodeStmt* nodep, AstNUser*) {}
    virtual void visit(AstNodeMath* nodep, AstNUser*) {}
    virtual void visit(AstNode* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
    }

public:
    // CONSTUCTORS
    InlineCollectVisitor(AstNodeModule* nodep) {  // passed OLD module, not new one
	nodep->accept(*this);
    }
    virtual ~InlineCollectVisitor() {}
};

//######################################################################
// After cell is cloned, relink the new module's contents

class InlineRelinkVisitor : public AstNVisitor {
private:
    // NODE STATE
    //  Input:
    //   See InlineVisitor

    // STATE
    AstNodeModule*	m_modp;		// Current module
    AstCell*		m_cellp;	// Cell being cloned

    static int debug() {
	static int level = -1;
	if (VL_UNLIKELY(level < 0)) level = v3Global.opt.debugSrcLevel(__FILE__);
	return level;
    }

    // VISITORS
    virtual void visit(AstCellInline* nodep, AstNUser*) {
	// Inlined cell under the inline cell, need to move to avoid conflicts
	nodep->unlinkFrBack();
	m_modp->addInlinesp(nodep);
	// Rename
	string name = m_cellp->name() + "__DOT__" + nodep->name();
	nodep->name(name);
	UINFO(6, "    Inline "<<nodep<<endl);
	// Do CellInlines under this, but don't move them
	nodep->iterateChildren(*this);
    }
    virtual void visit(AstCell* nodep, AstNUser*) {
	// Cell under the inline cell, need to rename to avoid conflicts
	string name = m_cellp->name() + "__DOT__" + nodep->name();
	nodep->name(name);
	nodep->iterateChildren(*this);
    }
    virtual void visit(AstVar* nodep, AstNUser*) {
	if (nodep->user2p()) {
	    // Make an assignment, so we'll trace it properly
	    // user2p is either a const or a var.
	    AstConst*  exprconstp  = nodep->user2p()->castNode()->castConst();
	    AstVarRef* exprvarrefp = nodep->user2p()->castNode()->castVarRef();
	    UINFO(8,"connectto: "<<nodep->user2p()->castNode()<<endl);
	    if (!exprconstp && !exprvarrefp) {
		nodep->v3fatalSrc("Unknown interconnect type; pinReconnectSimple should have cleared up\n");
	    }
	    if (exprconstp) {
		m_modp->addStmtp(new AstAssignW(nodep->fileline(),
						new AstVarRef(nodep->fileline(), nodep, true),
						exprconstp->cloneTree(true)));
	    } else if (nodep->user3()) {
		// Public variable at the lower module end - we need to make sure we propagate
		// the logic changes up and down; if we aliased, we might remove the change detection
		// on the output variable.
		UINFO(9,"public pin assign: "<<exprvarrefp<<endl);
		if (nodep->isInput()) nodep->v3fatalSrc("Outputs only - inputs use AssignAlias");
		m_modp->addStmtp(new AstAssignW(nodep->fileline(),
						new AstVarRef(nodep->fileline(), exprvarrefp->varp(), true),
						new AstVarRef(nodep->fileline(), nodep, false)));
	    } else if (nodep->isIfaceRef()) {
		m_modp->addStmtp(new AstAssignVarScope(nodep->fileline(),
						       new AstVarRef(nodep->fileline(), nodep, true),
						       new AstVarRef(nodep->fileline(), exprvarrefp->varp(), false)));
		AstNode* nodebp=exprvarrefp->varp();
		nodep ->fileline()->modifyStateInherit(nodebp->fileline());
		nodebp->fileline()->modifyStateInherit(nodep ->fileline());
	    } else {
		// Do to inlining child's variable now within the same module, so a AstVarRef not AstVarXRef below
		m_modp->addStmtp(new AstAssignAlias(nodep->fileline(),
						    new AstVarRef(nodep->fileline(), nodep, true),
						    new AstVarRef(nodep->fileline(), exprvarrefp->varp(), false)));
		AstNode* nodebp=exprvarrefp->varp();
		nodep ->fileline()->modifyStateInherit(nodebp->fileline());
		nodebp->fileline()->modifyStateInherit(nodep ->fileline());
	    }
	}
	// Variable under the inline cell, need to rename to avoid conflicts
	// Also clear I/O bits, as it is now local.
	string name = m_cellp->name() + "__DOT__" + nodep->name();
	if (!nodep->isFuncLocal()) nodep->inlineAttrReset(name);
	if (!m_cellp->isTrace()) nodep->trace(false);
	if (debug()>=9) { nodep->dumpTree(cout,"varchanged:"); }
	if (debug()>=9) { nodep->valuep()->dumpTree(cout,"varchangei:"); }
	// Iterate won't hit AstIfaceRefDType directly as it is no longer underneath the module
	if (AstIfaceRefDType* ifacerefp = nodep->dtypep()->castIfaceRefDType()) {
	    // Relink to point to newly cloned cell
	    if (ifacerefp->cellp()) {
		if (AstCell* newcellp = ifacerefp->cellp()->user4p()->castNode()->castCell()) {
		    ifacerefp->cellp(newcellp);
		    ifacerefp->cellName(newcellp->name());
		}
	    }
	}
	nodep->iterateChildren(*this);
    }
    virtual void visit(AstNodeFTask* nodep, AstNUser*) {
	// Function under the inline cell, need to rename to avoid conflicts
	nodep->name(m_cellp->name() + "__DOT__" + nodep->name());
	nodep->iterateChildren(*this);
    }
    virtual void visit(AstTypedef* nodep, AstNUser*) {
	// Typedef under the inline cell, need to rename to avoid conflicts
	nodep->name(m_cellp->name() + "__DOT__" + nodep->name());
	nodep->iterateChildren(*this);
    }
    virtual void visit(AstVarRef* nodep, AstNUser*) {
	if (nodep->varp()->user2p()  // It's being converted to an alias.
	    && !nodep->varp()->user3()
	    && !nodep->backp()->castAssignAlias()) { 	// Don't constant propagate aliases (we just made)
	    AstConst*  exprconstp  = nodep->varp()->user2p()->castNode()->castConst();
	    AstVarRef* exprvarrefp = nodep->varp()->user2p()->castNode()->castVarRef();
	    if (exprconstp) {
		nodep->replaceWith(exprconstp->cloneTree(true));
		nodep->deleteTree(); nodep=NULL;
		return;
	    }
	    else if (exprvarrefp) {
		nodep->varp( exprvarrefp->varp() );
	    }
	    else {
		nodep->v3fatalSrc("Null connection?\n");
	    }
	}
	nodep->name(nodep->varp()->name());
	nodep->iterateChildren(*this);
    }
    virtual void visit(AstVarXRef* nodep, AstNUser*) {
	// Track what scope it was originally under so V3LinkDot can resolve it
	string newname = m_cellp->name();
	if (nodep->inlinedDots() != "") { newname += "." + nodep->inlinedDots(); }
	nodep->inlinedDots(newname);
	UINFO(8,"   "<<nodep<<endl);
	nodep->iterateChildren(*this);
    }
    virtual void visit(AstNodeFTaskRef* nodep, AstNUser*) {
	// Track what scope it was originally under so V3LinkDot can resolve it
	string newname = m_cellp->name();
	if (nodep->inlinedDots() != "") { newname += "." + nodep->inlinedDots(); }
	nodep->inlinedDots(newname);
	UINFO(8,"   "<<nodep<<endl);
	nodep->iterateChildren(*this);
    }

    // Not needed, as V3LinkDot doesn't care about typedefs
    //virtual void visit(AstRefDType* nodep, AstNUser*) {}

    virtual void visit(AstScopeName* nodep, AstNUser*) {
	// If there's a %m in the display text, we add a special node that will contain the name()
	// Similar code in V3Begin
	// To keep correct visual order, must add before other Text's
	AstNode* afterp = nodep->scopeAttrp();
	if (afterp) afterp->unlinkFrBackWithNext();
	nodep->scopeAttrp(new AstText(nodep->fileline(), (string)"__DOT__"+m_cellp->name()));
	if (afterp) nodep->scopeAttrp(afterp);
	afterp = nodep->scopeEntrp();
	if (afterp) afterp->unlinkFrBackWithNext();
	nodep->scopeEntrp(new AstText(nodep->fileline(), (string)"__DOT__"+m_cellp->name()));
	if (afterp) nodep->scopeEntrp(afterp);
	nodep->iterateChildren(*this);
    }
    virtual void visit(AstCoverDecl* nodep, AstNUser*) {
	// Fix path in coverage statements
	nodep->hier(m_cellp->prettyName()
		    + (nodep->hier()!="" ? ".":"")
		    + nodep->hier());
	nodep->iterateChildren(*this);
    }
    virtual void visit(AstNode* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
    }

public:
    // CONSTUCTORS
    InlineRelinkVisitor(AstNodeModule* cloneModp, AstNodeModule* oldModp, AstCell* cellp) {
	m_modp = oldModp;
	m_cellp = cellp;
	cloneModp->accept(*this);
    }
    virtual ~InlineRelinkVisitor() {}
};

//######################################################################
// Inline state, as a visitor of each AstNode

class InlineVisitor : public AstNVisitor {
private:
    // NODE STATE
    // Cleared entire netlist
    //  Input:
    //   AstNodeModule::user1p()	// bool. True to inline this module (from InlineMarkVisitor)
    // Cleared each cell
    //   AstVar::user2p()	// AstVarRef*/AstConst*  Points to signal this is a direct connect to
    //   AstVar::user3()	// bool    Don't alias the user2, keep it as signal
    //   AstCell::user4		// AstCell* of the created clone

    AstUser4InUse	m_inuser4;

    // STATE
    AstNodeModule*	m_modp;		// Current module
    V3Double0		m_statCells;	// Statistic tracking

    static int debug() {
	static int level = -1;
	if (VL_UNLIKELY(level < 0)) level = v3Global.opt.debugSrcLevel(__FILE__);
	return level;
    }

    // VISITORS
    virtual void visit(AstNetlist* nodep, AstNUser*) {
	// Iterate modules backwards, in bottom-up order.  Required!
	nodep->iterateChildrenBackwards(*this);
    }
    virtual void visit(AstNodeModule* nodep, AstNUser*) {
	m_modp = nodep;
	nodep->iterateChildren(*this);
    }
    virtual void visit(AstCell* nodep, AstNUser*) {
	if (nodep->modp()->user1()) {  // Marked with inline request
	    UINFO(5," Inline CELL   "<<nodep<<endl);
	    UINFO(5,"   To MOD      "<<m_modp<<endl);
	    ++m_statCells;

	    // Before cloning simplify pin assignments
	    // Better off before, as if module has multiple instantiations
	    // we'll save work, and we can't call pinReconnectSimple in
	    // this loop as it clone()s itself.
	    for (AstPin* pinp = nodep->pinsp(); pinp; pinp=pinp->nextp()->castPin()) {
		if (!pinp->exprp()) continue;
		V3Inst::pinReconnectSimple(pinp, nodep, m_modp, false);
	    }

	    // Clone original module
	    if (debug()>=9) { nodep->dumpTree(cout,"inlcell:"); }
	    //if (debug()>=9) { nodep->modp()->dumpTree(cout,"oldmod:"); }
	    AstNodeModule* newmodp = nodep->modp()->cloneTree(false);
	    if (debug()>=9) { newmodp->dumpTree(cout,"newmod:"); }
	    // Clear var markings and find cell cross references
	    AstNode::user2ClearTree();
	    AstNode::user4ClearTree();
	    { InlineCollectVisitor(nodep->modp()); }  // {} to destroy visitor immediately
	    // Create data for dotted variable resolution
	    AstCellInline* inlinep = new AstCellInline(nodep->fileline(),
						       nodep->name(), nodep->modp()->origName());
	    m_modp->addInlinesp(inlinep);  // Must be parsed before any AstCells
	    // Create assignments to the pins
	    for (AstPin* pinp = nodep->pinsp(); pinp; pinp=pinp->nextp()->castPin()) {
		if (!pinp->exprp()) continue;
		UINFO(6,"     Pin change from "<<pinp->modVarp()<<endl);
		// Make new signal; even though we'll optimize the interconnect, we
		// need an alias to trace correctly.  If tracing is disabled, we'll
		// delete it in later optimizations.
		AstVar* pinOldVarp = pinp->modVarp();
		AstVar* pinNewVarp = pinOldVarp->clonep()->castVar();

		AstNode* connectRefp = pinp->exprp();
		if (!connectRefp->castConst() && !connectRefp->castVarRef()) {
		    pinp->v3fatalSrc("Unknown interconnect type; pinReconnectSimple should have cleared up\n");
		}
		if (pinNewVarp->isOutOnly() && connectRefp->castConst()) {
		    pinp->v3error("Output port is connected to a constant pin, electrical short");
		}

		// Propagate any attributes across the interconnect
		pinNewVarp->propagateAttrFrom(pinOldVarp);
		if (connectRefp->castVarRef()) {
		    connectRefp->castVarRef()->varp()->propagateAttrFrom(pinOldVarp);
		}

		// One to one interconnect won't make a temporary variable.
		// This prevents creating a lot of extra wires for clock signals.
		// It will become a tracing alias.
		UINFO(6,"One-to-one "<<connectRefp<<endl);
		UINFO(6,"       -to "<<pinNewVarp<<endl);
		pinNewVarp->user2p(connectRefp);
		// Public output inside the cell must go via an assign rather than alias
		// Else the public logic will set the alias, losing the value to be propagated up
		// (InOnly isn't a problem as the AssignAlias will create the assignment for us)
		pinNewVarp->user3(pinNewVarp->isSigUserRWPublic() && pinNewVarp->isOutOnly());
	    }
	    // Cleanup var names, etc, to not conflict
	    { InlineRelinkVisitor(newmodp, m_modp, nodep); }
	    // Move statements to top module
	    if (debug()>=9) { newmodp->dumpTree(cout,"fixmod:"); }
	    AstNode* stmtsp = newmodp->stmtsp();
	    if (stmtsp) stmtsp->unlinkFrBackWithNext();
	    if (stmtsp) m_modp->addStmtp(stmtsp);
	    // Remove the cell
	    newmodp->deleteTree(); newmodp=NULL; // Clear any leftover ports, etc
	    nodep->unlinkFrBack();
	    pushDeletep(nodep); nodep = NULL;
	    if (debug()>=9) { m_modp->dumpTree(cout,"donemod:"); }
	}
    }

    //--------------------
    virtual void visit(AstNodeMath* nodep, AstNUser*) {}  // Accelerate
    virtual void visit(AstNodeStmt* nodep, AstNUser*) {}  // Accelerate
    virtual void visit(AstNode* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
    }

public:
    // CONSTUCTORS
    InlineVisitor(AstNode* nodep) {
	m_modp = NULL;
	nodep->accept(*this);
    }
    virtual ~InlineVisitor() {
	V3Stats::addStat("Optimizations, Inlined cells", m_statCells);
    }
};

//######################################################################
// Inline class functions

void V3Inline::inlineAll(AstNetlist* nodep) {
    UINFO(2,__FUNCTION__<<": "<<endl);
    InlineMarkVisitor mvisitor (nodep);
    InlineVisitor visitor (nodep);
    // Remove all modules that were inlined
    // V3Dead will also clean them up, but if we have debug on, it's a good
    // idea to avoid dumping the hugely exploded tree.
    AstNodeModule* nextmodp;
    for (AstNodeModule* modp = v3Global.rootp()->modulesp(); modp; modp=nextmodp) {
	nextmodp = modp->nextp()->castNodeModule();
	if (modp->user1()) { // Was inlined
	    modp->unlinkFrBack()->deleteTree(); modp=NULL;
	}
    }
    V3Global::dumpCheckGlobalTree("inline.tree", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}
