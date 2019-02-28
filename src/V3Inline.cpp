// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Add temporaries, such as for inline nodes
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

#include "V3Global.h"
#include "V3Inline.h"
#include "V3Inst.h"
#include "V3Stats.h"
#include "V3Ast.h"
#include "V3String.h"

#include <algorithm>
#include <cstdarg>
#include <vector>
#include VL_INCLUDE_UNORDERED_SET

// CONFIG
static const int INLINE_MODS_SMALLER = 100;	// If a mod is < this # nodes, can always inline it

//######################################################################
// Inline state, as a visitor of each AstNode

class InlineMarkVisitor : public AstNVisitor {
private:
    // NODE STATE
    // Output
    //  AstNodeModule::user1()	// OUTPUT: bool. User request to inline this module
    // Internal state (can be cleared after this visit completes)
    //  AstNodeModule::user2()	// CIL_*. Allowed to automatically inline module
    //  AstNodeModule::user3()	// int. Number of cells referencing this module
    //  AstNodeModule::user4()  // int. Statements in module
    AstUser2InUse	m_inuser2;
    AstUser3InUse	m_inuser3;
    AstUser4InUse       m_inuser4;

    // For the user2 field:
    enum {CIL_NOTHARD=0, // Inline not supported
          CIL_NOTSOFT,   // Don't inline unless user overrides
          CIL_MAYBE,     // Might inline
          CIL_USER};     // Pragma suggests inlining

    // STATE
    AstNodeModule*      m_modp;         // Current module
    V3Double0		m_statUnsup;	// Statistic tracking

    typedef std::vector<AstNodeModule*> ModVec;
    ModVec m_allMods;   // All modules, in top-down order.

    // Within the context of a given module, LocalInstanceMap maps
    // from child modules to the count of each child's local instantiations.
    typedef std::map<AstNodeModule*, int> LocalInstanceMap;

    // We keep a LocalInstanceMap for each module in the design
    std::map<AstNodeModule*, LocalInstanceMap> m_instances;

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()
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
    virtual void visit(AstNodeModule* nodep) {
	m_modp = nodep;
        m_allMods.push_back(nodep);
	m_modp->user2(CIL_MAYBE);
        m_modp->user4(0); // statement count
        if (VN_IS(m_modp, Iface)) {
	    // Inlining an interface means we no longer have a cell handle to resolve to.
	    // If inlining moves post-scope this can perhaps be relaxed.
	    cantInline("modIface",true);
	}
	if (m_modp->modPublic()) cantInline("modPublic",false);

        iterateChildren(nodep);
	m_modp = NULL;
    }
    virtual void visit(AstCell* nodep) {
        nodep->modp()->user3Inc();  // Inc refs
        m_instances[m_modp][nodep->modp()]++;
        iterateChildren(nodep);
    }
    virtual void visit(AstPragma* nodep) {
	if (nodep->pragType() == AstPragmaType::INLINE_MODULE) {
	    //UINFO(0,"PRAG MARK "<<m_modp<<endl);
	    if (!m_modp) {
		nodep->v3error("Inline pragma not under a module");
            } else if (m_modp->user2() == CIL_MAYBE
                       || m_modp->user2() == CIL_NOTSOFT) {
                m_modp->user2(CIL_USER);
	    }
	    nodep->unlinkFrBack()->deleteTree(); VL_DANGLING(nodep);  // Remove so don't propagate to upper cell...
	} else if (nodep->pragType() == AstPragmaType::NO_INLINE_MODULE) {
	    if (!m_modp) {
		nodep->v3error("Inline pragma not under a module");
	    } else {
		cantInline("Pragma NO_INLINE_MODULE",false);
	    }
	    nodep->unlinkFrBack()->deleteTree(); VL_DANGLING(nodep);  // Remove so don't propagate to upper cell...
	} else {
            iterateChildren(nodep);
	}
    }
    virtual void visit(AstVarXRef* nodep) {
	// Cleanup link until V3LinkDot can correct it
	nodep->varp(NULL);
    }
    virtual void visit(AstNodeFTaskRef* nodep) {
	// Cleanup link until V3LinkDot can correct it
	if (!nodep->packagep()) nodep->taskp(NULL);
        iterateChildren(nodep);
    }
    virtual void visit(AstAlways* nodep) {
        iterateChildren(nodep);
        m_modp->user4Inc(); // statement count
    }
    virtual void visit(AstNodeAssign* nodep) {
	// Don't count assignments, as they'll likely flatten out
	// Still need to iterate though to nullify VarXRefs
        int oldcnt = m_modp->user4();
        iterateChildren(nodep);
        m_modp->user4(oldcnt);
    }
    virtual void visit(AstNetlist* nodep) {
        // Build user2, user3, and user4 for all modules.
        // Also build m_allMods and m_instances.
        iterateChildren(nodep);

        // Iterate through all modules in bottom-up order.
        // Make a final inlining decision for each.
        for (ModVec::reverse_iterator it=m_allMods.rbegin(); it!=m_allMods.rend(); ++it) {
            AstNodeModule* modp = *it;

            // If we're going to inline some modules into this one,
            // update user4 (statement count) to reflect that:
            int statements = modp->user4();
            LocalInstanceMap& localsr = m_instances[modp];
            for (LocalInstanceMap::iterator it = localsr.begin(); it != localsr.end(); ++it) {
                AstNodeModule* childp = it->first;
                if (childp->user1()) {  // inlining child
                    statements += (childp->user4() * it->second);
                }
            }
            modp->user4(statements);

            int allowed = modp->user2();
            int refs = modp->user3();

            // Should we automatically inline this module?
            // inlineMult = 2000 by default.
            // If a mod*#refs is < this # nodes, can inline it
            bool doit = ((allowed == CIL_USER)
                         || ((allowed == CIL_MAYBE)
                             && (refs==1
                                 || statements < INLINE_MODS_SMALLER
                                 || v3Global.opt.inlineMult() < 1
                                 || refs*statements < v3Global.opt.inlineMult())));
            // Packages aren't really "under" anything so they confuse this algorithm
            if (VN_IS(modp, Package)) doit = false;
            UINFO(4, " Inline="<<doit<<" Possible="<<allowed
                  <<" Refs="<<refs<<" Stmts="<<statements<<"  "<<modp<<endl);
            modp->user1(doit);
        }
    }
    //--------------------
    // Default: Just iterate
    virtual void visit(AstNode* nodep) {
        iterateChildren(nodep);
        if (m_modp) {
            m_modp->user4Inc();  // Inc statement count
	}
    }

public:
    // CONSTUCTORS
    explicit InlineMarkVisitor(AstNode* nodep) {
	m_modp = NULL;
        iterate(nodep);
    }
    virtual ~InlineMarkVisitor() {
	V3Stats::addStat("Optimizations, Inline unsupported", m_statUnsup);
	// Done with these, are not outputs
	AstNode::user2ClearTree();
	AstNode::user3ClearTree();
        AstNode::user4ClearTree();
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

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    // VISITORS
    virtual void visit(AstCell* nodep) {
	nodep->user4p(nodep->clonep());
    }
    // Accelerate
    virtual void visit(AstNodeStmt* nodep) {}
    virtual void visit(AstNodeMath* nodep) {}
    virtual void visit(AstNode* nodep) {
        iterateChildren(nodep);
    }

public:
    // CONSTUCTORS
    explicit InlineCollectVisitor(AstNodeModule* nodep) {  // passed OLD module, not new one
        iterate(nodep);
    }
    virtual ~InlineCollectVisitor() {}
};

//######################################################################
// After cell is cloned, relink the new module's contents

class InlineRelinkVisitor : public AstNVisitor {
private:
    typedef vl_unordered_set<string> StringSet;

    // NODE STATE
    //  Input:
    //   See InlineVisitor

    // STATE
    StringSet           m_renamedInterfaces;  // Name of renamed interface variables
    AstNodeModule*	m_modp;		// Current module
    AstCell*		m_cellp;	// Cell being cloned

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    // VISITORS
    virtual void visit(AstCellInline* nodep) {
	// Inlined cell under the inline cell, need to move to avoid conflicts
	nodep->unlinkFrBack();
	m_modp->addInlinesp(nodep);
	// Rename
	string name = m_cellp->name() + "__DOT__" + nodep->name();
	nodep->name(name);
	UINFO(6, "    Inline "<<nodep<<endl);
	// Do CellInlines under this, but don't move them
        iterateChildren(nodep);
    }
    virtual void visit(AstCell* nodep) {
	// Cell under the inline cell, need to rename to avoid conflicts
	string name = m_cellp->name() + "__DOT__" + nodep->name();
	nodep->name(name);
        iterateChildren(nodep);
    }
    virtual void visit(AstModule* nodep) {
	m_renamedInterfaces.clear();
        iterateChildren(nodep);
    }
    virtual void visit(AstVar* nodep) {
	if (nodep->user2p()) {
	    // Make an assignment, so we'll trace it properly
	    // user2p is either a const or a var.
            AstConst*  exprconstp  = VN_CAST(nodep->user2p(), Const);
            AstVarRef* exprvarrefp = VN_CAST(nodep->user2p(), VarRef);
	    UINFO(8,"connectto: "<<nodep->user2p()<<endl);
	    if (!exprconstp && !exprvarrefp) {
		nodep->v3fatalSrc("Unknown interconnect type; pinReconnectSimple should have cleared up");
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
                if (nodep->isNonOutput()) nodep->v3fatalSrc("Outputs only - inputs use AssignAlias");
                m_modp->addStmtp(
                    new AstAssignW(nodep->fileline(),
                                   new AstVarRef(nodep->fileline(), exprvarrefp->varp(), true),
                                   new AstVarRef(nodep->fileline(), nodep, false)));
            } else if (nodep->isIfaceRef()) {
                m_modp->addStmtp(
                    new AstAssignVarScope(nodep->fileline(),
                                          new AstVarRef(nodep->fileline(), nodep, true),
                                          new AstVarRef(nodep->fileline(), exprvarrefp->varp(), false)));
                AstNode* nodebp=exprvarrefp->varp();
                nodep ->fileline()->modifyStateInherit(nodebp->fileline());
                nodebp->fileline()->modifyStateInherit(nodep ->fileline());
            } else {
                // Do to inlining child's variable now within the same module, so a AstVarRef not AstVarXRef below
                m_modp->addStmtp(
                    new AstAssignAlias(nodep->fileline(),
                                       new AstVarRef(nodep->fileline(), nodep, true),
                                       new AstVarRef(nodep->fileline(), exprvarrefp->varp(), false)));
		AstNode* nodebp=exprvarrefp->varp();
		nodep ->fileline()->modifyStateInherit(nodebp->fileline());
		nodebp->fileline()->modifyStateInherit(nodep ->fileline());
	    }
	}
	// Iterate won't hit AstIfaceRefDType directly as it is no longer underneath the module
        if (AstIfaceRefDType* ifacerefp = VN_CAST(nodep->dtypep(), IfaceRefDType)) {
	    m_renamedInterfaces.insert(nodep->name());
	    // Each inlined cell that contain an interface variable need to copy the IfaceRefDType and point it to
	    // the newly cloned interface cell.
            AstIfaceRefDType* newdp = VN_CAST(ifacerefp->cloneTree(false), IfaceRefDType);
	    nodep->dtypep(newdp);
	    ifacerefp->addNextHere(newdp);
	    // Relink to point to newly cloned cell
	    if (newdp->cellp()) {
                if (AstCell* newcellp = VN_CAST(newdp->cellp()->user4p(), Cell)) {
		    newdp->cellp(newcellp);
		    newdp->cellName(newcellp->name());
		    // Tag the old ifacerefp to ensure it leaves no stale reference to the inlined cell.
		    newdp->user5(false);
		    ifacerefp->user5(true);
		}
	    }
	}
	// Variable under the inline cell, need to rename to avoid conflicts
	// Also clear I/O bits, as it is now local.
	string name = m_cellp->name() + "__DOT__" + nodep->name();
	if (!nodep->isFuncLocal()) nodep->inlineAttrReset(name);
	if (!m_cellp->isTrace()) nodep->trace(false);
	if (debug()>=9) { nodep->dumpTree(cout,"varchanged:"); }
	if (debug()>=9 && nodep->valuep()) { nodep->valuep()->dumpTree(cout,"varchangei:"); }
        iterateChildren(nodep);
    }
    virtual void visit(AstNodeFTask* nodep) {
	// Function under the inline cell, need to rename to avoid conflicts
	nodep->name(m_cellp->name() + "__DOT__" + nodep->name());
        iterateChildren(nodep);
    }
    virtual void visit(AstTypedef* nodep) {
	// Typedef under the inline cell, need to rename to avoid conflicts
	nodep->name(m_cellp->name() + "__DOT__" + nodep->name());
        iterateChildren(nodep);
    }
    virtual void visit(AstVarRef* nodep) {
	if (nodep->varp()->user2p()  // It's being converted to an alias.
	    && !nodep->varp()->user3()
            && !VN_IS(nodep->backp(), AssignAlias)) {  // Don't constant propagate aliases (we just made)
            AstConst*  exprconstp  = VN_CAST(nodep->varp()->user2p(), Const);
            AstVarRef* exprvarrefp = VN_CAST(nodep->varp()->user2p(), VarRef);
	    if (exprconstp) {
		nodep->replaceWith(exprconstp->cloneTree(true));
		nodep->deleteTree(); VL_DANGLING(nodep);
		return;
	    }
	    else if (exprvarrefp) {
		nodep->varp( exprvarrefp->varp() );
	    }
	    else {
		nodep->v3fatalSrc("Null connection?");
	    }
	}
	nodep->name(nodep->varp()->name());
        iterateChildren(nodep);
    }
    virtual void visit(AstVarXRef* nodep) {
	// Track what scope it was originally under so V3LinkDot can resolve it
        string newdots = VString::dot(m_cellp->name(), ".", nodep->inlinedDots());
        nodep->inlinedDots(newdots);
        for (string tryname = nodep->dotted(); 1;) {
            if (m_renamedInterfaces.count(tryname)) {
                nodep->dotted(m_cellp->name() + "__DOT__" + nodep->dotted());
                break;
            }
            // If foo.bar, and foo is an interface, then need to search again for foo
            string::size_type pos = tryname.rfind('.');
            if (pos == string::npos || pos==0) {
                break;
            } else {
                tryname = tryname.substr(0, pos);
            }
        }
        iterateChildren(nodep);
    }
    virtual void visit(AstNodeFTaskRef* nodep) {
	// Track what scope it was originally under so V3LinkDot can resolve it
        string newdots = VString::dot(m_cellp->name(), ".", nodep->inlinedDots());
        nodep->inlinedDots(newdots);
	if (m_renamedInterfaces.count(nodep->dotted())) {
	    nodep->dotted(m_cellp->name() + "__DOT__" + nodep->dotted());
	}
	UINFO(8,"   "<<nodep<<endl);
        iterateChildren(nodep);
    }

    // Not needed, as V3LinkDot doesn't care about typedefs
    //virtual void visit(AstRefDType* nodep) {}

    virtual void visit(AstScopeName* nodep) {
	// If there's a %m in the display text, we add a special node that will contain the name()
	// Similar code in V3Begin
	// To keep correct visual order, must add before other Text's
	AstNode* afterp = nodep->scopeAttrp();
	if (afterp) afterp->unlinkFrBackWithNext();
        nodep->scopeAttrp(new AstText(nodep->fileline(), string("__DOT__")+m_cellp->name()));
	if (afterp) nodep->scopeAttrp(afterp);
	afterp = nodep->scopeEntrp();
	if (afterp) afterp->unlinkFrBackWithNext();
        nodep->scopeEntrp(new AstText(nodep->fileline(), string("__DOT__")+m_cellp->name()));
	if (afterp) nodep->scopeEntrp(afterp);
        iterateChildren(nodep);
    }
    virtual void visit(AstCoverDecl* nodep) {
	// Fix path in coverage statements
        nodep->hier(VString::dot(m_cellp->prettyName(), ".", nodep->hier()));
        iterateChildren(nodep);
    }
    virtual void visit(AstNode* nodep) {
        iterateChildren(nodep);
    }

public:
    // CONSTUCTORS
    InlineRelinkVisitor(AstNodeModule* cloneModp, AstNodeModule* oldModp, AstCell* cellp) {
	m_modp = oldModp;
	m_cellp = cellp;
        iterate(cloneModp);
    }
    virtual ~InlineRelinkVisitor() {}
};

//######################################################################
// Inline state, as a visitor of each AstNode

class InlineVisitor : public AstNVisitor {
private:
    // NODE STATE
    // Cleared entire netlist
    //  AstIfaceRefDType::user5p() // Whether the cell pointed to by this AstIfaceRefDType has been inlined
    //  Input:
    //   AstNodeModule::user1p()	// bool. True to inline this module (from InlineMarkVisitor)
    // Cleared each cell
    //   AstVar::user2p()	// AstVarRef*/AstConst*  Points to signal this is a direct connect to
    //   AstVar::user3()	// bool    Don't alias the user2, keep it as signal
    //   AstCell::user4		// AstCell* of the created clone

    AstUser2InUse       m_inuser2;
    AstUser3InUse       m_inuser3;
    AstUser4InUse       m_inuser4;
    AstUser5InUse	m_inuser5;

    // STATE
    AstNodeModule*      m_modp;         // Current module
    V3Double0		m_statCells;	// Statistic tracking

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    // VISITORS
    virtual void visit(AstNetlist* nodep) {
	// Iterate modules backwards, in bottom-up order.  Required!
        iterateChildrenBackwards(nodep);
    }
    virtual void visit(AstIfaceRefDType* nodep) {
	if (nodep->user5()) {
	    // The cell has been removed so let's make sure we don't leave a reference to it
	    // This dtype may still be in use by the AstAssignVarScope created earlier
	    // but that'll get cleared up later
	    nodep->cellp(NULL);
	}
    }
    virtual void visit(AstNodeModule* nodep) {
	m_modp = nodep;
        iterateChildren(nodep);
    }
    virtual void visit(AstCell* nodep) {
	if (nodep->modp()->user1()) {  // Marked with inline request
	    UINFO(5," Inline CELL   "<<nodep<<endl);
	    UINFO(5,"   To MOD      "<<m_modp<<endl);
	    ++m_statCells;

	    // Before cloning simplify pin assignments
	    // Better off before, as if module has multiple instantiations
	    // we'll save work, and we can't call pinReconnectSimple in
	    // this loop as it clone()s itself.
            for (AstPin* pinp = nodep->pinsp(); pinp; pinp=VN_CAST(pinp->nextp(), Pin)) {
		if (!pinp->exprp()) continue;
                V3Inst::pinReconnectSimple(pinp, nodep, false);
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
            for (AstPin* pinp = nodep->pinsp(); pinp; pinp=VN_CAST(pinp->nextp(), Pin)) {
		if (!pinp->exprp()) continue;
		UINFO(6,"     Pin change from "<<pinp->modVarp()<<endl);
		// Make new signal; even though we'll optimize the interconnect, we
		// need an alias to trace correctly.  If tracing is disabled, we'll
		// delete it in later optimizations.
		AstVar* pinOldVarp = pinp->modVarp();
		AstVar* pinNewVarp = pinOldVarp->clonep();
		if (!pinNewVarp) pinOldVarp->v3fatalSrc("Cloning failed");

                AstNode* connectRefp = pinp->exprp();
                if (!VN_IS(connectRefp, Const) && !VN_IS(connectRefp, VarRef)) {
                    pinp->v3fatalSrc("Unknown interconnect type; pinReconnectSimple should have cleared up");
                }
                V3Inst::checkOutputShort(pinp);

		// Propagate any attributes across the interconnect
		pinNewVarp->propagateAttrFrom(pinOldVarp);
                if (VN_IS(connectRefp, VarRef)) {
                    VN_CAST(connectRefp, VarRef)->varp()->propagateAttrFrom(pinOldVarp);
		}

		// One to one interconnect won't make a temporary variable.
		// This prevents creating a lot of extra wires for clock signals.
		// It will become a tracing alias.
		UINFO(6,"One-to-one "<<connectRefp<<endl);
		UINFO(6,"       -to "<<pinNewVarp<<endl);
		pinNewVarp->user2p(connectRefp);
                // Public output inside the cell must go via an assign rather
                // than alias.  Else the public logic will set the alias, losing
                // the value to be propagated up (InOnly isn't a problem as the
                // AssignAlias will create the assignment for us)
                pinNewVarp->user3(pinNewVarp->isSigUserRWPublic()
                                  && pinNewVarp->direction()==VDirection::OUTPUT);
            }
	    // Cleanup var names, etc, to not conflict
	    { InlineRelinkVisitor(newmodp, m_modp, nodep); }
	    // Move statements to top module
	    if (debug()>=9) { newmodp->dumpTree(cout,"fixmod:"); }
	    AstNode* stmtsp = newmodp->stmtsp();
	    if (stmtsp) stmtsp->unlinkFrBackWithNext();
	    if (stmtsp) m_modp->addStmtp(stmtsp);
	    // Remove the cell
	    newmodp->deleteTree(); VL_DANGLING(newmodp); // Clear any leftover ports, etc
	    nodep->unlinkFrBack();
	    pushDeletep(nodep); VL_DANGLING(nodep);
	    if (debug()>=9) { m_modp->dumpTree(cout,"donemod:"); }
	}
    }

    //--------------------
    virtual void visit(AstNodeMath* nodep) {}  // Accelerate
    virtual void visit(AstNodeStmt* nodep) {}  // Accelerate
    virtual void visit(AstNode* nodep) {
        iterateChildren(nodep);
    }

public:
    // CONSTUCTORS
    explicit InlineVisitor(AstNode* nodep) {
	m_modp = NULL;
        iterate(nodep);
    }
    virtual ~InlineVisitor() {
	V3Stats::addStat("Optimizations, Inlined cells", m_statCells);
    }
};

//######################################################################
// Inline class functions

void V3Inline::inlineAll(AstNetlist* nodep) {
    UINFO(2,__FUNCTION__<<": "<<endl);
    AstUser1InUse m_inuser1; // output of InlineMarkVisitor,
                             // input to InlineVisitor.
    {
        // Scoped to clean up temp userN's
        InlineMarkVisitor mvisitor (nodep);
    }
    {
        InlineVisitor visitor (nodep);
    }
    // Remove all modules that were inlined
    // V3Dead will also clean them up, but if we have debug on, it's a good
    // idea to avoid dumping the hugely exploded tree.
    AstNodeModule* nextmodp;
    for (AstNodeModule* modp = v3Global.rootp()->modulesp(); modp; modp=nextmodp) {
        nextmodp = VN_CAST(modp->nextp(), NodeModule);
	if (modp->user1()) { // Was inlined
	    modp->unlinkFrBack()->deleteTree(); VL_DANGLING(modp);
	}
    }
    V3Global::dumpCheckGlobalTree("inline", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}
