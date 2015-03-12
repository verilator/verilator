// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Break always into sensitivity block domains
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
// V3Scope's Transformations:
//
//	For every CELL that references this module, create a
//		SCOPE
//			{all blocked statements}
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"
#include <cstdio>
#include <cstdarg>
#include <unistd.h>
#include <algorithm>
#include <iomanip>
#include <map>

#include "V3Global.h"
#include "V3Scope.h"
#include "V3Ast.h"

//######################################################################
// Scope class functions

class ScopeVisitor : public AstNVisitor {
private:
    // NODE STATE
    // AstVar::user1p		-> AstVarScope replacement for this variable
    // AstTask::user2p		-> AstTask*.  Replacement task
    AstUser1InUse	m_inuser1;
    AstUser2InUse	m_inuser2;

    // TYPES
    typedef map<AstPackage*, AstScope*> PackageScopeMap;
    typedef map<pair<AstVar*, AstScope*>, AstVarScope*> VarScopeMap;
    typedef set<pair<AstVarRef*, AstScope*> > VarRefScopeSet;

    // STATE, inside processing a single module
    AstNodeModule* m_modp;	// Current module
    AstScope*	m_scopep;	// Current scope we are building
    // STATE, for passing down one level of hierarchy (may need save/restore)
    AstCell*	m_aboveCellp;	// Cell that instantiates this module
    AstScope*	m_aboveScopep;	// Scope that instantiates this scope
    
    PackageScopeMap	m_packageScopes;	// Scopes for each package
    VarScopeMap		m_varScopes;		// Varscopes created for each scope and var
    VarRefScopeSet	m_varRefScopes;		// Varrefs-in-scopes needing fixup when donw

    // METHODS
    static int debug() {
	static int level = -1;
	if (VL_UNLIKELY(level < 0)) level = v3Global.opt.debugSrcLevel(__FILE__);
	return level;
    }

    void cleanupVarRefs() {
	for (VarRefScopeSet::iterator it = m_varRefScopes.begin();
	     it!=m_varRefScopes.end(); ++it) {
	    AstVarRef* nodep = it->first;
	    AstScope* scopep = it->second;
	    if (nodep->packagep()) {
		PackageScopeMap::iterator it2 = m_packageScopes.find(nodep->packagep());
		if (it2==m_packageScopes.end()) nodep->v3fatalSrc("Can't locate package scope");
		scopep = it2->second;
	    }
	    VarScopeMap::iterator it3 = m_varScopes.find(make_pair(nodep->varp(), scopep));
	    if (it3==m_varScopes.end()) nodep->v3fatalSrc("Can't locate varref scope");
	    AstVarScope* varscp = it3->second;
	    nodep->varScopep(varscp);
	}
    }

    // VISITORS
    virtual void visit(AstNetlist* nodep, AstNUser*) {
	AstNodeModule* modp = nodep->topModulep();
	if (!modp) { nodep->v3error("No root module specified"); return; }
	// Operate starting at the top of the hierarchy
	m_aboveCellp = NULL;
	m_aboveScopep = NULL;
	modp->accept(*this);
	cleanupVarRefs();
    }
    virtual void visit(AstNodeModule* nodep, AstNUser*) {
	// Create required blocks and add to module
	string scopename;
	if (!m_aboveScopep) scopename = "TOP";
	else scopename = m_aboveScopep->name()+"."+m_aboveCellp->name();

	UINFO(4," MOD AT "<<scopename<<"  "<<nodep<<endl);
        AstNode::user1ClearTree();

	m_scopep = new AstScope((m_aboveCellp?(AstNode*)m_aboveCellp:(AstNode*)nodep)->fileline(),
				nodep, scopename, m_aboveScopep, m_aboveCellp);
	if (nodep->castPackage()) m_packageScopes.insert(make_pair(nodep->castPackage(), m_scopep));

	// Now for each child cell, iterate the module this cell points to
	for (AstNode* cellnextp = nodep->stmtsp(); cellnextp; cellnextp=cellnextp->nextp()) {
	    if (AstCell* cellp = cellnextp->castCell()) {
		AstScope* oldScopep = m_scopep;
		AstCell* oldAbCellp = m_aboveCellp;
		AstScope* oldAbScopep = m_aboveScopep;
		{
		    m_aboveCellp = cellp;
		    m_aboveScopep = m_scopep;
		    AstNodeModule* modp = cellp->modp();
		    if (!modp) cellp->v3fatalSrc("Unlinked mod");
		    modp->accept(*this);  // Recursive call to visit(AstNodeModule)
		}
		// Done, restore vars
		m_scopep = oldScopep;
		m_aboveCellp = oldAbCellp;
		m_aboveScopep = oldAbScopep;
	    }
	}

	// Create scope for the current usage of this module
	UINFO(4," back AT "<<scopename<<"  "<<nodep<<endl);
        AstNode::user1ClearTree();
	m_modp = nodep;
	if (m_modp->isTop()) {
	    AstTopScope* topscp = new AstTopScope(nodep->fileline(), m_scopep);
	    m_modp->addStmtp(topscp);
	} else {
	    m_modp->addStmtp(m_scopep);
	}

	// Copy blocks into this scope
	// If this is the first usage of the block ever, we can simply move the reference
	nodep->iterateChildren(*this);

	// ***Note m_scopep is passed back to the caller of the routine (above)
    }
    virtual void visit(AstActive* nodep, AstNUser*) {
	nodep->v3fatalSrc("Actives now made after scoping");
    }
    virtual void visit(AstInitial* nodep, AstNUser*) {
	// Add to list of blocks under this scope
	UINFO(4,"    Move "<<nodep<<endl);
	AstInitial* clonep = nodep->cloneTree(false);
	nodep->user2p(clonep);
	m_scopep->addActivep(clonep);
	clonep->iterateChildren(*this);	// We iterate under the *clone*
    }
    virtual void visit(AstFinal* nodep, AstNUser*) {
	// Add to list of blocks under this scope
	UINFO(4,"    Move "<<nodep<<endl);
	AstFinal* clonep = nodep->cloneTree(false);
	nodep->user2p(clonep);
	m_scopep->addActivep(clonep);
	clonep->iterateChildren(*this);	// We iterate under the *clone*
    }
    virtual void visit(AstAssignAlias* nodep, AstNUser*) {
	// Add to list of blocks under this scope
	UINFO(4,"    Move "<<nodep<<endl);
	AstNode* clonep = nodep->cloneTree(false);
	nodep->user2p(clonep);
	m_scopep->addActivep(clonep);
	clonep->iterateChildren(*this);	// We iterate under the *clone*
    }
    virtual void visit(AstAssignVarScope* nodep, AstNUser*) {
	// Copy under the scope but don't recurse
	UINFO(4,"    Move "<<nodep<<endl);
	AstNode* clonep = nodep->cloneTree(false);
	nodep->user2p(clonep);
	m_scopep->addActivep(clonep);
	clonep->iterateChildren(*this);	// We iterate under the *clone*
    }
    virtual void visit(AstAssignW* nodep, AstNUser*) {
	// Add to list of blocks under this scope
	UINFO(4,"    Move "<<nodep<<endl);
	AstNode* clonep = nodep->cloneTree(false);
	nodep->user2p(clonep);
	m_scopep->addActivep(clonep);
	clonep->iterateChildren(*this);	// We iterate under the *clone*
    }
    virtual void visit(AstAlways* nodep, AstNUser*) {
	// Add to list of blocks under this scope
	UINFO(4,"    Move "<<nodep<<endl);
	AstNode* clonep = nodep->cloneTree(false);
	nodep->user2p(clonep);
	m_scopep->addActivep(clonep);
	clonep->iterateChildren(*this);	// We iterate under the *clone*
    }
    virtual void visit(AstAlwaysPublic* nodep, AstNUser*) {
	// Add to list of blocks under this scope
	UINFO(4,"    Move "<<nodep<<endl);
	AstNode* clonep = nodep->cloneTree(false);
	nodep->user2p(clonep);
	m_scopep->addActivep(clonep);
	clonep->iterateChildren(*this);	// We iterate under the *clone*
    }
    virtual void visit(AstCoverToggle* nodep, AstNUser*) {
	// Add to list of blocks under this scope
	UINFO(4,"    Move "<<nodep<<endl);
	AstNode* clonep = nodep->cloneTree(false);
	nodep->user2p(clonep);
	m_scopep->addActivep(clonep);
	clonep->iterateChildren(*this);	// We iterate under the *clone*
    }
    virtual void visit(AstCFunc* nodep, AstNUser*) {
	// Add to list of blocks under this scope
	UINFO(4,"    CFUNC "<<nodep<<endl);
	AstCFunc* clonep = nodep->cloneTree(false);
	nodep->user2p(clonep);
	m_scopep->addActivep(clonep);
	clonep->scopep(m_scopep);
	// We iterate under the *clone*
	clonep->iterateChildren(*this);
    }
    virtual void visit(AstNodeFTask* nodep, AstNUser*) {
	// Add to list of blocks under this scope
	UINFO(4,"    FTASK "<<nodep<<endl);
	AstNodeFTask* clonep = nodep->cloneTree(false);
	nodep->user2p(clonep);
	m_scopep->addActivep(clonep);
	// We iterate under the *clone*
	clonep->iterateChildren(*this);
    }
    virtual void visit(AstVar* nodep, AstNUser*) {
	// Make new scope variable
	// This is called cross-module by AstVar, so we cannot trust any m_ variables
	if (!nodep->user1p()) {
	    AstVarScope* varscp = new AstVarScope(nodep->fileline(), m_scopep, nodep);
	    UINFO(6,"   New scope "<<varscp<<endl);
	    if (m_aboveCellp && !m_aboveCellp->isTrace()) varscp->trace(false);
	    nodep->user1p(varscp);
	    if (v3Global.opt.isClocker(varscp->prettyName())) {
		nodep->attrClocker(AstVarAttrClocker::CLOCKER_YES);
	    }
	    if (v3Global.opt.isNoClocker(varscp->prettyName())) {
		nodep->attrClocker(AstVarAttrClocker::CLOCKER_NO);
	    }
	    if (!m_scopep) nodep->v3fatalSrc("No scope for var");
	    m_varScopes.insert(make_pair(make_pair(nodep, m_scopep), varscp));
	    m_scopep->addVarp(varscp);
	}
    }
    virtual void visit(AstVarRef* nodep, AstNUser*) {
	// VarRef needs to point to VarScope
	// Make sure variable has made user1p.
	if (!nodep->varp()) nodep->v3fatalSrc("Unlinked");
	if (nodep->varp()->isIfaceRef()) {
	    nodep->varScopep(NULL);
	} else {
	    // We may have not made the variable yet, and we can't make it now as
	    // the var's referenced package etc might not be created yet.
	    // So push to a list and post-correct
	    m_varRefScopes.insert(make_pair(nodep, m_scopep));
	} 
   }
    virtual void visit(AstScopeName* nodep, AstNUser*) {
	// If there's a %m in the display text, we add a special node that will contain the name()
	string prefix = (string)("__DOT__")+m_scopep->name();
	// TOP and above will be the user's name().
	// Note 'TOP.' is stripped by scopePrettyName
	// To keep correct visual order, must add before other Text's
	AstNode* afterp = nodep->scopeAttrp();
	if (afterp) afterp->unlinkFrBackWithNext();
	nodep->scopeAttrp(new AstText(nodep->fileline(), prefix));
	if (afterp) nodep->scopeAttrp(afterp);
	afterp = nodep->scopeEntrp();
	if (afterp) afterp->unlinkFrBackWithNext();
	nodep->scopeEntrp(new AstText(nodep->fileline(), prefix));
	if (afterp) nodep->scopeEntrp(afterp);
	nodep->iterateChildren(*this);
    }
    virtual void visit(AstScope* nodep, AstNUser*) {
	// Scope that was made by this module for different cell;
	// Want to ignore blocks under it, so just do nothing
    }
    //--------------------
    // Default
    virtual void visit(AstNode* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
    }
public:
    // CONSTUCTORS
    ScopeVisitor(AstNetlist* nodep) {
	m_aboveCellp = NULL;
	m_aboveScopep = NULL;
	m_modp = NULL;
	m_scopep = NULL;
	//
	nodep->accept(*this);
    }
    virtual ~ScopeVisitor() {}
};

//######################################################################
// Scope cleanup -- remove unused activates

class ScopeCleanupVisitor : public AstNVisitor {
private:
    // STATE
    AstScope*	m_scopep;	// Current scope we are building

    // METHODS
    static int debug() {
	static int level = -1;
	if (VL_UNLIKELY(level < 0)) level = v3Global.opt.debugSrcLevel(__FILE__);
	return level;
    }

    // VISITORS
    virtual void visit(AstScope* nodep, AstNUser*) {
	// Want to ignore blocks under it
	m_scopep = nodep;
	nodep->iterateChildren(*this);
	m_scopep = NULL;
    }

    virtual void movedDeleteOrIterate(AstNode* nodep) {
	if (m_scopep) {
	    // The new block; repair varrefs
	    nodep->iterateChildren(*this);
	} else {
	    // A block that was just moved under a scope, Kill it.
	    nodep->unlinkFrBack()->deleteTree(); nodep=NULL;
	}
    }

    virtual void visit(AstInitial* nodep, AstNUser*) {
	movedDeleteOrIterate(nodep);
    }
    virtual void visit(AstFinal* nodep, AstNUser*) {
	movedDeleteOrIterate(nodep);
    }
    virtual void visit(AstAssignAlias* nodep, AstNUser*) {
	movedDeleteOrIterate(nodep);
    }
    virtual void visit(AstAssignVarScope* nodep, AstNUser*) {
	movedDeleteOrIterate(nodep);
    }
    virtual void visit(AstAssignW* nodep, AstNUser*) {
	movedDeleteOrIterate(nodep);
    }
    virtual void visit(AstAlways* nodep, AstNUser*) {
	movedDeleteOrIterate(nodep);
    }
    virtual void visit(AstAlwaysPublic* nodep, AstNUser*) {
	movedDeleteOrIterate(nodep);
    }
    virtual void visit(AstCoverToggle* nodep, AstNUser*) {
	movedDeleteOrIterate(nodep);
    }
    virtual void visit(AstNodeFTask* nodep, AstNUser*) {
	movedDeleteOrIterate(nodep);
    }
    virtual void visit(AstCFunc* nodep, AstNUser*) {
	movedDeleteOrIterate(nodep);
    }

    virtual void visit(AstVarXRef* nodep, AstNUser*) {
	// The crossrefs are dealt with in V3LinkDot
	nodep->varp(NULL);
    }
    virtual void visit(AstNodeFTaskRef* nodep, AstNUser*) {
	// The crossrefs are dealt with in V3LinkDot
	UINFO(9,"   Old pkg-taskref "<<nodep<<endl);
	if (nodep->packagep()) {
	    // Point to the clone
	    if (!nodep->taskp()) nodep->v3fatalSrc("Unlinked");
	    AstNodeFTask* newp = nodep->taskp()->user2p()->castNode()->castNodeFTask();
	    if (!newp) nodep->v3fatalSrc("No clone for package function");
	    nodep->taskp(newp);
	    UINFO(9,"   New pkg-taskref "<<nodep<<endl);
	} else {
	    nodep->taskp(NULL);
	    UINFO(9,"   New pkg-taskref "<<nodep<<endl);
	}
	nodep->iterateChildren(*this);
    }
    virtual void visit(AstModportFTaskRef* nodep, AstNUser*) {
	// The crossrefs are dealt with in V3LinkDot
	nodep->ftaskp(NULL);
	nodep->iterateChildren(*this);
    }

    //--------------------
    // Default
    virtual void visit(AstNode* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
    }
public:
    // CONSTUCTORS
    ScopeCleanupVisitor(AstNetlist* nodep) {
	m_scopep = NULL;
	nodep->accept(*this);
    }
    virtual ~ScopeCleanupVisitor() {}
};

//######################################################################
// Scope class functions

void V3Scope::scopeAll(AstNetlist* nodep) {
    UINFO(2,__FUNCTION__<<": "<<endl);
    ScopeVisitor visitor (nodep);
    ScopeCleanupVisitor cleanVisitor (nodep);
    V3Global::dumpCheckGlobalTree("scope.tree", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}
