// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Resolve module/signal name references
//
// Code available from: http://www.veripool.org/verilator
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
// LinkDot TRANSFORMATIONS:
//	Top-down traversal
//	    Cells:
//		Make graph of cell hierarchy
//	    Var/Funcs's:
//		Collect all names into symtable under appropriate cell
//	Top-down traversal
//	    VarXRef/Func's:
//		Find appropriate named cell and link to var they reference
//*************************************************************************
// TOP
//      {name-of-top-modulename}
//      a          (VSymEnt->AstCell)
//	  {name-of-cell}
//	  {name-of-cell-module}
//        aa         (VSymEnt->AstCell)
//          var        (AstVar) -- no sub symbol table needed
//          beg        (VSymEnt->AstBegin) -- can see "upper" a's symbol table
//      a__DOT__aa (VSymEnt->AstCellInline) -- points to a.aa's symbol table
//      b          (VSymEnt->AstCell)
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
#include "V3LinkDot.h"
#include "V3SymTable.h"
#include "V3Graph.h"
#include "V3Ast.h"

//######################################################################
// LinkDot state, as a visitor of each AstNode

class LinkDotState {
private:
    // NODE STATE
    // Cleared on Netlist
    //  AstNodeModule::user1p()	-> VSymEnt*.  Last cell that uses this module
    //  AstVarScope::user2p()	-> AstVarScope*.  Base alias for this signal
    AstUser1InUse	m_inuser1;
    AstUser2InUse	m_inuser2;

    // TYPES
    typedef std::multimap<string,VSymEnt*> NameScopeMap;
    // MEMBERS
    VSymGraph		m_syms;			// Symbol table
    NameScopeMap	m_nameScopeMap;		// Hash of scope referenced by non-pretty textual name
    bool		m_forPrearray;		// Compress cell__[array] refs
    bool		m_forScopeCreation;	// Remove VarXRefs for V3Scope
public:

    static int debug() {
	static int level = -1;
	if (VL_UNLIKELY(level < 0)) level = v3Global.opt.debugSrcLevel(__FILE__);
	return level;
    }

    // CONSTRUCTORS
    LinkDotState(AstNetlist* rootp, bool forPrearray, bool forScopeCreation)
	: m_syms(rootp) {
	UINFO(4,__FUNCTION__<<": "<<endl);
	m_forPrearray = forPrearray;
	m_forScopeCreation = forScopeCreation;
    }
    ~LinkDotState() {}

    // ACCESSORS
    bool forScopeCreation() const { return m_forScopeCreation; }

    // METHODS
private:
    VSymEnt* findWithAltFallback(VSymEnt* symp, const string& name, const string& altname) {
	VSymEnt* findp = symp->findIdFallback(name);
	if (findp) return findp;
	findp = symp->findIdFallback(altname);
	return findp;
    }
public:
    VSymEnt* insertTopCell(AstNodeModule* nodep, const string& scopename) {
	// Only called on the module at the very top of the hierarchy
	VSymEnt* symp = new VSymEnt(&m_syms, nodep);
	UINFO(9,"      INSERTtop se"<<(void*)symp<<"  "<<scopename<<" "<<nodep<<endl);
	symp->parentp(m_syms.rootp());  // Needed so backward search can find name of top module
	nodep->user1p(symp);
	m_syms.rootp()->insert(nodep->origName(),symp);
	if (forScopeCreation()) m_nameScopeMap.insert(make_pair(scopename, symp));
	return symp;
    }
    VSymEnt* insertCell(VSymEnt* abovep, VSymEnt* modSymp,
			AstCell* nodep, const string& scopename) {
	VSymEnt* symp = new VSymEnt(&m_syms, nodep);
	UINFO(9,"      INSERTcel se"<<(void*)symp<<"  "<<scopename<<" above=se"<<(void*)abovep<<" mods=se"<<(void*)modSymp<<" node="<<nodep<<endl);
	symp->parentp(abovep);
	symp->fallbackp(modSymp);
	if (nodep->modp()) nodep->modp()->user1p(symp);
	abovep->reinsert(nodep->origName(), symp);
	if (abovep != modSymp) {
	    // If it's foo_DOT_bar, we need to be able to find it under that too.
	    // Duplicates are possible, as until resolve generates might have 2 same cells under an if
	    modSymp->reinsert(nodep->name(), symp);
	}
	if (forScopeCreation()) m_nameScopeMap.insert(make_pair(scopename, symp));
	return symp;
    }
    VSymEnt* insertInline(VSymEnt* abovep, VSymEnt* modSymp,
			  AstCellInline* nodep, const string& basename) {
	// A fake point in the hierarchy, corresponding to an inlined module
	// This refrences to another Sym, and eventually resolves to a module with a prefix
	if (!abovep) nodep->v3fatalSrc("Null symbol table inserting node");
	VSymEnt* symp = new VSymEnt(&m_syms, nodep);
	UINFO(9,"      INSERTinl se"<<(void*)symp<<"  "<<basename<<" above=se"<<(void*)abovep<<" mods=se"<<(void*)modSymp<<" node="<<nodep<<endl);
	symp->parentp(abovep);
	symp->fallbackp(modSymp);
	symp->symPrefix(nodep->name()+"__DOT__");
	abovep->reinsert(basename, symp);
	if (abovep != modSymp) {
	    // If it's foo_DOT_bar, we need to be able to find it under that too.
	    modSymp->reinsert(nodep->name(), symp);
	}
	return symp;
    }
    VSymEnt* insertBegin(VSymEnt* abovep, VSymEnt* modSymp,
			 AstBegin* nodep) {
	// A fake point in the hierarchy, corresponding to a begin block
	// After we remove begins these will go away
	// Note we fallback to the symbol table of the parent, as we want to find variables there
	// However, cells walk the graph, so cells will appear under the begin itself
	if (!abovep) nodep->v3fatalSrc("Null symbol table inserting node");
	VSymEnt* symp = new VSymEnt(&m_syms, nodep);
	UINFO(9,"      INSERTblk se"<<(void*)symp<<"  above=se"<<(void*)abovep<<"  node="<<nodep<<endl);
	symp->parentp(abovep);
	symp->symPrefix(nodep->name()+"__DOT__");
	if (nodep->name() != "") {
	    // Duplicates are possible, as until resolve generates might have 2 same cells under an if
	    abovep->reinsert(nodep->name(), symp);
	}
	return symp;
    }
    void insertSym(VSymEnt* abovep, const string& name, AstNode* nodep) {
	if (!abovep) nodep->v3fatalSrc("Null symbol table inserting node");
	// We don't remember the ent associated with each node, because we need a unique scope entry for each instantiation
	VSymEnt* symp = new VSymEnt(&m_syms, nodep);
	UINFO(9,"      INSERTsym name='"<<name<<"' above="<<(void*)abovep<<"  node="<<nodep<<endl);
	abovep->insert(name, symp);
    }
    static bool existsModScope(AstNodeModule* nodep) {
	return nodep->user1p()!=NULL;
    }
    static VSymEnt* getNodeSym(AstNodeModule* nodep) {
	VSymEnt* symp = nodep->user1p()->castSymEnt();
	if (!symp) nodep->v3fatalSrc("Module never assigned a symbol entry?");
	return symp;
    }
    VSymEnt* getScopeSym(AstScope* nodep) {
	NameScopeMap::iterator iter = m_nameScopeMap.find(nodep->name());
	if (iter == m_nameScopeMap.end()) {
	    nodep->v3fatalSrc("Scope never assigned a symbol entry?");
	}
	return iter->second;
    }
    void dump() {
	if (debug()>=6) m_syms.dumpFilePrefixed("linkdot");
    }
    void preErrorDump() {
	static bool diddump = false;
	if (!diddump && v3Global.opt.dumpTree()) {
	    diddump = true;
	    m_syms.dumpFilePrefixed("linkdot-preerr");
	}
    }
    VSymEnt* findDotted(VSymEnt* lookupSymp, const string& dotname,
			string& baddot, VSymEnt*& okSymp) {
	// Given a dotted hierarchy name, return where in scope it is
	// Note when dotname=="" we just fall through and return lookupSymp
	UINFO(8,"    dottedFind se"<<(void*)lookupSymp<<" '"<<dotname<<"'"<<endl);
	bool firstId = true;
	string leftname = dotname;
	okSymp = lookupSymp;  // So can list bad scopes
	while (leftname != "") {  // foreach dotted part of xref name
	    string::size_type pos;
	    string ident;
	    if ((pos = leftname.find(".")) != string::npos) {
		ident = leftname.substr(0,pos);
		leftname = leftname.substr(pos+1);
	    } else {
		ident = leftname;
		leftname = "";
	    }
	    baddot = ident;   // So user can see where they botched it
	    okSymp = lookupSymp;
	    string altIdent = "";
	    if (m_forPrearray) {
		// Cell foo__[array] before we've expanded arrays is just foo.
		if ((pos = ident.find("__BRA__")) != string::npos) {
		    altIdent = ident.substr(0,pos);
		}
	    }
	    UINFO(8,"         id "<<ident<<" left "<<leftname<<" at se"<<lookupSymp<<endl);
	    // Spec says; Look at exiting module (cellnames then modname),
	    // then look up (inst name or modname)
	    if (firstId) {
		// Check this module - subcellnames
		AstCell* cellp = lookupSymp->nodep()->castCell();  // Replicated below
		AstCellInline* inlinep = lookupSymp->nodep()->castCellInline(); // Replicated below
		if (VSymEnt* findSymp = findWithAltFallback(lookupSymp, ident, altIdent)) {
		    lookupSymp = findSymp;
		}
		// Check this module - cur modname
		else if ((cellp && cellp->modp()->origName() == ident)
			 || (inlinep && inlinep->origModName() == ident)) {}
		// Move up and check cellname + modname
		else {
		    while (lookupSymp) {
			lookupSymp = lookupSymp->parentp();
			cellp = lookupSymp->nodep()->castCell(); // Replicated above
			inlinep = lookupSymp->nodep()->castCellInline(); // Replicated above
			if (lookupSymp) {
			    UINFO(9,"\t\tUp to "<<lookupSymp<<endl);
			    if ((cellp && cellp->modp()->origName() == ident)
				|| (inlinep && inlinep->origModName() == ident)) {
				break;
			    }
			    else if (VSymEnt* findSymp = findWithAltFallback(lookupSymp, ident, altIdent)) {
				lookupSymp = findSymp;
				break;
			    }
			} else break;
		    }
		    if (!lookupSymp) return NULL;  // Not found
		}
	    } else { // Searching for middle submodule, must be a cell name
		if (VSymEnt* findSymp = findWithAltFallback(lookupSymp, ident, altIdent)) {
		    lookupSymp = findSymp;
		} else {
		    return NULL;  // Not found
		}
	    }
	    firstId = false;
	}
	return lookupSymp;
    }

    AstNode* findSymPrefixed(VSymEnt* lookupSymp, const string& dotname, string& baddot) {
	// Find symbol in given point in hierarchy
	// For simplicity lookupSymp may be passed NULL result from findDotted
	if (!lookupSymp) return NULL;
	UINFO(8,"\t\tfindSymPrefixed "<<dotname
	      <<((lookupSymp->symPrefix()=="") ? "" : " as ")
	      <<((lookupSymp->symPrefix()=="") ? "" : lookupSymp->symPrefix()+dotname)
	      <<"  at se"<<lookupSymp
	      <<endl);
	AstNode* nodep = lookupSymp->findIdFallback(lookupSymp->symPrefix() + dotname)->nodep();  // Might be NULL
	if (!nodep) baddot = dotname;
	return nodep;
    }
};

//======================================================================

class LinkDotFindVisitor : public AstNVisitor {
private:
    // STATE
    LinkDotState*	m_statep;	// State to pass between visitors, including symbol table
    VSymEnt*		m_modSymp;	// Symbol Entry for current module
    VSymEnt*		m_curSymp;	// Symbol Entry for current module, possibly a fake inlined one
    string		m_scope;	// Scope text
    AstBegin*		m_beginp;	// Current Begin/end block

    int debug() { return LinkDotState::debug(); }

    // VISITs
    virtual void visit(AstNetlist* nodep, AstNUser*) {
	// Process $unit or other packages
	// Not needed - dotted references not allowed from inside packages
	//for (AstNodeModule* nodep = v3Global.rootp()->modulesp(); nodep; nodep=nodep->nextp()->castNodeModule()) {
	//    if (nodep->castPackage()) {}}

	// The first module in the list is always the top module (sorted before this is called).
	// This may not be the module with isTop() set, as early in the steps,
	// wrapTop may have not been created yet.
	AstNodeModule* topmodp = nodep->modulesp();
	if (!topmodp) {
	    nodep->v3error("No top level module found");
	} else {
	    UINFO(8,"Top Module: "<<topmodp<<endl);
	    m_scope = "TOP";
	    m_curSymp = m_modSymp = m_statep->insertTopCell(topmodp, m_scope);
	    {
		topmodp->accept(*this);
	    }
	    m_scope = "";
	    m_curSymp = m_modSymp = NULL;
	}
    }
    virtual void visit(AstNodeModule* nodep, AstNUser*) {
	// Called on top module from Netlist, other modules from the cell creating them,
	// and packages
	UINFO(8,"   "<<nodep<<endl);
	if (!m_modSymp) {
	    // Will be optimized away later
	    UINFO(5, "Module not under any CELL or top - dead module\n");
	} else {
	    nodep->iterateChildren(*this);
	}
    }
    virtual void visit(AstScope* nodep, AstNUser*) {
	if (!m_statep->forScopeCreation()) v3fatalSrc("Scopes should only exist right after V3Scope");
	// Ignored.  Processed in next step
    }
    virtual void visit(AstCell* nodep, AstNUser*) {
	UINFO(5,"   CELL under "<<m_scope<<" is "<<nodep<<endl);
	// Process XREFs/etc inside pins
	nodep->iterateChildren(*this);
	// Recurse in, preserving state
	string oldscope = m_scope;
	AstBegin* oldbeginp = m_beginp;
	VSymEnt* oldModSymp = m_modSymp;
	VSymEnt* oldCurSymp = m_curSymp;
	// Where do we add it?
	VSymEnt* aboveSymp = m_curSymp;
	string origname = AstNode::dedotName(nodep->name());
	string::size_type pos;
	if ((pos = origname.rfind(".")) != string::npos) {
	    // Flattened, find what CellInline it should live under
	    string scope = origname.substr(0,pos);
	    string baddot;
	    VSymEnt* okSymp;
	    aboveSymp = m_statep->findDotted(aboveSymp, scope, baddot, okSymp);
	    if (!aboveSymp) nodep->v3fatalSrc("Can't find cell insertion point at '"<<baddot<<"' in: "<<nodep->prettyName());
	}
	{
	    m_scope = m_scope+"."+nodep->name();
	    m_curSymp = m_modSymp = m_statep->insertCell(aboveSymp, m_modSymp, nodep, m_scope);
	    m_beginp = NULL;
	    if (nodep->modp()) nodep->modp()->accept(*this);
	}
	m_scope = oldscope;
	m_beginp = oldbeginp;
	m_modSymp = oldModSymp;
	m_curSymp = oldCurSymp;
    }
    virtual void visit(AstCellInline* nodep, AstNUser*) {
	UINFO(5,"   CELLINLINE under "<<m_scope<<" is "<<nodep<<endl);
	VSymEnt* aboveSymp = m_curSymp;
	// If baz__DOT__foo__DOT__bar, we need to find baz__DOT__foo and add bar to it.
	string dottedname = nodep->name();
	string::size_type pos;
	if ((pos=dottedname.rfind("__DOT__")) != string::npos) {
	    string dotted = dottedname.substr(0, pos);
	    string ident  = dottedname.substr(pos+strlen("__DOT__"));
	    string baddot;
	    VSymEnt* okSymp;
	    aboveSymp = m_statep->findDotted(aboveSymp, dotted, baddot, okSymp);
	    if (!aboveSymp) nodep->v3fatalSrc("Can't find cellinline insertion point at '"<<baddot<<"' in: "<<nodep->prettyName());
	    m_statep->insertInline(aboveSymp, m_modSymp, nodep, ident);
	} else {  // No __DOT__, just directly underneath
	    m_statep->insertInline(aboveSymp, m_modSymp, nodep, nodep->name());
	}
    }
    virtual void visit(AstBegin* nodep, AstNUser*) {
	UINFO(5,"   "<<nodep<<endl);
	AstBegin* oldbegin = m_beginp;
	VSymEnt* oldSymp = m_curSymp;
	{
	    m_beginp = nodep;
	    // We don't pickup variables (as not supported yet), but do need to find cells
	    m_curSymp = m_statep->insertBegin(m_curSymp, m_modSymp, nodep);
	    nodep->stmtsp()->iterateAndNext(*this);
	}
	m_curSymp = oldSymp;
	m_beginp = oldbegin;
	//
	nodep->flatsp()->iterateAndNext(*this);
    }
    virtual void visit(AstNodeFTask* nodep, AstNUser*) {
	if (!m_beginp) {	// For now, we don't support xrefs into functions inside begin blocks
	    m_statep->insertSym(m_modSymp, nodep->name(), nodep);
	}
	// No recursion, we don't want to pick up variables
    }
    virtual void visit(AstVar* nodep, AstNUser*) {
	if (!m_statep->forScopeCreation()
	    && !m_beginp	// For now, we don't support xrefs into begin blocks
	    && !nodep->isFuncLocal()) {
	    m_statep->insertSym(m_modSymp, nodep->name(), nodep);
	} else {
	    UINFO(9,"       Not allowing dot refs to: "<<nodep<<endl);
	}
    }
    virtual void visit(AstCFunc* nodep, AstNUser*) {
	// Ignore all AstVars under functions
    }

    // For speed, don't recurse things that can't have cells
    // Note we allow AstNodeStmt's as generates may be under them
    virtual void visit(AstNodeMath*, AstNUser*) {}
    virtual void visit(AstNode* nodep, AstNUser*) {
	// Default: Just iterate
	nodep->iterateChildren(*this);
    }

public:
    // CONSTUCTORS
    LinkDotFindVisitor(AstNetlist* rootp, LinkDotState* statep) {
	UINFO(4,__FUNCTION__<<": "<<endl);
	m_curSymp = m_modSymp = NULL;
	m_statep = statep;
	m_beginp = NULL;
	//
	rootp->accept(*this);
    }
    virtual ~LinkDotFindVisitor() {}
};

//======================================================================

class LinkDotScopeVisitor : public AstNVisitor {
private:
    // STATE
    LinkDotState*	m_statep;	// State to pass between visitors, including symbol table
    VSymEnt*		m_modSymp;	// Symbol entry for current module

    int debug() { return LinkDotState::debug(); }

    // VISITs
    virtual void visit(AstScope* nodep, AstNUser*) {
	UINFO(8,"  SCOPE "<<nodep<<endl);
	if (!m_statep->forScopeCreation()) v3fatalSrc("Scopes should only exist right after V3Scope");
	// Using the CELL names, we created all hierarchy.  We now need to match this Scope
	// up with the hierarchy created by the CELL names.
	m_modSymp = m_statep->getScopeSym(nodep);
	nodep->iterateChildren(*this);
	m_modSymp = NULL;
    }
    virtual void visit(AstVarScope* nodep, AstNUser*) {
	if (!nodep->varp()->isFuncLocal()) {
	    m_statep->insertSym(m_modSymp, nodep->varp()->name(), nodep);
	}
    }
    virtual void visit(AstNodeFTask* nodep, AstNUser*) {
	m_statep->insertSym(m_modSymp, nodep->name(), nodep);
	// No recursion, we don't want to pick up variables
    }
    virtual void visit(AstAssignAlias* nodep, AstNUser*) {
	// Track aliases created by V3Inline; if we get a VARXREF(aliased_from)
	// we'll need to replace it with a VARXREF(aliased_to)
	if (m_statep->forScopeCreation()) {
	    if (debug()>=9) nodep->dumpTree(cout,"-\t\t\t\talias: ");
	    AstVarScope* fromVscp = nodep->lhsp()->castVarRef()->varScopep();
	    AstVarScope* toVscp   = nodep->rhsp()->castVarRef()->varScopep();
	    if (!fromVscp || !toVscp) nodep->v3fatalSrc("Bad alias scopes");
	    fromVscp->user2p(toVscp);
	}
	nodep->iterateChildren(*this);
    }
    // For speed, don't recurse things that can't have scope
    // Note we allow AstNodeStmt's as generates may be under them
    virtual void visit(AstCell*, AstNUser*) {}
    virtual void visit(AstVar*, AstNUser*) {}
    virtual void visit(AstNodeMath*, AstNUser*) {}
    virtual void visit(AstNode* nodep, AstNUser*) {
	// Default: Just iterate
	nodep->iterateChildren(*this);
    }

public:
    // CONSTUCTORS
    LinkDotScopeVisitor(AstNetlist* rootp, LinkDotState* statep) {
	UINFO(4,__FUNCTION__<<": "<<endl);
	m_modSymp = NULL;
	m_statep = statep;
	//
	rootp->accept(*this);
    }
    virtual ~LinkDotScopeVisitor() {}
};

//======================================================================

class LinkDotResolveVisitor : public AstNVisitor {
private:
    // STATE
    LinkDotState*	m_statep;	// State, including dotted symbol table
    VSymEnt*		m_modSymp;	// SymEnt for current module

    int debug() { return LinkDotState::debug(); }

    // METHODS

    // VISITs
    virtual void visit(AstNodeModule* nodep, AstNUser*) {
	UINFO(8,"  "<<nodep<<endl);
	if (!m_statep->existsModScope(nodep)) {
	    UINFO(5,"Dead module for "<<nodep<<endl);
	    m_modSymp = NULL;
	} else {
	    m_modSymp = m_statep->getNodeSym(nodep);
	}
	nodep->iterateChildren(*this);
	m_modSymp = NULL;
    }
    virtual void visit(AstScope* nodep, AstNUser*) {
	UINFO(8,"   "<<nodep<<endl);
	m_modSymp = m_statep->getScopeSym(nodep);
	nodep->iterateChildren(*this);
	m_modSymp = NULL;
    }
    virtual void visit(AstCellInline* nodep, AstNUser*) {
	if (m_statep->forScopeCreation()) {
	    nodep->unlinkFrBack(); pushDeletep(nodep); nodep=NULL;
	}
    }
    virtual void visit(AstVarXRef* nodep, AstNUser*) {
	// VarRef: Resolve its reference
	// We always link even if varp() is set, because the module we choose may change
	// due to creating new modules, flattening, etc.
	UINFO(8,"     "<<nodep<<endl);
	if (!m_modSymp) {
	    UINFO(9,"Dead module for "<<nodep<<endl);
	    nodep->varp(NULL);  // Module that is not in hierarchy.  We'll be dead code eliminating it later.
	} else {
	    string baddot;
	    VSymEnt* okSymp;
	    VSymEnt* dotSymp = m_modSymp;  // Start search at current scope
	    if (nodep->inlinedDots()!="") {  // Correct for current scope
		string inl = AstNode::dedotName(nodep->inlinedDots());
		dotSymp = m_statep->findDotted(dotSymp, inl, baddot, okSymp);
		if (!dotSymp) {
		    m_statep->preErrorDump();
		    nodep->v3fatalSrc("Couldn't resolve inlined scope '"<<baddot<<"' in: "<<nodep->inlinedDots());
		}
	    }
	    dotSymp = m_statep->findDotted(dotSymp, nodep->dotted(), baddot, okSymp); // Maybe NULL
	    if (!m_statep->forScopeCreation()) {
		AstVar* varp = (m_statep->findSymPrefixed(dotSymp, nodep->name(), baddot)
				->castVar());  // maybe NULL
		nodep->varp(varp);
		UINFO(7,"         Resolved "<<nodep<<endl);  // Also prints varp
		if (!nodep->varp()) {
		    m_statep->preErrorDump();
		    nodep->v3error("Can't find definition of '"<<baddot<<"' in dotted signal: "<<nodep->dotted()+"."+nodep->prettyName());
		    okSymp->cellErrorScopes(nodep);
		}
	    } else {
		string baddot;
		AstVarScope* vscp = (m_statep->findSymPrefixed(dotSymp, nodep->name(), baddot)
				     ->castVarScope());  // maybe NULL
		if (!vscp) {
		    m_statep->preErrorDump();
		    nodep->v3error("Can't find varpin scope of '"<<baddot<<"' in dotted signal: "<<nodep->dotted()+"."+nodep->prettyName());
		    okSymp->cellErrorScopes(nodep);
		} else {
		    while (vscp->user2p()) {  // If V3Inline aliased it, pick up the new signal
			UINFO(7,"         Resolved pre-alias "<<vscp<<endl);  // Also prints taskp
			vscp = vscp->user2p()->castNode()->castVarScope();
		    }
		    // Convert the VarXRef to a VarRef, so we don't need later optimizations to deal with VarXRef.
		    nodep->varp(vscp->varp());
		    nodep->varScopep(vscp);
		    UINFO(7,"         Resolved "<<nodep<<endl);  // Also prints taskp
		    AstVarRef* newvscp = new AstVarRef(nodep->fileline(), vscp, nodep->lvalue());
		    nodep->replaceWith(newvscp);
		    nodep->deleteTree(); nodep=NULL;
		}
	    }
	}
    }
    virtual void visit(AstNodeFTaskRef* nodep, AstNUser*) {
	UINFO(8,"     "<<nodep<<endl);
	if (nodep->packagep()) {
	    // References into packages don't care about cell hierarchy.
	} else if (!m_modSymp) {
	    UINFO(9,"Dead module for "<<nodep<<endl);
	    nodep->taskp(NULL);  // Module that is not in hierarchy.  We'll be dead code eliminating it later.
	} else if (nodep->dotted()=="" && nodep->taskp()) {
	    // Earlier should have setup the links
	    // Might be under a BEGIN we're not processing, so don't relink it
	} else {
	    string baddot;
	    VSymEnt* okSymp;
	    VSymEnt* dotSymp = m_modSymp;  // Start search at current scope
	    if (nodep->inlinedDots()!="") {  // Correct for current scope
		string inl = AstNode::dedotName(nodep->inlinedDots());
		UINFO(8,"\t\tInlined "<<inl<<endl);
		dotSymp = m_statep->findDotted(dotSymp, inl, baddot, okSymp);
		if (!dotSymp) {
		    m_statep->preErrorDump();
		    okSymp->cellErrorScopes(nodep);
		    nodep->v3fatalSrc("Couldn't resolve inlined scope '"<<baddot<<"' in: "<<nodep->inlinedDots());
		}
	    }
	    dotSymp = m_statep->findDotted(dotSymp, nodep->dotted(), baddot, okSymp); // Maybe NULL

	    AstNodeFTask* taskp = (m_statep->findSymPrefixed(dotSymp, nodep->name(), baddot)
				   ->castNode()->castNodeFTask()); // maybe NULL
	    nodep->taskp(taskp);
	    UINFO(7,"         Resolved "<<nodep<<endl);  // Also prints taskp
	    if (!nodep->taskp()) {
		m_statep->preErrorDump();
		nodep->v3error("Can't find definition of '"<<baddot<<"' in dotted task/function: "<<nodep->dotted()+"."+nodep->prettyName());
		okSymp->cellErrorScopes(nodep);
	    }
	}
	nodep->iterateChildren(*this);
    }
    virtual void visit(AstNode* nodep, AstNUser*) {
	// Default: Just iterate
	nodep->iterateChildren(*this);
    }
public:
    // CONSTUCTORS
    LinkDotResolveVisitor(AstNetlist* rootp, LinkDotState* statep) {
	UINFO(4,__FUNCTION__<<": "<<endl);
	m_statep = statep;
	m_modSymp = NULL;
	//
	rootp->accept(*this);
    }
    virtual ~LinkDotResolveVisitor() {}
};

//######################################################################
// Link class functions

void V3LinkDot::linkDotGuts(AstNetlist* rootp, bool prearray, bool scoped) {
    UINFO(2,__FUNCTION__<<": "<<endl);
    if (LinkDotState::debug()>=5 || v3Global.opt.dumpTree()>=9) v3Global.rootp()->dumpTreeFile(v3Global.debugFilename("prelinkdot.tree"));
    LinkDotState state (rootp, prearray, scoped);
    LinkDotFindVisitor visitor(rootp,&state);
    if (LinkDotState::debug()>=5 || v3Global.opt.dumpTree()>=9) v3Global.rootp()->dumpTreeFile(v3Global.debugFilename("prelinkdot-find.tree"));
    if (scoped) {
	// Well after the initial link when we're ready to operate on the flat design,
	// process AstScope's.  This needs to be separate pass after whole hierarchy graph created.
	LinkDotScopeVisitor visitors(rootp,&state);
	if (LinkDotState::debug()>=5 || v3Global.opt.dumpTree()>=9) v3Global.rootp()->dumpTreeFile(v3Global.debugFilename("prelinkdot-scoped.tree"));
    }
    state.dump();
    LinkDotResolveVisitor visitorb(rootp,&state);
}
