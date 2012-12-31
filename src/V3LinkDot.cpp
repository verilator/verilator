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
//	Top-down traversal in LinkDotFindVisitor
//	    Cells:
//		Make graph of cell hierarchy
//	    Var/Funcs's:
//		Collect all names into symtable under appropriate cell
//	Top-down traversal in LinkDotScopeVisitor
//	    Find VarScope versions of signals (well past original link)
//	Top-down traversal in LinkDotParamVisitor
//	    Create implicit signals
//	Top-down traversal in LinkDotResolveVisitor
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
    //  AstNodeModule::user1p()		// VSymEnt*.      Last symbol created for this node
    //	...				      Note maybe more than one, as can be multiple hierarchy places
    //  AstVarScope::user2p()		// AstVarScope*.  Base alias for AstInline of this signal
    //  AstVar::user2p()		// AstFTask*.     If a function variable, the task that links to the variable
    //  AstVar::user4()			// bool.          True if port set for this variable
    //  AstBegin::user4()		// bool.	  Did name processing
    //  AstNodeModule::user4()		// bool.          Live module
    AstUser1InUse	m_inuser1;
    AstUser2InUse	m_inuser2;
    AstUser4InUse	m_inuser4;

    // TYPES
    typedef std::multimap<string,VSymEnt*> NameScopeMap;
    typedef set <pair<AstNodeModule*,string> > ImplicitNameSet;

    // MEMBERS
    VSymGraph		m_syms;			// Symbol table
    VSymEnt*		m_dunitEntp;		// $unit entry
    NameScopeMap	m_nameScopeMap;		// Hash of scope referenced by non-pretty textual name
    ImplicitNameSet	m_implicitNameSet;	// For [module][signalname] if we can implicitly create it
    bool		m_forPrimary;		// First link
    bool		m_forPrearray;		// Compress cell__[array] refs
    bool		m_forScopeCreation;	// Remove VarXRefs for V3Scope
public:

    static int debug() {
	static int level = -1;
	if (VL_UNLIKELY(level < 0)) level = v3Global.opt.debugSrcLevel(__FILE__);
	return level;
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

    // CONSTRUCTORS
    LinkDotState(AstNetlist* rootp, VLinkDotStep step)
	: m_syms(rootp) {
	UINFO(4,__FUNCTION__<<": "<<endl);
	m_forPrimary = (step==LDS_PRIMARY);
	m_forPrearray = (step == LDS_PARAMED || step==LDS_PRIMARY);
	m_forScopeCreation = (step == LDS_SCOPED);
	m_dunitEntp = NULL;
    }
    ~LinkDotState() {}

    // ACCESSORS
    VSymGraph* symsp() { return &m_syms; }
    bool forPrimary() const { return m_forPrimary; }
    bool forPrearray() const { return m_forPrearray; }
    bool forScopeCreation() const { return m_forScopeCreation; }

    // METHODS
    static string nodeTextType(AstNode* nodep) {
	if (nodep->castVar()) return "variable";
	else if (nodep->castCell()) return "cell";
	else if (nodep->castTask()) return "task";
	else if (nodep->castFunc()) return "function";
	else if (nodep->castBegin()) return "block";
	else return nodep->prettyTypeName();
    }
    static string ucfirst(const string& text) {
	string out = text;
	out[0] = toupper(out[0]);
	return out;
    }

    VSymEnt* rootEntp() const { return m_syms.rootp(); }
    VSymEnt* dunitEntp() const { return m_dunitEntp; }
    void checkDuplicate(VSymEnt* lookupSymp, AstNode* nodep, const string& name) {
	// Lookup the given name under current symbol table
	// Insert if not found
	// Report error if there's a duplicate
	//
	// Note we only check for conflicts at the same level; it's ok if one block hides another
	// We also wouldn't want to not insert it even though it's lower down
	VSymEnt* foundp = lookupSymp->findIdFlat(name);
	AstNode* fnodep = foundp->nodep();
	if (!fnodep) {
	    // Not found, will add in a moment.
	} else if (nodep==fnodep) {  // Already inserted.
	    // Good.
	} else if (nodep->castBegin() && fnodep->castBegin()
		   && nodep->castBegin()->generate()) {
	    // Begin: ... blocks often replicate under genif/genfor, so simply suppress duplicate checks
	    // See t_gen_forif.v for an example.
	} else {
	    preErrorDump();
	    UINFO(4,"name "<<name<<endl);  // Not always same as nodep->name
	    UINFO(4,"Var1 "<<nodep<<endl);
	    UINFO(4,"Var2 "<<fnodep<<endl);
	    if (nodep->type() == fnodep->type()) {
		nodep->v3error("Duplicate declaration of "<<nodeTextType(fnodep)<<": "<<nodep->prettyName()<<endl
			       <<fnodep->warnMore()<<"... Location of original declaration");
	    } else {
		nodep->v3error("Unsupported in C: "<<ucfirst(nodeTextType(nodep))<<" has the same name as "
			       <<nodeTextType(fnodep)<<": "<<nodep->prettyName()<<endl
			       <<fnodep->warnMore()<<"... Location of original declaration");
	    }
	}
    }
    void insertDUnit(AstNetlist* nodep) {
	// $unit on top scope
	VSymEnt* symp = new VSymEnt(&m_syms, nodep);
	UINFO(9,"      INSERTdunit se"<<(void*)symp<<endl);
	symp->parentp(rootEntp());  // Needed so backward search can find name of top module
	symp->fallbackp(NULL);
	rootEntp()->insert("$unit ",symp);  // Space so can never name conflict with user code
	//
	if (m_dunitEntp) nodep->v3fatalSrc("Call insertDUnit only once");
	m_dunitEntp = symp;
    }
    VSymEnt* insertTopCell(AstNodeModule* nodep, const string& scopename) {
	// Only called on the module at the very top of the hierarchy
	VSymEnt* symp = new VSymEnt(&m_syms, nodep);
	UINFO(9,"      INSERTtop se"<<(void*)symp<<"  "<<scopename<<" "<<nodep<<endl);
	symp->parentp(rootEntp());  // Needed so backward search can find name of top module
	symp->fallbackp(dunitEntp());  // Needed so can find $unit stuff
	nodep->user1p(symp);
	checkDuplicate(rootEntp(), nodep, nodep->origName());
	rootEntp()->insert(nodep->origName(),symp);
	if (forScopeCreation()) m_nameScopeMap.insert(make_pair(scopename, symp));
	return symp;
    }
    VSymEnt* insertCell(VSymEnt* abovep, VSymEnt* modSymp,
			AstCell* nodep, const string& scopename) {
	if (!abovep) nodep->v3fatalSrc("Null symbol table inserting node");
	VSymEnt* symp = new VSymEnt(&m_syms, nodep);
	UINFO(9,"      INSERTcel se"<<(void*)symp<<"  "<<scopename<<" above=se"<<(void*)abovep<<" mods=se"<<(void*)modSymp<<" node="<<nodep<<endl);
	symp->parentp(abovep);
	symp->fallbackp(dunitEntp());  // Needed so can find $unit stuff
	nodep->user1p(symp);
	if (nodep->modp()) nodep->modp()->user1p(symp);
	checkDuplicate(abovep, nodep, nodep->origName());
	abovep->reinsert(nodep->origName(), symp);
	if (abovep != modSymp && !modSymp->findIdFlat(nodep->name())) {
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
	nodep->user1p(symp);
	checkDuplicate(abovep, nodep, nodep->name());
	abovep->reinsert(basename, symp);
	if (abovep != modSymp && !modSymp->findIdFlat(nodep->name())) {
	    // If it's foo_DOT_bar, we need to be able to find it under that too.
	    modSymp->reinsert(nodep->name(), symp);
	}
	return symp;
    }
    VSymEnt* insertBlock(VSymEnt* abovep, const string& name, AstNode* nodep, AstPackage* packagep) {
	// A fake point in the hierarchy, corresponding to a begin or function/task block
	// After we remove begins these will go away
	// Note we fallback to the symbol table of the parent, as we want to find variables there
	// However, cells walk the graph, so cells will appear under the begin/ftask itself
	if (!abovep) nodep->v3fatalSrc("Null symbol table inserting node");
	VSymEnt* symp = new VSymEnt(&m_syms, nodep);
	UINFO(9,"      INSERTblk se"<<(void*)symp<<"  above=se"<<(void*)abovep<<"  node="<<nodep<<endl);
	symp->parentp(abovep);
	symp->packagep(packagep);
	symp->fallbackp(abovep);  // Needed so can find $unit stuff
	nodep->user1p(symp);
	if (name != "") {
	    checkDuplicate(abovep, nodep, name);
	}
	// Duplicates are possible, as until resolve generates might have 2 same cells under an if
	abovep->reinsert(name, symp);
	return symp;
    }
    VSymEnt* insertSym(VSymEnt* abovep, const string& name, AstNode* nodep, AstPackage* packagep) {
	if (!abovep) nodep->v3fatalSrc("Null symbol table inserting node");
	VSymEnt* symp = new VSymEnt(&m_syms, nodep);
	UINFO(9,"      INSERTsym se"<<(void*)symp<<"  name='"<<name<<"' above=se"<<(void*)abovep<<"  node="<<nodep<<endl);
	// We don't remember the ent associated with each node, because we need a unique scope entry for each instantiation
	symp->packagep(packagep);
	symp->parentp(abovep);
	symp->fallbackp(abovep);
	nodep->user1p(symp);
	checkDuplicate(abovep, nodep, name);
	abovep->insert(name, symp);
	return symp;
    }
    static bool existsModScope(AstNodeModule* nodep) {
	return nodep->user1p()!=NULL;
    }
    static VSymEnt* getNodeSym(AstNode* nodep) {
	// Don't use this in ResolveVisitor, as we need to pick up the proper reference under each SCOPE
	VSymEnt* symp = nodep->user1p()->castSymEnt();
	if (!symp) nodep->v3fatalSrc("Module/etc never assigned a symbol entry?");
	return symp;
    }
    VSymEnt* getScopeSym(AstScope* nodep) {
	NameScopeMap::iterator iter = m_nameScopeMap.find(nodep->name());
	if (iter == m_nameScopeMap.end()) {
	    nodep->v3fatalSrc("Scope never assigned a symbol entry?");
	}
	return iter->second;
    }
    void implicitOkAdd(AstNodeModule* nodep, const string& varname) {
	// Mark the given variable name as being allowed to be implicitly declared
	if (nodep) {
	    ImplicitNameSet::iterator iter = m_implicitNameSet.find(make_pair(nodep,varname));
	    if (iter == m_implicitNameSet.end()) {
		m_implicitNameSet.insert(make_pair(nodep,varname));
	    }
	}
    }
    bool implicitOk(AstNodeModule* nodep, const string& varname) {
	return nodep
	    && (m_implicitNameSet.find(make_pair(nodep,varname)) != m_implicitNameSet.end());
    }

private:
    VSymEnt* findWithAltFallback(VSymEnt* symp, const string& name, const string& altname) {
	VSymEnt* findp = symp->findIdFallback(name);
	if (findp) return findp;
	if (altname != "") {
	    UINFO(8,"     alt fallback\n");
	    findp = symp->findIdFallback(altname);
	}
	return findp;
    }
public:
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
		// GENFOR Begin is foo__BRA__##__KET__ after we've genloop unrolled,
		// but presently should be just "foo".
		// Likewise cell foo__[array] before we've expanded arrays is just foo
		if ((pos = ident.rfind("__BRA__")) != string::npos) {
		    altIdent = ident.substr(0,pos);
		}
	    }
	    UINFO(8,"         id "<<ident<<" alt "<<altIdent<<" left "<<leftname<<" at se"<<lookupSymp<<endl);
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

    VSymEnt* findSymPrefixed(VSymEnt* lookupSymp, const string& dotname, string& baddot) {
	// Find symbol in given point in hierarchy, allowing prefix (post-Inline)
	// For simplicity lookupSymp may be passed NULL result from findDotted
	if (!lookupSymp) return NULL;
	UINFO(8,"\t\tfindSymPrefixed "<<dotname
	      <<" under se"<<(void*)lookupSymp
	      <<((lookupSymp->symPrefix()=="") ? "" : " as ")
	      <<((lookupSymp->symPrefix()=="") ? "" : lookupSymp->symPrefix()+dotname)
	      <<"  at se"<<lookupSymp
	      <<endl);
	VSymEnt* foundp = lookupSymp->findIdFallback(lookupSymp->symPrefix() + dotname);  // Might be NULL
	if (!foundp) baddot = dotname;
	return foundp;
    }
};

//======================================================================

class LinkDotFindVisitor : public AstNVisitor {
private:
    // STATE
    LinkDotState*	m_statep;	// State to pass between visitors, including symbol table
    AstPackage*		m_packagep;	// Current package
    VSymEnt*		m_modSymp;	// Symbol Entry for current module
    VSymEnt*		m_curSymp;	// Symbol Entry for current table, where to lookup/insert
    string		m_scope;	// Scope text
    AstBegin*		m_beginp;	// Current Begin/end block
    AstNodeFTask*	m_ftaskp;	// Current function/task
    bool		m_inGenerate;	// Inside a generate
    int			m_paramNum;	// Parameter number, for position based connection
    int			m_beginNum;	// Begin block number, 0=none seen
    int			m_modBeginNum;	// Begin block number in module, 0=none seen

    // METHODS
    int debug() { return LinkDotState::debug(); }

    // VISITs
    virtual void visit(AstNetlist* nodep, AstNUser*) {
	// Process $unit or other packages
	// Not needed - dotted references not allowed from inside packages
	//for (AstNodeModule* nodep = v3Global.rootp()->modulesp(); nodep; nodep=nodep->nextp()->castNodeModule()) {
	//    if (nodep->castPackage()) {}}

	m_statep->insertDUnit(nodep);

	// First back iterate, to find all packages. Backward as must do base packages before using packages
	nodep->iterateChildrenBackwards(*this);

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
    virtual void visit(AstTypeTable* nodep, AstNUser*) {}
    virtual void visit(AstNodeModule* nodep, AstNUser*) {
	// Called on top module from Netlist, other modules from the cell creating them,
	// and packages
	UINFO(8,"   "<<nodep<<endl);
	// m_curSymp/m_modSymp maybe NULL for packages and non-top modules
	// Packages will be under top after the initial phases, but until then need separate handling
	bool standalonePkg = !m_modSymp && (m_statep->forPrearray() && nodep->castPackage());
	bool doit = (m_modSymp || standalonePkg);
	string oldscope = m_scope;
	VSymEnt* oldModSymp = m_modSymp;
	VSymEnt* oldCurSymp = m_curSymp;
        int      oldParamNum    = m_paramNum;
        int      oldBeginNum    = m_beginNum;
        int      oldModBeginNum = m_modBeginNum;
	if (doit) {
	    UINFO(2,"     Link Module: "<<nodep<<endl);
	    if (nodep->dead()) nodep->v3fatalSrc("Module in cell tree mislabeled as dead?");
	    VSymEnt* upperSymp = m_curSymp ? m_curSymp : m_statep->rootEntp();
	    m_packagep = nodep->castPackage();
	    if (standalonePkg) {
		if (m_packagep->isDollarUnit()) {
		    m_curSymp = m_modSymp = m_statep->dunitEntp();
		    nodep->user1p(m_curSymp);
		} else {
		    m_scope = nodep->name();
		    m_curSymp = m_modSymp = m_statep->insertBlock(upperSymp, nodep->name()+"::", nodep, m_packagep);
		    UINFO(9, "New module scope "<<m_curSymp<<endl);
		}
	    }
	    //
	    m_paramNum = 0;
	    m_beginNum = 0;
	    m_modBeginNum = 0;
	    // m_modSymp/m_curSymp for non-packages set by AstCell above this module
	    // Iterate
	    nodep->iterateChildren(*this);
	    nodep->user4(true);
	} else { //!doit
	    // Will be optimized away later
	    // Can't remove now, as our backwards iterator will throw up
	    UINFO(5, "Module not under any CELL or top - dead module: "<<nodep<<endl);
	}
	m_scope = oldscope;
	m_modSymp = oldModSymp;
	m_curSymp = oldCurSymp;
        m_paramNum    = oldParamNum;
        m_beginNum    = oldBeginNum;
        m_modBeginNum = oldModBeginNum;
	// Prep for next
	m_packagep = NULL;
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
	int oldParamNum = m_paramNum;
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
	    if (!aboveSymp) {
		m_statep->preErrorDump();
		nodep->v3fatalSrc("Can't find cell insertion point at '"<<baddot<<"' in: "<<nodep->prettyName());
	    }
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
	m_paramNum = oldParamNum;
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
	    if (!aboveSymp) {
		m_statep->preErrorDump();
		nodep->v3fatalSrc("Can't find cellinline insertion point at '"<<baddot<<"' in: "<<nodep->prettyName());
	    }
	    m_statep->insertInline(aboveSymp, m_modSymp, nodep, ident);
	} else {  // No __DOT__, just directly underneath
	    m_statep->insertInline(aboveSymp, m_modSymp, nodep, nodep->name());
	}
    }
    virtual void visit(AstDefParam* nodep, AstNUser*) {
	nodep->user1p(m_curSymp);
	nodep->iterateChildren(*this);
    }
    virtual void visit(AstGenerate* nodep, AstNUser*) {
	// Begin: ... blocks often replicate under genif/genfor, so simply suppress duplicate checks
	// See t_gen_forif.v for an example.
	bool lastInGen = m_inGenerate;
	{
	    m_inGenerate = true;
	    nodep->iterateChildren(*this);
	}
	m_inGenerate = lastInGen;
    }
    virtual void visit(AstBegin* nodep, AstNUser*) {
	UINFO(5,"   "<<nodep<<endl);
	// Rename "genblk"s to include a number
	if (m_statep->forPrimary() && !nodep->user4SetOnce()) {
	    if (nodep->name() == "genblk") {
		++m_beginNum;
		nodep->name(nodep->name()+cvtToStr(m_beginNum));
	    }
	    // Just for loop index, make special name.  The [00] is so it will "dearray" to same
	    // name as after we expand the GENFOR
	    if (nodep->genforp()) nodep->name(nodep->name());
	}
	// All blocks are numbered in the standard, IE we start with "genblk1" even if only one.
	if (nodep->name()=="" && nodep->unnamed()) {
	    // Unnamed blocks are only important when they contain var
	    // decls, so search for them. (Otherwise adding all the
	    // unnamed#'s would just confuse tracing variables in
	    // places such as tasks, where "task ...; begin ... end"
	    // are common.
	    for (AstNode* stmtp = nodep->stmtsp(); stmtp; stmtp=stmtp->nextp()) {
		if (stmtp->castVar()) {
		    ++m_modBeginNum;
		    nodep->name("unnamedblk"+cvtToStr(m_modBeginNum));
		    break;
		}
	    }
	}
	int oldNum = m_beginNum;
	AstBegin* oldbegin = m_beginp;
	VSymEnt* oldCurSymp = m_curSymp;
	{
	    m_beginNum = 0;
	    m_beginp = nodep;
	    m_curSymp = m_statep->insertBlock(m_curSymp, nodep->name(), nodep, m_packagep);
	    m_curSymp->fallbackp(oldCurSymp);
	    // Iterate
	    nodep->iterateChildren(*this);
	}
	m_curSymp = oldCurSymp;
	m_beginp = oldbegin;
	m_beginNum = oldNum;
    }
    virtual void visit(AstNodeFTask* nodep, AstNUser*) {
	// NodeTask: Remember its name for later resolution
	UINFO(5,"   "<<nodep<<endl);
	if (!m_curSymp || !m_modSymp) nodep->v3fatalSrc("Function/Task not under module??\n");
	// Remember the existing symbol table scope
	VSymEnt* oldCurSymp = m_curSymp;
	{
	    // Create symbol table for the task's vars
	    m_curSymp = m_statep->insertBlock(m_curSymp, nodep->name(), nodep, m_packagep);
	    m_curSymp->fallbackp(oldCurSymp);
	    // Convert the func's range to the output variable
	    // This should probably be done in the Parser instead, as then we could
	    // just attact normal signal attributes to it.
	    if (nodep->fvarp()
		&& !nodep->fvarp()->castVar()) {
		AstNodeDType* dtypep = nodep->fvarp()->castNodeDType();
		// If unspecified, function returns one bit; however when we support NEW() it could
		// also return the class reference.
		if (dtypep) dtypep->unlinkFrBack();
		else dtypep = new AstBasicDType(nodep->fileline(), AstBasicDTypeKwd::LOGIC);
		AstVar* newvarp = new AstVar(nodep->fileline(), AstVarType::OUTPUT, nodep->name(),
					     VFlagChildDType(), dtypep);  // Not dtype resolved yet
		newvarp->funcReturn(true);
		newvarp->trace(false);  // Not user visible
		newvarp->attrIsolateAssign(nodep->attrIsolateAssign());
		nodep->addFvarp(newvarp);
		// Explicit insert required, as the var name shadows the upper level's task name
		m_statep->insertSym(m_curSymp, newvarp->name(), newvarp, NULL/*packagep*/);
	    }
	    m_ftaskp = nodep;
	    nodep->iterateChildren(*this);
	    m_ftaskp = NULL;
	}
	m_curSymp = oldCurSymp;
    }
    virtual void visit(AstVar* nodep, AstNUser*) {
	// Var: Remember its name for later resolution
	if (!m_curSymp || !m_modSymp) nodep->v3fatalSrc("Var not under module??\n");
	nodep->iterateChildren(*this);
	if (!m_statep->forScopeCreation()) {
	    // Find under either a task or the module's vars
	    VSymEnt* foundp = m_curSymp->findIdFallback(nodep->name());
	    if (!foundp && m_modSymp && nodep->name() == m_modSymp->nodep()->name()) foundp = m_modSymp;  // Conflicts with modname?
	    AstVar* findvarp = foundp->nodep()->castVar();
	    bool ins=false;
	    if (!foundp) {
		ins=true;
	    } else if (!findvarp && foundp && m_curSymp->findIdFlat(nodep->name())) {
		m_statep->preErrorDump();
		nodep->v3error("Unsupported in C: Variable has same name as "
			       <<LinkDotState::nodeTextType(foundp->nodep())<<": "<<nodep->prettyName());
	    } else if (findvarp != nodep) {
		UINFO(4,"DupVar: "<<nodep<<" ;; "<<foundp->nodep()<<endl);
		UINFO(4,"    found  cur=se"<<(void*)m_curSymp<<" ;; parent=se"<<(void*)foundp->parentp()<<endl);
		if (foundp && foundp->parentp() == m_curSymp) {  // Only when on same level
		    if ((findvarp->isIO() && nodep->isSignal())
			|| (findvarp->isSignal() && nodep->isIO())) {
			findvarp->combineType(nodep);
			nodep->fileline()->modifyStateInherit(nodep->fileline());
			AstBasicDType* bdtypep = findvarp->childDTypep()->castBasicDType();
			if (bdtypep && bdtypep->implicit()) {
			    // Then have "input foo" and "real foo" so the dtype comes from the other side.
			    AstNodeDType* newdtypep = nodep->subDTypep();
			    if (!newdtypep || !nodep->childDTypep()) findvarp->v3fatalSrc("No child type?");
			    bdtypep->unlinkFrBack()->deleteTree();
			    newdtypep->unlinkFrBack();
			    findvarp->childDTypep(newdtypep);
			}
			nodep->unlinkFrBack()->deleteTree(); nodep=NULL;
		    } else {
			nodep->v3error("Duplicate declaration of signal: "<<nodep->prettyName()<<endl
				       <<findvarp->warnMore()<<"... Location of original declaration");
		    }
		} else {
		    // User can disable the message at either point
		    if (!(m_ftaskp && m_ftaskp->dpiImport())
			&& (!m_ftaskp || m_ftaskp != foundp->nodep())  // Not the function's variable hiding function
			&& !nodep->fileline()->warnIsOff(V3ErrorCode::VARHIDDEN)
			&& !foundp->nodep()->fileline()->warnIsOff(V3ErrorCode::VARHIDDEN)) {
			nodep->v3warn(VARHIDDEN,"Declaration of signal hides declaration in upper scope: "<<nodep->name()<<endl
				      <<foundp->nodep()->warnMore()<<"... Location of original declaration");
		    }
		    ins = true;
		}
	    }
	    if (ins) {
		m_statep->insertSym(m_curSymp, nodep->name(), nodep, m_packagep);
		if (m_statep->forPrimary() && nodep->isGParam()) {
		    m_paramNum++;
		    VSymEnt* symp = m_statep->insertSym(m_curSymp, "__paramNumber"+cvtToStr(m_paramNum), nodep, m_packagep);
		    symp->exported(false);
		}
	    }
	}
    }
    virtual void visit(AstTypedef* nodep, AstNUser*) {
	// Remember its name for later resolution
	if (!m_curSymp) nodep->v3fatalSrc("Typedef not under module??\n");
	nodep->iterateChildren(*this);
	m_statep->insertSym(m_curSymp, nodep->name(), nodep, m_packagep);
    }
    virtual void visit(AstCFunc* nodep, AstNUser*) {
	// For dotted resolution, ignore all AstVars under functions, otherwise shouldn't exist
	if (m_statep->forScopeCreation()) nodep->v3fatalSrc("No CFuncs expected in tree yet");
    }
    virtual void visit(AstEnumItem* nodep, AstNUser*) {
	// EnumItem: Remember its name for later resolution
	nodep->iterateChildren(*this);
	// Find under either a task or the module's vars
	VSymEnt* foundp = m_curSymp->findIdFallback(nodep->name());
	if (!foundp && m_modSymp && nodep->name() == m_modSymp->nodep()->name()) foundp = m_modSymp;  // Conflicts with modname?
	AstEnumItem* findvarp = foundp->nodep()->castEnumItem();
	bool ins=false;
	if (!foundp) {
	    ins=true;
	} else if (findvarp != nodep) {
	    UINFO(4,"DupVar: "<<nodep<<" ;; "<<foundp<<endl);
	    if (foundp && foundp->parentp() == m_curSymp) {  // Only when on same level
		nodep->v3error("Duplicate declaration of enum value: "<<nodep->prettyName()<<endl
			       <<findvarp->warnMore()<<"... Location of original declaration");
	    } else {
		// User can disable the message at either point
		if (!nodep->fileline()->warnIsOff(V3ErrorCode::VARHIDDEN)
		    && !foundp->nodep()->fileline()->warnIsOff(V3ErrorCode::VARHIDDEN)) {
		    nodep->v3warn(VARHIDDEN,"Declaration of enum value hides declaration in upper scope: "<<nodep->name()<<endl
				  <<foundp->nodep()->warnMore()<<"... Location of original declaration");
		}
		ins = true;
	    }
	}
	if (ins) {
	    m_statep->insertSym(m_curSymp, nodep->name(), nodep, m_packagep);
	}
    }
    virtual void visit(AstPackageImport* nodep, AstNUser*) {
	UINFO(2,"  Link: "<<nodep<<endl);
	VSymEnt* srcp = m_statep->getNodeSym(nodep->packagep());
	if (nodep->name()!="*") {
	    VSymEnt* impp = srcp->findIdFlat(nodep->name());
	    if (!impp) {
		nodep->v3error("Import object not found: "<<nodep->packagep()->prettyName()<<"::"<<nodep->prettyName());
	    }
	}
	m_curSymp->import(m_statep->symsp(), srcp, nodep->name());
	UINFO(2,"    Link Done: "<<nodep<<endl);
	// No longer needed, but can't delete until any multi-instantiated modules are expanded
    }

    virtual void visit(AstNode* nodep, AstNUser*) {
	// Default: Just iterate
	nodep->iterateChildren(*this);
    }

public:
    // CONSTUCTORS
    LinkDotFindVisitor(AstNetlist* rootp, LinkDotState* statep) {
	UINFO(4,__FUNCTION__<<": "<<endl);
	m_packagep = NULL;
	m_curSymp = m_modSymp = NULL;
	m_statep = statep;
	m_beginp = NULL;
	m_ftaskp = NULL;
	m_inGenerate = false;
	m_paramNum = 0;
	m_beginNum = 0;
	m_modBeginNum = 0;
	//
	rootp->accept(*this);
    }
    virtual ~LinkDotFindVisitor() {}
};

//======================================================================

class LinkDotParamVisitor : public AstNVisitor {
private:
    // NODE STATE
    // Cleared on global
    //  *::user1p()		-> See LinkDotState
    //  *::user2p()		-> See LinkDotState
    //  *::user4()		-> See LinkDotState

    // STATE
    LinkDotState*	m_statep;	// State to pass between visitors, including symbol table
    AstNodeModule*	m_modp;		// Current module

    int debug() { return LinkDotState::debug(); }

    void pinImplicitExprRecurse(AstNode* nodep) {
	// Under a pin, Check interconnect expression for a pin reference or a concat.
	// Create implicit variable as needed
	if (nodep->castDot()) {  // Not creating a simple implied type,
	    // and implying something else would just confuse later errors
	}
	else if (nodep->castVarRef() || (nodep->castParseRef() && nodep->castParseRef()->start())) {
	    // To prevent user errors, we should only do single bit
	    // implicit vars, however some netlists (MIPS) expect single
	    // bit implicit wires to get created with range 0:0 etc.
	    m_statep->implicitOkAdd(m_modp, nodep->name());
	}
	// These are perhaps a little too generous, as a SELect of siga[sigb]
	// perhaps shouldn't create an implicit variable.  But, we've warned...
	else {
	    if (nodep->op1p()) pinImplicitExprRecurse(nodep->op1p());
	    if (nodep->op2p()) pinImplicitExprRecurse(nodep->op2p());
	    if (nodep->op3p()) pinImplicitExprRecurse(nodep->op3p());
	    if (nodep->op4p()) pinImplicitExprRecurse(nodep->op4p());
	    if (nodep->nextp()) pinImplicitExprRecurse(nodep->nextp());
	}
    }

    // VISITs
    virtual void visit(AstTypeTable* nodep, AstNUser*) {}
    virtual void visit(AstNodeModule* nodep, AstNUser*) {
	UINFO(5,"   "<<nodep<<endl);
	if (nodep->dead() || !nodep->user4()) {
	    UINFO(4,"Mark dead module "<<nodep<<endl);
	    if (!m_statep->forPrearray()) nodep->v3fatalSrc("Dead module persisted past where should have removed");
	    // Don't remove now, because we may have a tree of parameterized modules with VARXREFs into the deleted module region
	    // V3Dead should cleanup.
	    // Downstream visitors up until V3Dead need to check for nodep->dead.
	    nodep->dead(true);
	} else {
	    m_modp = nodep;
	    nodep->iterateChildren(*this);
	    m_modp = NULL;
	}
    }
    virtual void visit(AstPin* nodep, AstNUser*) {
	// Pin: Link to submodule's port
	// Deal with implicit definitions - do before Resolve visitor as may be referenced above declaration
	if (nodep->exprp() // Else specifically unconnected pin
	    && !nodep->svImplicit()) {   // SV 19.11.3: .name pins don't allow implicit decls
	    pinImplicitExprRecurse(nodep->exprp());
	}
    }
    virtual void visit(AstDefParam* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
	nodep->v3warn(DEFPARAM,"Suggest replace defparam with Verilog 2001 #(."<<nodep->name()<<"(...etc...))");
	VSymEnt* foundp = m_statep->getNodeSym(nodep)->findIdFallback(nodep->path());
	AstCell* cellp = foundp->nodep()->castCell();
	if (!cellp) {
	    nodep->v3error("In defparam, cell "<<nodep->path()<<" never declared");
	} else {
	    AstNode* exprp = nodep->rhsp()->unlinkFrBack();
	    UINFO(9,"Defparam cell "<<nodep->path()<<"."<<nodep->name()
		  <<" attach-to "<<cellp
		  <<"  <= "<<exprp<<endl);
	    // Don't need to check the name of the defparam exists.  V3Param does.
	    AstPin* pinp = new AstPin (nodep->fileline(),
				       -1, // Pin# not relevant
				       nodep->name(),
				       exprp);
	    cellp->addParamsp(pinp);
	    nodep->unlinkFrBack()->deleteTree(); nodep=NULL;
	}
    }
    virtual void visit(AstPort* nodep, AstNUser*) {
	// Port: Stash the pin number
	// Need to set pin numbers after varnames are created
	// But before we do the final resolution based on names
	VSymEnt* foundp = m_statep->getNodeSym(m_modp)->findIdFlat(nodep->name());
	AstVar* refp = foundp->nodep()->castVar();
	if (!refp) {
	    nodep->v3error("Input/output/inout declaration not found for port: "<<nodep->prettyName());
	} else if (!refp->isIO()) {
	    nodep->v3error("Pin is not an in/out/inout: "<<nodep->prettyName());
	} else {
	    refp->user4(true);
	    VSymEnt* symp = m_statep->insertSym(m_statep->getNodeSym(m_modp),
						"__pinNumber"+cvtToStr(nodep->pinNum()), refp, NULL/*packagep*/);
	    symp->exported(false);
	}
	// Ports not needed any more
	nodep->unlinkFrBack()->deleteTree();  nodep=NULL;
    }
    virtual void visit(AstAssignW* nodep, AstNUser*) {
	// Deal with implicit definitions
	// We used to nodep->allowImplicit() here, but it turns out
	// normal "assigns" can also make implicit wires.  Yuk.
	pinImplicitExprRecurse(nodep->lhsp());
	nodep->iterateChildren(*this);
    }
    virtual void visit(AstAssignAlias* nodep, AstNUser*) {
	// tran gates need implicit creation
	// As VarRefs don't exist in forPrimary, sanity check
	if (m_statep->forPrimary()) nodep->v3fatalSrc("Assign aliases unexpected pre-dot");
	if (AstVarRef* forrefp = nodep->lhsp()->castVarRef()) {
	    pinImplicitExprRecurse(forrefp);
	}
	if (AstVarRef* forrefp = nodep->rhsp()->castVarRef()) {
	    pinImplicitExprRecurse(forrefp);
	}
	nodep->iterateChildren(*this);
    }
    virtual void visit(AstImplicit* nodep, AstNUser*) {
	// Unsupported gates need implicit creation
	pinImplicitExprRecurse(nodep);
	// We're done with implicit gates
	nodep->unlinkFrBack()->deleteTree(); nodep=NULL;
    }
    virtual void visit(AstNode* nodep, AstNUser*) {
	// Default: Just iterate
	nodep->iterateChildren(*this);
    }

public:
    // CONSTUCTORS
    LinkDotParamVisitor(AstNetlist* rootp, LinkDotState* statep) {
	UINFO(4,__FUNCTION__<<": "<<endl);
	m_statep = statep;
	m_modp = NULL;
	//
	rootp->accept(*this);
    }
    virtual ~LinkDotParamVisitor() {}
};


//======================================================================

class LinkDotScopeVisitor : public AstNVisitor {
private:
    // STATE
    LinkDotState*	m_statep;	// State to pass between visitors, including symbol table
    VSymEnt*		m_modSymp;	// Symbol entry for current module

    int debug() { return LinkDotState::debug(); }

    // VISITs
    virtual void visit(AstNetlist* nodep, AstNUser* vup) {
	// Recurse..., backward as must do packages before using packages
	nodep->iterateChildrenBackwards(*this);
    }
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
	    m_statep->insertSym(m_modSymp, nodep->varp()->name(), nodep, NULL);
	}
    }
    virtual void visit(AstNodeFTask* nodep, AstNUser*) {
	VSymEnt* symp = m_statep->insertBlock(m_modSymp, nodep->name(), nodep, NULL);
	symp->fallbackp(m_modSymp);
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
    // NODE STATE
    // Cleared on global
    //  *::user1p()		-> See LinkDotState
    //  *::user2p()		-> See LinkDotState
    //  *::user3()		// bool.	  Processed
    //  *::user4()		-> See LinkDotState
    // Cleared on Cell
    //  AstVar::user5()		// bool.	  True if pin used in this cell
    AstUser3InUse	m_inuser3;
    AstUser5InUse	m_inuser5;

    // TYPES
    enum DotPosition { DP_SCOPE, DP_VAR_ETC, DP_MEMBER };

    // STATE
    LinkDotState*	m_statep;	// State, including dotted symbol table
    VSymEnt*		m_curSymp;	// SymEnt for current lookup point
    VSymEnt*		m_modSymp;	// SymEnt for current module
    VSymEnt*		m_pinSymp;	// SymEnt for pin lookups
    AstCell*		m_cellp;	// Current cell
    AstNodeModule*	m_modp;		// Current module
    AstNodeFTask* 	m_ftaskp;	// Current function/task

    struct DotStates {
	VSymEnt*	m_dotSymp;	// SymEnt for dotted AstParse lookup
	AstDot*		m_dotp;		// Current dot
	DotPosition	m_dotPos;	// Scope part of dotted resolution
	bool		m_dotErr;	// Error found in dotted resolution, ignore upwards
	string		m_dotText;	// String of dotted names found in below parseref
	void init(VSymEnt* curSymp) {
	    m_dotSymp = curSymp;  m_dotp = NULL;  m_dotPos = DP_VAR_ETC;  m_dotErr = false;  m_dotText = "";
	}
	DotStates() { init(NULL); }
	~DotStates() {}
    } m_ds;  // State to preserve across recursions

    int debug() { return LinkDotState::debug(); }

    // METHODS - Variables
    void createImplicitVar (VSymEnt* lookupSymp, AstVarRef* nodep, AstNodeModule* modp, VSymEnt* moduleSymp, bool noWarn) {
	// Create implicit after warning
	if (!nodep->varp()) {
	    if (!noWarn) {
		if (nodep->fileline()->warnIsOff(V3ErrorCode::I_DEF_NETTYPE_WIRE)) {
		    nodep->v3error("Signal definition not found, and implicit disabled with `default_nettype: "<<nodep->prettyName());
		} else {
		    nodep->v3warn(IMPLICIT,"Signal definition not found, creating implicitly: "<<nodep->prettyName());
		}
	    }
	    AstVar* newp = new AstVar (nodep->fileline(), AstVarType::WIRE,
				       nodep->name(), VFlagLogicPacked(), 1);
	    newp->trace(modp->modTrace());
	    nodep->varp(newp);
	    modp->addStmtp(newp);
	    // Link it to signal list, must add the variable under the module; current scope might be lower now
	    m_statep->insertSym(moduleSymp, newp->name(), newp, NULL/*packagep*/);
	}
    }
    void taskFuncSwapCheck(AstNodeFTaskRef* nodep) {
	if (nodep->taskp() && nodep->taskp()->castTask()
	    && nodep->castFuncRef()) nodep->v3error("Illegal call of a task as a function: "<<nodep->prettyName());
    }

    // VISITs
    virtual void visit(AstNetlist* nodep, AstNUser* vup) {
	// Recurse..., backward as must do packages before using packages
	nodep->iterateChildrenBackwards(*this);
    }
    virtual void visit(AstTypeTable* nodep, AstNUser*) {}
    virtual void visit(AstNodeModule* nodep, AstNUser*) {
	if (nodep->dead()) return;
	UINFO(8,"  "<<nodep<<endl);
	m_ds.init(m_curSymp);
	m_ds.m_dotSymp = m_curSymp = m_modSymp = m_statep->getNodeSym(nodep);  // Until overridden by a SCOPE
	m_cellp = NULL;
	m_modp = nodep;
	nodep->iterateChildren(*this);
	m_modp = NULL;
	m_ds.m_dotSymp = m_curSymp = m_modSymp = NULL;
    }
    virtual void visit(AstScope* nodep, AstNUser*) {
	UINFO(8,"   "<<nodep<<endl);
	m_ds.m_dotSymp = m_curSymp = m_statep->getScopeSym(nodep);
	nodep->iterateChildren(*this);
	m_ds.m_dotSymp = m_curSymp = NULL;
    }
    virtual void visit(AstCellInline* nodep, AstNUser*) {
	if (m_statep->forScopeCreation()) {
	    nodep->unlinkFrBack(); pushDeletep(nodep); nodep=NULL;
	}
    }
    virtual void visit(AstCell* nodep, AstNUser*) {
	// Cell: Resolve its filename.  If necessary, parse it.
	m_cellp = nodep;
	AstNode::user5ClearTree();
	if (!nodep->modp()) {
	    nodep->v3fatalSrc("Cell has unlinked module"); // V3LinkCell should have errored out
	}
	else {
	    if (nodep->modp()->castNotFoundModule()) {
		// Prevent warnings about missing pin connects
		if (nodep->pinsp()) nodep->pinsp()->unlinkFrBackWithNext()->deleteTree();
		if (nodep->paramsp()) nodep->paramsp()->unlinkFrBackWithNext()->deleteTree();
	    }
	    // Need to pass the module info to this cell, so we can link up the pin names
	    // However can't use m_curSymp as pin connections need to use the instantiator's symbols
	    else {
		m_pinSymp = m_statep->getNodeSym(nodep->modp());
		UINFO(4,"(Backto) Link Cell: "<<nodep<<endl);
		//if (debug()) { nodep->dumpTree(cout,"linkcell:"); }
		//if (debug()) { nodep->modp()->dumpTree(cout,"linkcemd:"); }
		nodep->iterateChildren(*this);
		m_pinSymp = NULL;
	    }
	}
	m_cellp = NULL;
	// Parent module inherits child's publicity
	// This is done bottom up in the LinkBotupVisitor stage
    }
    virtual void visit(AstPin* nodep, AstNUser*) {
	// Pin: Link to submodule's port
	if (!nodep->modVarp()) {
	    if (!m_pinSymp) nodep->v3fatalSrc("Pin not under cell?\n");
	    VSymEnt* foundp = m_pinSymp->findIdFlat(nodep->name());
	    AstVar* refp = foundp->nodep()->castVar();
	    if (!refp) {
		if (nodep->name() == "__paramNumber1" && m_cellp->modp()->castPrimitive()) {
		    // Primitive parameter is really a delay we can just ignore
		    nodep->unlinkFrBack()->deleteTree(); nodep=NULL;
		    return;
		}
		nodep->v3error("Pin not found: "<<nodep->prettyName());
	    } else if (!refp->isIO() && !refp->isParam()) {
		nodep->v3error("Pin is not an in/out/inout/param: "<<nodep->prettyName());
	    } else {
		nodep->modVarp(refp);
		if (refp->user5p() && refp->user5p()->castNode()!=nodep) {
		    nodep->v3error("Duplicate pin connection: "<<nodep->prettyName()<<endl
				   <<refp->user5p()->castNode()->warnMore()
				   <<"... Location of original pin connection");
		} else {
		    refp->user5p(nodep);
		}
	    }
	    nodep->iterateChildren(*this);
	}
	// Early return() above when deleted
    }
    virtual void visit(AstDot* nodep, AstNUser*) {
	if (nodep->user3SetOnce()) return;
	UINFO(8,"     "<<nodep<<endl);
	DotStates lastStates = m_ds;
	bool start = nodep->start();  // Save, as nodep may go NULL
	{
	    if (start) {  // Starting dot sequence
		if (debug()>=9) nodep->dumpTree("-dot-in: ");
		m_ds.init(m_curSymp);  // Start from current point
	    }
	    m_ds.m_dotp = nodep;  // Always, not just at start
	    m_ds.m_dotPos = DP_SCOPE;
	    // m_ds.m_dotText communicates the cell prefix between stages
	    nodep->lhsp()->iterateAndNext(*this);
	    if (!m_ds.m_dotErr) {  // Once something wrong, give up
		if (start && m_ds.m_dotPos==DP_SCOPE) m_ds.m_dotPos = DP_VAR_ETC;  // Top dot RHS is final RHS, else it's a DOT(DOT(x,*here*),real-rhs) which we consider a RHS
		nodep->rhsp()->iterateAndNext(*this);
	    }
	    if (start) {
		AstNode* newp;
		if (m_ds.m_dotErr) {
		    newp = new AstConst(nodep->fileline(),AstConst::LogicFalse());
		} else {
		    // RHS is what we're left with
		    newp = nodep->rhsp()->unlinkFrBack();
		}
		if (debug()>=9) newp->dumpTree("-dot-out: ");
		nodep->replaceWith(newp);
		pushDeletep(nodep); nodep=NULL;
	    } else {  // Dot midpoint
		AstNode* newp = nodep->rhsp()->unlinkFrBack();
		nodep->replaceWith(newp);
		pushDeletep(nodep); nodep=NULL;
	    }
	}
	if (start) {
	    m_ds = lastStates;
	} else {
	    m_ds.m_dotp = lastStates.m_dotp;
	}
    }
    virtual void visit(AstParseRef* nodep, AstNUser*) {
	if (nodep->user3SetOnce()) return;
	UINFO(9,"   linkPARSEREF se"<<(void*)m_ds.m_dotSymp<<"  pos="<<m_ds.m_dotPos<<"  txt="<<m_ds.m_dotText<<"  n="<<nodep<<endl);
	// m_curSymp is symbol table of outer expression
	// m_ds.m_dotSymp is symbol table relative to "."'s above now
	if (!m_ds.m_dotSymp) nodep->v3fatalSrc("NULL lookup symbol table");
	if (!m_statep->forPrimary()) nodep->v3fatalSrc("ParseRefs should no longer exist");
	DotStates lastStates = m_ds;
	bool start = nodep->start();  // Save, as nodep may go NULL
	if (start) {
	    m_ds.init(m_curSymp);
	}
	if (m_ds.m_dotPos == DP_MEMBER) {
	    // Found a Var, everything following is membership.  {scope}.{var}.HERE {member}
	    AstNode* varEtcp = m_ds.m_dotp->lhsp()->unlinkFrBack();
	    AstNode* newp = new AstMemberSel(nodep->fileline(), varEtcp, VFlagChildDType(), nodep->name());
	    nodep->replaceWith(newp);
	    pushDeletep(nodep); nodep=NULL;
	}
	else {
	    //
	    string expectWhat;
	    bool allowScope = false;
	    bool allowVar = false;
	    bool onlyVar = false;
	    if (nodep->expect() == AstParseRefExp::PX_PREDOT) {
		// {a}.{b}, where {a} maybe a module name
		// or variable, where dotting into structure member
		expectWhat = "scope/variable";
		allowScope = true;
		allowVar = true;
	    } else if (nodep->expect() == AstParseRefExp::PX_VAR_ANY) {
		expectWhat = "variable";
		onlyVar = true;
		allowVar = true;
	    } else if (nodep->expect() == AstParseRefExp::PX_FTASK) {
		expectWhat = "task/function";
	    } else {
		nodep->v3fatalSrc("Unhandled AstParseRefExp");
	    }
	    // Lookup
	    VSymEnt* foundp;
	    string baddot;
	    VSymEnt* okSymp = NULL;
	    if (allowScope) {
		foundp = m_statep->findDotted(m_ds.m_dotSymp, nodep->name(), baddot, okSymp); // Maybe NULL
	    } else {
		foundp = m_ds.m_dotSymp->findIdFallback(nodep->name());
	    }
	    if (foundp) UINFO(9,"     found=se"<<(void*)foundp<<"  n="<<foundp->nodep()<<endl);
	    // What fell out?
	    bool ok = false;
	    if (foundp->nodep()->castCell() || foundp->nodep()->castBegin()
		|| foundp->nodep()->castModule()) {  // if top
		if (allowScope) {
		    ok = true;
		    if (m_ds.m_dotText!="") m_ds.m_dotText += ".";
		    m_ds.m_dotText += nodep->name();
		    m_ds.m_dotSymp = foundp;
		    m_ds.m_dotPos = DP_SCOPE;
		    // Upper AstDot visitor will handle it from here
		}
	    }
	    else if (AstVar* varp = foundp->nodep()->castVar()) {
		if (allowVar) {
		    AstNodeVarRef* newp;
		    if (m_ds.m_dotText != "") {
			newp = new AstVarXRef(nodep->fileline(), nodep->name(), m_ds.m_dotText, false);  // lvalue'ness computed later
			newp->varp(varp);
			m_ds.m_dotText = "";
		    } else {
			newp = new AstVarRef(nodep->fileline(), nodep->name(), false);  // lvalue'ness computed later
			newp->varp(varp);
			newp->packagep(foundp->packagep());
		    }
		    nodep->replaceWith(newp); pushDeletep(nodep); nodep = NULL;
		    m_ds.m_dotPos = DP_MEMBER;
		    ok = true;
		}
	    }
	    else if (AstEnumItem* valuep = foundp->nodep()->castEnumItem()) {
		if (allowVar) {
		    AstNode* newp = new AstEnumItemRef(nodep->fileline(), valuep, foundp->packagep());
		    nodep->replaceWith(newp); pushDeletep(nodep); nodep = NULL;
		    ok = true;
		    m_ds.m_dotText = "";
		}
	    }
	    else if (AstNodeFTask* ftaskp = foundp->nodep()->castNodeFTask()) {
		if (nodep->expect() == AstParseRefExp::PX_FTASK) {
		    AstNodeFTaskRef* refp = nodep->ftaskrefp()->castNodeFTaskRef();
		    if (!refp) nodep->v3fatalSrc("Parseref indicates FTASKref but none found");
		    refp->name(nodep->name());
		    refp->dotted(m_ds.m_dotText);  // Maybe ""
		    refp->taskp(ftaskp);
		    refp->packagep(foundp->packagep());  // Generally set by parse, but might be an import
		    taskFuncSwapCheck(refp);
		    refp->unlinkFrBack();
		    nodep->replaceWith(refp); pushDeletep(nodep); nodep = NULL;
		    ok = true;
		}
	    }
	    //
	    if (!ok) {
		bool checkImplicit = (onlyVar && m_ds.m_dotText=="");
		bool err = !(checkImplicit && m_statep->implicitOk(m_modp, nodep->name()));
		if (err) {
		    m_statep->preErrorDump();
		    if (foundp) {
			nodep->v3error("Found definition of '"<<m_ds.m_dotText<<(m_ds.m_dotText==""?"":".")<<nodep->prettyName()
				       <<"'"<<" as a "<<foundp->nodep()->typeName()
				       <<" but expected a "<<expectWhat);
		    } else if (m_ds.m_dotText=="") {
			UINFO(7,"   ErrParseRef curSymp=se"<<(void*)m_curSymp<<" dotSymp=se"<<(void*)m_ds.m_dotSymp<<endl);
			nodep->v3error("Can't find definition of "<<expectWhat
				       <<": "<<nodep->prettyName());
		    } else {
			nodep->v3error("Can't find definition of '"<<(baddot!=""?baddot:nodep->prettyName())<<"' in dotted "
				       <<expectWhat<<": "<<m_ds.m_dotText+"."+nodep->prettyName());
			okSymp->cellErrorScopes(nodep, AstNode::prettyName(m_ds.m_dotText));
		    }
		    m_ds.m_dotErr = true;
		}
		if (checkImplicit) {  // Else if a scope is allowed, making a signal won't help error cascade
		    // Create if implicit, and also if error (so only complain once)
		    AstVarRef* newp = new AstVarRef(nodep->fileline(), nodep->name(), false);
		    nodep->replaceWith(newp);
		    pushDeletep(nodep); nodep = NULL;
		    createImplicitVar (m_curSymp, newp, m_modp, m_modSymp, err);
		}
	    }
	}
	if (start) {
	    m_ds = lastStates;
	}
    }
    virtual void visit(AstVarRef* nodep, AstNUser*) {
	// VarRef: Resolve its reference
	// ParseRefs are used the first pass (forPrimary) so we shouldn't get can't find
	// errors here now that we have a VarRef.
	nodep->iterateChildren(*this);
	if (!nodep->varp()) {
	    UINFO(9," linkVarRef se"<<(void*)m_curSymp<<"  n="<<nodep<<endl);
	    if (!m_curSymp) nodep->v3fatalSrc("NULL lookup symbol table");
	    VSymEnt* foundp = m_curSymp->findIdFallback(nodep->name());
	    if (AstVar* varp = foundp->nodep()->castVar()) {
		nodep->varp(varp);
		nodep->packagep(foundp->packagep());  // Generally set by parse, but might be an import
	    }
	    if (!nodep->varp()) {
		m_statep->preErrorDump();
		nodep->v3error("Can't find definition of signal, again: "<<nodep->prettyName());
	    }
	}
    }
    virtual void visit(AstVarXRef* nodep, AstNUser*) {
	// VarRef: Resolve its reference
	// We always link even if varp() is set, because the module we choose may change
	// due to creating new modules, flattening, etc.
	if (nodep->user3SetOnce()) return;
	UINFO(8,"     "<<nodep<<endl);
	if (!m_modSymp) {
	    UINFO(9,"Dead module for "<<nodep<<endl);
	    nodep->varp(NULL);  // Module that is not in hierarchy.  We'll be dead code eliminating it later.
	} else {
	    string baddot;
	    VSymEnt* okSymp;
	    VSymEnt* dotSymp = m_curSymp;  // Start search at current scope
	    if (nodep->inlinedDots()!="") {  // Correct for current scope
		dotSymp = m_modSymp; // Dotted lookup is always relative to module, as maybe variable name lower down with same scope name we want to ignore (t_math_divw)
		string inl = AstNode::dedotName(nodep->inlinedDots());
		dotSymp = m_statep->findDotted(dotSymp, inl, baddot, okSymp);
		if (!dotSymp) {
		    m_statep->preErrorDump();
		    nodep->v3fatalSrc("Couldn't resolve inlined scope '"<<baddot<<"' in: "<<nodep->inlinedDots());
		}
	    }
	    dotSymp = m_statep->findDotted(dotSymp, nodep->dotted(), baddot, okSymp); // Maybe NULL
	    if (!m_statep->forScopeCreation()) {
		VSymEnt* foundp = m_statep->findSymPrefixed(dotSymp, nodep->name(), baddot);
		AstVar* varp = foundp->nodep()->castVar();  // maybe NULL
		nodep->varp(varp);
		UINFO(7,"         Resolved "<<nodep<<endl);  // Also prints varp
		if (!nodep->varp()) {
		    m_statep->preErrorDump();
		    nodep->v3error("Can't find definition of '"<<baddot<<"' in dotted signal: "<<nodep->dotted()+"."+nodep->prettyName());
		    okSymp->cellErrorScopes(nodep);
		}
	    } else {
		string baddot;
		VSymEnt* foundp = m_statep->findSymPrefixed(dotSymp, nodep->name(), baddot);
		AstVarScope* vscp = foundp->nodep()->castVarScope();  // maybe NULL
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
    virtual void visit(AstVar* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
	if (m_statep->forPrimary() && nodep->isIO() && !m_ftaskp && !nodep->user4()) {
	    nodep->v3error("Input/output/inout does not appear in port list: "<<nodep->prettyName());
	}
    }
    virtual void visit(AstNodeFTaskRef* nodep, AstNUser*) {
	if (nodep->user3SetOnce()) return;
	UINFO(8,"     "<<nodep<<endl);
	if (nodep->packagep() && nodep->taskp()) {
	    // References into packages don't care about cell hierarchy.
	} else if (!m_modSymp) {
	    UINFO(9,"Dead module for "<<nodep<<endl);
	    nodep->taskp(NULL);  // Module that is not in hierarchy.  We'll be dead code eliminating it later.
	} else if (nodep->dotted()=="" && nodep->taskp()) {
	    // Earlier should have setup the links
	    // Might be under a BEGIN we're not processing, so don't relink it
	} else {
	    string baddot;
	    VSymEnt* okSymp = NULL;
	    VSymEnt* dotSymp = m_curSymp;  // Start search at module, as a variable of same name under a subtask isn't a relevant hit
	    //				   // however a function under a begin/end is.  So we want begins, but not the function
	    if (nodep->packagep()) {	// Look only in specified package
		dotSymp = m_statep->getNodeSym(nodep->packagep());
	    } else {
		if (nodep->inlinedDots()!="") {  // Correct for current scope
		    dotSymp = m_modSymp; // Dotted lookup is always relative to module, as maybe variable name lower down with same scope name we want to ignore (t_math_divw)
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
	    }
	    VSymEnt* foundp = NULL;
	    AstNodeFTask* taskp = NULL;
	    foundp = m_statep->findSymPrefixed(dotSymp, nodep->name(), baddot);
	    taskp = foundp->nodep()->castNodeFTask(); // Maybe NULL
	    if (taskp) {
		nodep->taskp(taskp);
		nodep->packagep(foundp->packagep());
		UINFO(7,"         Resolved "<<nodep<<endl);  // Also prints taskp
	    } else {
		// Note ParseRef has similar error handling/message output
		m_statep->preErrorDump();
		UINFO(7,"   ErrFtask curSymp=se"<<(void*)m_curSymp<<" dotSymp=se"<<(void*)dotSymp<<endl);
		if (nodep->dotted() == "") {
		    nodep->v3error("Can't find definition of task/function: "<<nodep->prettyName());
		} else {
		    nodep->v3error("Can't find definition of '"<<baddot<<"' in dotted task/function: "<<nodep->dotted()+"."+nodep->prettyName());
		    okSymp->cellErrorScopes(nodep);
		}
	    }
	    taskFuncSwapCheck(nodep);
	}
	nodep->iterateChildren(*this);
    }
    virtual void visit(AstSelBit* nodep, AstNUser*) {
	if (nodep->user3SetOnce()) return;
	nodep->lhsp()->iterateAndNext(*this);
	if (m_ds.m_dotPos == DP_SCOPE) { // Already under dot, so this is {modulepart} DOT {modulepart}
	    if (AstConst* constp = nodep->rhsp()->castConst()) {
		string index = AstNode::encodeNumber(constp->toSInt());
		m_ds.m_dotText += "__BRA__"+index+"__KET__";
	    } else {
		nodep->v3error("Unsupported: Non-constant inside []'s in the cell part of a dotted reference");
	    }
	    // And pass up m_ds.m_dotText
	}
	nodep->fromp()->iterateAndNext(*this);
	nodep->bitp()->iterateAndNext(*this);
	nodep->attrp()->iterateAndNext(*this);
    }
    virtual void visit(AstBegin* nodep, AstNUser*) {
	UINFO(5,"   "<<nodep<<endl);
	VSymEnt* oldCurSymp = m_curSymp;
	{
	    m_ds.m_dotSymp = m_curSymp = m_statep->getNodeSym(nodep);
	    UINFO(5,"   cur=se"<<(void*)m_curSymp<<endl);
	    nodep->iterateChildren(*this);
	}
	m_ds.m_dotSymp = m_curSymp = oldCurSymp;
	UINFO(5,"   cur=se"<<(void*)m_curSymp<<endl);
    }
    virtual void visit(AstNodeFTask* nodep, AstNUser*) {
	UINFO(5,"   "<<nodep<<endl);
	VSymEnt* oldCurSymp = m_curSymp;
	{
	    m_ftaskp = nodep;
	    m_ds.m_dotSymp = m_curSymp = m_statep->getNodeSym(nodep);
	    nodep->iterateChildren(*this);
	}
	m_ds.m_dotSymp = m_curSymp = oldCurSymp;
	m_ftaskp = NULL;
    }
    virtual void visit(AstRefDType* nodep, AstNUser*) {
	// Resolve its reference
	if (nodep->user3SetOnce()) return;
	if (!nodep->defp()) {
	    VSymEnt* foundp;
	    if (nodep->packagep()) {
		foundp = m_statep->getNodeSym(nodep->packagep())->findIdFlat(nodep->name());
	    } else {
		foundp = m_curSymp->findIdFallback(nodep->name());
	    }
	    if (AstTypedef* defp = foundp->nodep()->castTypedef()) {
		nodep->refDTypep(defp->subDTypep());
		nodep->packagep(foundp->packagep());
	    } else {
		nodep->v3error("Can't find typedef: "<<nodep->prettyName());
	    }
	}
	nodep->iterateChildren(*this);
    }
    virtual void visit(AstDpiExport* nodep, AstNUser*) {
	// AstDpiExport: Make sure the function referenced exists, then dump it
	nodep->iterateChildren(*this);
	VSymEnt* foundp = m_curSymp->findIdFallback(nodep->name());
	AstNodeFTask* taskp = foundp->nodep()->castNodeFTask();
	if (!taskp) { nodep->v3error("Can't find definition of exported task/function: "<<nodep->prettyName()); }
	else if (taskp->dpiExport()) {
	    nodep->v3error("Function was already DPI Exported, duplicate not allowed: "<<nodep->prettyName());
	} else {
	    taskp->dpiExport(true);
	    if (nodep->cname()!="") taskp->cname(nodep->cname());
	}
	nodep->unlinkFrBack()->deleteTree();
    }
    virtual void visit(AstPackageImport* nodep, AstNUser*) {
	// No longer needed
	nodep->unlinkFrBack()->deleteTree(); nodep=NULL;
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
	m_curSymp = NULL;
	m_pinSymp = NULL;
	m_cellp = NULL;
	m_modp = NULL;
	m_ftaskp = NULL;
	//
	rootp->accept(*this);
    }
    virtual ~LinkDotResolveVisitor() {}
};

//######################################################################
// Link class functions

int V3LinkDot::debug() { return LinkDotState::debug(); }

void V3LinkDot::linkDotGuts(AstNetlist* rootp, VLinkDotStep step) {
    if (LinkDotState::debug()>=5 || v3Global.opt.dumpTree()>=9) v3Global.rootp()->dumpTreeFile(v3Global.debugFilename("prelinkdot.tree"));
    LinkDotState state (rootp, step);
    LinkDotFindVisitor visitor(rootp,&state);
    if (LinkDotState::debug()>=5 || v3Global.opt.dumpTree()>=9) v3Global.rootp()->dumpTreeFile(v3Global.debugFilename("prelinkdot-find.tree"));
    if (step == LDS_PRIMARY || step == LDS_PARAMED) {
	// Initial link stage, resolve parameters
	LinkDotParamVisitor visitors(rootp,&state);
	if (LinkDotState::debug()>=5 || v3Global.opt.dumpTree()>=9) v3Global.rootp()->dumpTreeFile(v3Global.debugFilename("prelinkdot-param.tree"));
    }
    else if (step == LDS_SCOPED) {
	// Well after the initial link when we're ready to operate on the flat design,
	// process AstScope's.  This needs to be separate pass after whole hierarchy graph created.
	LinkDotScopeVisitor visitors(rootp,&state);
	if (LinkDotState::debug()>=5 || v3Global.opt.dumpTree()>=9) v3Global.rootp()->dumpTreeFile(v3Global.debugFilename("prelinkdot-scoped.tree"));
    }
    state.dump();
    LinkDotResolveVisitor visitorb(rootp,&state);
}
