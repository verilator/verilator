//*************************************************************************
// DESCRIPTION: Verilator: Resolve module/signal name references
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

class LinkDotGraph : public V3Graph {
public:
    LinkDotGraph() {}
    virtual ~LinkDotGraph() {}
    virtual string dotRankDir() { return "LR"; }
};

class LinkDotBaseVertex : public V3GraphVertex {
    typedef std::map<string,LinkDotBaseVertex*> NameVtxMap;
    // A point in the hierarchy, either inlined or real
    string	m_symPrefix;	// String to prefix symbols with
    NameVtxMap	m_nameToVtxMap;	// Lookup of name -> to vertexes
public:
    LinkDotBaseVertex(V3Graph* graphp, const string& symPrefix)
	: V3GraphVertex(graphp), m_symPrefix(symPrefix) {}
    virtual ~LinkDotBaseVertex() {}
    virtual string modName() const = 0;
    virtual string cellName() const = 0;
    virtual V3SymTable& syms() = 0;
    string symPrefix() const { return m_symPrefix; }
    void insertSubcellName(const string& name, LinkDotBaseVertex* toVertexp) {
	m_nameToVtxMap.insert(make_pair(name,toVertexp));
    }
    LinkDotBaseVertex* findSubcell(const string& name, const string& altname) {
	// Find a vertex under this one by name.
	// We could walk the edge top() list, but that would be O(n) for large lists of cells
	{
	    NameVtxMap::iterator iter = m_nameToVtxMap.find(name);
	    if (iter != m_nameToVtxMap.end()) return iter->second;
	}
	if (altname != "") {
	    NameVtxMap::iterator iter = m_nameToVtxMap.find(altname);
	    if (iter != m_nameToVtxMap.end()) return iter->second;
	}
	return NULL;
    }
    void errorScopes(AstNode* nodep) {
	if (!this) {  // Silence if we messed it up and aren't debugging
	    if (debug()) nodep->v3fatalSrc("Void pointer; perhaps used null vxp instead of okVxp?");
	    return;
	}
	{
	    string scopes;
	    for (NameVtxMap::iterator it = m_nameToVtxMap.begin(); it!=m_nameToVtxMap.end(); ++it) {
		if (scopes != "") scopes += ", ";
		scopes += AstNode::prettyName(it->second->cellName());
	    }
	    cerr<<V3Error::msgPrefix()<<"     Known scopes under '"<<cellName()<<"': "
		<<scopes<<endl;
	}
	if (debug()) {
	    for (NameVtxMap::iterator it = m_nameToVtxMap.begin(); it!=m_nameToVtxMap.end(); ++it) {
		UINFO(1,"\t\t      KnownScope: "<<it->second->name()<<endl);
	    }
	}
    }
};

class LinkDotCellVertex : public LinkDotBaseVertex {
    // A real point in the hierarchy, corresponding to a instantiated module
    AstNodeModule*	m_modp;		// Module
    AstCell*	m_cellp;	// Cell creating this vertex **NULL AT TOP**
    V3SymTable  m_syms;		// Symbol table of variable/task names for global lookup
public:
    LinkDotCellVertex(V3Graph* graphp, AstCell* nodep)
	: LinkDotBaseVertex(graphp, ""), m_modp(nodep->modp()), m_cellp(nodep) {}
    LinkDotCellVertex(V3Graph* graphp, AstNodeModule* nodep)
	: LinkDotBaseVertex(graphp, ""), m_modp(nodep), m_cellp(NULL) {}
    virtual ~LinkDotCellVertex() {}
    AstNodeModule* modp() const { return m_modp; }   // May be NULL
    AstCell* cellp() const { return m_cellp; }   // Is NULL at TOP
    virtual V3SymTable& syms() { return m_syms; }
    // We need to use origName as parameters may have renamed the modname
    virtual string modName() const { return (modp() ? modp()->origName() : "*NULL*"); }
    virtual string cellName() const { return (cellp() ? cellp()->origName() : "*NULL*"); }
    virtual string name() const { return (string)("C:")+cellName()+" M:"+modName(); }
};

class LinkDotInlineVertex : public LinkDotBaseVertex {
    // A fake point in the hierarchy, corresponding to a inlined module
    // This refrences to another vertex, and eventually resolves to a module with a prefix
    string	m_basename;		// Name with dotteds stripped
    AstCellInline* m_cellInlinep; 	// Inlined cell
    LinkDotCellVertex* m_symVxp;	// Above cell so we can find real symbol table
    //					// (Could walk graph to find it, but that's much slower.)
public:
    LinkDotInlineVertex(V3Graph* graphp, AstCellInline* nodep, LinkDotCellVertex* symVxp,
			const string& basename)
	: LinkDotBaseVertex(graphp, nodep->name()+"__DOT__")
	, m_basename(basename), m_cellInlinep(nodep), m_symVxp(symVxp) {}
    virtual ~LinkDotInlineVertex() {}
    AstCellInline* cellInlinep() const { return m_cellInlinep; }
    // Search up through tree to find the real symbol table.
    virtual V3SymTable& syms() { return m_symVxp->syms(); }
    virtual string modName() const { return cellInlinep()->origModName(); }
    virtual string cellName() const { return m_basename; }
    virtual string name() const { return (string)("INL C:")+cellName()+" M:"+modName()+" P:"+symPrefix(); }
    virtual string dotColor() const { return "yellow"; }
};

class LinkDotBeginVertex : public LinkDotBaseVertex {
    // A fake point in the hierarchy, corresponding to a begin block
    // After we remove begins these will go away
    // Note we use the symbol table of the parent, as we want to find variables there
    // However, cells walk the graph, so cells will appear under the begin itself
    AstBegin*	m_nodep; 		// Relevant node
    LinkDotCellVertex* m_symVxp;	// Above cell so we can find real symbol table
    //					// (Could walk graph to find it, but that's much slower.)
public:
    LinkDotBeginVertex(V3Graph* graphp, AstBegin* nodep, LinkDotCellVertex* symVxp)
	: LinkDotBaseVertex(graphp, nodep->name()+"__DOT__")
	, m_nodep(nodep), m_symVxp(symVxp) {}
    virtual ~LinkDotBeginVertex() {}
    // Search up through tree to find the real symbol table.
    virtual V3SymTable& syms() { return m_symVxp->syms(); }
    virtual string modName() const { return m_nodep->name(); }
    virtual string cellName() const { return m_nodep->name(); }
    virtual string name() const { return (string)("BEG C:")+cellName(); }
    virtual string dotColor() const { return "blue"; }
};

//######################################################################
// LinkDot state, as a visitor of each AstNode

class LinkDotState {
private:
    // NODE STATE
    // Cleared on Netlist
    //  AstNodeModule::user1p()	-> LinkDotCellVertex*.  Last cell that uses this module
    //  AstVarScope::user2p()	-> AstVarScope*.  Base alias for this signal
    AstUser1InUse	m_inuser1;
    AstUser2InUse	m_inuser2;

    // TYPES
    typedef std::multimap<string,LinkDotCellVertex*> NameScopeMap;
    // MEMBERS
    LinkDotGraph	m_graph;		// Graph of hierarchy
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
    LinkDotState(bool forPrearray, bool forScopeCreation) {
	UINFO(4,__FUNCTION__<<": "<<endl);
	m_forPrearray = forPrearray;
	m_forScopeCreation = forScopeCreation;
	//VV*****  We reset all userp() on each netlist!!!
	AstNode::user1ClearTree();
	AstNode::user2ClearTree();
    }
    ~LinkDotState() {}

    // ACCESSORS
    bool forScopeCreation() const { return m_forScopeCreation; }

    // METHODS
    LinkDotCellVertex* insertTopCell(AstNodeModule* nodep, const string& scopename) {
	// Only called on the module at the very top of the hierarchy
	UINFO(9,"      INSERTcell "<<scopename<<" "<<nodep<<endl);
	LinkDotCellVertex* vxp = new LinkDotCellVertex(&m_graph, nodep);
	nodep->user1p(vxp);
	if (forScopeCreation()) m_nameScopeMap.insert(make_pair(scopename, vxp));
	return vxp;
    }
    LinkDotCellVertex* insertCell(LinkDotBaseVertex* abovep, LinkDotCellVertex* cellVxp,
				  AstCell* nodep, const string& scopename) {
	UINFO(9,"      INSERTcell "<<scopename<<" "<<nodep<<endl);
	LinkDotCellVertex* vxp = new LinkDotCellVertex(&m_graph, nodep);
	if (nodep->modp()) nodep->modp()->user1p(vxp);
	new V3GraphEdge(&m_graph, abovep, vxp, 1, false);
	abovep->insertSubcellName(nodep->origName(), vxp);
	if (abovep != cellVxp) {
	    // If it's foo_DOT_bar, we need to be able to find it under that too.
	    cellVxp->insertSubcellName(nodep->name(), vxp);
	}
	if (forScopeCreation()) m_nameScopeMap.insert(make_pair(scopename, vxp));
	return vxp;
    }
    LinkDotInlineVertex* insertInline(LinkDotBaseVertex* abovep, LinkDotCellVertex* cellVxp,
				      AstCellInline* nodep, const string& basename) {
	UINFO(9,"      INSERTcinl "<<nodep<<endl);
	LinkDotInlineVertex* vxp = new LinkDotInlineVertex(&m_graph, nodep, cellVxp, basename);
	new V3GraphEdge(&m_graph, abovep, vxp, 1, false);
	abovep->insertSubcellName(basename, vxp);
	if (abovep != cellVxp) {
	    // If it's foo_DOT_bar, we need to be able to find it under that too.
	    cellVxp->insertSubcellName(nodep->name(), vxp);
	}
	return vxp;
    }
    LinkDotBeginVertex* insertBegin(LinkDotBaseVertex* abovep, LinkDotCellVertex* cellVxp,
				    AstBegin* nodep) {
	UINFO(9,"      INSERTbeg "<<nodep<<endl);
	LinkDotBeginVertex* vxp = new LinkDotBeginVertex(&m_graph, nodep, cellVxp);
	new V3GraphEdge(&m_graph, abovep, vxp, 1, false);
	abovep->insertSubcellName(nodep->name(), vxp);
	return vxp;
    }
    void insertSym(LinkDotCellVertex* abovep, const string& name, AstNode* nodep) {
	UINFO(9,"      INSERTsym "<<name<<" "<<nodep<<endl);
	abovep->syms().insert(name, nodep);
    }
    bool existsModScope(AstNodeModule* nodep) {
	return nodep->user1p()!=NULL;
    }
    LinkDotCellVertex* findModScope(AstNodeModule* nodep) {
	LinkDotCellVertex* vxp = (LinkDotCellVertex*)(nodep->user1p());
	if (!vxp) nodep->v3fatalSrc("Module never assigned a vertex");
	return vxp;
    }
    LinkDotCellVertex* findScope(AstScope* nodep) {
	NameScopeMap::iterator iter = m_nameScopeMap.find(nodep->name());
	if (iter == m_nameScopeMap.end()) {
	    nodep->v3fatalSrc("Scope never assigned a vertex");
	}
	return iter->second;
    }
    void dump() {
	if (debug()>=6) m_graph.dumpDotFilePrefixed("linkdot");
    }
private:
    LinkDotBaseVertex* parentOfCell(LinkDotBaseVertex* lowerVxp) {
	for (V3GraphEdge* edgep = lowerVxp->inBeginp(); edgep; edgep=edgep->inNextp()) {
	    LinkDotBaseVertex* fromVxp = dynamic_cast<LinkDotBaseVertex*>(edgep->fromp());
	    return fromVxp;
	}
	return NULL;
    }
public:
    LinkDotBaseVertex* findDotted(LinkDotBaseVertex* cellVxp, const string& dotname,
				  string& baddot, LinkDotBaseVertex*& okVxp) {
	// Given a dotted hierarchy name, return where in scope it is
	// Note when dotname=="" we just fall through and return cellVxp
	UINFO(8,"    dottedFind "<<dotname<<endl);
	bool firstId = true;
	string leftname = dotname;
	okVxp = cellVxp;  // So can list bad scopes
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
	    okVxp = cellVxp;
	    string altIdent = "";
	    if (m_forPrearray) {
		// Cell foo__[array] before we've expanded arrays is just foo.
		if ((pos = ident.find("__BRA__")) != string::npos) {
		    altIdent = ident.substr(0,pos);
		}
	    }
	    UINFO(8,"         id "<<ident<<" left "<<leftname<<" at "<<cellVxp<<endl);
	    // Spec says; Look at exiting module (cellnames then modname),
	    // then look up (inst name or modname)
	    if (firstId) {
		// Check this module - subcellnames
		if (LinkDotBaseVertex* findVxp = cellVxp->findSubcell(ident, altIdent)) {
		    cellVxp = findVxp;
		}
		// Check this module - cur modname
		else if (cellVxp->modName() == ident) {}
		// Check this module - cur cellname
		else if (cellVxp->cellName() == ident) {}
		else if (cellVxp->cellName() == altIdent) {}
		// Move up and check cellname + modname
		else {
		    while (cellVxp) {
			cellVxp = parentOfCell(cellVxp);
			if (cellVxp) {
			    UINFO(9,"\t\tUp to "<<cellVxp<<endl);
			    if (cellVxp->modName() == ident
				|| cellVxp->cellName() == ident
				|| cellVxp->cellName() == altIdent) {
				break;
			    }
			    else if (LinkDotBaseVertex* findVxp = cellVxp->findSubcell(ident, altIdent)) {
				cellVxp = findVxp;
				break;
			    }
			}
		    }
		    if (!cellVxp) return NULL;  // Not found
		}
	    } else { // Searching for middle submodule, must be a cell name
		if (LinkDotBaseVertex* findVxp = cellVxp->findSubcell(ident, altIdent)) {
		    cellVxp = findVxp;
		} else {
		    return NULL;  // Not found
		}
	    }
	    firstId = false;
	}
	return cellVxp;
    }

    AstNode* findSym(LinkDotBaseVertex* cellVxp, const string& dotname, string& baddot) {
	// Find symbol in given point in hierarchy
	// For simplicity cellVxp may be passed NULL result from findDotted
	if (!cellVxp) return NULL;
	UINFO(8,"\t\tfindSym "<<dotname
	      <<((cellVxp->symPrefix()=="") ? "" : " as ")
	      <<((cellVxp->symPrefix()=="") ? "" : cellVxp->symPrefix()+dotname)
	      <<"  at  "<<cellVxp
	      <<endl);
	AstNode* nodep = cellVxp->syms().findIdFlat(cellVxp->symPrefix() + dotname);  // Might be NULL
	if (!nodep) baddot = dotname;
	return nodep;
    }
};

//======================================================================

class LinkDotFindVisitor : public AstNVisitor {
private:
    // STATE
    LinkDotState*	m_statep;	// State to pass between visitors, including symbol table
    LinkDotCellVertex*	m_cellVxp;	// Vertex for current module
    LinkDotBaseVertex*	m_inlineVxp;	// Vertex for current module, possibly a fake inlined one
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
	    m_cellVxp = m_statep->insertTopCell(topmodp, m_scope);
	    m_inlineVxp = m_cellVxp;
	    {
		topmodp->accept(*this);
	    }
	    m_scope = "";
	    m_cellVxp = NULL;
	    m_inlineVxp = m_cellVxp;
	}
    }
    virtual void visit(AstNodeModule* nodep, AstNUser*) {
	// Called on top module from Netlist, other modules from the cell creating them,
	// and packages
	UINFO(8,"   "<<nodep<<endl);
	if (!m_cellVxp) {
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
	// Process XREFs inside pins
	nodep->iterateChildren(*this);
	// Recurse in, preserving state
	string oldscope = m_scope;
	AstBegin* oldbeginp = m_beginp;
	LinkDotCellVertex* oldVxp = m_cellVxp;
	LinkDotBaseVertex* oldInlineVxp = m_inlineVxp;
	// Where do we add it?
	LinkDotBaseVertex* aboveVxp = m_inlineVxp;
	string origname = AstNode::dedotName(nodep->name());
	string::size_type pos;
	if ((pos = origname.rfind(".")) != string::npos) {
	    // Flattened, find what CellInline it should live under
	    string scope = origname.substr(0,pos);
	    string baddot;
	    LinkDotBaseVertex* okVxp;
	    aboveVxp = m_statep->findDotted(aboveVxp, scope, baddot, okVxp);
	    if (!aboveVxp) nodep->v3fatalSrc("Can't find cell insertion point at '"<<baddot<<"' in: "<<nodep->prettyName());
	}
	{
	    m_scope = m_scope+"."+nodep->name();
	    m_cellVxp = m_statep->insertCell(aboveVxp, m_cellVxp, nodep, m_scope);
	    m_inlineVxp = m_cellVxp;
	    m_beginp = NULL;
	    if (nodep->modp()) nodep->modp()->accept(*this);
	}
	m_scope = oldscope;
	m_beginp = oldbeginp;
	m_cellVxp = oldVxp;
	m_inlineVxp = oldInlineVxp;
    }
    virtual void visit(AstCellInline* nodep, AstNUser*) {
	UINFO(5,"   CELLINLINE under "<<m_scope<<" is "<<nodep<<endl);
	LinkDotBaseVertex* aboveVxp = m_inlineVxp;
	// If baz__DOT__foo__DOT__bar, we need to find baz__DOT__foo and add bar to it.
	string dottedname = nodep->name();
	string::size_type pos;
	if ((pos=dottedname.rfind("__DOT__")) != string::npos) {
	    string dotted = dottedname.substr(0, pos);
	    string ident  = dottedname.substr(pos+strlen("__DOT__"));
	    string baddot;
	    LinkDotBaseVertex* okVxp;
	    aboveVxp = m_statep->findDotted(aboveVxp, dotted, baddot, okVxp);
	    if (!aboveVxp) nodep->v3fatalSrc("Can't find cellinline insertion point at '"<<baddot<<"' in: "<<nodep->prettyName());
	    m_statep->insertInline(aboveVxp, m_cellVxp, nodep, ident);
	} else {  // No __DOT__, just directly underneath
	    m_statep->insertInline(aboveVxp, m_cellVxp, nodep, nodep->name());
	}
    }
    virtual void visit(AstBegin* nodep, AstNUser*) {
	UINFO(5,"   "<<nodep<<endl);
	AstBegin* oldbegin = m_beginp;
	LinkDotBaseVertex* oldVxp = m_inlineVxp;
	{
	    m_beginp = nodep;
	    // We don't pickup variables (as not supported yet), but do need to find cells
	    m_inlineVxp = m_statep->insertBegin(m_inlineVxp, m_cellVxp, nodep);
	    nodep->stmtsp()->iterateAndNext(*this);
	}
	m_inlineVxp = oldVxp;
	m_beginp = oldbegin;
	//
	nodep->flatsp()->iterateAndNext(*this);
    }
    virtual void visit(AstVar* nodep, AstNUser*) {
	if (!m_statep->forScopeCreation()
	    && !m_beginp	// For now, we don't support xrefs into begin blocks
	    && !nodep->isFuncLocal()) {
	    m_statep->insertSym(m_cellVxp, nodep->name(), nodep);
	} else {
	    UINFO(9,"       Not allowing dot refs to: "<<nodep<<endl);
	}
    }
    virtual void visit(AstNodeFTask* nodep, AstNUser*) {
	if (!m_beginp) {	// For now, we don't support xrefs into functions inside begin blocks
	    m_statep->insertSym(m_cellVxp, nodep->name(), nodep);
	}
	// No recursion, we don't want to pick up variables
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
	m_cellVxp = NULL;
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
    LinkDotCellVertex*	m_cellVxp;	// Vertex for current module

    int debug() { return LinkDotState::debug(); }

    // VISITs
    virtual void visit(AstScope* nodep, AstNUser*) {
	UINFO(8,"  SCOPE "<<nodep<<endl);
	if (!m_statep->forScopeCreation()) v3fatalSrc("Scopes should only exist right after V3Scope");
	// Using the CELL names, we created all hierarchy.  We now need to match this Scope
	// up with the hierarchy created by the CELL names.
	m_cellVxp = m_statep->findScope(nodep);
	nodep->iterateChildren(*this);
	m_cellVxp = NULL;
    }
    virtual void visit(AstVarScope* nodep, AstNUser*) {
	if (!nodep->varp()->isFuncLocal()) {
	    m_statep->insertSym(m_cellVxp, nodep->varp()->name(), nodep);
	}
    }
    virtual void visit(AstNodeFTask* nodep, AstNUser*) {
	m_statep->insertSym(m_cellVxp, nodep->name(), nodep);
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
	m_cellVxp = NULL;
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
    LinkDotCellVertex*	m_cellVxp;	// Vertex for current module

    int debug() { return LinkDotState::debug(); }

    // METHODS

    // VISITs
    virtual void visit(AstNodeModule* nodep, AstNUser*) {
	UINFO(8,"  "<<nodep<<endl);
	if (!m_statep->existsModScope(nodep)) {
	    UINFO(5,"Dead module for "<<nodep<<endl);
	    m_cellVxp = NULL;
	} else {
	    m_cellVxp = m_statep->findModScope(nodep);
	}
	nodep->iterateChildren(*this);
	m_cellVxp = NULL;
    }
    virtual void visit(AstScope* nodep, AstNUser*) {
	UINFO(8,"   "<<nodep<<endl);
	m_cellVxp = m_statep->findScope(nodep);
	nodep->iterateChildren(*this);
	m_cellVxp = NULL;
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
	if (!m_cellVxp) {
	    UINFO(9,"Dead module for "<<nodep<<endl);
	    nodep->varp(NULL);  // Module that is not in hierarchy.  We'll be dead code eliminating it later.
	} else {
	    string baddot;
	    LinkDotBaseVertex* okVxp;
	    LinkDotBaseVertex* dotVxp = m_cellVxp;  // Start search at current scope
	    if (nodep->inlinedDots()!="") {  // Correct for current scope
		string inl = AstNode::dedotName(nodep->inlinedDots());
		dotVxp = m_statep->findDotted(dotVxp, inl, baddot, okVxp);
		if (!dotVxp) nodep->v3fatalSrc("Couldn't resolve inlined scope '"<<baddot<<"' in: "<<nodep->inlinedDots());
	    }
	    dotVxp = m_statep->findDotted(dotVxp, nodep->dotted(), baddot, okVxp); // Maybe NULL
	    if (!m_statep->forScopeCreation()) {
		AstVar* varp = (m_statep->findSym(dotVxp, nodep->name(), baddot)
				->castVar());  // maybe NULL
		nodep->varp(varp);
		UINFO(7,"         Resolved "<<nodep<<endl);  // Also prints varp
		if (!nodep->varp()) {
		    nodep->v3error("Can't find definition of '"<<baddot<<"' in dotted signal: "<<nodep->dotted()+"."+nodep->prettyName());
		    okVxp->errorScopes(nodep);
		}
	    } else {
		string baddot;
		AstVarScope* vscp = (m_statep->findSym(dotVxp, nodep->name(), baddot)
				     ->castVarScope());  // maybe NULL
		if (!vscp) {
		    nodep->v3error("Can't find varpin scope of '"<<baddot<<"' in dotted signal: "<<nodep->dotted()+"."+nodep->prettyName());
		    okVxp->errorScopes(nodep);
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
	} else if (!m_cellVxp) {
	    UINFO(9,"Dead module for "<<nodep<<endl);
	    nodep->taskp(NULL);  // Module that is not in hierarchy.  We'll be dead code eliminating it later.
	} else if (nodep->dotted()=="" && nodep->taskp()) {
	    // V3Link should have setup the links
	    // Might be under a BEGIN we're not processing, so don't relink it
	} else {
	    string baddot;
	    LinkDotBaseVertex* okVxp;
	    LinkDotBaseVertex* dotVxp = m_cellVxp;  // Start search at current scope
	    if (nodep->inlinedDots()!="") {  // Correct for current scope
		string inl = AstNode::dedotName(nodep->inlinedDots());
		UINFO(8,"\t\tInlined "<<inl<<endl);
		dotVxp = m_statep->findDotted(dotVxp, inl, baddot, okVxp);
		if (!dotVxp) {
		    okVxp->errorScopes(nodep);
		    nodep->v3fatalSrc("Couldn't resolve inlined scope '"<<baddot<<"' in: "<<nodep->inlinedDots());
		}
	    }
	    dotVxp = m_statep->findDotted(dotVxp, nodep->dotted(), baddot, okVxp); // Maybe NULL

	    AstNodeFTask* taskp = (m_statep->findSym(dotVxp, nodep->name(), baddot)
				   ->castNodeFTask()); // maybe NULL
	    nodep->taskp(taskp);
	    UINFO(7,"         Resolved "<<nodep<<endl);  // Also prints taskp
	    if (!nodep->taskp()) {
		nodep->v3error("Can't find definition of '"<<baddot<<"' in dotted task/function: "<<nodep->dotted()+"."+nodep->prettyName());
		okVxp->errorScopes(nodep);
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
	m_cellVxp = NULL;
	//
	rootp->accept(*this);
    }
    virtual ~LinkDotResolveVisitor() {}
};

//######################################################################
// Link class functions

void V3LinkDot::linkDotGuts(AstNetlist* rootp, bool prearray, bool scoped) {
    UINFO(2,__FUNCTION__<<": "<<endl);
    if (LinkDotState::debug()>=5) v3Global.rootp()->dumpTreeFile(v3Global.debugFilename("prelinkdot.tree"));
    LinkDotState state (prearray,scoped);
    LinkDotFindVisitor visitor(rootp,&state);
    if (scoped) {
	// Process AstScope's.  This needs to be separate pass after whole hierarchy graph created.
	LinkDotScopeVisitor visitors(rootp,&state);
    }
    state.dump();
    LinkDotResolveVisitor visitorb(rootp,&state);
}
