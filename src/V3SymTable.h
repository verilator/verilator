// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Symbol table
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

#ifndef _V3LINKSYMTABLE_H_
#define _V3LINKSYMTABLE_H_ 1

#include "config_build.h"
#include "verilatedos.h"
#include <cstdio>
#include <cstdarg>
#include <unistd.h>
#include <map>
#include <iomanip>
#include <memory>

#include "V3Global.h"
#include "V3Ast.h"
#include "V3File.h"

class VSymGraph;
class VSymEnt;

//######################################################################
// Symbol table

typedef set<VSymEnt*> VSymMap;

class VSymEnt {
    // Symbol table that can have a "superior" table for resolving upper references
private:
    // MEMBERS
    typedef std::multimap<string,VSymEnt*> IdNameMap;
    IdNameMap	m_idNameMap;	// Hash of variables by name
    AstNode*	m_nodep;	// Node that entry belongs to
    VSymEnt*	m_fallbackp;	// Table "above" this one in name scope, for fallback resolution
    VSymEnt*	m_parentp;	// Table that created this table, dot notation needed to resolve into it
    AstPackage*	m_packagep;	// Package node is in (for V3LinkDot, unused here)
    string	m_symPrefix;	// String to prefix symbols with (for V3LinkDot, unused here)
    bool	m_exported;	// Allow importing
    bool	m_imported;	// Was imported
#ifdef VL_DEBUG
    static int debug() {
	static int level = -1;
	if (VL_UNLIKELY(level < 0)) level = v3Global.opt.debugSrcLevel("V3LinkDot.cpp");
	return level;
    }
#else
    static inline int debug() { return 0; }  // NOT runtime, too hot of a function
#endif
public:
    void dumpIterate(ostream& os, VSymMap& doneSymsr, const string& indent, int numLevels, const string& searchName) {
	os<<indent<<"+ "<<left<<setw(30)<<(searchName==""?"\"\"":searchName)<<setw(0)<<right;
	os<<"  se"<<(void*)(this)<<setw(0);
	os<<"  fallb=se"<<(void*)(m_fallbackp);
	os<<"  n="<<nodep();
	os<<endl;
	if (doneSymsr.find(this) != doneSymsr.end()) {
	    os<<indent<<"| ^ duplicate, so no children printed\n";
	} else {
	    doneSymsr.insert(this);
	    for (IdNameMap::const_iterator it=m_idNameMap.begin(); it!=m_idNameMap.end(); ++it) {
		if (numLevels >= 1) {
		    it->second->dumpIterate(os, doneSymsr, indent+"| ", numLevels-1, it->first);
		}
	    }
	}
    }
    void dump(ostream& os, const string& indent="", int numLevels=1) {
	VSymMap doneSyms;
	dumpIterate(os, doneSyms, indent, numLevels, "TOP");
    }

    // METHODS
    VSymEnt(VSymGraph* graphp, const VSymEnt* symp);  // Below
    VSymEnt(VSymGraph* graphp, AstNode* nodep);  // Below
    ~VSymEnt() {
	// Change links so we coredump if used
#ifdef VL_DEBUG
	m_nodep = (AstNode*)1;
	m_fallbackp = (VSymEnt*)1;
	m_parentp = (VSymEnt*)1;
	m_packagep = (AstPackage*)1;
#endif
    }
#if defined(VL_DEBUG) && !defined(VL_LEAK_CHECKS)
    void operator delete(void* objp, size_t size) {} // For testing, leak so above destructor 1 assignments work
#endif
    void fallbackp(VSymEnt* entp) { m_fallbackp = entp; }
    void parentp(VSymEnt* entp) { m_parentp = entp; }
    VSymEnt* parentp() const { return m_parentp; }
    void packagep(AstPackage* entp) { m_packagep = entp; }
    AstPackage* packagep() const { return m_packagep; }
    AstNode* nodep() const { if (!this) return NULL; else return m_nodep; }  // null check so can call .findId(...)->nodep()
    string symPrefix() const { return m_symPrefix; }
    void symPrefix(const string& name) { m_symPrefix = name; }
    bool exported() const { return m_exported; }
    void exported(bool flag) { m_exported = flag; }
    bool imported() const { return m_imported; }
    void imported(bool flag) { m_imported = flag; }
    void insert(const string& name, VSymEnt* entp) {
	UINFO(9, "     SymInsert se"<<(void*)this<<" '"<<name<<"' se"<<(void*)entp<<"  "<<entp->nodep()<<endl);
	if (name != "" && m_idNameMap.find(name) != m_idNameMap.end()) {
	    if (!V3Error::errorCount()) {   // Else may have just reported warning
		if (debug()>=9 || V3Error::debugDefault()) dump(cout,"- err-dump: ", 1);
		entp->nodep()->v3fatalSrc("Inserting two symbols with same name: "<<name<<endl);
	    }
	} else {
	    m_idNameMap.insert(make_pair(name, entp));
	}
    }
    void reinsert(const string& name, VSymEnt* entp) {
	IdNameMap::iterator it = m_idNameMap.find(name);
	if (name!="" && it != m_idNameMap.end()) {
	    UINFO(9, "     SymReinsert se"<<(void*)this<<" '"<<name<<"' se"<<(void*)entp<<"  "<<entp->nodep()<<endl);
	    it->second = entp;  // Replace
	} else {
	    insert(name,entp);
	}
    }
    VSymEnt* findIdFlat(const string& name) const {
	// Find identifier without looking upward through symbol hierarchy
	// First, scan this begin/end block or module for the name
	IdNameMap::const_iterator it = m_idNameMap.find(name);
	UINFO(9, "     SymFind   se"<<(void*)this<<" '"<<name
	      <<"' -> "<<(it == m_idNameMap.end() ? "NONE"
			  : "se"+cvtToStr((void*)(it->second))+" n="+cvtToStr((void*)(it->second->nodep())))<<endl);
	if (it != m_idNameMap.end()) return (it->second);
	return NULL;
    }
    VSymEnt* findIdFallback(const string& name) const {
	// Find identifier looking upward through symbol hierarchy
	// First, scan this begin/end block or module for the name
	if (VSymEnt* entp = findIdFlat(name)) return entp;
	// Then scan the upper begin/end block or module for the name
	if (m_fallbackp) return m_fallbackp->findIdFallback(name);
	return NULL;
    }
private:
    bool importOneSymbol(VSymGraph* graphp, const string& name, const VSymEnt* srcp) {
	if (srcp->exported()
	    && !findIdFlat(name)) {  // Don't insert over existing entry
	    VSymEnt* symp = new VSymEnt(graphp, srcp);
	    symp->exported(false);  // Can't reimport an import without an export
	    symp->imported(true);
	    reinsert(name, symp);
	    return true;
	} else {
	    return false;
	}
    }
public:
    bool importFromPackage(VSymGraph* graphp, const VSymEnt* srcp, const string& id_or_star) {
	// Import tokens from source symbol table into this symbol table
	// Returns true if successful
	bool any = false;
	if (id_or_star != "*") {
	    IdNameMap::const_iterator it = srcp->m_idNameMap.find(id_or_star);
	    if (it != m_idNameMap.end()) {
		importOneSymbol(graphp, it->first, it->second);
	    }
	    any = true;  // Legal, though perhaps lint questionable to import nothing
	} else {
	    for (IdNameMap::const_iterator it=srcp->m_idNameMap.begin(); it!=srcp->m_idNameMap.end(); ++it) {
		if (importOneSymbol(graphp, it->first, it->second)) any = true;
	    }
	}
	return any;
    }
    void importFromIface(VSymGraph* graphp, const VSymEnt* srcp) {
	// Import interface tokens from source symbol table into this symbol table, recursively
	UINFO(9, "     importIf  se"<<(void*)this<<" from se"<<(void*)srcp<<endl);
	for (IdNameMap::const_iterator it=srcp->m_idNameMap.begin(); it!=srcp->m_idNameMap.end(); ++it) {
	    const string& name = it->first;
	    VSymEnt* subSrcp = it->second;
	    VSymEnt* subSymp = new VSymEnt(graphp, subSrcp);
	    reinsert(name, subSymp);
	    // And recurse to create children
	    subSymp->importFromIface(graphp, subSrcp);
	}
    }
    void cellErrorScopes(AstNode* lookp, string prettyName="") {
	if (prettyName=="") prettyName = lookp->prettyName();
	string scopes;
	for (IdNameMap::iterator it = m_idNameMap.begin(); it!=m_idNameMap.end(); ++it) {
	    AstNode* nodep = it->second->nodep();
	    if (nodep->castCell()
		|| (nodep->castModule() && nodep->castModule()->isTop())) {
		if (scopes != "") scopes += ", ";
		scopes += AstNode::prettyName(it->first);
	    }
	}
	if (scopes=="") scopes="<no cells found>";
	cerr<<V3Error::msgPrefix()<<"     Known scopes under '"<<prettyName<<"': "
	    <<scopes<<endl;
	if (debug()) dump(cerr,"\t\t      KnownScope: ", 1);
    }
};

//######################################################################
// Symbol tables

class VSymGraph {
    // Collection of symbol tables
    // TYPES
    typedef vector<VSymEnt*>	SymStack;

private:
    // MEMBERS
    VSymEnt*	m_symRootp;		// Root symbol table
    SymStack	m_symsp;		// All symbol tables, to cleanup

protected:
    friend class VSymEnt;
    void pushNewEnt(VSymEnt* entp) { m_symsp.push_back(entp); }

public:
    VSymEnt* rootp() const { return m_symRootp; }
    // Debug
    void dump(ostream& os, const string& indent="") {
	VSymMap doneSyms;
	os<<"SymEnt Dump:\n";
	m_symRootp->dumpIterate(os, doneSyms, indent, 9999, "$root");
	bool first = true;
	for (SymStack::iterator it = m_symsp.begin(); it != m_symsp.end(); ++it) {
	    if (doneSyms.find(*it) == doneSyms.end()) {
		if (first) { first=false; os<<"%%Warning: SymEnt Orphans:\n"; }
		(*it)->dumpIterate(os, doneSyms, indent, 9999, "Orphan");
	    }
	}
    }
    void dumpFilePrefixed(const string& nameComment) {
	if (v3Global.opt.dumpTree()) {
	    string filename = v3Global.debugFilename(nameComment)+".txt";
	    UINFO(2,"Dumping "<<filename<<endl);
	    const auto_ptr<ofstream> logp (V3File::new_ofstream(filename));
	    if (logp->fail()) v3fatalSrc("Can't write "<<filename);
	    dump(*logp, "");
	}
    }
public:
    // CREATORS
    VSymGraph(AstNetlist* nodep) {
	m_symRootp = new VSymEnt(this, nodep);
    }
    ~VSymGraph() {
	for (SymStack::iterator it = m_symsp.begin(); it != m_symsp.end(); ++it) {
	    delete (*it);
	}
    }
};

//######################################################################

inline VSymEnt::VSymEnt(VSymGraph* graphp, AstNode* nodep)
    : m_nodep(nodep) {
    // No argument to set fallbackp, as generally it's wrong to set it in the new call,
    // Instead it needs to be set on a "findOrNew()" return, as it may have been new'ed
    // by an earlier search insertion.
    m_fallbackp = NULL;
    m_parentp = NULL;
    m_packagep = NULL;
    m_exported = true;
    m_imported = false;
    graphp->pushNewEnt(this);
}

inline VSymEnt::VSymEnt(VSymGraph* graphp, const VSymEnt* symp)
    : m_nodep(symp->nodep()) {
    m_fallbackp = symp->m_fallbackp;
    m_parentp  = symp->m_parentp;
    m_packagep = symp->m_packagep;
    m_exported = symp->m_exported;
    m_imported = symp->m_imported;
    graphp->pushNewEnt(this);
}

#endif // guard
