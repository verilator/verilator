// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Symbol table
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

//######################################################################
// Symbol table

class VSymEnt {
    // Symbol table that can have a "superior" table for resolving upper references
private:
    // MEMBERS
    typedef std::map<string,VSymEnt*> IdNameMap;
    IdNameMap	m_idNameMap;	// Hash of variables by name
    AstNode*	m_nodep;	// Node that entry belongs to
    VSymEnt*	m_fallbackp;	// Table "above" this one in name scope, for fallback resolution
    VSymEnt*	m_parentp;	// Table that created this table, dot notation needed to resolve into it
    string	m_symPrefix;	// String to prefix symbols with (for V3LinkDot, unused here)
    static int debug() { return 0; }  // NOT runtime, too hot of a function
private:
    void dumpIterate(ostream& os, const string& indent, int numLevels, const string& searchName) const {
	os<<indent<<left<<setw(30)<<searchName<<setw(0)<<right;
	os<<"  "<<setw(16)<<(void*)(this)<<setw(0);
	os<<"  n="<<nodep();
	os<<endl;
	for (IdNameMap::const_iterator it=m_idNameMap.begin(); it!=m_idNameMap.end(); ++it) {
	    if (numLevels >= 1) {
		it->second->dumpIterate(os, indent+"+ ", numLevels-1, it->first);
	    }
	}
    }

public:
    // METHODS
    VSymEnt(VSymGraph* graphp, AstNode* nodep);  // Below
    ~VSymEnt() {}
    void fallbackp(VSymEnt* entp) { m_fallbackp = entp; }
    void parentp(VSymEnt* entp) { m_parentp = entp; }
    VSymEnt* parentp() const { return m_parentp; }
    AstNode* nodep() const { if (!this) return NULL; else return m_nodep; }  // null check so can call .findId(...)->nodep()
    string symPrefix() const { return m_symPrefix; }
    void symPrefix(const string& name) { m_symPrefix = name; }
    void insert(const string& name, VSymEnt* entp) {
	UINFO(9, "     SymInsert "<<this<<" '"<<name<<"' "<<(void*)entp<<"  "<<entp->nodep()<<endl);
	if (m_idNameMap.find(name) != m_idNameMap.end()) {
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
	if (it != m_idNameMap.end()) {
	    UINFO(9, "     SymReinsert "<<this<<" '"<<name<<"' "<<(void*)entp<<"  "<<entp->nodep()<<endl);
	    it->second = entp;  // Replace
	} else {
	    insert(name,entp);
	}
    }
    VSymEnt* findIdFlat(const string& name) const {
	// Find identifier without looking upward through symbol hierarchy
	// First, scan this begin/end block or module for the name
	IdNameMap::const_iterator iter = m_idNameMap.find(name);
	UINFO(9, "     SymFind   "<<this<<" '"<<name<<"' -> "<<(iter == m_idNameMap.end() ? "NONE" : cvtToStr((void*)(iter->second->nodep())))<<endl);
	if (iter != m_idNameMap.end()) return (iter->second);
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
    bool import(const VSymEnt* srcp, const string& id_or_star) {
	// Import tokens from source symbol table into this symbol table
	// Returns true if successful
	bool any = false;
	if (id_or_star != "*") {
	    IdNameMap::const_iterator it = srcp->m_idNameMap.find(id_or_star);
	    if (it != m_idNameMap.end()) {
		reinsert(it->first, it->second);
		any = true;
	    }
	} else {
	    for (IdNameMap::const_iterator it=srcp->m_idNameMap.begin(); it!=srcp->m_idNameMap.end(); ++it) {
		reinsert(it->first, it->second);
		any = true;
	    }
	}
	return any;
    }
    void cellErrorScopes(AstNode* lookp) {
	string scopes;
	for (IdNameMap::iterator it = m_idNameMap.begin(); it!=m_idNameMap.end(); ++it) {
	    AstNode* nodep = it->second->nodep();
	    if (nodep->castCell()
		|| (nodep->castModule() && nodep->castModule()->isTop())) {
		if (scopes != "") scopes += ", ";
		scopes += AstNode::prettyName(it->first);
	    }
	}
	cerr<<V3Error::msgPrefix()<<"     Known scopes under '"<<lookp->prettyName()<<"': "
	    <<scopes<<endl;
	if (debug()) dump(cerr,"\t\t      KnownScope: ", 1);
    }
    void dump(ostream& os, const string& indent="", int numLevels=1) const {
	dumpIterate(os,indent,numLevels,"TOP");
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
	os<<"SymEnt Dump:\n";
	m_symRootp->dump(os, indent, 9999);
    }
    void dumpFilePrefixed(const string& nameComment) {
	if (v3Global.opt.dumpTree()) {
	    string filename = v3Global.debugFilename(nameComment)+".txt";
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

inline VSymEnt::VSymEnt(VSymGraph* m_graphp, AstNode* nodep)
    : m_nodep(nodep) {
    // No argument to set fallbackp, as generally it's wrong to set it in the new call,
    // Instead it needs to be set on a "findOrNew()" return, as it may have been new'ed
    // by an earlier search insertion.
    m_fallbackp = NULL;
    m_parentp = NULL;
    m_graphp->pushNewEnt(this);
}

#endif // guard
