// -*- C++ -*-
//*************************************************************************
// DESCRIPTION: Verilator: Symbol table
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

#ifndef _V3LINKSYMTABLE_H_
#define _V3LINKSYMTABLE_H_ 1

#include "config_build.h"
#include "verilatedos.h"
#include <cstdio>
#include <cstdarg>
#include <unistd.h>
#include <map>
#include <iomanip>

#include "V3Global.h"
#include "V3Ast.h"

//######################################################################
// Symbol table

class V3SymTable : public AstNUser {
    // Symbol table that can have a "superior" table for resolving upper references
  private:
    // MEMBERS
    typedef std::map<string,AstNode*> IdNameMap;
    IdNameMap	m_idNameMap;	// Hash of variables by name
    AstNode*	m_ownerp;	// Node that table belongs to
    V3SymTable*	m_upperp;	// Table "above" this one in name scope
  public:
    // METHODS
    V3SymTable(AstNode* ownerp, V3SymTable* upperTablep) {
	m_ownerp = ownerp; m_upperp = upperTablep; }
    V3SymTable() {
	m_ownerp = NULL; m_upperp = NULL; }
    ~V3SymTable() {}
    AstNode* ownerp() const { return m_ownerp; }
    void insert(const string& name, AstNode* nodep) {
	//UINFO(9, "     SymInsert "<<this<<" '"<<name<<"' "<<nodep<<endl);
	if (m_idNameMap.find(name) != m_idNameMap.end()) {
	    if (!V3Error::errorCount()) {   // Else may have just reported warning
		nodep->v3fatalSrc("Inserting two symbols with same name: "<<name<<endl);
	    }
	} else {
	    m_idNameMap.insert(make_pair(name, nodep));
	}
    }
    void reinsert(const string& name, AstNode* nodep) {
	IdNameMap::iterator it = m_idNameMap.find(name);
	if (it != m_idNameMap.end()) {
	    //UINFO(9, "     SymReinsert "<<this<<" '"<<name<<"' "<<nodep<<endl);
	    it->second = nodep;  // Replace
	} else {
	    insert(name,nodep);
	}
    }
    AstNode* findIdFlat(const string& name) const {
	// Find identifier without looking upward through symbol hierarchy
	//UINFO(9, "     SymFind   "<<this<<" '"<<name<<"' "<<endl);
	// First, scan this begin/end block or module for the name
	IdNameMap::const_iterator iter = m_idNameMap.find(name);
	if (iter != m_idNameMap.end()) return (iter->second);
	return NULL;
    }
    AstNode* findIdUpward(const string& name) const {
	// Find identifier looking upward through symbol hierarchy
	// First, scan this begin/end block or module for the name
	if (AstNode* nodep = findIdFlat(name)) return nodep;
	// Then scan the upper begin/end block or module for the name
	if (m_upperp) return m_upperp->findIdUpward(name);
	return NULL;
    }
    bool import(const V3SymTable* srcp, const string& id_or_star) {
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
    void dump(ostream& os, const string& indent="", bool user4p_is_table=false) const {
	if (user4p_is_table) { AstUser4InUse::check(); }
	for (IdNameMap::const_iterator it=m_idNameMap.begin(); it!=m_idNameMap.end(); ++it) {
	    os<<indent<<it->first;
	    for (size_t i=it->first.length(); i<30; ++i) os<<" ";
	    if (user4p_is_table) {
		V3SymTable* belowp = (it->second)->user4p()->castSymTable();
		os<<setw(10)<<(void*)(belowp)<<setw(0)<<"  "<<it->second<<endl;
		if (belowp) belowp->dump(os, indent+"+ ", user4p_is_table);
	    } else {
		os<<it->second<<endl;
	    }
	}
    }
};

#endif // guard
