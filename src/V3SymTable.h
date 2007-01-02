// $Id$
//*************************************************************************
// DESCRIPTION: Verilator: Symbol table
//
// Code available from: http://www.veripool.com/verilator
//
// AUTHORS: Wilson Snyder with Paul Wasson, Duane Gabli
//
//*************************************************************************
//
// Copyright 2003-2007 by Wilson Snyder.  This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// General Public License or the Perl Artistic License.
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
#include <stdio.h>
#include <stdarg.h>
#include <unistd.h>
#include <map>

#include "V3Global.h"

//######################################################################
// Symbol table

class V3SymTable : public AstNUser {
    // Symbol table that can have a "superior" table for resolving upper references
  private:
    // MEMBERS
    typedef std::map<string,AstNode*> IdNameMap;
    IdNameMap	m_idNameMap;		// Hash of variables by name
    V3SymTable*	m_upperp;	// Table "above" this one in name scope
  public:
    // METHODS
    V3SymTable(V3SymTable* upperTablep) { m_upperp = upperTablep; }
    V3SymTable() { m_upperp = NULL; }
    ~V3SymTable() {}
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
    AstNode* findIdName(const string& name) {
	//UINFO(9, "     SymFind   "<<this<<" '"<<name<<"' "<<endl);
	// First, scan this begin/end block or module for the name
	IdNameMap::iterator iter = m_idNameMap.find(name);
	if (iter != m_idNameMap.end()) return (iter->second);
	// Then scan the upper begin/end block or module for the name
	if (m_upperp) return m_upperp->findIdName(name);
	return NULL;
    }
};

#endif // guard
