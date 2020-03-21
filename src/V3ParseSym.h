// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Common header between parser and lex
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2009-2020 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#ifndef _V3PARSESYM_H_
#define _V3PARSESYM_H_ 1

#include "config_build.h"
#include "verilatedos.h"

#include "V3Error.h"
#include "V3FileLine.h"
#include "V3Global.h"
#include "V3SymTable.h"

#include <deque>

//######################################################################
// Symbol table for parsing

class V3ParseSym {
    // TYPES
    typedef std::vector<VSymEnt*> SymStack;

private:
    // MEMBERS
    static int  s_anonNum;              // Number of next anonymous object (parser use only)
    VSymGraph   m_syms;                 // Graph of symbol tree
    VSymEnt*    m_symTableNextId;       // Symbol table for next lexer lookup (parser use only)
    VSymEnt*    m_symCurrentp;          // Active symbol table for additions/lookups
    SymStack    m_sympStack;            // Stack of upper nodes with pending symbol tables

public:
    // CONSTRUCTORS
    explicit V3ParseSym(AstNetlist* rootp)
        : m_syms(rootp) {
        s_anonNum = 0;  // Number of next anonymous object
        pushScope(findNewTable(rootp));
        m_symTableNextId = NULL;
        m_symCurrentp = symCurrentp();
    }
    ~V3ParseSym() {}

private:
    // METHODS
    static VSymEnt* getTable(AstNode* nodep) {
        UASSERT_OBJ(nodep->user4p(), nodep, "Current symtable not found");
        return nodep->user4u().toSymEnt();
    }

public:
    VSymEnt* nextId() const { return m_symTableNextId; }
    VSymEnt* symCurrentp() const { return m_symCurrentp; }
    VSymEnt* symRootp() const { return m_syms.rootp(); }

    VSymEnt* findNewTable(AstNode* nodep) {
        if (!nodep->user4p()) {
            VSymEnt* symsp = new VSymEnt(&m_syms, nodep);
            nodep->user4p(symsp);
        }
        return getTable(nodep);
    }
    void nextId(AstNode* entp) {
        if (entp) {
            UINFO(9,"symTableNextId under "<<entp<<"-"<<entp->type().ascii()<<endl);
            m_symTableNextId = getTable(entp);
        }
        else {
            UINFO(9,"symTableNextId under NULL"<<endl);
            m_symTableNextId = NULL;
        }
    }
    void reinsert(AstNode* nodep, VSymEnt* parentp=NULL) {
        reinsert(nodep, parentp, nodep->name());
    }
    void reinsert(AstNode* nodep, VSymEnt* parentp, string name) {
        if (!parentp) parentp = symCurrentp();
        if (name == "") {  // New name with space in name so can't collide with users
            name = string(" anon") + nodep->type().ascii() + cvtToStr(++s_anonNum);
        }
        parentp->reinsert(name, findNewTable(nodep));
    }
    void pushNew(AstNode* nodep) { pushNewUnder(nodep, NULL); }
    void pushNewUnder(AstNode* nodep, VSymEnt* parentp) {
        if (!parentp) parentp = symCurrentp();
        VSymEnt* symp = findNewTable(nodep);  // Will set user4p, which is how we connect table to node
        symp->fallbackp(parentp);
        reinsert(nodep, parentp);
        pushScope(symp);
    }
    void pushScope(VSymEnt* symp) {
        m_sympStack.push_back(symp);
        m_symCurrentp = symp;
    }
    void popScope(AstNode* nodep) {
        if (symCurrentp()->nodep() != nodep) {
            if (debug()) { showUpward(); dump(cout, "-mism: "); }
            nodep->v3fatalSrc("Symbols suggest ending "<<symCurrentp()->nodep()->prettyTypeName()
                              <<" but parser thinks ending "<<nodep->prettyTypeName());
            return;
        }
        m_sympStack.pop_back();
        UASSERT_OBJ(!m_sympStack.empty(), nodep, "symbol stack underflow");
        m_symCurrentp = m_sympStack.back();
    }
    void showUpward() {
        UINFO(1,"ParseSym Stack:\n");
        for (SymStack::reverse_iterator it=m_sympStack.rbegin(); it!=m_sympStack.rend(); ++it) {
            VSymEnt* symp = *it;
            UINFO(1,"    "<<symp->nodep()<<endl);
        }
        UINFO(1,"ParseSym Current: "<<symCurrentp()->nodep()<<endl);
    }
    void dump(std::ostream& os, const string& indent="") {
        m_syms.dump(os, indent);
    }
    AstNode* findEntUpward(const string& name) {
        // Lookup the given string as an identifier, return type of the id, scanning upward
        VSymEnt* foundp = symCurrentp()->findIdFallback(name);
        if (foundp) return foundp->nodep();
        else return NULL;
    }
    void importItem(AstNode* packagep, const string& id_or_star) {
        // Import from package::id_or_star to this
        VSymEnt* symp = getTable(packagep);
        UASSERT_OBJ(symp, packagep,
                    // Internal problem, because we earlier found pkg to label it an ID__aPACKAGE
                    "Import package not found");
        // Walk old sym table and reinsert into current table
        // We let V3LinkDot report the error instead of us
        symCurrentp()->importFromPackage(&m_syms, symp, id_or_star);
    }
    void exportItem(AstNode* packagep, const string& id_or_star) {
        // Export from this the remote package::id_or_star
        VSymEnt* symp = getTable(packagep);
        UASSERT_OBJ(symp, packagep,
                    // Internal problem, because we earlier found pkg to label it an ID__aPACKAGE
                    "Export package not found");
        symCurrentp()->exportFromPackage(&m_syms, symp, id_or_star);
    }
    void exportStarStar(AstNode* packagep) {
        // Export *::* from remote packages
        symCurrentp()->exportStarStar(&m_syms);
    }
};

#endif  // Guard
