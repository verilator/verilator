// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Common header between parser and lex
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2009-2022 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#ifndef VERILATOR_V3PARSESYM_H_
#define VERILATOR_V3PARSESYM_H_

#include "config_build.h"
#include "verilatedos.h"

#include "V3Error.h"
#include "V3FileLine.h"
#include "V3Global.h"
#include "V3SymTable.h"

#include <deque>
#include <vector>

//######################################################################
// Symbol table for parsing

class V3ParseSym final {
    // TYPES
    using SymStack = std::vector<VSymEnt*>;

private:
    // MEMBERS
    static int s_anonNum;  // Number of next anonymous object (parser use only)
    VSymGraph m_syms;  // Graph of symbol tree
    VSymEnt* m_symTableNextId = nullptr;  // Symbol table for next lexer lookup (parser use only)
    VSymEnt* m_symCurrentp = nullptr;  // Active symbol table for additions/lookups
    std::vector<VSymEnt*> m_sympStack;  // Stack of upper nodes with pending symbol tables

public:
    // CONSTRUCTORS
    explicit V3ParseSym(AstNetlist* rootp)
        : m_syms{rootp} {
        s_anonNum = 0;  // Number of next anonymous object
        pushScope(findNewTable(rootp));
        m_symCurrentp = symCurrentp();
    }
    ~V3ParseSym() = default;

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
            VSymEnt* const symsp = new VSymEnt{&m_syms, nodep};
            nodep->user4p(symsp);
        }
        return getTable(nodep);
    }
    void nextId(AstNode* entp) {
        if (entp) {
            UINFO(9, "symTableNextId under " << entp << "-" << entp->type().ascii() << endl);
            m_symTableNextId = getTable(entp);
        } else {
            UINFO(9, "symTableNextId under nullptr" << endl);
            m_symTableNextId = nullptr;
        }
    }
    void reinsert(AstNode* nodep, VSymEnt* parentp = nullptr) {
        reinsert(nodep, parentp, nodep->name());
    }
    void reinsert(AstNode* nodep, VSymEnt* parentp, string name) {
        if (!parentp) parentp = symCurrentp();
        if (name == "") {  // New name with space in name so can't collide with users
            name = std::string{" anon"} + nodep->type().ascii() + cvtToStr(++s_anonNum);
        }
        parentp->reinsert(name, findNewTable(nodep));
    }
    void pushNew(AstNode* nodep) { pushNewUnder(nodep, nullptr); }
    void pushNewUnder(AstNode* nodep, VSymEnt* parentp) {
        if (!parentp) parentp = symCurrentp();
        VSymEnt* const symp
            = findNewTable(nodep);  // Will set user4p, which is how we connect table to node
        symp->fallbackp(parentp);
        reinsert(nodep, parentp);
        pushScope(symp);
    }
    void pushNewUnderNodeOrCurrent(AstNode* nodep, AstNode* parentp) {
        if (parentp) {
            pushNewUnder(nodep, findNewTable(parentp));
        } else {
            pushNewUnder(nodep, nullptr);
        }
    }
    void pushScope(VSymEnt* symp) {
        m_sympStack.push_back(symp);
        m_symCurrentp = symp;
    }
    void popScope(AstNode* nodep) {
        if (VL_UNCOVERABLE(symCurrentp()->nodep() != nodep)) {  // LCOV_EXCL_START
            if (debug()) {
                showUpward();
                dump(cout, "-mism: ");
            }
            nodep->v3fatalSrc("Symbols suggest ending " << symCurrentp()->nodep()->prettyTypeName()
                                                        << " but parser thinks ending "
                                                        << nodep->prettyTypeName());
            return;
        }  // LCOV_EXCL_STOP
        m_sympStack.pop_back();
        UASSERT_OBJ(!m_sympStack.empty(), nodep, "symbol stack underflow");
        m_symCurrentp = m_sympStack.back();
    }
    void showUpward() {  // LCOV_EXCL_START
        UINFO(1, "ParseSym Stack:\n");
        for (VSymEnt* const symp : vlstd::reverse_view(m_sympStack)) {
            UINFO(1, "    " << symp->nodep() << endl);
        }
        UINFO(1, "ParseSym Current: " << symCurrentp()->nodep() << endl);
    }  // LCOV_EXCL_STOP
    void dump(std::ostream& os, const string& indent = "") { m_syms.dump(os, indent); }
    AstNode* findEntUpward(const string& name) const {
        // Lookup the given string as an identifier, return type of the id, scanning upward
        VSymEnt* const foundp = symCurrentp()->findIdFallback(name);
        if (foundp) {
            return foundp->nodep();
        } else {
            return nullptr;
        }
    }
    void importExtends(AstNode* classp) {
        // Import from package::id_or_star to this
        VSymEnt* const symp = getTable(classp);
        UASSERT_OBJ(symp, classp,  // Internal problem, because we earlier found it
                    "Extends class package not found");
        // Walk old sym table and reinsert into current table
        // We let V3LinkDot report the error instead of us
        symCurrentp()->importFromClass(&m_syms, symp);
    }
    void importItem(AstNode* packagep, const string& id_or_star) {
        // Import from package::id_or_star to this
        VSymEnt* const symp = getTable(packagep);
        UASSERT_OBJ(symp, packagep,  // Internal problem, because we earlier found it
                    "Import package not found");
        // Walk old sym table and reinsert into current table
        // We let V3LinkDot report the error instead of us
        symCurrentp()->importFromPackage(&m_syms, symp, id_or_star);
    }
    void exportItem(AstNode* packagep, const string& id_or_star) {
        // Export from this the remote package::id_or_star
        VSymEnt* const symp = getTable(packagep);
        UASSERT_OBJ(symp, packagep,  // Internal problem, because we earlier found it
                    "Export package not found");
        symCurrentp()->exportFromPackage(&m_syms, symp, id_or_star);
    }
    void exportStarStar() {
        // Export *::* from remote packages
        symCurrentp()->exportStarStar(&m_syms);
    }
};

#endif  // Guard
