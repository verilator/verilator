// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Break always into sensitivity block domains
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2020 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
// V3Block's Transformations:
//
// Note this can be called multiple times.
//   Create a IBLOCK(initial), SBLOCK(combo)
//      ALWAYS: Remove any-edges from sense list
//          If no POS/NEG in senselist, Fold into SBLOCK(combo)
//          Else fold into SBLOCK(sequent).
//          OPTIMIZE: When support async clocks, fold into that block if possible
//      INITIAL: Move into IBLOCK
//      WIRE: Move into SBLOCK(combo)
//
//*************************************************************************

#ifndef _V3SENTREE_H_
#define _V3SENTREE_H_

#include "config_build.h"
#include "verilatedos.h"

#include "V3Global.h"
#include "V3Ast.h"
#include "V3Hashed.h"

#include <cstdarg>
#include <map>
#include <algorithm>
#include <vector>
#include VL_INCLUDE_UNORDERED_SET

//######################################################################
// Collect SenTrees under the entire scope
// And provide functions to find/add a new one

class SenTreeSet {
    // Hash table of sensitive blocks.
private:
    // TYPES
    class HashSenTree {
    public:
        HashSenTree() {}
        size_t operator() (const AstSenTree* kp) const {
            return V3Hashed::uncachedHash(kp).fullValue();
        }
        // Copying required for OSX's libc++
    };

    class EqSenTree {
    public:
        EqSenTree() {}
        bool operator() (const AstSenTree* ap, const AstSenTree* bp) const {
            return ap->sameTree(bp);
        }
        // Copying required for OSX's libc++
    };

    // MEMBERS
    typedef vl_unordered_set<AstSenTree*, HashSenTree, EqSenTree> Set;
    Set m_trees;  // Set of sensitive blocks, for folding.

public:
    // CONSTRUCTORS
    SenTreeSet() {}

    // METHODS
    void add(AstSenTree* nodep) { m_trees.insert(nodep); }
    AstSenTree* find(AstSenTree* likep) {
        AstSenTree* resultp = NULL;
        Set::iterator it = m_trees.find(likep);
        if (it != m_trees.end()) {
            resultp = *it;
        }
        return resultp;
    }
    void clear() { m_trees.clear(); }

private:
    VL_UNCOPYABLE(SenTreeSet);
};

class SenTreeFinder : public AstNVisitor {
private:
    // STATE
    AstTopScope* m_topscopep;  // Top scope to add statement to
    SenTreeSet m_trees;  // Set of sensitive blocks, for folding

    // VISITORS
    VL_DEBUG_FUNC;  // Declare debug()

    virtual void visit(AstNodeModule* nodep) VL_OVERRIDE {
        // Only do the top
        if (nodep->isTop()) {
            iterateChildren(nodep);
        }
    }
    virtual void visit(AstTopScope* nodep) VL_OVERRIDE {
        m_topscopep = nodep;
        iterateChildren(nodep);
        // Don't clear topscopep, the namer persists beyond this visit
    }
    virtual void visit(AstScope* nodep) VL_OVERRIDE {
        // But no SenTrees under TopScope's scope
    }
    // Memorize existing block names
    virtual void visit(AstActive* nodep) VL_OVERRIDE {
        // Don't grab SenTrees under Actives, only those that are global (under Scope directly)
        iterateChildren(nodep);
    }
    virtual void visit(AstSenTree* nodep) VL_OVERRIDE { m_trees.add(nodep); }
    // Empty visitors, speed things up
    virtual void visit(AstNodeStmt* nodep) VL_OVERRIDE { }
    virtual void visit(AstNode* nodep) VL_OVERRIDE {
        iterateChildren(nodep);
    }
    // METHODS
public:
    void clear() {
        m_topscopep = NULL;
        m_trees.clear();
    }
    AstSenTree* getSenTree(FileLine* fl, AstSenTree* sensesp) {
        // Return a global sentree that matches given sense list.
        AstSenTree* treep = m_trees.find(sensesp);
        // Not found, form a new one
        if (!treep) {
            UASSERT(m_topscopep, "Never called main()");
            treep = sensesp->cloneTree(false);
            m_topscopep->addStmtsp(treep);
            UINFO(8,"    New SENTREE "<<treep<<endl);
            m_trees.add(treep);
            // Note blocks may have also been added above in the Active visitor
        }
        return treep;
    }
public:
    // CONSTRUCTORS
    SenTreeFinder() {
        clear();
    }
    virtual ~SenTreeFinder() {}
    void main(AstTopScope* nodep) {
        iterate(nodep);
    }
};

#endif  // Guard
