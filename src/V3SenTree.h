// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Break always into sensitivity block domains
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2021 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
// AstSenTree related utilities.
//*************************************************************************

#ifndef VERILATOR_V3SENTREE_H_
#define VERILATOR_V3SENTREE_H_

#include "config_build.h"
#include "verilatedos.h"

#include "V3Ast.h"
#include "V3Hasher.h"

#include <unordered_set>

//######################################################################
// Collect SenTrees under the entire scope
// And provide functions to find/add a new one

class SenTreeSet final {
    // Hash table of sensitive blocks.
private:
    // TYPES
    struct HashSenTree {
        size_t operator()(const AstSenTree* kp) const {
            return V3Hasher::uncachedHash(kp).value();
        }
    };

    struct EqSenTree {
        bool operator()(const AstSenTree* ap, const AstSenTree* bp) const {
            return ap->sameTree(bp);
        }
    };

    // MEMBERS
    using Set = std::unordered_set<AstSenTree*, HashSenTree, EqSenTree>;
    Set m_trees;  // Set of sensitive blocks, for folding.

public:
    // CONSTRUCTORS
    SenTreeSet() = default;

    // METHODS
    void add(AstSenTree* nodep) { m_trees.insert(nodep); }

    AstSenTree* find(AstSenTree* likep) {
        AstSenTree* resultp = nullptr;
        const auto it = m_trees.find(likep);
        if (it != m_trees.end()) resultp = *it;
        return resultp;
    }

    void clear() { m_trees.clear(); }

private:
    VL_UNCOPYABLE(SenTreeSet);
};

class SenTreeFinder final {
private:
    // STATE
    AstTopScope* m_topScopep = nullptr;  // Top scope to add global SenTrees to
    SenTreeSet m_trees;  // Set of global SenTrees

    VL_UNCOPYABLE(SenTreeFinder);

public:
    // CONSTRUCTORS
    SenTreeFinder() = default;

    // METHODS
    AstSenTree* getSenTree(AstSenTree* senTreep) {
        // Return a global SenTree that matches given SenTree. If no such global
        // SenTree exists, create one and add it to the stored TopScope.
        AstSenTree* treep = m_trees.find(senTreep);
        // Not found, form a new one
        if (!treep) {
            UASSERT(m_topScopep, "Never called init()");
            treep = senTreep->cloneTree(false);
            m_topScopep->addStmtsp(treep);
            UINFO(8, "    New SENTREE " << treep << endl);
            m_trees.add(treep);
        }
        return treep;
    }

    void init(AstTopScope* topScopep) {
        // Keep hold of top scope so we can add global SenTrees later
        m_topScopep = topScopep;
        // Gather existing global SenTrees
        for (AstNode* nodep = topScopep->stmtsp(); nodep; nodep = nodep->nextp()) {
            if (AstSenTree* senTreep = VN_CAST(nodep, SenTree)) m_trees.add(senTreep);
        }
    }
};

#endif  // Guard
