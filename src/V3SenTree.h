// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Break always into sensitivity block domains
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2024 by Wilson Snyder. This program is free software; you
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

class SenTreeFinder final {
    // STATE
    AstTopScope* const m_topScopep;  // Top scope to add global SenTrees to
    std::unordered_set<VNRef<AstSenTree>> m_trees;  // Set of global SenTrees
    AstSenTree* m_combop = nullptr;  // The unique combinational domain SenTree
    AstSenTree* m_initialp = nullptr;  // The unique initial domain SenTree

    VL_UNCOPYABLE(SenTreeFinder);

    template <typename T_Domain>  //
    AstSenTree* makeUnique() {
        FileLine* const fl = m_topScopep->fileline();
        AstSenTree* const senTreep = new AstSenTree{fl, new AstSenItem{fl, T_Domain{}}};
        AstSenTree* const restultp = getSenTree(senTreep);
        VL_DO_DANGLING(senTreep->deleteTree(), senTreep);  // getSenTree clones, so can delete
        return restultp;
    }

public:
    // CONSTRUCTORS
    SenTreeFinder()
        : SenTreeFinder{v3Global.rootp()} {}

    explicit SenTreeFinder(AstNetlist* netlistp)
        : m_topScopep{netlistp->topScopep()} {
        // Gather existing global SenTrees
        for (AstSenTree* senTreep = m_topScopep->senTreesp(); senTreep;
             senTreep = VN_AS(senTreep->nextp(), SenTree)) {
            m_trees.emplace(*senTreep);
            if (senTreep->hasCombo()) m_combop = senTreep;
            if (senTreep->hasInitial()) m_initialp = senTreep;
        }
    }

    // METHODS

    // Return a global AstSenTree equivalent to the given senTreep.
    // If no such global AstSenTree exists create one and add it to the stored AstTopScope.
    AstSenTree* getSenTree(AstSenTree* senTreep) {
        auto it = m_trees.find(*senTreep);
        // If match found, return it.
        if (it != m_trees.end()) return &(*it).get();

        // Not found, create a new one
        AstSenTree* const newSenTreep = senTreep->cloneTree(false);
        m_topScopep->addSenTreesp(newSenTreep);
        m_trees.emplace(*newSenTreep);
        return newSenTreep;
    }

    // Return the global combinational AstSenTree.
    // If no such global SenTree exists create one and add it to the stored AstTopScope.
    AstSenTree* getComb() {
        if (!m_combop) m_combop = makeUnique<AstSenItem::Combo>();
        return m_combop;
    }

    // Return the global initial AstSenTree.
    // If no such global SenTree exists create one and add it to the stored AstTopScope.
    AstSenTree* getInitial() {
        if (!m_initialp) m_initialp = makeUnique<AstSenItem::Initial>();
        return m_initialp;
    }
};

#endif  // Guard
