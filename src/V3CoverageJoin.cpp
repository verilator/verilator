// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Netlist (top level) functions
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2022 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
// COVERAGEJOIN TRANSFORMATIONS:
//      If two COVERTOGGLEs have same VARSCOPE, combine them
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3CoverageJoin.h"

#include "V3DupFinder.h"
#include "V3Global.h"
#include "V3Stats.h"

#include <vector>

//######################################################################
// CoverageJoin state, as a visitor of each AstNode

class CoverageJoinVisitor final : public VNVisitor {
private:
    // NODE STATE
    // VNUser4InUse     In V3Hasher via V3DupFinder

    // STATE
    std::vector<AstCoverToggle*> m_toggleps;  // List of of all AstCoverToggle's

    VDouble0 m_statToggleJoins;  // Statistic tracking

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    void detectDuplicates() {
        UINFO(9, "Finding duplicates\n");
        // Note uses user4
        V3DupFinder dupFinder;  // Duplicate code detection
        // Hash all of the original signals we toggle cover
        for (AstCoverToggle* nodep : m_toggleps) dupFinder.insert(nodep->origp());
        // Find if there are any duplicates
        for (AstCoverToggle* nodep : m_toggleps) {
            // nodep->backp() is null if we already detected it's a duplicate and unlinked it.
            if (nodep->backp()) {
                // Want to choose a base node, and keep finding duplicates that are identical.
                // This prevents making chains where a->b, then c->d, then b->c, as we'll
                // find a->b, a->c, a->d directly.
                while (true) {
                    const auto dupit = dupFinder.findDuplicate(nodep->origp());
                    if (dupit == dupFinder.end()) break;
                    //
                    const AstNode* const duporigp = dupit->second;
                    // Note hashed will point to the original variable (what's
                    // duplicated), not the covertoggle, but we need to get back to the
                    // covertoggle which is immediately above, so:
                    AstCoverToggle* const removep = VN_AS(duporigp->backp(), CoverToggle);
                    UASSERT_OBJ(removep, nodep, "CoverageJoin duplicate of wrong type");
                    UINFO(8, "  Orig " << nodep << " -->> " << nodep->incp()->declp() << endl);
                    UINFO(8, "   dup " << removep << " -->> " << removep->incp()->declp() << endl);
                    // The CoverDecl the duplicate pointed to now needs to point to the
                    // original's data. I.e. the duplicate will get the coverage number
                    // from the non-duplicate
                    AstCoverDecl* const datadeclp = nodep->incp()->declp()->dataDeclThisp();
                    removep->incp()->declp()->dataDeclp(datadeclp);
                    UINFO(8, "   new " << removep->incp()->declp() << endl);
                    // Mark the found node as a duplicate of the first node
                    // (Not vice-versa as we have the iterator for the found node)
                    removep->unlinkFrBack();
                    VL_DO_DANGLING(pushDeletep(removep), removep);
                    // Remove node from comparison so don't hit it again
                    dupFinder.erase(dupit);
                    ++m_statToggleJoins;
                }
            }
        }
    }

    // VISITORS
    virtual void visit(AstNetlist* nodep) override {
        // Find all Coverage's
        iterateChildren(nodep);
        // Simplify
        detectDuplicates();
    }
    virtual void visit(AstCoverToggle* nodep) override {
        m_toggleps.push_back(nodep);
        iterateChildren(nodep);
    }
    //--------------------
    virtual void visit(AstNodeMath*) override {}  // Accelerate
    virtual void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit CoverageJoinVisitor(AstNetlist* nodep) { iterate(nodep); }
    virtual ~CoverageJoinVisitor() override {
        V3Stats::addStat("Coverage, Toggle points joined", m_statToggleJoins);
    }
};

//######################################################################
// Coverage class functions

void V3CoverageJoin::coverageJoin(AstNetlist* rootp) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    { CoverageJoinVisitor{rootp}; }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("coveragejoin", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}
