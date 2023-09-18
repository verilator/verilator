// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Break always into separate statements to reduce temps
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2023 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
// V3SplitAs's Transformations:
//
//      Search each ALWAYS for a VARREF lvalue with a /*isolate_assignments*/ attribute
//      If found, color statements with both, assignment to that varref, or other assignments.
//      Replicate the Always, and remove mis-colored duplicate code.
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3SplitAs.h"

#include "V3Ast.h"
#include "V3Global.h"
#include "V3Stats.h"

#include <map>

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// Find all split variables in a block

class SplitAsFindVisitor final : public VNVisitor {
private:
    // STATE - across all visitors
    AstVarScope* m_splitVscp = nullptr;  // Variable we want to split

    // METHODS
    void visit(AstVarRef* nodep) override {
        if (nodep->access().isWriteOrRW() && !m_splitVscp && nodep->varp()->attrIsolateAssign()) {
            m_splitVscp = nodep->varScopep();
        }
    }
    void visit(AstExprStmt* nodep) override {
        // A function call inside the splitting assignment
        // We need to presume the whole call is preserved (if the upper statement is)
        // This will break if the m_splitVscp is a "ref" argument to the function,
        // but little we can do.
    }
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit SplitAsFindVisitor(AstAlways* nodep) { iterate(nodep); }
    ~SplitAsFindVisitor() override = default;
    // METHODS
    AstVarScope* splitVscp() const { return m_splitVscp; }
};

//######################################################################
// Remove nodes not containing proper references

class SplitAsCleanVisitor final : public VNVisitor {
private:
    // STATE - across all visitors
    const AstVarScope* const m_splitVscp;  // Variable we want to split
    const bool m_modeMatch;  // Remove matching Vscp, else non-matching
    // STATE - for current visit position (use VL_RESTORER)
    bool m_keepStmt = false;  // Current Statement must be preserved
    bool m_matches = false;  // Statement below has matching lvalue reference

    // METHODS
    void visit(AstVarRef* nodep) override {
        if (nodep->access().isWriteOrRW()) {
            if (nodep->varScopep() == m_splitVscp) {
                UINFO(6, "       CL VAR " << nodep << endl);
                m_matches = true;
            }
        }
    }
    void visit(AstNodeStmt* nodep) override {
        UINFO(6, "     CL STMT " << nodep << endl);
        const bool oldKeep = m_keepStmt;
        {
            VL_RESTORER(m_matches);
            m_matches = false;
            m_keepStmt = false;

            iterateChildren(nodep);

            if (m_keepStmt || (m_modeMatch ? m_matches : !m_matches)) {
                UINFO(6, "     Keep   STMT " << nodep << endl);
                m_keepStmt = true;
            } else {
                UINFO(6, "     Delete STMT " << nodep << endl);
                nodep->unlinkFrBack();
                pushDeletep(nodep);
            }
        }
        // If something below matches, the upper statement remains too.
        m_keepStmt = oldKeep || m_keepStmt;
        UINFO(9, "     upKeep=" << m_keepStmt << " STMT " << nodep << endl);
    }
    void visit(AstExprStmt* nodep) override {
        // A function call inside the splitting assignment
        // We need to presume the whole call is preserved (if the upper statement is)
        // This will break if the m_splitVscp is a "ref" argument to the function,
        // but little we can do.
    }
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    SplitAsCleanVisitor(AstAlways* nodep, AstVarScope* vscp, bool modeMatch)
        : m_splitVscp{vscp}
        , m_modeMatch{modeMatch} {
        iterate(nodep);
    }
    ~SplitAsCleanVisitor() override = default;
};

//######################################################################
// SplitAs class functions

class SplitAsVisitor final : public VNVisitor {
private:
    // NODE STATE
    //  AstAlways::user()       -> bool.  True if already processed
    const VNUser1InUse m_inuser1;

    // STATE - across all visitors
    VDouble0 m_statSplits;  // Statistic tracking

    // METHODS
    void splitAlways(AstAlways* nodep, AstVarScope* splitVscp) {
        if (debug() >= 9) nodep->dumpTree("-  in: ");
        // Duplicate it and link in
        // Below cloneTree should perhaps be cloneTreePure, but given
        // isolate_assignments is required to hit this code, we presume the user
        // knows what they are asking for
        AstAlways* const newp = nodep->cloneTree(false);
        newp->user1(true);  // So we don't clone it again
        nodep->addNextHere(newp);
        {  // Delete stuff we don't want in old
            const SplitAsCleanVisitor visitor{nodep, splitVscp, false};
            if (debug() >= 9) nodep->dumpTree("-  out0: ");
        }
        {  // Delete stuff we don't want in new
            const SplitAsCleanVisitor visitor{newp, splitVscp, true};
            if (debug() >= 9) newp->dumpTree("-  out1: ");
        }
    }

    void visit(AstAlways* nodep) override {
        // Are there any lvalue references below this?
        // There could be more than one.  So, we process the first one found first.
        const AstVarScope* lastSplitVscp = nullptr;
        while (!nodep->user1()) {
            // Find any splittable variables
            const SplitAsFindVisitor visitor{nodep};
            AstVarScope* const splitVscp = visitor.splitVscp();
            // Now isolate the always
            if (splitVscp) {
                UINFO(3, "Split  " << nodep << endl);
                UINFO(3, "   For " << splitVscp << endl);
                if (splitVscp == lastSplitVscp) {
                    // We did this last time!  Something's stuck!
                    nodep->v3fatalSrc("Infinite loop in isolate_assignments removal for: "
                                      << splitVscp->prettyNameQ());
                }
                lastSplitVscp = splitVscp;
                splitAlways(nodep, splitVscp);
                ++m_statSplits;
            } else {
                nodep->user1(true);
            }
        }
    }

    void visit(AstNodeExpr*) override {}  // Accelerate
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit SplitAsVisitor(AstNetlist* nodep) { iterate(nodep); }
    ~SplitAsVisitor() override {
        V3Stats::addStat("Optimizations, isolate_assignments blocks", m_statSplits);
    }
};

//######################################################################
// SplitAs class functions

void V3SplitAs::splitAsAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    { SplitAsVisitor{nodep}; }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("splitas", 0, dumpTreeLevel() >= 3);
}
