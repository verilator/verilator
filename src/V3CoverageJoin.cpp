// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Netlist (top level) functions
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2003-2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
// COVERAGEJOIN TRANSFORMATIONS:
//      If two COVERTOGGLEs have same VARSCOPE, combine them
//      Lower the remaining COVERTOGGLEs to IFs
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3CoverageJoin.h"

#include "V3DupFinder.h"
#include "V3Stats.h"

#include <vector>

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// CoverageJoin state, as a visitor of each AstNode

class CoverageJoinVisitor final : public VNVisitor {
    // NODE STATE
    // VNUser4InUse     In V3Hasher via V3DupFinder

    // STATE - per active
    std::vector<AstCoverToggle*> m_toggleps;  // List of of all AstCoverToggle's

    // STATE - Statistic tracking
    VDouble0 m_statToggleJoins;  // Statistic tracking

    // METHODS

    void detectDuplicates() {
        UINFO(9, "Finding duplicates");
        // Note uses user4
        V3DupFinder dupFinder;  // Duplicate code detection
        // Hash all of the original signals we toggle cover
        for (const AstCoverToggle* const nodep : m_toggleps) dupFinder.insert(nodep->origp());
        if (dumpLevel() || debug() >= 9)
            dupFinder.dumpFile(v3Global.debugFilename("coveragejoin") + ".hash", false);
        // Find if there are any duplicates
        for (AstCoverToggle* nodep : m_toggleps) {
            // nodep->backp() is null if we already detected it's a duplicate and unlinked earlier
            if (!nodep->backp()) continue;
            // Want to choose a base node, and keep finding duplicates that are identical.
            // This prevents making chains where a->b, then c->d, then b->c, as we'll
            // find a->b, a->c, a->d directly.
            while (true) {
                const auto dupit = dupFinder.findDuplicate(nodep->origp());
                if (dupit == dupFinder.end()) break;
                const AstNode* const duporigp = dupit->second;
                // Remove node from comparison so don't hit it again
                dupFinder.erase(dupit);
                //
                // Note dupFinder will point to the original toggle-increment equation (what's
                // duplicated), not the covertoggle, but we need to get back to the
                // covertoggle which is immediately above, so:
                AstCoverToggle* const removep = VN_AS(duporigp->backp(), CoverToggle);
                UASSERT_OBJ(removep, nodep, "CoverageJoin duplicate of wrong type");
                UINFO(8, "  Orig " << nodep << " -->> " << nodep->incp()->declp());
                UINFO(8, "   dup " << removep << " -->> " << removep->incp()->declp());
                // The CoverDecl the duplicate pointed to now needs to point to the
                // original's data. I.e. the duplicate will get the coverage number
                // from the non-duplicate
                AstNodeCoverDecl* const datadeclp = nodep->incp()->declp()->dataDeclThisp();
                removep->incp()->declp()->dataDeclp(datadeclp);
                UINFO(8, "   new " << removep->incp()->declp());
                // Mark the found node as a duplicate of the first node
                // (Not vice-versa as we have the iterator for the found node)
                // Remove its process too, which holds nothing else
                AstAlways* const alwaysp = VN_AS(removep->backp(), Always);
                UASSERT_OBJ(!removep->nextp(), removep, "Toggle process should hold only it");
                removep->unlinkFrBack();
                VL_DO_DANGLING(pushDeletep(removep), removep);
                VL_DO_DANGLING(pushDeletep(alwaysp->unlinkFrBack()), alwaysp);
                ++m_statToggleJoins;
            }
        }
    }

    static void lower(AstCoverToggle* nodep) {
        // COVERTOGGLE(INC, ORIG, CHANGE) ->
        //   IF(ORIG ^ CHANGE) { INC; CHANGE = ORIG; }
        AstCoverInc* const incp = nodep->incp()->unlinkFrBack();
        AstNodeExpr* const origp = nodep->origp()->unlinkFrBack();
        AstNodeExpr* const changeWrp = nodep->changep()->unlinkFrBack();
        AstNodeExpr* const changeRdp = changeWrp->cloneTree(false);
        changeRdp->foreach([](AstVarRef* refp) { refp->access(VAccess::READ); });
        changeWrp->foreach([](AstVarRef* refp) { refp->varp()->setIgnoreSchedWrite(); });
        AstNodeExpr* comparedp = nullptr;
        incp->toggleExprp(origp->cloneTree(false));
        incp->toggleCovExprp(changeRdp->cloneTree(false));
        FileLine* const flp = nodep->fileline();
        // Xor will optimize better than Eq, when CoverToggle has bit selects,
        // but can only use Xor with non-opaque types
        if (const AstBasicDType* const bdtypep
            = VN_CAST(origp->dtypep()->skipRefp(), BasicDType)) {
            if (!bdtypep->isOpaque()) {
                AstNodeExpr* const zp = new AstConst{flp, AstConst::DTyped{}, origp->dtypep()};
                comparedp = new AstNeq{flp, zp, new AstXor{flp, origp, changeRdp}};
            }
        }
        if (!comparedp) comparedp = AstNeq::newTyped(flp, origp, changeRdp);
        AstIf* const newp = new AstIf{flp, comparedp, incp};
        // We could add another IF to detect posedges, and only increment if so.
        // It's another whole branch though versus a potential memory miss.
        // We'll go with the miss.
        newp->addThensp(new AstAssign{flp, changeWrp, origp->cloneTree(false)});
        nodep->replaceWith(newp);
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
    }

    // VISITORS
    void visit(AstActive* nodep) override {
        m_toggleps.clear();
        // Find all Coverage's
        iterateChildren(nodep);
        // Simplify
        detectDuplicates();
        // Lower those remaining
        for (AstCoverToggle* const togglep : m_toggleps) {
            if (togglep->backp()) lower(togglep);
        }
    }
    void visit(AstCoverToggle* nodep) override {
        m_toggleps.push_back(nodep);
        iterateChildren(nodep);
    }
    //--------------------
    void visit(AstNodeExpr*) override {}  // Accelerate
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit CoverageJoinVisitor(AstNetlist* nodep) { iterate(nodep); }
    ~CoverageJoinVisitor() override {
        V3Stats::addStat("Coverage, Toggle points joined", m_statToggleJoins);
    }
};

//######################################################################
// Coverage class functions

void V3CoverageJoin::coverageJoin(AstNetlist* rootp) {
    UINFO(2, __FUNCTION__ << ":");
    { CoverageJoinVisitor{rootp}; }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("coveragejoin", 0, dumpTreeEitherLevel() >= 3);
}
