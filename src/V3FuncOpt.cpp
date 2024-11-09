// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Generic optimizations on a per function basis
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
//
// - Split assignments to wide locations with Concat on the RHS
//   at word boundaries:
//    foo = {l, r};
//   becomes (recursively):
//    foo[_:_] = r;
//    foo[_:_] = l;
//
//*************************************************************************

#include "V3PchAstMT.h"

#include "V3FuncOpt.h"

#include "V3Global.h"
#include "V3Stats.h"
#include "V3ThreadPool.h"

VL_DEFINE_DEBUG_FUNCTIONS;

class FuncOptVisitor final : public VNVisitor {
    // NODE STATE
    //  AstNodeAssign::user()     -> bool.  Already checked, safe to split. Omit expensive check.

    // STATE - Statistic tracking
    VDouble0 m_concatSplits;  // Number of splits in assignments with Concat on RHS

    // True for e.g.: foo = foo >> 1; or foo[foo[0]] = ...;
    static bool readsLhs(AstNodeAssign* nodep) {
        // It is expected that the number of vars written on the LHS is very small (should be 1).
        std::unordered_set<const AstVar*> lhsWrVarps;
        std::unordered_set<const AstVar*> lhsRdVarps;
        nodep->lhsp()->foreach([&](const AstVarRef* refp) {
            if (refp->access().isWriteOrRW()) lhsWrVarps.emplace(refp->varp());
            if (refp->access().isReadOrRW()) lhsRdVarps.emplace(refp->varp());
        });

        // Common case of 1 variable on the LHS - special handling for speed
        if (lhsWrVarps.size() == 1) {
            const AstVar* const lhsWrVarp = *lhsWrVarps.begin();
            // Check Rhs doesn't read the written var
            const bool rhsReadsWritten = nodep->rhsp()->exists([=](const AstVarRef* refp) {  //
                return refp->varp() == lhsWrVarp;
            });
            if (rhsReadsWritten) return true;
            // Check Lhs doesn't read the written var
            return lhsRdVarps.count(lhsWrVarp);
        }

        // Generic case of multiple vars written on LHS
        // TODO: this might be impossible due to earlier transforms, not sure
        // Check Rhs doesn't read the written vars
        const bool rhsReadsWritten = nodep->rhsp()->exists([&](const AstVarRef* refp) {  //
            return lhsWrVarps.count(refp->varp());
        });
        if (rhsReadsWritten) return true;
        // Check Lhs doesn't read the written vars
        for (const AstVar* const lhsWrVarp : lhsWrVarps) {
            if (lhsRdVarps.count(lhsWrVarp)) return true;
        }
        return false;
    }

    // METHODS
    // Split wide assignments with a wide concatenation on the RHS.
    // Returns true if 'nodep' was deleted
    bool splitConcat(AstNodeAssign* nodep) {
        UINFO(9, "splitConcat " << nodep << "\n");
        // Only care about concatenations on the right
        AstConcat* const rhsp = VN_CAST(nodep->rhsp(), Concat);
        if (!rhsp) return false;
        // Will need the LHS
        AstNodeExpr* lhsp = nodep->lhsp();
        UASSERT_OBJ(lhsp->width() == rhsp->width(), nodep, "Inconsistent assignment");
        // Only consider pure assignments. Nodes inserted below are safe.
        if (!nodep->user1() && (!lhsp->isPure() || !rhsp->isPure())) return false;
        // Check for a Sel on the LHS if present, and skip over it
        uint32_t lsb = 0;
        if (AstSel* const selp = VN_CAST(lhsp, Sel)) {
            if (AstConst* const lsbp = VN_CAST(selp->lsbp(), Const)) {
                lhsp = selp->fromp();
                lsb = lsbp->toUInt();
            } else {
                // Don't optimize if it's a variable select
                return false;
            }
        }
        // No need to split assignments targeting storage smaller than a machine register
        if (lhsp->width() <= VL_QUADSIZE) return false;

        // If it's a concat straddling a word boundary, try to split it.
        // The next visit on the new nodes will split it recursively.
        // Otherwise, keep the original assignment.
        const int lsbWord = lsb / VL_EDATASIZE;
        const int msbWord = (lsb + rhsp->width() - 1) / VL_EDATASIZE;
        if (lsbWord == msbWord) return false;

        // If the RHS reads the LHS, we can't actually do this. Nodes inserted below are safe.
        if (!nodep->user1() && readsLhs(nodep)) return false;

        // Ok, actually split it now
        UINFO(5, "splitConcat optimizing " << nodep << "\n");
        ++m_concatSplits;
        // The 2 parts and their offsets
        AstNodeExpr* const rrp = rhsp->rhsp()->unlinkFrBack();
        AstNodeExpr* const rlp = rhsp->lhsp()->unlinkFrBack();
        const int rLsb = lsb;
        const int lLsb = lsb + rrp->width();
        // Insert the 2 assignment right after the original. They will be visited next.
        AstAssign* const arp = new AstAssign{
            nodep->fileline(),
            new AstSel{lhsp->fileline(), lhsp->cloneTreePure(false), rLsb, rrp->width()}, rrp};
        AstAssign* const alp = new AstAssign{
            nodep->fileline(),
            new AstSel{lhsp->fileline(), lhsp->unlinkFrBack(), lLsb, rlp->width()}, rlp};
        nodep->addNextHere(arp);
        arp->addNextHere(alp);
        // Safe to split these.
        arp->user1(true);
        alp->user1(true);
        // Nuke what is left
        VL_DO_DANGLING(pushDeletep(nodep->unlinkFrBack()), nodep);
        return true;
    }

    // VISIT
    void visit(AstNodeAssign* nodep) override {
        // TODO: Only thing remaining inside functions should be AstAssign (that is, an actual
        //       assignment statemant), but we stil use AstAssignW, AstAssignDly, and all, fix.
        if (v3Global.opt.fFuncSplitCat()) {
            if (splitConcat(nodep)) return;  // Must return here, in case more code is added below
        }
    }

    void visit(AstNodeExpr*) override {}  // No need to descend further (Ignore AstExprStmt...)

    void visit(AstNode* nodep) override { iterateChildren(nodep); }

    // CONSTRUCTORS
    explicit FuncOptVisitor(AstCFunc* funcp) { iterateChildren(funcp); }
    ~FuncOptVisitor() override {
        V3Stats::addStatSum("Optimizations, FuncOpt concat splits", m_concatSplits);
    }

public:
    static void apply(AstCFunc* funcp) { FuncOptVisitor{funcp}; }
};

//######################################################################

void V3FuncOpt::funcOptAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    {
        const VNUser1InUse user1InUse;
        V3ThreadScope threadScope;
        for (AstNodeModule *modp = nodep->modulesp(), *nextModp; modp; modp = nextModp) {
            nextModp = VN_AS(modp->nextp(), NodeModule);
            for (AstNode *nodep = modp->stmtsp(), *nextNodep; nodep; nodep = nextNodep) {
                nextNodep = nodep->nextp();
                if (AstCFunc* const cfuncp = VN_CAST(nodep, CFunc)) {
                    threadScope.enqueue([cfuncp]() { FuncOptVisitor::apply(cfuncp); });
                }
            }
        }
    }
    V3Global::dumpCheckGlobalTree("funcopt", 0, dumpTreeEitherLevel() >= 3);
}
