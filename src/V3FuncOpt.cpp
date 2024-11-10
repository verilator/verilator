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
// - Balance concatenation trees, e.g.:
//    {a, {b, {c, d}}
//   becomes:
//    {{a, b}, {c, d}}
//   Reality is more complex here, see the code.
//
//*************************************************************************

#include "V3PchAstMT.h"

#include "V3FuncOpt.h"

#include "V3Global.h"
#include "V3Stats.h"
#include "V3ThreadPool.h"

VL_DEFINE_DEBUG_FUNCTIONS;

class BalanceConcatTree final {
    // STATELESS

    // We keep the expressions, together with their offsets within a concatenation tree
    struct Term final {
        AstNodeExpr* exprp = nullptr;
        size_t offset = 0;

        Term() = default;
        Term(AstNodeExpr* exprp, size_t offset)
            : exprp{exprp}
            , offset{offset} {}
    };

    // Recursive implementation of 'gatherTerms' below.
    static void gatherTermsRecursive(AstNodeExpr* exprp, std::vector<AstNodeExpr*>& terms) {
        if (AstConcat* const catp = VN_CAST(exprp, Concat)) {
            // Recursive case: gather sub terms, right to left
            gatherTermsRecursive(catp->rhsp(), terms);
            gatherTermsRecursive(catp->lhsp(), terms);
            return;
        }

        // Base case: different operation
        terms.emplace_back(exprp);
    }

    // Gather terms in the tree rooted at the given node.
    // Results are right to left, that is, index 0 in the returned vector
    // is the rightmost term, index size()-1 is the leftmost term.
    static std::vector<AstNodeExpr*> gatherTerms(AstConcat* rootp) {
        std::vector<AstNodeExpr*> terms;
        gatherTermsRecursive(rootp->rhsp(), terms);
        gatherTermsRecursive(rootp->lhsp(), terms);
        return terms;
    }

    // Construct a balanced concatenation from the given terms,
    // between indices begin (inclusive), and end (exclusive).
    // Note term[end].offset must be valid. term[end].vtxp is
    // never referenced.
    static AstNodeExpr* construct(const std::vector<Term>& terms, const size_t begin,
                                  const size_t end) {
        UASSERT(end < terms.size(), "Invalid end");
        UASSERT(begin < end, "Invalid range");
        // Base case: just return the term
        if (end == begin + 1) return terms[begin].exprp;

        // Recursive case:
        // Compute the mid-point, trying to create roughly equal width intermediates
        const size_t width = terms[end].offset - terms[begin].offset;
        const size_t midOffset = width / 2 + terms[begin].offset;
        const auto beginIt = terms.begin() + begin;
        const auto endIt = terms.begin() + end;
        const auto midIt = std::lower_bound(beginIt + 1, endIt - 1, midOffset,  //
                                            [&](const Term& term, size_t value) {  //
                                                return term.offset < value;
                                            });
        const size_t mid = begin + std::distance(beginIt, midIt);
        UASSERT(begin < mid && mid < end, "Must make some progress");
        // Construct the subtrees
        AstNodeExpr* const rhsp = construct(terms, begin, mid);
        AstNodeExpr* const lhsp = construct(terms, mid, end);
        // Construct new node
        AstNodeExpr* newp = new AstConcat{lhsp->fileline(), lhsp, rhsp};
        newp->user1(true);  // Must not attempt to balance again.
        return newp;
    }

    // Returns replacement node, or nullptr if no change
    static AstConcat* balance(AstConcat* const rootp) {
        UINFO(9, "balanceConcat " << rootp << "\n");
        // Gather all input vertices of the tree
        const std::vector<AstNodeExpr*> exprps = gatherTerms(rootp);
        // Don't bother with trivial trees
        if (exprps.size() <= 3) return nullptr;
        // Don't do it if any of the terms are impure
        for (AstNodeExpr* const exprp : exprps) {
            if (!exprp->isPure()) return nullptr;
        }

        // Construct the terms Vector that we are going to do processing on
        std::vector<Term> terms(exprps.size() + 1);
        // These are redundant (constructor does the same), but here they are for clarity
        terms[0].offset = 0;
        terms[exprps.size()].exprp = nullptr;
        for (size_t i = 0; i < exprps.size(); ++i) {
            terms[i].exprp = exprps[i]->unlinkFrBack();
            terms[i + 1].offset = terms[i].offset + exprps[i]->width();
        }

        // Round 1: try to create terms ending on VL_EDATASIZE boundaries.
        // This ensures we pack bits within a VL_EDATASIZE first is possible,
        // and then hopefully we can just assemble VL_EDATASIZE words afterward.
        std::vector<Term> terms2;
        {
            terms2.reserve(terms.size());

            size_t begin = 0;  // Start of current range considered
            size_t end = 0;  // End of current range considered
            size_t offset = 0;  // Offset of current range considered

            // Create a term from the current range
            const auto makeTerm = [&]() {
                AstNodeExpr* const exprp = construct(terms, begin, end);
                terms2.emplace_back(exprp, offset);
                offset += exprp->width();
                begin = end;
            };

            // Create all terms ending on a boundary.
            while (++end < terms.size() - 1) {
                if (terms[end].offset % VL_EDATASIZE == 0) makeTerm();
            }
            // Final term. Loop condition above ensures this always exists,
            // and might or might not be on a boundary.
            makeTerm();
            // Sentinel term
            terms2.emplace_back(nullptr, offset);
            // should have ended up with the same number of bits at least...
            UASSERT(terms2.back().offset == terms.back().offset, "Inconsitent terms");
        }

        // Round 2: Combine the partial terms
        return VN_AS(construct(terms2, 0, terms2.size() - 1), Concat);
    }

public:
    static AstConcat* apply(AstConcat* rootp) { return balance(rootp); }
};

class FuncOptVisitor final : public VNVisitor {
    // NODE STATE
    //  AstNodeAssign::user()     -> bool.  Already checked, safe to split. Omit expensive check.
    //  AstConcat::user()         -> bool.  Already balanced.

    // STATE - Statistic tracking
    VDouble0 m_balancedConcats;  // Number of concatenations balanced
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
        iterateChildren(nodep);

        if (v3Global.opt.fFuncSplitCat()) {
            if (splitConcat(nodep)) return;  // Must return here, in case more code is added below
        }
    }

    void visit(AstConcat* nodep) override {
        if (v3Global.opt.fFuncBalanceCat() && !nodep->user1() && !VN_IS(nodep->backp(), Concat)) {
            if (AstConcat* const newp = BalanceConcatTree::apply(nodep)) {
                UINFO(5, "balanceConcat optimizing " << nodep << "\n");
                ++m_balancedConcats;
                nodep->replaceWith(newp);
                VL_DO_DANGLING(pushDeletep(nodep), nodep);
                newp->user1(true);  // Must not attempt again.
                // Return here. The new node will be iterated next.
                return;
            }
        }
        iterateChildren(nodep);
    }

    void visit(AstNode* nodep) override { iterateChildren(nodep); }

    // CONSTRUCTORS
    explicit FuncOptVisitor(AstCFunc* funcp) { iterateChildren(funcp); }
    ~FuncOptVisitor() override {
        V3Stats::addStatSum("Optimizations, FuncOpt concat trees balanced", m_balancedConcats);
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
