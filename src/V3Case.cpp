// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Break case statements up and add Unknown assigns
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2026 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
// V3Case's Transformations:
//
// Each module:
//      TBD: Eliminate tristates by adding __in, __inen, __en wires in parallel
//          Need __en in changed list if a signal is on the LHS of a assign
//      Cases:
//          CASE(v) CASEITEM(items,body) ->  IF (OR (EQ (AND v mask)
//                                                      (AND item1 mask))
//                                                  (other items))
//                                              body
//              Or, converts to a if/else tree.
//      FUTURES:
//          Large 16+ bit tables with constants and no masking (address muxes)
//              Enter all into std::multimap, sort by value and use a tree of < and == compares.
//          "Diagonal" find of {rightmost,leftmost} bit {set,clear}
//              Ignoring mask, check each value is unique (using std::multimap as above?)
//              Each branch is then mask-and-compare operation (IE
//              <000000001_000000000 at midpoint.)
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Case.h"

#include "V3Stats.h"

VL_DEFINE_DEBUG_FUNCTIONS;

#define CASE_OVERLAP_WIDTH 16  // Maximum width we can check for overlaps in
#define CASE_BARF 999999  // Magic width when non-constant
#define CASE_ENCODER_GROUP_DEPTH 8  // Levels of priority to be ORed together in top IF tree

//######################################################################

class CaseLintVisitor final : public VNVisitorConst {
    // Under a CASE value node, if so the relevant case statement
    const AstNode* m_casep = nullptr;

    // METHODS
    template <typename CaseItem>
    static void detectMultipleDefaults(CaseItem* itemsp) {
        bool hitDefault = false;
        for (CaseItem* itemp = itemsp; itemp; itemp = AstNode::as<CaseItem>(itemp->nextp())) {
            if (!itemp->isDefault()) continue;
            if (hitDefault) itemp->v3error("Multiple default statements in case statement.");
            hitDefault = true;
        }
    }

    template <typename CaseItem>
    void checkXZinNonCaseX(AstNode* casep, AstNodeExpr* exprp, CaseItem* itemsp) {
        VL_RESTORER(m_casep);
        m_casep = casep;
        iterateConst(exprp);
        for (CaseItem* itemp = itemsp; itemp; itemp = AstNode::as<CaseItem>(itemp->nextp())) {
            iterateAndNextConstNull(itemp->condsp());
        }
    }

    // VISITORS
    void visit(AstGenCase* nodep) override {
        // Detect multiple defaults
        detectMultipleDefaults(nodep->itemsp());
        // Check for X/Z in non-casex statements
        checkXZinNonCaseX(nodep, nodep->exprp(), nodep->itemsp());
    }

    void visit(AstCase* nodep) override {
        if (nodep->casex()) {
            nodep->v3warn(CASEX, "Suggest casez (with ?'s) in place of casex (with X's)");
        }
        // Detect multiple defaults
        detectMultipleDefaults(nodep->itemsp());
        // Check for X/Z in non-casex statements
        checkXZinNonCaseX(nodep, nodep->exprp(), nodep->itemsp());
    }
    void visit(AstConst* nodep) override {
        if (!nodep->num().isFourState()) return;

        // Error if generate case
        if (VN_IS(m_casep, GenCase)) {
            nodep->v3error("Use of x/? constant in generate case statement, "
                           "(no such thing as 'generate casez')");
            return;
        }

        // Otherwise must be a case statement
        const AstCase* const casep = VN_AS(m_casep, Case);

        // Don't sweat it, we already complained about casex in general
        if (casep->casex()) return;

        if (casep->casez() || casep->caseInside()) {
            if (nodep->num().isAnyX()) {
                nodep->v3warn(CASEWITHX, "Use of x constant in casez statement, "
                                         "(perhaps intended ?/z in constant)");
            }
            return;
        }

        nodep->v3warn(CASEWITHX, "Use of x/? constant in case statement, "
                                 "(perhaps intended casex/casez)");
    }
    void visit(AstNode* nodep) override { iterateChildrenConst(nodep); }

public:
    // CONSTRUCTORS
    explicit CaseLintVisitor(AstCase* nodep) { iterateConst(nodep); }
    explicit CaseLintVisitor(AstGenCase* nodep) { iterateConst(nodep); }
    ~CaseLintVisitor() override = default;
};

//######################################################################
// Case state, as a visitor of each AstNode

class CaseVisitor final : public VNVisitor {
    // NODE STATE
    // Cleared each Case
    //  AstIf::user3()          -> bool.  Set true to indicate clone not needed
    const VNUser3InUse m_inuser3;

    // STATE
    VDouble0 m_statCaseFast;  // Statistic tracking
    VDouble0 m_statCaseSlow;  // Statistic tracking
    const AstNode* m_alwaysp = nullptr;  // Always in which case is located

    // Per-CASE
    int m_caseWidth = 0;  // Width of valueItems
    int m_caseItems = 0;  // Number of caseItem unique values
    bool m_caseIncomplete = false;  // Proven incomplete
    bool m_caseNoOverlapsAllCovered = false;  // Proven to be synopsys parallel_case compliant
    // For each possible value, the case branch we need
    std::array<AstNode*, 1 << CASE_OVERLAP_WIDTH> m_valueItem;
    bool m_needToClearCache = false;  // Whether cache needs to be cleared

    // METHODS
    //! Determine whether we should check case items are complete
    //! @return  Enum's dtype if should check, nullptr if shouldn't
    const AstEnumDType* getEnumCompletionCheckDType(const AstCase* const nodep) {
        if (!nodep->uniquePragma() && !nodep->unique0Pragma()) return nullptr;
        const AstEnumDType* const enumDtp
            = VN_CAST(nodep->exprp()->dtypep()->skipRefToEnump(), EnumDType);
        if (!enumDtp) return nullptr;  // Case isn't enum
        const AstBasicDType* const basicp = enumDtp->subDTypep()->basicp();
        if (!basicp) return nullptr;  // Not simple type (perhaps IEEE illegal)
        if (basicp->width() > 32) return nullptr;
        return enumDtp;
    }
    //! @return  True if case items are complete, false if there are uncovered enums
    bool checkCaseEnumComplete(const AstCase* const nodep, const AstEnumDType* const dtype) {
        const uint32_t numCases = 1UL << m_caseWidth;
        for (AstEnumItem* itemp = dtype->itemsp(); itemp;
             itemp = VN_AS(itemp->nextp(), EnumItem)) {
            AstConst* const econstp = VN_AS(itemp->valuep(), Const);
            V3Number nummask{itemp, econstp->width()};
            nummask.opBitsNonX(econstp->num());
            const uint32_t mask = nummask.toUInt();
            V3Number numval{itemp, econstp->width()};
            numval.opBitsOne(econstp->num());
            const uint32_t val = numval.toUInt();

            for (uint32_t i = 0; i < numCases; ++i) {
                if ((i & mask) == val) {
                    if (!m_valueItem[i]) {
                        nodep->v3warn(CASEINCOMPLETE, "Enum item " << itemp->prettyNameQ()
                                                                   << " not covered by case\n");
                        m_caseIncomplete = true;
                        return false;  // enum has uncovered value by case items
                    }
                }
            }
        }
        return true;  // enum is fully covered
    }
    bool isCaseTreeFast(AstCase* nodep) {
        int width = 0;
        bool opaque = false;
        m_caseItems = 0;
        m_caseNoOverlapsAllCovered = true;
        for (AstCaseItem* itemp = nodep->itemsp(); itemp;
             itemp = VN_AS(itemp->nextp(), CaseItem)) {
            for (AstNode* icondp = itemp->condsp(); icondp; icondp = icondp->nextp()) {
                if (icondp->width() > width) width = icondp->width();
                if (icondp->isDouble()) opaque = true;
                if (!VN_IS(icondp, Const)) width = CASE_BARF;  // Can't parse; not a constant
                m_caseItems++;
            }
        }
        m_caseWidth = width;
        if (width == 0 || width > CASE_OVERLAP_WIDTH || opaque) {
            m_caseNoOverlapsAllCovered = false;
            return false;  // Too wide for analysis
        }
        UINFO(8, "Simple case statement: " << nodep);
        const uint32_t numCases = 1UL << m_caseWidth;
        // Zero list of items for each value
        for (uint32_t i = 0; i < numCases; ++i) m_valueItem[i] = nullptr;
        // Now pick up the values for each assignment
        // We can cheat and use uint32_t's because we only support narrow case's
        bool reportedOverlap = false;
        bool reportedSubcase = false;
        bool hasDefaultCase = false;
        std::map<AstNode*, AstCaseItem*> caseItemMap;  // case condition -> case item
        for (AstCaseItem* itemp = nodep->itemsp(); itemp;
             itemp = VN_AS(itemp->nextp(), CaseItem)) {
            for (AstNode* icondp = itemp->condsp(); icondp; icondp = icondp->nextp()) {
                // UINFOTREE(9, icondp, "", "caseitem");
                AstConst* const iconstp = VN_AS(icondp, Const);
                UASSERT_OBJ(iconstp, nodep, "above 'can't parse' should have caught this");
                if (neverItem(nodep, iconstp)) {
                    // X in casez can't ever be executed
                } else {
                    const bool isCondWildcard = iconstp->num().isAnyXZ();
                    V3Number nummask{itemp, iconstp->width()};
                    nummask.opBitsNonX(iconstp->num());
                    const uint32_t mask = nummask.toUInt();
                    V3Number numval{itemp, iconstp->width()};
                    numval.opBitsOne(iconstp->num());
                    const uint32_t val = numval.toUInt();

                    uint32_t firstOverlap = 0;
                    const AstNode* overlappedCondp = nullptr;
                    bool foundHit = false;
                    for (uint32_t i = 0; i < numCases; ++i) {
                        if ((i & mask) == val) {
                            if (!m_valueItem[i]) {
                                m_valueItem[i] = icondp;
                                caseItemMap[icondp] = itemp;
                                foundHit = true;
                            } else if (!overlappedCondp) {
                                // Overlapping case item expressions in the
                                // same case item are legal
                                if (caseItemMap[m_valueItem[i]] != itemp) {
                                    firstOverlap = i;
                                    overlappedCondp = m_valueItem[i];
                                    m_caseNoOverlapsAllCovered = false;
                                }
                            }
                        }
                    }
                    if (!nodep->priorityPragma()) {
                        // If this case statement doesn't have the priority
                        // keyword, we want to warn on any overlap.
                        if (!reportedOverlap && overlappedCondp) {
                            std::ostringstream examplePattern;
                            if (isCondWildcard) {
                                examplePattern << " (example pattern 0x" << std::hex
                                               << firstOverlap << ")";
                            }
                            icondp->v3warn(CASEOVERLAP,
                                           "Case conditions overlap"
                                               << examplePattern.str() << "\n"
                                               << icondp->warnContextPrimary() << '\n'
                                               << overlappedCondp->warnOther()
                                               << "... Location of overlapping condition\n"
                                               << overlappedCondp->warnContextSecondary());
                            reportedOverlap = true;
                        }
                    } else {
                        // If this is a priority case, we only want to complain
                        // if every possible value for this item is already hit
                        // by some other item. This is true if foundHit is
                        // false.
                        if (!reportedSubcase && !foundHit) {
                            icondp->v3warn(CASEOVERLAP,
                                           "Case item ignored: every matching value is covered "
                                           "by an earlier condition\n"
                                               << icondp->warnContextPrimary() << '\n'
                                               << overlappedCondp->warnOther()
                                               << "... Location of previous condition\n"
                                               << overlappedCondp->warnContextPrimary());
                            reportedSubcase = true;
                        }
                    }
                }
            }
            // Defaults were moved to last in the caseitem list by V3LinkDot
            if (itemp->isDefault()) {  // Case statement's default... Fill the table
                for (uint32_t i = 0; i < numCases; ++i) {
                    if (!m_valueItem[i]) m_valueItem[i] = itemp;
                }
                caseItemMap[itemp] = itemp;
                hasDefaultCase = true;
            }
        }
        if (!hasDefaultCase) {
            const AstEnumDType* const dtype = getEnumCompletionCheckDType(nodep);
            if (dtype) {
                if (!checkCaseEnumComplete(nodep, dtype)) {
                    // checkCaseEnumComplete has already warned of incompletion
                    m_caseNoOverlapsAllCovered = false;
                    return false;
                }
            } else {
                for (uint32_t i = 0; i < numCases; ++i) {
                    if (!m_valueItem[i]) {  // has uncovered case
                        nodep->v3warn(CASEINCOMPLETE, "Case values incompletely covered "
                                                      "(example pattern 0x"
                                                          << std::hex << i << ")");
                        m_caseIncomplete = true;
                        m_caseNoOverlapsAllCovered = false;
                        return false;
                    }
                }
            }
        }

        if (m_caseItems <= 3
            // Avoid e.g. priority expanders from going crazy in expansion
            || (m_caseWidth >= 8 && (m_caseItems <= (m_caseWidth + 1)))) {
            return false;  // Not worth simplifying
        }

        // Convert valueItem from AstCaseItem* to the expression
        // Not done earlier, as we may now have a nullptr because it's just a ";" NOP branch
        for (uint32_t i = 0; i < numCases; ++i) {
            if (AstNode* const condp = m_valueItem[i]) {
                const AstCaseItem* const caseItemp = caseItemMap[condp];
                UASSERT_OBJ(caseItemp, condp, "caseItemp should exist");
                m_valueItem[i] = caseItemp->stmtsp();
            }
        }
        return true;  // All is fine
    }

    AstNode* replaceCaseFastRecurse(AstNodeExpr* cexprp, int msb, uint32_t upperValue) {
        if (msb < 0) {
            // There's no space for a IF.  We know upperValue is thus down to a specific
            // exact value, so just return the tree value
            // Note can't clone here, as we're going to check for equivalence above
            AstNode* const foundp = m_valueItem[upperValue];
            return foundp;
        } else {
            // Make left and right subtrees
            // cexpr[msb:lsb] == 1
            AstNode* tree0p = replaceCaseFastRecurse(cexprp, msb - 1, upperValue);
            AstNode* tree1p = replaceCaseFastRecurse(
                cexprp, msb - 1, upperValue | (1UL << static_cast<uint32_t>(msb)));

            if (tree0p == tree1p) {
                // Same logic on both sides, so we can just return one of 'em
                return tree0p;
            }
            // We could have a "checkerboard" with A B A B, we can use the same IF on both edges
            bool same = true;
            for (uint32_t a = upperValue, b = (upperValue | (1UL << msb));
                 a < (upperValue | (1UL << msb)); a++, b++) {
                if (m_valueItem[a] != m_valueItem[b]) {
                    same = false;
                    break;
                }
            }
            if (same) {
                VL_DO_DANGLING(tree1p->deleteTree(), tree1p);
                return tree0p;
            }

            // Must have differing logic, so make a selection

            // Case expressions can't be linked twice, so clone them
            if (tree0p && !tree0p->user3()) tree0p = tree0p->cloneTree(true);
            if (tree1p && !tree1p->user3()) tree1p = tree1p->cloneTree(true);

            // Alternate scheme if we ever do multiple bits at a time:
            // V3Number nummask (cexprp, cexprp->width(), (1UL<<msb));
            // AstNode* and1p = new AstAnd(cexprp->fileline(), cexprp->cloneTreePure(false),
            //                            new AstConst(cexprp->fileline(), nummask));
            AstNodeExpr* const and1p
                = new AstSel{cexprp->fileline(), cexprp->cloneTreePure(false), msb, 1};
            AstNodeExpr* const eqp
                = new AstNeq{cexprp->fileline(), new AstConst{cexprp->fileline(), 0}, and1p};
            AstIf* const ifp = new AstIf{cexprp->fileline(), eqp, tree1p, tree0p};
            ifp->user3(1);  // So we don't bother to clone it
            return ifp;
        }
    }

    void replaceCaseFast(AstCase* nodep) {
        // CASEx(cexpr,....
        // ->  tree of IF(msb,  IF(msb-1, 11, 10)
        //                      IF(msb-1, 01, 00))
        AstNodeExpr* cexprp;
        AstExprStmt* cexprStmtp = nullptr;
        if (nodep->exprp()->isPure()) {
            cexprp = nodep->exprp()->unlinkFrBack();
        } else {
            cexprStmtp = VN_AS(nodep->exprp()->unlinkFrBack(), ExprStmt);
            cexprp = cexprStmtp->resultp()->cloneTreePure(false);
        }

        if (debug() >= 9) {  // LCOV_EXCL_START
            for (uint32_t i = 0; i < (1UL << m_caseWidth); ++i) {
                if (const AstNode* const itemp = m_valueItem[i]) {
                    UINFO(9, "Value " << std::hex << i << " " << itemp);
                }
            }
        }  // LCOV_EXCL_STOP

        // Handle any assertions
        replaceCaseParallel(nodep, m_caseNoOverlapsAllCovered);

        AstNode::user3ClearTree();
        AstNode* ifrootp = replaceCaseFastRecurse(cexprp, m_caseWidth - 1, 0UL);
        if (cexprStmtp) {
            cexprStmtp->resultp()->unlinkFrBack()->deleteTree();
            AstIf* const ifp = VN_AS(ifrootp, If);
            cexprStmtp->resultp(ifp->condp()->unlinkFrBack());
            ifp->condp(cexprStmtp);
            m_needToClearCache = true;
        }

        // Case expressions can't be linked twice, so clone them
        if (ifrootp && !ifrootp->user3()) ifrootp = ifrootp->cloneTree(true);

        if (ifrootp) {
            nodep->replaceWith(ifrootp);
        } else {
            nodep->unlinkFrBack();
        }
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
        VL_DO_DANGLING(cexprp->deleteTree(), cexprp);
        UINFOTREE(9, ifrootp, "", "_simp");
    }

    void replaceCaseComplicated(AstCase* nodep) {
        // CASEx(cexpr,ITEM(icond1,istmts1),ITEM(icond2,istmts2),ITEM(default,istmts3))
        // ->  IF((cexpr==icond1),istmts1,
        //                       IF((EQ (AND MASK cexpr) (AND MASK icond1)
        //                              ,istmts2, istmts3
        AstNodeExpr* cexprp;
        AstExprStmt* cexprStmtp = nullptr;
        if (nodep->exprp()->isPure()) {
            cexprp = nodep->exprp()->unlinkFrBack();
        } else {
            cexprStmtp = VN_AS(nodep->exprp(), ExprStmt)->unlinkFrBack();
            cexprp = cexprStmtp->resultp()->cloneTreePure(false);
        }
        // We'll do this in two stages.  First stage, convert the conditions to
        // the appropriate IF AND terms.
        UINFOTREE(9, nodep, "", "_comp_IN::");
        bool hadDefault = false;
        for (AstCaseItem* itemp = nodep->itemsp(); itemp;
             itemp = VN_AS(itemp->nextp(), CaseItem)) {
            if (!itemp->condsp()) {
                // Default clause.  Just make true, we'll optimize it away later
                itemp->addCondsp(new AstConst{itemp->fileline(), AstConst::BitTrue{}});
                hadDefault = true;
            } else {
                // Expressioned clause
                AstNodeExpr* icondNextp = nullptr;
                AstNodeExpr* ifexprp = nullptr;  // If expression to test
                for (AstNodeExpr* icondp = itemp->condsp(); icondp; icondp = icondNextp) {
                    icondNextp = VN_AS(icondp->nextp(), NodeExpr);
                    icondp->unlinkFrBack();

                    AstNodeExpr* condp = nullptr;  // Default is to use and1p/and2p
                    AstConst* const iconstp = VN_CAST(icondp, Const);
                    if (iconstp && neverItem(nodep, iconstp)) {
                        // X in casez can't ever be executed
                        VL_DO_DANGLING(icondp->deleteTree(), icondp);
                        VL_DANGLING(iconstp);
                        // For simplicity, make expression that is not equal, and let later
                        // optimizations remove it
                        condp = new AstConst{itemp->fileline(), AstConst::BitFalse{}};
                    } else if (AstInsideRange* const irangep = VN_CAST(icondp, InsideRange)) {
                        // Similar logic in V3Width::visit(AstInside)
                        condp = irangep->newAndFromInside(cexprp->cloneTreePure(true),
                                                          irangep->lhsp()->unlinkFrBack(),
                                                          irangep->rhsp()->unlinkFrBack());
                        VL_DO_DANGLING2(icondp->deleteTree(), icondp, irangep);
                    } else if (iconstp && iconstp->num().isFourState()
                               && (nodep->casex() || nodep->casez() || nodep->caseInside())) {
                        V3Number nummask{itemp, iconstp->width()};
                        nummask.opBitsNonX(iconstp->num());
                        V3Number numval{itemp, iconstp->width()};
                        numval.opBitsOne(iconstp->num());
                        AstNodeExpr* const and1p
                            = new AstAnd{itemp->fileline(), cexprp->cloneTreePure(false),
                                         new AstConst{itemp->fileline(), nummask}};
                        AstNodeExpr* const and2p = new AstAnd{
                            itemp->fileline(), new AstConst{itemp->fileline(), numval},
                            new AstConst{itemp->fileline(), nummask}};
                        VL_DO_DANGLING(icondp->deleteTree(), icondp);
                        VL_DANGLING(iconstp);
                        condp = AstEq::newTyped(itemp->fileline(), and1p, and2p);
                    } else {
                        // Not a caseX mask, we can build CASEEQ(cexpr icond)
                        AstNodeExpr* const and1p = cexprp->cloneTreePure(false);
                        AstNodeExpr* const and2p = icondp;
                        condp = AstEq::newTyped(itemp->fileline(), and1p, and2p);
                    }
                    if (!ifexprp) {
                        ifexprp = condp;
                    } else {
                        ifexprp = new AstLogOr{itemp->fileline(), ifexprp, condp};
                    }
                }
                // Replace expression in tree
                itemp->addCondsp(ifexprp);
            }
        }
        VL_DO_DANGLING(cexprp->deleteTree(), cexprp);
        if (!hadDefault) {
            // If there was no default, add a empty one, this greatly simplifies below code
            // and constant propagation will just eliminate it for us later.
            nodep->addItemsp(new AstCaseItem{
                nodep->fileline(), new AstConst{nodep->fileline(), AstConst::BitTrue{}}, nullptr});
        }
        UINFOTREE(9, nodep, "", "_comp_COND");
        // Now build the IF statement tree
        // The tree can be quite huge.  Pull ever group of 8 out, and make a OR tree.
        // This reduces the depth for the bottom elements, at the cost of
        // some of the top elements.  If we ever have profiling data, we
        // should pull out the most common item from here and instead make
        // it the first IF branch.
        int depth = 0;
        AstIf* grouprootp = nullptr;
        AstIf* groupnextp = nullptr;
        AstIf* itemnextp = nullptr;
        for (AstCaseItem* itemp = nodep->itemsp(); itemp;
             itemp = VN_AS(itemp->nextp(), CaseItem)) {
            AstNode* const istmtsp = itemp->stmtsp();  // Maybe null -- no action.
            if (istmtsp) istmtsp->unlinkFrBackWithNext();
            // Expressioned clause
            AstNodeExpr* const ifexprp = itemp->condsp()->unlinkFrBack();
            {  // Prepare for next group
                if (++depth > CASE_ENCODER_GROUP_DEPTH) depth = 1;
                if (depth == 1) {  // First group or starting new group
                    itemnextp = nullptr;
                    AstIf* const newp = new AstIf{itemp->fileline(), ifexprp->cloneTreePure(true)};
                    if (groupnextp) {
                        groupnextp->addElsesp(newp);
                    } else {
                        grouprootp = newp;
                    }
                    groupnextp = newp;
                } else {  // Continue group, modify if condition to OR in this new condition
                    AstNodeExpr* const condp = groupnextp->condp()->unlinkFrBack();
                    groupnextp->condp(
                        new AstOr{ifexprp->fileline(), condp, ifexprp->cloneTreePure(true)});
                }
            }
            {  // Make the new lower IF and attach in the tree
                AstNodeExpr* itemexprp = ifexprp;
                VL_DANGLING(ifexprp);
                if (depth == CASE_ENCODER_GROUP_DEPTH) {  // End of group - can skip the condition
                    VL_DO_DANGLING(itemexprp->deleteTree(), itemexprp);
                    itemexprp = new AstConst{itemp->fileline(), AstConst::BitTrue{}};
                }
                AstIf* const newp = new AstIf{itemp->fileline(), itemexprp, istmtsp};
                if (itemnextp) {
                    itemnextp->addElsesp(newp);
                } else {
                    groupnextp->addThensp(newp);  // First in a new group
                }
                itemnextp = newp;
            }
        }
        UINFOTREE(9, nodep, "", "_comp_TREE");
        // Handle any assertions
        replaceCaseParallel(nodep, false);
        // Replace the CASE... with IF...
        if (grouprootp) {
            UINFOTREE(9, grouprootp, "", "_new");
            nodep->replaceWith(grouprootp);
            if (cexprStmtp) {
                pushDeletep(cexprStmtp->resultp()->unlinkFrBack());
                cexprStmtp->resultp(grouprootp->condp()->unlinkFrBack());
                grouprootp->condp(cexprStmtp);
                m_needToClearCache = true;
            }
        } else {
            nodep->unlinkFrBack();
        }
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
    }

    void replaceCaseParallel(AstCase* nodep, bool noOverlapsAllCovered) {
        // Take the notParallelp tree under the case statement created by V3Assert
        // If the statement was proven to have no overlaps and all cases
        // covered, we're done with it.
        // Else, convert to a normal statement parallel with the case statement.
        if (nodep->notParallelp() && !noOverlapsAllCovered) {
            AstNode* const parp = nodep->notParallelp()->unlinkFrBackWithNext();
            nodep->addNextHere(parp);
        }
    }

    bool neverItem(const AstCase* casep, const AstConst* itemp) {
        // Xs in case or casez are impossible due to two state simulations
        if (casep->casex()) {
        } else if (casep->casez() || casep->caseInside()) {
            if (itemp->num().isAnyX()) return true;
        } else {
            if (itemp->num().isFourState()) return true;
        }
        return false;
    }

    // VISITORS
    void visit(AstCase* nodep) override {
        VL_RESTORER(m_caseIncomplete);
        { CaseLintVisitor{nodep}; }
        iterateChildren(nodep);
        UINFOTREE(9, nodep, "", "case_old");
        if (isCaseTreeFast(nodep) && v3Global.opt.fCase()) {
            // It's a simple priority encoder or complete statement
            // we can make a tree of statements to avoid extra comparisons
            ++m_statCaseFast;
            VL_DO_DANGLING(replaceCaseFast(nodep), nodep);
        } else {
            // If a case statement is whole, presume signals involved aren't forming a latch
            if (m_alwaysp && !m_caseIncomplete)
                m_alwaysp->fileline()->warnOff(V3ErrorCode::LATCH, true);
            ++m_statCaseSlow;
            VL_DO_DANGLING(replaceCaseComplicated(nodep), nodep);
        }
    }
    //--------------------
    void visit(AstAlways* nodep) override {
        VL_RESTORER(m_alwaysp);
        m_alwaysp = nodep;
        iterateChildren(nodep);
    }
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit CaseVisitor(AstNetlist* nodep) {
        for (auto& itr : m_valueItem) itr = nullptr;
        iterate(nodep);
        if (m_needToClearCache) VIsCached::clearCacheTree();
    }
    ~CaseVisitor() override {
        V3Stats::addStat("Optimizations, Cases parallelized", m_statCaseFast);
        V3Stats::addStat("Optimizations, Cases complex", m_statCaseSlow);
    }
};

//######################################################################
// Case class functions

void V3Case::caseAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ":");
    { CaseVisitor{nodep}; }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("case", 0, dumpTreeEitherLevel() >= 3);
}
void V3Case::caseLint(AstGenCase* nodep) {
    UINFO(4, __FUNCTION__ << ": ");
    { CaseLintVisitor{nodep}; }
}
