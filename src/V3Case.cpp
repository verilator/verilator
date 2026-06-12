// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Break case statements up and add Unknown assigns
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

    // CONSTRUCTORS
    explicit CaseLintVisitor(AstCase* nodep) { iterateConst(nodep); }
    explicit CaseLintVisitor(AstGenCase* nodep) { iterateConst(nodep); }
    ~CaseLintVisitor() override = default;

public:
    static void apply(AstCase* nodep) { CaseLintVisitor{nodep}; }
    static void apply(AstGenCase* nodep) { CaseLintVisitor{nodep}; }
};

//######################################################################
// Case state, as a visitor of each AstNode

class CaseVisitor final : public VNVisitor {
    // Maximum width we can check for overlaps/exhaustiveness
    constexpr static int CASE_OVERLAP_WIDTH = 16;
    // Maximum number of case values for exhaustive analysis/optimization
    constexpr static int CASE_MAX_VALUES = 1 << CASE_OVERLAP_WIDTH;
    // Levels of priority to be ORed together in top IF tree
    constexpr static int CASE_ENCODER_GROUP_DEPTH = 8;

    // TYPES
    // Record for each case value
    struct CaseRecord final {
        AstCaseItem* itemp;  // Case item that covers value
        AstConst* constp;  // Expression within 'itemp' that covers value (nullptr for default)
        AstNode* stmtsp;  // Statements of 'itemp' (might be nullptr if case is empty)
    };

    // STATE
    VDouble0 m_statCaseFast;  // Statistic tracking
    VDouble0 m_statCaseSlow;  // Statistic tracking
    const AstNode* m_alwaysp = nullptr;  // Always in which case is located

    // Per-CASE
    bool m_caseExhaustive = false;  // Proven exhaustive
    bool m_caseNoOverlaps = false;  // Proven no overlaps between cases
    // Map from value (index) to the CaseRecord that covers this value
    std::array<CaseRecord, CASE_MAX_VALUES> m_value2CaseRecord;

    // METHODS
    // Determine whether we should check case items are complete
    // Returns enum's dtype if should check, nullptr if shouldn't
    static const AstEnumDType* getEnumCompletionCheckDType(const AstCase* const nodep) {
        if (!nodep->uniquePragma() && !nodep->unique0Pragma()) return nullptr;
        const AstEnumDType* const enumDtp
            = VN_CAST(nodep->exprp()->dtypep()->skipRefToEnump(), EnumDType);
        if (!enumDtp) return nullptr;  // Case isn't enum
        const AstBasicDType* const basicp = enumDtp->subDTypep()->basicp();
        if (!basicp) return nullptr;  // Not simple type (perhaps IEEE illegal)
        return enumDtp;
    }

    // Check and warn if case items are not complete over the given enum type.
    // Returns true iff the case items cover all enum values/patterns.
    bool checkExhaustiveEnum(const AstCase* const nodep, const AstEnumDType* const enump) {
        const uint32_t numCases = 1UL << nodep->exprp()->width();
        for (AstEnumItem* eip = enump->itemsp(); eip; eip = VN_AS(eip->nextp(), EnumItem)) {
            AstConst* const econstp = VN_AS(eip->valuep(), Const);
            V3Number nummask{eip, econstp->width()};
            nummask.opBitsNonX(econstp->num());
            V3Number numval{eip, econstp->width()};
            numval.opBitsOne(econstp->num());

            const uint32_t mask = nummask.toUInt();
            const uint32_t val = numval.toUInt();

            // Check all cases to see if they cover this enum value/pattern
            for (uint32_t i = 0; i < numCases; ++i) {
                if ((i & mask) != val) continue;  // This case is not for this enum value
                if (m_value2CaseRecord[i].itemp) continue;  // Covered case
                // Warn unless unique0 case which allows no-match
                if (!nodep->unique0Pragma()) {
                    nodep->v3warn(CASEINCOMPLETE,
                                  "Enum item " << eip->prettyNameQ() << " not covered by case");
                }
                // TODO: warn for all uncovered enum values, not just the first
                return false;  // enum has uncovered value by case items
            }
        }
        return true;  // enum is fully covered
    }

    // Check and warn if case items are not complete over all possible values.
    // Returns true iff the case items cover all values of the case expression.
    bool checkExhaustivePacked(AstCase* nodep) {
        const uint32_t numCases = 1UL << nodep->exprp()->width();
        for (uint32_t i = 0; i < numCases; ++i) {
            if (m_value2CaseRecord[i].itemp) continue;  // Covered case
            if (!nodep->unique0Pragma()) {
                nodep->v3warn(CASEINCOMPLETE,
                              "Case values incompletely covered (example pattern 0x" << std::hex
                                                                                     << i << ")");
            }
            // TODO: warn for more than one uncovered case, not just the first
            return false;
        }

        // It's an exhaustive case statement
        return true;
    }

    bool checkExhaustive(AstCase* nodep) {
        if (const AstEnumDType* const enump = getEnumCompletionCheckDType(nodep)) {
            return checkExhaustiveEnum(nodep, enump);
        }
        return checkExhaustivePacked(nodep);
    }

    bool isCaseTreeFast(AstCase* nodep) {
        m_caseExhaustive = true;  // TODO: we haven't proven this yet, but is as was before
        m_caseNoOverlaps = false;

        AstNode* const caseExprp = nodep->exprp();
        if (caseExprp->isDouble() || caseExprp->isString()) return false;

        const int caseWidth = caseExprp->width();
        if (!caseWidth) return false;
        if (caseWidth > CASE_OVERLAP_WIDTH) return false;

        int caseConditions = 0;

        for (AstCaseItem* cip = nodep->itemsp(); cip; cip = VN_AS(cip->nextp(), CaseItem)) {
            for (AstNode* condp = cip->condsp(); condp; condp = condp->nextp()) {
                // Can't do anything with non-constants
                if (!VN_IS(condp, Const)) return false;
                // Count conditions
                ++caseConditions;
            }
        }

        UINFO(8, "Simple case statement: " << nodep);
        const uint32_t numCases = 1UL << caseWidth;
        // Zero list of items for each value
        for (uint32_t i = 0; i < numCases; ++i) {
            m_value2CaseRecord[i].itemp = nullptr;
            m_value2CaseRecord[i].constp = nullptr;
            m_value2CaseRecord[i].stmtsp = nullptr;
        }
        // Now pick up the values for each assignment
        // We can cheat and use uint32_t's because we only support narrow case's
        bool reportedOverlap = false;
        bool reportedSubcase = false;
        bool hasDefault = false;
        m_caseNoOverlaps = true;
        for (AstCaseItem* itemp = nodep->itemsp(); itemp;
             itemp = VN_AS(itemp->nextp(), CaseItem)) {

            // Default case
            if (itemp->isDefault()) {
                // Default was moved to be the last item by V3LinkDot. Fill remaining cases
                for (uint32_t i = 0; i < numCases; ++i) {
                    CaseRecord& caseRecord = m_value2CaseRecord[i];
                    if (!caseRecord.itemp) {
                        caseRecord.itemp = itemp;
                        caseRecord.stmtsp = itemp->stmtsp();
                    }
                }
                hasDefault = true;
                continue;
            }

            for (AstConst* iconstp = VN_AS(itemp->condsp(), Const); iconstp;
                 iconstp = VN_AS(iconstp->nextp(), Const)) {
                // Some items can never match due to 2-state simulation
                if (neverItem(nodep, iconstp)) continue;

                V3Number nummask{itemp, iconstp->width()};
                nummask.opBitsNonX(iconstp->num());
                V3Number numval{itemp, iconstp->width()};
                numval.opBitsOne(iconstp->num());

                const uint32_t mask = nummask.toUInt();
                const uint32_t val = numval.toUInt();

                bool foundNewCase = false;
                const AstConst* firstOverlapConstp = nullptr;
                uint32_t firstOverlapValue = 0;
                for (uint32_t i = 0; i < numCases; ++i) {
                    if ((i & mask) != val) continue;

                    CaseRecord& caseRecord = m_value2CaseRecord[i];

                    // If this is the first case that covers this value, record it
                    if (!caseRecord.itemp) {
                        caseRecord.itemp = itemp;
                        caseRecord.constp = iconstp;
                        caseRecord.stmtsp = itemp->stmtsp();
                        foundNewCase = true;
                        continue;
                    }

                    // There is an overlap. If it's within the same CaseItem, it is legal
                    if (caseRecord.itemp == itemp) continue;

                    // Otherwise record the first overlapping case
                    if (!firstOverlapConstp) {
                        firstOverlapConstp = caseRecord.constp;
                        firstOverlapValue = i;
                        m_caseNoOverlaps = false;
                    }
                }
                if (nodep->priorityPragma()) {
                    // If this is a priority case, we only want to complain if every possible value
                    // for this item is already hit by some other item. This is true if
                    // 'foundNewCase' is false. 'firstOverlapConstp' is null when the only covering
                    // item is this item itself, which is legal overlap within one item.
                    if (!reportedSubcase && !foundNewCase && firstOverlapConstp) {
                        iconstp->v3warn(CASEOVERLAP,
                                        "Case item ignored: every matching value is covered "
                                        "by an earlier condition\n"
                                            << iconstp->warnContextPrimary() << '\n'
                                            << firstOverlapConstp->warnOther()
                                            << "... Location of previous condition\n"
                                            << firstOverlapConstp->warnContextPrimary());
                        reportedSubcase = true;
                    }
                } else {
                    // If this case statement doesn't have the priority keyword,
                    // we want to warn on any overlap.
                    if (!reportedOverlap && firstOverlapConstp) {
                        std::ostringstream examplePattern;
                        if (iconstp->num().isAnyXZ()) {
                            examplePattern << " (example pattern 0x" << std::hex
                                           << firstOverlapValue << ")";
                        }
                        iconstp->v3warn(CASEOVERLAP,
                                        "Case conditions overlap"
                                            << examplePattern.str() << "\n"
                                            << iconstp->warnContextPrimary() << '\n'
                                            << firstOverlapConstp->warnOther()
                                            << "... Location of overlapping condition\n"
                                            << firstOverlapConstp->warnContextSecondary());
                        reportedOverlap = true;
                    }
                }
            }
        }

        // If there was no default, check exhaustiveness
        m_caseExhaustive = hasDefault || checkExhaustive(nodep);
        if (!m_caseExhaustive) {
            m_caseNoOverlaps = false;
            return false;
        }

        if (caseConditions <= 3
            // Avoid e.g. priority expanders from going crazy in expansion
            || (caseWidth >= 8 && (caseConditions <= (caseWidth + 1)))) {
            return false;  // Not worth simplifying
        }

        return true;  // All is fine
    }

    // TODO: should return AstNodeStmt after #6280
    AstNode* replaceCaseFastRecurse(AstNodeExpr* cexprp, int msb, uint32_t upperValue) {
        // Base case: If reached the last bit, upperValue equals an exact value, just return
        // the statements from that CaseItem. Note: Not cloning here as the caller will do
        // an identity check.
        if (msb < 0) return m_value2CaseRecord[upperValue].stmtsp;

        // Recursive case:
        // Make left and right subtrees assuming cexpr[msb] is 0 and 1 respectively
        const uint32_t upperValue0 = upperValue;
        const uint32_t upperValue1 = upperValue | (1UL << msb);
        AstNode* tree0p = replaceCaseFastRecurse(cexprp, msb - 1, upperValue0);
        AstNode* tree1p = replaceCaseFastRecurse(cexprp, msb - 1, upperValue1);

        // If same logic on both sides, we can just return one of them
        if (tree0p == tree1p) return tree0p;

        // We could have a "checkerboard" with A B A B, we can use the same IF on both edges
        {
            bool same = true;
            for (uint32_t a = upperValue0, b = upperValue1; a < upperValue1; ++a, ++b) {
                if (m_value2CaseRecord[a].stmtsp != m_value2CaseRecord[b].stmtsp) {
                    same = false;
                    break;
                }
            }
            if (same) {
                VL_DO_DANGLING(tree1p->deleteTree(), tree1p);
                return tree0p;
            }
        }

        // Must have differing logic. Test the bit and convert to an If.

        // Clone if needed
        if (tree0p && tree0p->backp()) tree0p = tree0p->cloneTree(true);
        if (tree1p && tree1p->backp()) tree1p = tree1p->cloneTree(true);
        // Create the If statement
        FileLine* const flp = cexprp->fileline();
        AstNodeExpr* const condp = new AstSel{flp, cexprp->cloneTreePure(false), msb, 1};
        AstIf* const ifp = new AstIf{flp, condp, tree1p, tree0p};
        return ifp;
    }

    // TODO: should return AstNodeStmt after #6280
    AstNode* replaceCaseFast(AstCase* nodep) {
        // CASEx(cexpr,....
        // ->  tree of IF(msb,  IF(msb-1, 11, 10)
        //                      IF(msb-1, 01, 00))
        const int caseWidth = nodep->exprp()->width();
        AstNode* const ifrootp = replaceCaseFastRecurse(nodep->exprp(), caseWidth - 1, 0UL);
        return ifrootp && ifrootp->backp() ? ifrootp->cloneTree(true) : ifrootp;
    }

    // TODO: should return AstNodeStmt after #6280
    AstNode* replaceCaseComplicated(AstCase* nodep) {
        // CASEx(cexpr,ITEM(icond1,istmts1),ITEM(icond2,istmts2),ITEM(default,istmts3))
        // ->  IF((cexpr==icond1),istmts1,
        //                       IF((EQ (AND MASK cexpr) (AND MASK icond1)
        //                              ,istmts2, istmts3

        // We'll do this in two stages.
        // First stage, convert the conditions to the appropriate IF AND terms.
        bool hasDefault = false;
        for (AstCaseItem* itemp = nodep->itemsp(); itemp;
             itemp = VN_AS(itemp->nextp(), CaseItem)) {

            FileLine* const flp = itemp->fileline();

            // Default clause. Just make true, we'll optimize it away later
            if (itemp->isDefault()) {
                itemp->addCondsp(new AstConst{flp, AstConst::BitTrue{}});
                hasDefault = true;
                continue;
            }

            // Regular clause. Construct the condition expression.
            AstNodeExpr* newCondp = nullptr;
            for (AstNodeExpr *itemExprp = itemp->condsp(), *nextp; itemExprp; itemExprp = nextp) {
                nextp = VN_AS(itemExprp->nextp(), NodeExpr);
                itemExprp->unlinkFrBack();

                // If case never matches, ignore it
                if (neverItem(nodep, itemExprp)) {
                    VL_DO_DANGLING(itemExprp->deleteTree(), itemExprp);
                    continue;
                }

                // Compute the term to add to the condition expression
                AstNodeExpr* const termp = [&]() -> AstNodeExpr* {
                    // Will need a copy of the caseExpr regardless
                    AstNodeExpr* const caseExprp = nodep->exprp()->cloneTreePure(false);

                    // InsideRange: Similar logic in V3Width::visit(AstInside)
                    if (AstInsideRange* const itemRangep = VN_CAST(itemExprp, InsideRange)) {
                        AstNodeExpr* const resultp = itemRangep->newAndFromInside(  //
                            caseExprp,  //
                            itemRangep->lhsp()->unlinkFrBack(),
                            itemRangep->rhsp()->unlinkFrBack());
                        VL_DO_DANGLING2(itemExprp->deleteTree(), itemExprp, itemRangep);
                        return resultp;
                    }

                    // Check if we need to perform a wildcard match, this needs masking
                    if (AstConst* const itemConstp = VN_CAST(itemExprp, Const)) {
                        // TODO: 4-state will need to fix this
                        if (itemConstp->num().isFourState()
                            && (nodep->casex() || nodep->casez() || nodep->caseInside())) {
                            // Wildcard match, make 'caseExpr' & 'mask' == 'itemExpr' & 'mask'
                            V3Number numMask{itemp, itemConstp->width()};
                            numMask.opBitsNonX(itemConstp->num());
                            V3Number numOne{itemp, itemConstp->width()};
                            numOne.opBitsOne(itemConstp->num());
                            V3Number numRhs{itemp, itemConstp->width()};
                            numRhs.opAnd(numOne, numMask);
                            VL_DO_DANGLING2(itemExprp->deleteTree(), itemExprp, itemConstp);
                            return AstEq::newTyped(
                                flp,  //
                                new AstConst{flp, numRhs},
                                new AstAnd{flp, caseExprp, new AstConst{flp, numMask}});
                        }
                    }

                    // Regular case, use simple equality comparison
                    return AstEq::newTyped(flp, caseExprp, itemExprp);
                }();

                // 'Or' new term with previous terms
                newCondp = newCondp ? new AstLogOr{flp, newCondp, termp} : termp;
            }
            // Replace expression in tree. Needs to be non-null, so add a constant false if needed
            if (!newCondp) newCondp = new AstConst{flp, AstConst::BitFalse{}};
            itemp->addCondsp(newCondp);
        }

        // If there was no default, add a empty one, this greatly simplifies below code
        // and constant propagation will just eliminate it for us later.
        if (!hasDefault) {
            nodep->addItemsp(new AstCaseItem{
                nodep->fileline(), new AstConst{nodep->fileline(), AstConst::BitTrue{}}, nullptr});
        }

        // Now build the IF statement tree
        // The tree can be quite huge.  Pull every group of 8 out, and make a OR tree.
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

            // Grab the statements from this item. May be empty.
            AstNode* const istmtsp = itemp->stmtsp();
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
        return grouprootp;
    }

    bool neverItem(const AstCase* casep, const AstNodeExpr* itemExprp) {
        const AstConst* const constp = VN_CAST(itemExprp, Const);
        if (!constp) return false;
        // Xs in case or casez are impossible due to two state simulations
        if (casep->casex() || casep->caseInside()) return false;
        if (casep->casez()) return constp->num().isAnyX();
        return constp->num().isFourState();
    }

    // VISITORS
    void visit(AstCase* nodep) override {
        UASSERT_OBJ(nodep->exprp()->isPure(), nodep,
                    "Impure case expression should have been removed by V3LiftExpr");

        CaseLintVisitor::apply(nodep);

        // Convert any children first
        iterateChildren(nodep);

        // Convert the case statement
        AstNode* replacementp = nullptr;
        if (isCaseTreeFast(nodep) && v3Global.opt.fCase()) {
            // It's a simple priority encoder or complete statement
            // we can make a tree of statements to avoid extra comparisons
            ++m_statCaseFast;
            replacementp = replaceCaseFast(nodep);
        } else {
            // If a case statement is exhaustive, presume signals involved aren't forming a latch
            // TODO: this is broken, but it is as was before
            if (m_alwaysp && m_caseExhaustive) {
                m_alwaysp->fileline()->warnOff(V3ErrorCode::LATCH, true);
            }
            ++m_statCaseSlow;
            m_caseExhaustive = false;
            m_caseNoOverlaps = false;
            replacementp = replaceCaseComplicated(nodep);
        }

        // Take the notParallelp tree under the case statement created by V3Assert
        // If the statement was proven to have no overlaps and all cases covered,
        // it can be removed. Otherwise insert the assertion after the case statement.
        if (nodep->notParallelp() && (!m_caseExhaustive || !m_caseNoOverlaps)) {
            nodep->addNextHere(nodep->notParallelp()->unlinkFrBackWithNext());
        }

        // Replace/remove the case statement
        if (replacementp) {
            nodep->replaceWith(replacementp);
        } else {
            nodep->unlinkFrBack();
        }
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
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
    explicit CaseVisitor(AstNetlist* nodep) { iterate(nodep); }
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
    CaseLintVisitor::apply(nodep);
}
