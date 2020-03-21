// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Break case statements up and add Unknown assigns
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

#include "config_build.h"
#include "verilatedos.h"

#include "V3Global.h"
#include "V3Case.h"
#include "V3Ast.h"
#include "V3Stats.h"

#include <algorithm>
#include <cstdarg>

#define CASE_OVERLAP_WIDTH 16           // Maximum width we can check for overlaps in
#define CASE_BARF          999999       // Magic width when non-constant
#define CASE_ENCODER_GROUP_DEPTH 8      // Levels of priority to be ORed together in top IF tree

//######################################################################

class CaseLintVisitor : public AstNVisitor {
private:
    AstNodeCase* m_caseExprp;  // Under a CASE value node, if so the relevant case statement

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    virtual void visit(AstNodeCase* nodep) VL_OVERRIDE {
        if (VN_IS(nodep, Case) && VN_CAST(nodep, Case)->casex()) {
            nodep->v3warn(CASEX, "Suggest casez (with ?'s) in place of casex (with X's)");
        }
        // Detect multiple defaults
        bool hitDefault = false;
        for (AstCaseItem* itemp = nodep->itemsp();
             itemp; itemp=VN_CAST(itemp->nextp(), CaseItem)) {
            if (itemp->isDefault()) {
                if (hitDefault) {
                    itemp->v3error("Multiple default statements in case statement.");
                }
                hitDefault = true;
            }
        }

        // Check for X/Z in non-casex statements
        {
            m_caseExprp = nodep;
            iterate(nodep->exprp());
            for (AstCaseItem* itemp = nodep->itemsp();
                 itemp; itemp=VN_CAST(itemp->nextp(), CaseItem)) {
                iterateAndNextNull(itemp->condsp());
            }
            m_caseExprp = NULL;
        }
    }
    virtual void visit(AstConst* nodep) VL_OVERRIDE {
        // See also neverItem
        if (m_caseExprp && nodep->num().isFourState()) {
            if (VN_IS(m_caseExprp, GenCase)) {
                nodep->v3error("Use of x/? constant in generate case statement, (no such thing as 'generate casez')");
            } else if (VN_IS(m_caseExprp, Case) && VN_CAST(m_caseExprp, Case)->casex()) {
                // Don't sweat it, we already complained about casex in general
            } else if (VN_IS(m_caseExprp, Case) && (VN_CAST(m_caseExprp, Case)->casez()
                                                   || VN_CAST(m_caseExprp, Case)->caseInside())) {
                if (nodep->num().isUnknown()) {
                    nodep->v3warn(CASEWITHX, "Use of x constant in casez statement, (perhaps intended ?/z in constant)");
                }
            } else {
                nodep->v3warn(CASEWITHX, "Use of x/? constant in case statement, (perhaps intended casex/casez)");
            }
        }
    }
    virtual void visit(AstNode* nodep) VL_OVERRIDE {
        iterateChildren(nodep);
    }
public:
    // CONSTRUCTORS
    explicit CaseLintVisitor(AstNodeCase* nodep) {
        m_caseExprp = NULL;
        iterate(nodep);
    }
    virtual ~CaseLintVisitor() {}
};

//######################################################################
// Case state, as a visitor of each AstNode

class CaseVisitor : public AstNVisitor {
private:
    // NODE STATE
    // Cleared each Case
    //  AstIf::user3()          -> bool.  Set true to indicate clone not needed
    AstUser3InUse       m_inuser3;

    // STATE
    VDouble0 m_statCaseFast;  // Statistic tracking
    VDouble0 m_statCaseSlow;  // Statistic tracking

    // Per-CASE
    int         m_caseWidth;    // Width of valueItems
    int         m_caseItems;    // Number of caseItem unique values
    bool        m_caseNoOverlapsAllCovered;     // Proven to be synopsys parallel_case compliant
    AstNode*    m_valueItem[1<<CASE_OVERLAP_WIDTH];  // For each possible value, the case branch we need

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    bool isCaseTreeFast(AstCase* nodep) {
        int width = 0;
        bool opaque = false;
        m_caseItems = 0;
        m_caseNoOverlapsAllCovered = true;
        for (AstCaseItem* itemp = nodep->itemsp();
             itemp; itemp=VN_CAST(itemp->nextp(), CaseItem)) {
            for (AstNode* icondp = itemp->condsp(); icondp!=NULL; icondp=icondp->nextp()) {
                if (icondp->width() > width) width = icondp->width();
                if (icondp->isDouble()) opaque = true;
                if (!VN_IS(icondp, Const)) width = CASE_BARF;  // Can't parse; not a constant
                m_caseItems++;
            }
        }
        m_caseWidth = width;
        if (width==0 || width > CASE_OVERLAP_WIDTH || opaque) {
            m_caseNoOverlapsAllCovered = false;
            return false;  // Too wide for analysis
        }
        UINFO(8,"Simple case statement: "<<nodep<<endl);
        // Zero list of items for each value
        for (uint32_t i=0; i<(1UL<<m_caseWidth); ++i) m_valueItem[i] = NULL;
        // Now pick up the values for each assignment
        // We can cheat and use uint32_t's because we only support narrow case's
        bool bitched = false;
        for (AstCaseItem* itemp = nodep->itemsp();
             itemp; itemp=VN_CAST(itemp->nextp(), CaseItem)) {
            for (AstNode* icondp = itemp->condsp(); icondp!=NULL; icondp=icondp->nextp()) {
                //if (debug()>=9) icondp->dumpTree(cout, " caseitem: ");
                AstConst* iconstp = VN_CAST(icondp, Const);
                UASSERT_OBJ(iconstp, nodep, "above 'can't parse' should have caught this");
                if (neverItem(nodep, iconstp)) {
                    // X in casez can't ever be executed
                } else {
                    V3Number nummask (itemp, iconstp->width());
                    nummask.opBitsNonX(iconstp->num());
                    uint32_t mask = nummask.toUInt();
                    V3Number numval (itemp, iconstp->width());
                    numval.opBitsOne(iconstp->num());
                    uint32_t val  = numval.toUInt();
                    for (uint32_t i=0; i<(1UL<<m_caseWidth); ++i) {
                        if ((i & mask) == val) {
                            if (!m_valueItem[i]) {
                                m_valueItem[i] = itemp;
                            } else if (!itemp->ignoreOverlap() && !bitched) {
                                icondp->v3warn(CASEOVERLAP, "Case values overlap (example pattern 0x"
                                               <<std::hex<<i<<")");
                                bitched = true;
                                m_caseNoOverlapsAllCovered = false;
                            }
                        }
                    }
                }
            }
            // Defaults were moved to last in the caseitem list by V3LinkDot
            if (itemp->isDefault()) {  // Case statement's default... Fill the table
                for (uint32_t i=0; i<(1UL<<m_caseWidth); ++i) {
                    if (!m_valueItem[i]) m_valueItem[i] = itemp;
                }
            }
        }
        for (uint32_t i=0; i<(1UL<<m_caseWidth); ++i) {
            if (!m_valueItem[i]) {
                nodep->v3warn(CASEINCOMPLETE, "Case values incompletely covered (example pattern 0x"
                              <<std::hex<<i<<")");
                m_caseNoOverlapsAllCovered = false;
                return false;
            }
        }
        if (m_caseItems <= 3
            // Avoid e.g. priority expanders from going crazy in expansion
            || (m_caseWidth >= 8 && (m_caseItems <= (m_caseWidth + 1)))) {
            return false;  // Not worth simplifying
        }

        // Convert valueItem from AstCaseItem* to the expression
        // Not done earlier, as we may now have a NULL because it's just a ";" NOP branch
        for (uint32_t i=0; i<(1UL<<m_caseWidth); ++i) {
            m_valueItem[i] = VN_CAST(m_valueItem[i], CaseItem)->bodysp();
        }
        return true;  // All is fine
    }

    AstNode* replaceCaseFastRecurse(AstNode* cexprp, int msb, uint32_t upperValue) {
        if (msb<0) {
            // There's no space for a IF.  We know upperValue is thus down to a specific
            // exact value, so just return the tree value
            // Note can't clone here, as we're going to check for equivalence above
            return m_valueItem[upperValue];
        }
        else {
            // Make left and right subtrees
            // cexpr[msb:lsb] == 1
            AstNode* tree0p = replaceCaseFastRecurse(cexprp, msb-1, upperValue | 0);
            AstNode* tree1p = replaceCaseFastRecurse(cexprp, msb-1, upperValue | (1UL<<msb));

            if (tree0p == tree1p) {
                // Same logic on both sides, so we can just return one of 'em
                return tree0p;
            }
            // We could have a "checkerboard" with A B A B, we can use the same IF on both edges
            bool same = true;
            for (uint32_t a=upperValue,
                     b=(upperValue|(1UL<<msb));
                 a < (upperValue|(1UL<<msb));
                 a++, b++) {
                if (m_valueItem[a] != m_valueItem[b]) { same = false; break; }
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
            //V3Number nummask (cexprp, cexprp->width(), (1UL<<msb));
            //AstNode* and1p = new AstAnd(cexprp->fileline(), cexprp->cloneTree(false),
            //                            new AstConst(cexprp->fileline(), nummask));
            AstNode* and1p = new AstSel(cexprp->fileline(), cexprp->cloneTree(false),
                                        msb, 1);
            AstNode* eqp = new AstNeq(cexprp->fileline(),
                                      new AstConst(cexprp->fileline(), 0),
                                      and1p);
            AstIf* ifp = new AstIf(cexprp->fileline(), eqp, tree1p, tree0p);
            ifp->user3(1);  // So we don't bother to clone it
            return ifp;
        }
    }

    void replaceCaseFast(AstCase* nodep) {
        // CASEx(cexpr,....
        // ->  tree of IF(msb,  IF(msb-1, 11, 10)
        //                      IF(msb-1, 01, 00))
        AstNode* cexprp = nodep->exprp()->unlinkFrBack();

        if (debug()>=9) {
            for (uint32_t i=0; i<(1UL<<m_caseWidth); ++i) {
                if (AstNode* itemp = m_valueItem[i]) {
                    UINFO(9,"Value "<<std::hex<<i<<" "<<itemp<<endl);
                }
            }
        }

        // Handle any assertions
        replaceCaseParallel(nodep, m_caseNoOverlapsAllCovered);

        AstNode::user3ClearTree();
        AstNode* ifrootp = replaceCaseFastRecurse(cexprp, m_caseWidth-1, 0UL);
        // Case expressions can't be linked twice, so clone them
        if (ifrootp && !ifrootp->user3()) ifrootp = ifrootp->cloneTree(true);

        if (ifrootp) nodep->replaceWith(ifrootp);
        else nodep->unlinkFrBack();
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
        VL_DO_DANGLING(cexprp->deleteTree(), cexprp);
        if (debug()>=9) ifrootp->dumpTree(cout, "    _simp: ");
    }

    void replaceCaseComplicated(AstCase* nodep) {
        // CASEx(cexpr,ITEM(icond1,istmts1),ITEM(icond2,istmts2),ITEM(default,istmts3))
        // ->  IF((cexpr==icond1),istmts1,
        //                       IF((EQ (AND MASK cexpr) (AND MASK icond1)
        //                              ,istmts2, istmts3
        AstNode* cexprp = nodep->exprp()->unlinkFrBack();
        // We'll do this in two stages.  First stage, convert the conditions to
        // the appropriate IF AND terms.
        if (debug()>=9) nodep->dumpTree(cout, "    _comp_IN:   ");
        bool hadDefault = false;
        for (AstCaseItem* itemp = nodep->itemsp(); itemp; itemp=VN_CAST(itemp->nextp(), CaseItem)) {
            if (!itemp->condsp()) {
                // Default clause.  Just make true, we'll optimize it away later
                itemp->condsp(new AstConst(itemp->fileline(), AstConst::LogicTrue()));
                hadDefault = true;
            } else {
                // Expressioned clause
                AstNode* icondNextp = NULL;
                AstNode* ifexprp = NULL;  // If expression to test
                for (AstNode* icondp = itemp->condsp(); icondp!=NULL; icondp=icondNextp) {
                    icondNextp = icondp->nextp();
                    icondp->unlinkFrBack();

                    AstNode* condp = NULL;  // Default is to use and1p/and2p
                    AstConst* iconstp = VN_CAST(icondp, Const);
                    if (iconstp && neverItem(nodep, iconstp)) {
                        // X in casez can't ever be executed
                        VL_DO_DANGLING(icondp->deleteTree(), icondp); VL_DANGLING(iconstp);
                        // For simplicity, make expression that is not equal, and let later
                        // optimizations remove it
                        condp = new AstConst(itemp->fileline(), AstConst::LogicFalse());
                    } else if (AstInsideRange* irangep = VN_CAST(icondp, InsideRange)) {
                        // Similar logic in V3Width::visit(AstInside)
                        AstNode* ap = AstGte::newTyped(itemp->fileline(),
                                                       cexprp->cloneTree(false),
                                                       irangep->lhsp()->unlinkFrBack());
                        AstNode* bp = AstLte::newTyped(itemp->fileline(),
                                                       cexprp->cloneTree(false),
                                                       irangep->rhsp()->unlinkFrBack());
                        ap->fileline()->modifyWarnOff(V3ErrorCode::UNSIGNED, true);
                        bp->fileline()->modifyWarnOff(V3ErrorCode::CMPCONST, true);
                        condp = new AstAnd(itemp->fileline(), ap, bp);
                    } else if (iconstp && iconstp->num().isFourState()
                               && (nodep->casex() || nodep->casez() || nodep->caseInside())) {
                        V3Number nummask (itemp, iconstp->width());
                        nummask.opBitsNonX(iconstp->num());
                        V3Number numval  (itemp, iconstp->width());
                        numval.opBitsOne(iconstp->num());
                        AstNode* and1p = new AstAnd(itemp->fileline(), cexprp->cloneTree(false),
                                                    new AstConst(itemp->fileline(), nummask));
                        AstNode* and2p = new AstAnd(itemp->fileline(),
                                                    new AstConst(itemp->fileline(), numval),
                                                    new AstConst(itemp->fileline(), nummask));
                        VL_DO_DANGLING(icondp->deleteTree(), icondp); VL_DANGLING(iconstp);
                        condp = AstEq::newTyped(itemp->fileline(), and1p, and2p);
                    } else {
                        // Not a caseX mask, we can simply build CASEEQ(cexpr icond)
                        AstNode* and1p = cexprp->cloneTree(false);
                        AstNode* and2p = icondp;
                        condp = AstEq::newTyped(itemp->fileline(), and1p, and2p);
                    }
                    if (!ifexprp) {
                        ifexprp = condp;
                    } else {
                        ifexprp = new AstLogOr(itemp->fileline(), ifexprp, condp);
                    }
                }
                // Replace expression in tree
                itemp->condsp(ifexprp);
            }
        }
        VL_DO_DANGLING(cexprp->deleteTree(), cexprp);
        if (!hadDefault) {
            // If there was no default, add a empty one, this greatly simplifies below code
            // and constant propagation will just eliminate it for us later.
            nodep->addItemsp(new AstCaseItem(nodep->fileline(),
                                             new AstConst(nodep->fileline(), AstConst::LogicTrue()),
                                             NULL));
        }
        if (debug()>=9) nodep->dumpTree(cout, "    _comp_COND: ");
        // Now build the IF statement tree
        // The tree can be quite huge.  Pull ever group of 8 out, and make a OR tree.
        // This reduces the depth for the bottom elements, at the cost of
        // some of the top elements.  If we ever have profiling data, we
        // should pull out the most common item from here and instead make
        // it the first IF branch.
        int depth = 0;
        AstNode* grouprootp = NULL;
        AstIf* groupnextp = NULL;
        AstIf* itemnextp = NULL;
        for (AstCaseItem* itemp = nodep->itemsp(); itemp; itemp=VN_CAST(itemp->nextp(), CaseItem)) {
            AstNode* istmtsp = itemp->bodysp();  // Maybe null -- no action.
            if (istmtsp) istmtsp->unlinkFrBackWithNext();
            // Expressioned clause
            AstNode* ifexprp = itemp->condsp()->unlinkFrBack();
            {   // Prepare for next group
                if (++depth > CASE_ENCODER_GROUP_DEPTH) depth = 1;
                if (depth == 1) {  // First group or starting new group
                    itemnextp = NULL;
                    AstIf* newp = new AstIf(itemp->fileline(),
                                            ifexprp->cloneTree(true), NULL, NULL);
                    if (groupnextp) groupnextp->addElsesp(newp);
                    else grouprootp = newp;
                    groupnextp = newp;
                } else {  // Continue group, modify if condition to OR in this new condition
                    AstNode* condp = groupnextp->condp()->unlinkFrBack();
                    groupnextp->condp(new AstOr(ifexprp->fileline(),
                                                condp,
                                                ifexprp->cloneTree(true)));
                }
            }
            {   // Make the new lower IF and attach in the tree
                AstNode* itemexprp = ifexprp; VL_DANGLING(ifexprp);
                if (depth == (CASE_ENCODER_GROUP_DEPTH)) {  // End of group - can skip the condition
                    VL_DO_DANGLING(itemexprp->deleteTree(), itemexprp);
                    itemexprp = new AstConst(itemp->fileline(), AstConst::LogicTrue());
                }
                AstIf* newp = new AstIf(itemp->fileline(), itemexprp, istmtsp, NULL);
                if (itemnextp) itemnextp->addElsesp(newp);
                else groupnextp->addIfsp(newp);  // First in a new group
                itemnextp = newp;
            }
        }
        if (debug()>=9) nodep->dumpTree(cout, "    _comp_TREE: ");
        // Handle any assertions
        replaceCaseParallel(nodep, false);
        // Replace the CASE... with IF...
        if (debug()>=9 && grouprootp) grouprootp->dumpTree(cout, "     _new: ");
        if (grouprootp) nodep->replaceWith(grouprootp);
        else nodep->unlinkFrBack();
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
    }

    void replaceCaseParallel(AstCase* nodep, bool noOverlapsAllCovered) {
        // Take the notParallelp tree under the case statement created by V3Assert
        // If the statement was proven to have no overlaps and all cases
        // covered, we're done with it.
        // Else, convert to a normal statement parallel with the case statement.
        if (nodep->notParallelp() && !noOverlapsAllCovered) {
            AstNode* parp = nodep->notParallelp()->unlinkFrBackWithNext();
            nodep->addNextHere(parp);
        }
    }

    bool neverItem(AstCase* casep, AstConst* itemp) {
        // Xs in case or casez are impossible due to two state simulations
        if (casep->casex()) {
        } else if (casep->casez() || casep->caseInside()) {
            if (itemp->num().isUnknown()) return true;
        } else {
            if (itemp->num().isFourState()) return true;
        }
        return false;
    }

    // VISITORS
    virtual void visit(AstCase* nodep) VL_OVERRIDE {
        V3Case::caseLint(nodep);
        iterateChildren(nodep);
        if (debug()>=9) nodep->dumpTree(cout, " case_old: ");
        if (isCaseTreeFast(nodep) && v3Global.opt.oCase()) {
            // It's a simple priority encoder or complete statement
            // we can make a tree of statements to avoid extra comparisons
            ++m_statCaseFast;
            VL_DO_DANGLING(replaceCaseFast(nodep), nodep);
        } else {
            ++m_statCaseSlow;
            VL_DO_DANGLING(replaceCaseComplicated(nodep), nodep);
        }
    }
    //--------------------
    // Default: Just iterate
    virtual void visit(AstNode* nodep) VL_OVERRIDE {
        iterateChildren(nodep);
    }

public:
    // CONSTRUCTORS
    explicit CaseVisitor(AstNetlist* nodep) {
        m_caseWidth = 0;
        m_caseItems = 0;
        m_caseNoOverlapsAllCovered = false;
        for (uint32_t i=0; i<(1UL<<CASE_OVERLAP_WIDTH); ++i) {
            m_valueItem[i] = NULL;
        }
        iterate(nodep);
    }
    virtual ~CaseVisitor() {
        V3Stats::addStat("Optimizations, Cases parallelized", m_statCaseFast);
        V3Stats::addStat("Optimizations, Cases complex", m_statCaseSlow);
    }
};

//######################################################################
// Case class functions

void V3Case::caseAll(AstNetlist* nodep) {
    UINFO(2,__FUNCTION__<<": "<<endl);
    {
        CaseVisitor visitor (nodep);
    }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("case", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}
void V3Case::caseLint(AstNodeCase* nodep) {
    UINFO(4,__FUNCTION__<<": "<<endl);
    CaseLintVisitor visitor (nodep);
}
