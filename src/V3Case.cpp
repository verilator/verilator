// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Break case statements up and add Unknown assigns
//
// Code available from: http://www.veripool.org/verilator
//
//*************************************************************************
//
// Copyright 2003-2015 by Wilson Snyder.  This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
//
// Verilator is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
//*************************************************************************
// V3Case's Transformations:
//
// Each module:
//	TBD: Eliminate tristates by adding __in, __inen, __en wires in parallel
//	    Need __en in changed list if a signal is on the LHS of a assign
//	Cases:
//	    CASE(v) CASEITEM(items,body) ->  IF (OR (EQ (AND v mask)
//							(AND item1 mask))
//						    (other items))
//						body
//		Or, converts to a if/else tree.
//	FUTURES:
//	    Large 16+ bit tables with constants and no masking (address muxes)
//		Enter all into multimap, sort by value and use a tree of < and == compares.
//	    "Diagonal" find of {rightmost,leftmost} bit {set,clear}
//		Ignoring mask, check each value is unique (using multimap as above?)
//		Each branch is then mask-and-compare operation (IE <000000001_000000000 at midpoint.)
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"
#include <cstdio>
#include <cstdarg>
#include <unistd.h>
#include <algorithm>

#include "V3Global.h"
#include "V3Case.h"
#include "V3Ast.h"
#include "V3Stats.h"

#define CASE_OVERLAP_WIDTH 12		// Maximum width we can check for overlaps in
#define CASE_BARF	   999999	// Magic width when non-constant
#define CASE_ENCODER_GROUP_DEPTH 8	// Levels of priority to be ORed together in top IF tree

//######################################################################

class CaseLintVisitor : public AstNVisitor {
private:
    AstNodeCase* m_caseExprp;	// Under a CASE value node, if so the relevant case statement

    static int debug() {
	static int level = -1;
	if (VL_UNLIKELY(level < 0)) level = v3Global.opt.debugSrcLevel(__FILE__);
	return level;
    }

    virtual void visit(AstNodeCase* nodep, AstNUser*) {
	if (nodep->castCase() && nodep->castCase()->casex()) {
	    nodep->v3warn(CASEX,"Suggest casez (with ?'s) in place of casex (with X's)");
	}
	// Detect multiple defaults
	bool hitDefault = false;
	for (AstCaseItem* itemp = nodep->itemsp(); itemp; itemp=itemp->nextp()->castCaseItem()) {
	    if (itemp->isDefault()) {
		if (hitDefault) {
		    nodep->v3error("Multiple default statements in case statement.");
		}
		hitDefault = true;
	    }
	}

	// Check for X/Z in non-casex statements
	{
	    m_caseExprp = nodep;
	    nodep->exprp()->accept(*this);
	    for (AstCaseItem* itemp = nodep->itemsp(); itemp; itemp=itemp->nextp()->castCaseItem()) {
		itemp->condsp()->iterateAndNext(*this);
	    }
	    m_caseExprp = NULL;
	}
    }
    virtual void visit(AstConst* nodep, AstNUser*) {
	// See also neverItem
	if (m_caseExprp && nodep->num().isFourState()) {
	    if (m_caseExprp->castGenCase()) {
		nodep->v3error("Use of x/? constant in generate case statement, (no such thing as 'generate casez')");
	    } else if (m_caseExprp->castCase() && m_caseExprp->castCase()->casex()) {
		// Don't sweat it, we already complained about casex in general
	    } else if (m_caseExprp->castCase() && (m_caseExprp->castCase()->casez()
						   || m_caseExprp->castCase()->caseInside())) {
		if (nodep->num().isUnknown()) {
		    nodep->v3warn(CASEWITHX, "Use of x constant in casez statement, (perhaps intended ?/z in constant)");
		}
	    } else {
		nodep->v3warn(CASEWITHX, "Use of x/? constant in case statement, (perhaps intended casex/casez)");
	    }
	}
    }
    virtual void visit(AstNode* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
    }
public:
    // CONSTUCTORS
    CaseLintVisitor(AstNodeCase* nodep) {
	m_caseExprp = NULL;
	nodep->accept(*this);
    }
    virtual ~CaseLintVisitor() {}
};

//######################################################################
// Case state, as a visitor of each AstNode

class CaseVisitor : public AstNVisitor {
private:
    // NODE STATE
    // Cleared each Case
    //  AstIf::user3()		-> bool.  Set true to indicate clone not needed
    AstUser3InUse	m_inuser3;

    // STATE
    V3Double0	m_statCaseFast;	// Statistic tracking
    V3Double0	m_statCaseSlow;	// Statistic tracking

    // Per-CASE
    int		m_caseWidth;	// Width of valueItems
    int		m_caseItems;	// Number of caseItem unique values
    bool	m_caseNoOverlapsAllCovered;	// Proven to be synopsys parallel_case compliant
    AstNode*	m_valueItem[1<<CASE_OVERLAP_WIDTH];  // For each possible value, the case branch we need

    // METHODS
    static int debug() {
	static int level = -1;
	if (VL_UNLIKELY(level < 0)) level = v3Global.opt.debugSrcLevel(__FILE__);
	return level;
    }

    bool isCaseTreeFast(AstCase* nodep) {
	int width = 0;
	bool opaque = false;
	m_caseItems = 0;
	m_caseNoOverlapsAllCovered = true;
	for (AstCaseItem* itemp = nodep->itemsp(); itemp; itemp=itemp->nextp()->castCaseItem()) {
	    for (AstNode* icondp = itemp->condsp(); icondp!=NULL; icondp=icondp->nextp()) {
		if (icondp->width() > width) width = icondp->width();
		if (icondp->isDouble()) opaque = true;
		if (!icondp->castConst()) width = CASE_BARF;  // Can't parse; not a constant
		m_caseItems++;
	    }
	}
	m_caseWidth = width;
	if (width==0 || width > CASE_OVERLAP_WIDTH || opaque) {
	    m_caseNoOverlapsAllCovered = false;
	    return false;	// Too wide for analysis
	}
	UINFO(8,"Simple case statement: "<<nodep<<endl);
	// Zero list of items for each value
	for (uint32_t i=0; i<(1UL<<m_caseWidth); i++) m_valueItem[i] = NULL;
	// Now pick up the values for each assignment
	// We can cheat and use uint32_t's because we only support narrow case's
	bool bitched = false;
	for (AstCaseItem* itemp = nodep->itemsp(); itemp; itemp=itemp->nextp()->castCaseItem()) {
	    for (AstNode* icondp = itemp->condsp(); icondp!=NULL; icondp=icondp->nextp()) {
		//if (debug()>=9) icondp->dumpTree(cout," caseitem: ");
		AstConst* iconstp = icondp->castConst();
		if (!iconstp) nodep->v3fatalSrc("above 'can't parse' should have caught this\n");
		if (neverItem(nodep, iconstp)) {
		    // X in casez can't ever be executed
		} else {
		    V3Number nummask (itemp->fileline(), iconstp->width());
		    nummask.opBitsNonX(iconstp->num());
		    uint32_t mask = nummask.toUInt();
		    V3Number numval  (itemp->fileline(), iconstp->width());
		    numval.opBitsOne(iconstp->num());
		    uint32_t val  = numval.toUInt();
		    for (uint32_t i=0; i<(1UL<<m_caseWidth); i++) {
			if ((i & mask) == val) {
			    if (!m_valueItem[i]) {
				m_valueItem[i] = itemp;
			    } else if (!itemp->ignoreOverlap() && !bitched) {
				itemp->v3warn(CASEOVERLAP,"Case values overlap (example pattern 0x"<<hex<<i<<")");
				bitched = true;
				m_caseNoOverlapsAllCovered = false;
			    }
			}
		    }
		}
	    }
	    // Defaults were moved to last in the caseitem list by V3LinkDot
	    if (itemp->isDefault()) {  // Case statement's default... Fill the table
		for (uint32_t i=0; i<(1UL<<m_caseWidth); i++) {
		    if (!m_valueItem[i]) m_valueItem[i] = itemp;
		}
	    }
	}
	for (uint32_t i=0; i<(1UL<<m_caseWidth); i++) {
	    if (!m_valueItem[i]) {
		nodep->v3warn(CASEINCOMPLETE,"Case values incompletely covered (example pattern 0x"<<hex<<i<<")");
		m_caseNoOverlapsAllCovered = false;
		return false;
	    }
	}
	if (m_caseItems <= 3) return false;	// Not worth simplifing
	// Convert valueItem from AstCaseItem* to the expression
	// Not done earlier, as we may now have a NULL because it's just a ";" NOP branch
	for (uint32_t i=0; i<(1UL<<m_caseWidth); i++) {
	    m_valueItem[i] = m_valueItem[i]->castCaseItem()->bodysp();
	}
	return true;  // All is fine
    }

    AstNode* replaceCaseFastRecurse(AstNode* cexprp, int msb, uint32_t upperValue) {
	if (msb<0) {
	    // There's no space for a IF.  We know upperValue is thus down to a specific
	    // exact value, so just return the tree value
	    // Note can't clone here, as we're going to check for equivelence above
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
		if (m_valueItem[a] != m_valueItem[b]) { same=false; break; }
	    }
	    if (same) {
		tree1p->deleteTree(); tree1p=NULL;
		return tree0p;
	    }

	    // Must have differing logic, so make a selection

	    // Case expressions can't be linked twice, so clone them
	    if (tree0p && !tree0p->user3()) tree0p = tree0p->cloneTree(true);
	    if (tree1p && !tree1p->user3()) tree1p = tree1p->cloneTree(true);

	    // Alternate scheme if we ever do multiple bits at a time:
	    //V3Number nummask (cexprp->fileline(), cexprp->width(), (1UL<<msb));
	    //AstNode* and1p = new AstAnd(cexprp->fileline(), cexprp->cloneTree(false),
	    //                            new AstConst(cexprp->fileline(), nummask));
	    AstNode* and1p = new AstSel(cexprp->fileline(), cexprp->cloneTree(false),
					msb, 1);
	    AstNode* eqp = new AstNeq(cexprp->fileline(),
				      new AstConst(cexprp->fileline(), 0),
				      and1p);
	    AstIf* ifp = new AstIf(cexprp->fileline(), eqp, tree1p, tree0p);
	    ifp->user3(1);	// So we don't bother to clone it
	    return ifp;
	}
    }

    void replaceCaseFast(AstCase* nodep) {
	// CASEx(cexpr,....
	// ->  tree of IF(msb,  IF(msb-1, 11, 10)
	//                      IF(msb-1, 01, 00))
	AstNode* cexprp = nodep->exprp()->unlinkFrBack();

	if (debug()>=9) {
	    for (uint32_t i=0; i<(1UL<<m_caseWidth); i++) {
		if (AstNode* itemp = m_valueItem[i]) {
		    UINFO(9,"Value "<<hex<<i<<" "<<itemp<<endl);
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
	nodep->deleteTree(); nodep=NULL;
	cexprp->deleteTree(); cexprp=NULL;
	if (debug()>=9) ifrootp->dumpTree(cout,"    _simp: ");
    }

    void replaceCaseComplicated(AstCase* nodep) {
	// CASEx(cexpr,ITEM(icond1,istmts1),ITEM(icond2,istmts2),ITEM(default,istmts3))
	// ->  IF((cexpr==icond1),istmts1,
	//		         IF((EQ (AND MASK cexpr) (AND MASK icond1)
	//				,istmts2, istmts3
	AstNode* cexprp = nodep->exprp()->unlinkFrBack();
	// We'll do this in two stages.  First stage, convert the conditions to
	// the appropriate IF AND terms.
	if (debug()>=9) nodep->dumpTree(cout,"    _comp_IN:   ");
	bool hadDefault = false;
	for (AstCaseItem* itemp = nodep->itemsp(); itemp; itemp=itemp->nextp()->castCaseItem()) {
	    if (!itemp->condsp()) {
		// Default clause.  Just make true, we'll optimize it away later
		itemp->condsp(new AstConst(itemp->fileline(), AstConst::LogicTrue()));
		hadDefault = true;
	    } else {
		// Expressioned clause
		AstNode* icondNextp = NULL;
		AstNode* ifexprp = NULL;	// If expression to test
		for (AstNode* icondp = itemp->condsp(); icondp!=NULL; icondp=icondNextp) {
		    icondNextp = icondp->nextp();
		    icondp->unlinkFrBack();

		    AstNode* condp = NULL;  // Default is to use and1p/and2p
		    AstConst* iconstp = icondp->castConst();
		    if (iconstp && neverItem(nodep, iconstp)) {
			// X in casez can't ever be executed
			icondp->deleteTree(); icondp=NULL; iconstp=NULL;
			// For simplicity, make expression that is not equal, and let later
			// optimizations remove it
			condp = new AstConst(itemp->fileline(), AstConst::LogicFalse());
		    } else if (AstInsideRange* irangep = icondp->castInsideRange()) {
			// Similar logic in V3Width::visit(AstInside)
			AstNode* ap = AstGte::newTyped(itemp->fileline(),
						       cexprp->cloneTree(false),
						       irangep->lhsp()->unlinkFrBack());
			AstNode* bp = AstLte::newTyped(itemp->fileline(),
						       cexprp->cloneTree(false),
						       irangep->rhsp()->unlinkFrBack());
			condp = new AstAnd(itemp->fileline(), ap, bp);
		    } else if (iconstp && iconstp->num().isFourState()
			       && (nodep->casex() || nodep->casez() || nodep->caseInside())) {
			V3Number nummask (itemp->fileline(), iconstp->width());
			nummask.opBitsNonX(iconstp->num());
			V3Number numval  (itemp->fileline(), iconstp->width());
			numval.opBitsOne(iconstp->num());
			AstNode* and1p = new AstAnd(itemp->fileline(), cexprp->cloneTree(false),
						    new AstConst(itemp->fileline(), nummask));
			AstNode* and2p = new AstAnd(itemp->fileline(),
						    new AstConst(itemp->fileline(), numval),
						    new AstConst(itemp->fileline(), nummask));
			icondp->deleteTree(); icondp=NULL; iconstp=NULL;
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
	cexprp->deleteTree(); cexprp=NULL;
	if (!hadDefault) {
	    // If there was no default, add a empty one, this greatly simplifies below code
	    // and constant propagation will just eliminate it for us later.
	    nodep->addItemsp(new AstCaseItem(nodep->fileline(),
					     new AstConst(nodep->fileline(), AstConst::LogicTrue()),
					     NULL));
	}
	if (debug()>=9) nodep->dumpTree(cout,"    _comp_COND: ");
	// Now build the IF statement tree
	// The tree can be quite huge.  Pull ever group of 8 out, and make a OR tree.
	// This reduces the depth for the bottom elements, at the cost of some of the top elements.
	// If we ever have profiling data, we should pull out the most common item from here and
	// instead make it the first IF branch.
	int depth = 0;
	AstNode* grouprootp = NULL;
	AstIf* groupnextp = NULL;
	AstIf* itemnextp = NULL;
	for (AstCaseItem* itemp = nodep->itemsp(); itemp; itemp=itemp->nextp()->castCaseItem()) {
	    AstNode* istmtsp = itemp->bodysp();   // Maybe null -- no action.
	    if (istmtsp) istmtsp->unlinkFrBackWithNext();
	    // Expressioned clause
	    AstNode* ifexprp = itemp->condsp()->unlinkFrBack();
	    {   // Prepare for next group
		if (++depth > CASE_ENCODER_GROUP_DEPTH) depth = 1;
		if (depth == 1) {  // First group or starting new group
		    itemnextp = NULL;
		    AstIf* newp = new AstIf(itemp->fileline(), ifexprp->cloneTree(true), NULL, NULL);
		    if (groupnextp) groupnextp->addElsesp(newp);
		    else grouprootp = newp;
		    groupnextp = newp;
		} else { // Continue group, modify if condition to OR in this new condition
		    AstNode* condp = groupnextp->condp()->unlinkFrBack();
		    groupnextp->condp(new AstOr(ifexprp->fileline(),
						condp,
						ifexprp->cloneTree(true)));
		}
	    }
	    {   // Make the new lower IF and attach in the tree
		AstNode* itemexprp = ifexprp;  ifexprp=NULL;
		if (depth == (CASE_ENCODER_GROUP_DEPTH)) { // End of group - can skip the condition
		    itemexprp->deleteTree(); itemexprp=NULL;
		    // cppcheck-suppress redundantAssignment
		    itemexprp = new AstConst(itemp->fileline(), AstConst::LogicTrue());
		}
		AstIf* newp = new AstIf(itemp->fileline(), itemexprp, istmtsp, NULL);
		if (itemnextp) itemnextp->addElsesp(newp);
		else groupnextp->addIfsp(newp);  // First in a new group
		itemnextp = newp;
	    }
	}
	if (debug()>=9) nodep->dumpTree(cout,"    _comp_TREE: ");
	// Handle any assertions
	replaceCaseParallel(nodep, false);
	// Replace the CASE... with IF...
	if (debug()>=9) grouprootp->dumpTree(cout,"     _new: ");
	if (grouprootp) nodep->replaceWith(grouprootp);
	else nodep->unlinkFrBack();
	nodep->deleteTree(); nodep=NULL;
    }

    void replaceCaseParallel(AstCase* nodep, bool noOverlapsAllCovered) {
	// Take the notParallelp tree under the case statement created by V3Assert
	// If the statement was proven to have no overlaps and all cases covered, we're done with it.
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
    virtual void visit(AstCase* nodep, AstNUser*) {
	V3Case::caseLint(nodep);
	nodep->iterateChildren(*this);
	if (debug()>=9) nodep->dumpTree(cout," case_old: ");
	if (isCaseTreeFast(nodep) && v3Global.opt.oCase()) {
	    // It's a simple priority encoder or complete statement
	    // we can make a tree of statements to avoid extra comparisons
	    ++m_statCaseFast;
	    replaceCaseFast(nodep); nodep=NULL;
	} else {
	    ++m_statCaseSlow;
	    // cppcheck-supporess uselessAssignmentPtrArg
	    replaceCaseComplicated(nodep); nodep=NULL;
	}
    }
    //--------------------
    // Default: Just iterate
    virtual void visit(AstNode* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
    }

public:
    // CONSTUCTORS
    CaseVisitor(AstNetlist* nodep) {
	m_caseNoOverlapsAllCovered = false;
	nodep->accept(*this);
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
    CaseVisitor visitor (nodep);
    V3Global::dumpCheckGlobalTree("case.tree", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}
void V3Case::caseLint(AstNodeCase* nodep) {
    UINFO(4,__FUNCTION__<<": "<<endl);
    CaseLintVisitor visitor (nodep);
}
