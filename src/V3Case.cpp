// $Id$
//*************************************************************************
// DESCRIPTION: Verilator: Break case statements up and add Unknown assigns
//
// Code available from: http://www.veripool.com/verilator
//
// AUTHORS: Wilson Snyder with Paul Wasson, Duane Gabli
//
//*************************************************************************
//
// Copyright 2003-2006 by Wilson Snyder.  This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// General Public License or the Perl Artistic License.
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
//	Constants:
//	    RHS, Replace 5'bx_1_x with a module global we init to a random value
//		CONST(5'bx_1_x) -> VARREF(_{numberedtemp})
//				-> VAR(_{numberedtemp})
//				-> INITIAL(VARREF(_{numberedtemp}), OR(5'bx_1_x,AND(random,5'b0_1_x))
//		OPTIMIZE: Must not collapse this initial back into the equation.
//
//*************************************************************************

#include "config.h"
#include <stdio.h>
#include <stdarg.h>
#include <unistd.h>
#include <algorithm>

#include "V3Global.h"
#include "V3Case.h"
#include "V3Ast.h"
#include "V3Stats.h"

#define CASE_OVERLAP_WIDTH 12	// Maximum width we can check for overlaps in

//######################################################################

class CaseLintVisitor : public AstNVisitor {
private:
    AstNodeCase* m_caseExprp;	// Under a CASE value node, if so the relevant case statement
    //int debug() { return 9; }

    virtual void visit(AstNodeCase* nodep, AstNUser*) {
	// We report a syntax error on empty "case (x) endcase" blocks, so never no items at all
	if (!nodep->itemsp()) nodep->v3fatalSrc("No items (not even default) under case statement?\n");

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
	if (!nodep->castCase() || !nodep->castCase()->casex()) {
	    m_caseExprp = nodep;
	    nodep->exprp()->accept(*this);
	    for (AstCaseItem* itemp = nodep->itemsp(); itemp; itemp=itemp->nextp()->castCaseItem()) {
		itemp->condsp()->iterateAndNext(*this);
	    }
	    m_caseExprp = NULL;
	}
    }
    virtual void visit(AstConst* nodep, AstNUser*) {
	if (m_caseExprp && nodep->num().isFourState()) {
	    if (m_caseExprp->castGenCase()) {
		nodep->v3error("Use of x/? constant in generate case statement, (no such thing as 'generate casez')");
	    } else {
		nodep->v3error("Use of x/? constant in case statement, (perhaps intended casex/casez)");
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

    // STATE
    V3Double0	m_statCaseFast;	// Statistic tracking
    V3Double0	m_statCaseSlow;	// Statistic tracking

    // Per-CASE
    int		m_caseWidth;	// Width of valueItems
    int		m_caseItems;	// Number of caseItem unique values
    int		m_caseNoOverlapsAllCovered;	// Proven to be synopsys parallel_case compliant
    AstNode*	m_valueItem[1<<CASE_OVERLAP_WIDTH];  // For each possible value, the case branch we need

    //int debug() { return 9; }

    // METHODS
    bool checkCaseTree(AstCase* nodep) {
	int width = 0;
	m_caseItems = 0;
	m_caseNoOverlapsAllCovered = true;
	for (AstCaseItem* itemp = nodep->itemsp(); itemp; itemp=itemp->nextp()->castCaseItem()) {
	    for (AstNode* icondp = itemp->condsp(); icondp!=NULL; icondp=icondp->nextp()) {
		if (icondp->width() > width) width = icondp->width();
		if (!icondp->castConst()) width = 999;  // Can't parse; not a constant
		m_caseItems++;
	    }
	}
	if (width==0 || width > CASE_OVERLAP_WIDTH) {
	    m_caseNoOverlapsAllCovered = false;
	    return false;	// Too wide for analysis
	}
	m_caseWidth = width;
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
		V3Number nummask (itemp->fileline(), iconstp->width());
		nummask.opBitsNonX(iconstp->num());
		uint32_t mask = nummask.asInt();
		V3Number numval  (itemp->fileline(), iconstp->width());
		numval.opBitsOne(iconstp->num());
		uint32_t val  = numval.asInt();
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
	    // Defaults were moved to last in the caseitem list by V3Link
	    if (!itemp->condsp()) {  // Case statement's default... Fill the table
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
	    return m_valueItem[upperValue];
	}
	else {
	    // Make left and right subtrees
	    // cexpr[msb:lsb] == 1
	    AstNode* tree0p = replaceCaseFastRecurse(cexprp, msb-1, upperValue | 0);
	    AstNode* tree1p = replaceCaseFastRecurse(cexprp, msb-1, upperValue | (1UL<<msb));

	    if (tree0p == tree1p) {
		// Same logic on both sides, so we can just return one of em
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
	    if (same) return tree0p;

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
	AstNode* cexprp = nodep->exprp();
	cexprp->unlinkFrBack();

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

	if (ifrootp) nodep->replaceWith(ifrootp);
	else nodep->unlinkFrBack();
	if (debug()>=9) ifrootp->dumpTree(cout,"    _simp: ");
    }

    void replaceCaseComplicated(AstCase* nodep) {
	// CASEx(cexpr,ITEM(icond1,istmts1),ITEM(icond2,istmts2),ITEM(default,istmts3))
	// ->  IF((cexpr==icond1),istmts1,
	//		         IF((EQ (AND MASK cexpr) (AND MASK icond1)
	//				,istmts2, istmts3
	AstNode* cexprp = nodep->exprp()->unlinkFrBack();
	AstNode* ifrootp = NULL;
	AstNode* ifnextp = NULL;
	for (AstCaseItem* itemp = nodep->itemsp(); itemp; itemp=itemp->nextp()->castCaseItem()) {
	    AstNode* istmtsp = itemp->bodysp();   // Maybe null -- no action.
	    if (istmtsp) istmtsp->unlinkFrBackWithNext();
	    if (!itemp->condsp()) {
		// Default clause.  We reordered in link, so default is always last
		if (ifnextp) {
		    if (istmtsp) ifnextp->castIf()->addElsesp(istmtsp);
		} else {   // Just a empty case default: endcase
		    ifnextp = istmtsp;
		}
		if (!ifrootp) ifrootp = istmtsp;
		ifnextp = istmtsp;
		itemp = NULL; break;
	    } else {
		// Expressioned clause
		AstNode* icondNextp = NULL;
		AstNode* ifexprp = NULL;	// If expression to test
		for (AstNode* icondp = itemp->condsp(); icondp!=NULL; icondp=icondNextp) {
		    icondNextp = icondp->nextp();
		    icondp->unlinkFrBack();
		    
		    AstNode* and1p;
		    AstNode* and2p;
		    AstConst* iconstp = icondp->castConst();
		    if (iconstp && iconstp->num().isFourState()
			&& nodep->casex()) {
			V3Number nummask (itemp->fileline(), iconstp->width());
			nummask.opBitsNonX(iconstp->num());
			V3Number numval  (itemp->fileline(), iconstp->width());
			numval.opBitsOne(iconstp->num());
			and1p = new AstAnd(itemp->fileline(), cexprp->cloneTree(false),
					   new AstConst(itemp->fileline(), nummask));
			and2p = new AstAnd(itemp->fileline(), 
					   new AstConst(itemp->fileline(), numval),
					   new AstConst(itemp->fileline(), nummask));
		    } else {
			// Not a caseX mask, we can simply build CASEEQ(cexpr icond)
			and1p = cexprp->cloneTree(false);
			and2p = icondp;
		    }
		    AstEq* condp = new AstEq(itemp->fileline(), and1p, and2p);
		    if (!ifexprp) {
			ifexprp = condp;
		    } else {
			ifexprp = new AstLogOr(itemp->fileline(), ifexprp, condp);
		    }
		}

		// Make the new IF and attach in the tree
		if (ifexprp) {
		    AstIf* newp = new AstIf(itemp->fileline(), ifexprp, istmtsp, NULL);
		    if (ifnextp) {
			ifnextp->castIf()->addElsesp(newp);
		    }
		    if (!ifrootp) ifrootp = newp;
		    ifnextp = newp;
		}
	    }
	}
	// Handle any assertions
	replaceCaseParallel(nodep, false);
	// Replace the CASE... with IF...
	if (ifrootp) nodep->replaceWith(ifrootp);
	else nodep->unlinkFrBack();
	if (debug()>=9) ifrootp->dumpTree(cout,"     _new: ");
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

    // VISITORS
    virtual void visit(AstCase* nodep, AstNUser*) {
	V3Case::caseLint(nodep);
	nodep->iterateChildren(*this);
	if (debug()>=9) nodep->dumpTree(cout," case_old: ");
	if (checkCaseTree(nodep) && v3Global.opt.oCase()) {
	    // It's a simple priority encoder or complete statement
	    // we can make a tree of statements to avoid extra comparisons
	    m_statCaseFast++;
	    replaceCaseFast(nodep); nodep=NULL;
	} else {
	    m_statCaseSlow++;
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
    CaseVisitor(AstNode* nodep) {
	m_caseNoOverlapsAllCovered = false;
	nodep->accept(*this);
    }
    virtual ~CaseVisitor() {
	V3Stats::addStat("Optimizations, Cases parallelized", m_statCaseFast);
	V3Stats::addStat("Optimizations, Cases priority-encoded", m_statCaseSlow);
    }
};

//######################################################################
// Case class functions

void V3Case::caseAll(AstNetlist* nodep) {
    UINFO(2,__FUNCTION__<<": "<<endl);
    CaseVisitor visitor (nodep);
}
void V3Case::caseLint(AstNodeCase* nodep) {
    UINFO(2,__FUNCTION__<<": "<<endl);
    CaseLintVisitor visitor (nodep);
}
