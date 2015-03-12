// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Break always into sensitivity active domains
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
// V3Active's Transformations:
//
// Note this can be called multiple times.
//   Create a IACTIVE(initial), SACTIVE(combo)
//	ALWAYS: Remove any-edges from sense list
//	    If no POS/NEG in senselist, Fold into SACTIVE(combo)
//	    Else fold into SACTIVE(sequent).
//	    OPTIMIZE: When support async clocks, fold into that active if possible
//	INITIAL: Move into IACTIVE
//	WIRE: Move into SACTIVE(combo)
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"
#include <cstdio>
#include <cstdarg>
#include <unistd.h>
#include <map>
#include <algorithm>
#include <vector>

#include "V3Global.h"
#include "V3Active.h"
#include "V3Ast.h"
#include "V3EmitCBase.h"
#include "V3Const.h"

//***** See below for main transformation engine

//######################################################################
// Collect existing active names

class ActiveBaseVisitor : public AstNVisitor {
protected:
    static int debug() {
	static int level = -1;
	if (VL_UNLIKELY(level < 0)) level = v3Global.opt.debugSrcLevel(__FILE__);
	return level;
    }
};

class ActiveNamer : public ActiveBaseVisitor {
private:
    typedef std::map<string,AstActive*> ActiveNameMap;
    // STATE
    AstScope*	m_scopep;		// Current scope to add statement to
    AstActive*	m_iActivep;		// For current scope, the IActive we're building
    AstActive*	m_cActivep;		// For current scope, the SActive(combo) we're building
    vector<AstActive*>	m_activeVec;	// List of sensitive actives, for folding
    // METHODS
    void addActive(AstActive* nodep) {
	if (!m_scopep) nodep->v3fatalSrc("NULL scope");
	m_scopep->addActivep(nodep);
    }
    // VISITORS
    virtual void visit(AstScope* nodep, AstNUser*) {
	m_scopep = nodep;
	m_iActivep = NULL;
	m_cActivep = NULL;
	m_activeVec.clear();
	nodep->iterateChildren(*this);
	// Don't clear scopep, the namer persists beyond this visit
    }
    virtual void visit(AstSenTree* nodep, AstNUser*) {
	// Simplify sensitivity list
	V3Const::constifyExpensiveEdit(nodep); nodep=NULL;
    }
    // Empty visitors, speed things up
    virtual void visit(AstNodeStmt* nodep, AstNUser*) { }
    //--------------------
    // Default
    virtual void visit(AstNode* nodep, AstNUser*) {
	// Default: Just iterate
	nodep->iterateChildren(*this);
    }
    // METHODS
public:
    AstScope* scopep() { return m_scopep; }
    AstActive* getCActive(FileLine* fl) {
	if (!m_cActivep) {
	    m_cActivep = new AstActive(fl, "combo",
				       new AstSenTree(fl, new AstSenItem(fl,AstSenItem::Combo())));
	    m_cActivep->sensesStorep(m_cActivep->sensesp());
	    addActive(m_cActivep);
	}
	return m_cActivep;
    }
    AstActive* getIActive(FileLine* fl) {
	if (!m_iActivep) {
	    m_iActivep = new AstActive(fl, "initial",
				       new AstSenTree(fl, new AstSenItem(fl,AstSenItem::Initial())));
	    m_iActivep->sensesStorep(m_iActivep->sensesp());
	    addActive(m_iActivep);
	}
	return m_iActivep;
    }
    AstActive* getActive(FileLine* fl, AstSenTree* sensesp) {
	// Return a sentree in this scope that matches given sense list.
	// Not the fastest, but scopes tend to have few clocks
	AstActive* activep = NULL;
	//sitemsp->dumpTree(cout,"  Lookingfor: ");
	for (vector<AstActive*>::iterator it = m_activeVec.begin(); it!=m_activeVec.end(); ++it) {
	    activep = *it;
	    if (activep) {  // Not deleted
		// Compare the list
		AstSenTree* asenp = activep->sensesp();
		if (asenp->sameTree(sensesp)) {
		    UINFO(8,"    Found ACTIVE "<<activep<<endl);
		    goto found;
		}
	    }
	    activep = NULL;
	}
      found:
	// Not found, form a new one
	if (!activep) {
	    AstSenTree* newsenp = sensesp->cloneTree(false);
	    activep = new AstActive(fl, "sequent", newsenp);
	    activep->sensesStorep(activep->sensesp());
	    UINFO(8,"    New ACTIVE "<<activep<<endl);
	    // Form the sensitivity list
	    addActive(activep);
	    m_activeVec.push_back(activep);
	    // Note actives may have also been added above in the Active visitor
	}
	return activep;
    }
public:
    // CONSTUCTORS
    ActiveNamer() {
	m_scopep = NULL;
	m_iActivep = NULL;
	m_cActivep = NULL;
    }
    virtual ~ActiveNamer() {}
    void main(AstScope* nodep) {
	nodep->accept(*this);
    }
};

//######################################################################
// Active AssignDly replacement functions

class ActiveDlyVisitor : public ActiveBaseVisitor {
public:
    enum CheckType { CT_SEQ, CT_COMBO, CT_INITIAL, CT_LATCH };
private:
    CheckType 	m_check;	// Combo logic or other
    AstNode*	m_alwaysp;	// Always we're under
    AstNode*	m_assignp;	// In assign
    // VISITORS
    virtual void visit(AstAssignDly* nodep, AstNUser*) {
	if (m_check != CT_SEQ) {
	    // Convert to a non-delayed assignment
	    UINFO(5,"    ASSIGNDLY "<<nodep<<endl);
	    if (m_check == CT_INITIAL) {
		nodep->v3warn(INITIALDLY,"Delayed assignments (<=) in initial or final block; suggest blocking assignments (=).");
	    } else if (m_check == CT_LATCH) {
		// Suppress. Shouldn't matter that the interior of the latch races 
	    } else {
		nodep->v3warn(COMBDLY,"Delayed assignments (<=) in non-clocked (non flop or latch) block; suggest blocking assignments (=).");
	    }
	    AstNode* newp = new AstAssign (nodep->fileline(),
					   nodep->lhsp()->unlinkFrBack(),
					   nodep->rhsp()->unlinkFrBack());
	    nodep->replaceWith(newp);
	    nodep->deleteTree(); nodep = NULL;
	}
    }
    virtual void visit(AstAssign* nodep, AstNUser*) {
	if (m_check == CT_SEQ) {
	    AstNode* las = m_assignp;
	    m_assignp = nodep;
	    nodep->lhsp()->iterateAndNext(*this);
	    m_assignp = las;
	}
    }
    virtual void visit(AstVarRef* nodep, AstNUser*) {
	AstVar* varp=nodep->varp();
	if (m_check == CT_SEQ
	    && m_assignp
	    && !varp->isUsedLoopIdx() // Ignore loop indicies
	    && !varp->isTemp()
	    ) {
	    // Allow turning off warnings on the always, or the variable also
	    if (!m_alwaysp->fileline()->warnIsOff(V3ErrorCode::BLKSEQ)
		&& !m_assignp->fileline()->warnIsOff(V3ErrorCode::BLKSEQ)
		&& !varp->fileline()->warnIsOff(V3ErrorCode::BLKSEQ)
		) {
		m_alwaysp->fileline()->modifyWarnOff(V3ErrorCode::BLKSEQ, true);  // Complain just once for the entire always
		varp->fileline()->modifyWarnOff(V3ErrorCode::BLKSEQ, true);
		nodep->v3warn(BLKSEQ,"Blocking assignments (=) in sequential (flop or latch) block; suggest delayed assignments (<=).");
	    }
	}
    }
    //--------------------
    virtual void visit(AstNode* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
    }
public:
    // CONSTUCTORS
    ActiveDlyVisitor(AstNode* nodep, CheckType check) {
	m_alwaysp = nodep;
	m_check = check;
	m_assignp = NULL;
	nodep->accept(*this);
    }
    virtual ~ActiveDlyVisitor() {}
};

//######################################################################
// Active class functions

class ActiveVisitor : public ActiveBaseVisitor {
private:
    // NODE STATE
    //  Each call to V3Const::constify
    //   AstNode::user4()		Used by V3Const::constify, called below

    // STATE
    ActiveNamer	m_namer;	// Tracking of active names
    AstCFunc*   m_scopeFinalp;	// Final function for this scope
    bool	m_itemCombo;	// Found a SenItem combo
    bool	m_itemSequent;	// Found a SenItem sequential

    // VISITORS
    virtual void visit(AstScope* nodep, AstNUser*) {
	// Create required actives and add to scope
	UINFO(4," SCOPE   "<<nodep<<endl);
	// Clear last scope's names, and collect this scope's existing names
	m_namer.main(nodep);
	m_scopeFinalp = NULL;
	nodep->iterateChildren(*this);
    }
    virtual void visit(AstActive* nodep, AstNUser*) {
	// Actives are being formed, so we can ignore any already made
    }
    virtual void visit(AstInitial* nodep, AstNUser*) {
	// Relink to IACTIVE, unless already under it
	UINFO(4,"    INITIAL "<<nodep<<endl);
	ActiveDlyVisitor dlyvisitor (nodep, ActiveDlyVisitor::CT_INITIAL);
	AstActive* wantactivep = m_namer.getIActive(nodep->fileline());
	nodep->unlinkFrBack();
	wantactivep->addStmtsp(nodep);
    }
    virtual void visit(AstAssignAlias* nodep, AstNUser*) {
	// Relink to CACTIVE, unless already under it
	UINFO(4,"    ASSIGNW "<<nodep<<endl);
	AstActive* wantactivep = m_namer.getCActive(nodep->fileline());
	nodep->unlinkFrBack();
	wantactivep->addStmtsp(nodep);
    }
    virtual void visit(AstAssignW* nodep, AstNUser*) {
	// Relink to CACTIVE, unless already under it
	UINFO(4,"    ASSIGNW "<<nodep<<endl);
	AstActive* wantactivep = m_namer.getCActive(nodep->fileline());
	nodep->unlinkFrBack();
	wantactivep->addStmtsp(nodep);
    }
    virtual void visit(AstCoverToggle* nodep, AstNUser*) {
	// Relink to CACTIVE, unless already under it
	UINFO(4,"    COVERTOGGLE "<<nodep<<endl);
	AstActive* wantactivep = m_namer.getCActive(nodep->fileline());
	nodep->unlinkFrBack();
	wantactivep->addStmtsp(nodep);
    }
    virtual void visit(AstFinal* nodep, AstNUser*) {
	// Relink to CFUNC for the final
	UINFO(4,"    FINAL "<<nodep<<endl);
	if (!nodep->bodysp()) { // Empty, Kill it.
	    nodep->unlinkFrBack()->deleteTree(); nodep=NULL;
	    return;
	}
	ActiveDlyVisitor dlyvisitor (nodep, ActiveDlyVisitor::CT_INITIAL);
	if (!m_scopeFinalp) {
	    m_scopeFinalp = new AstCFunc(nodep->fileline(), "_final_"+m_namer.scopep()->nameDotless(), m_namer.scopep());
	    m_scopeFinalp->argTypes(EmitCBaseVisitor::symClassVar());
	    m_scopeFinalp->addInitsp(new AstCStmt(nodep->fileline(), EmitCBaseVisitor::symTopAssign()+"\n"));
	    m_scopeFinalp->dontCombine(true);
	    m_scopeFinalp->formCallTree(true);
	    m_scopeFinalp->slow(true);
	    m_namer.scopep()->addActivep(m_scopeFinalp);
	}
	nodep->unlinkFrBack();
	m_scopeFinalp->addStmtsp(new AstComment(nodep->fileline(), nodep->typeName()));
	m_scopeFinalp->addStmtsp(nodep->bodysp()->unlinkFrBackWithNext());
	nodep->deleteTree(); nodep = NULL;
    }

    // METHODS
    void visitAlways(AstNode* nodep, AstSenTree* oldsensesp, VAlwaysKwd kwd) {
	// Move always to appropriate ACTIVE based on its sense list
	if (oldsensesp
	    && oldsensesp->sensesp()
	    && oldsensesp->sensesp()->castSenItem()
	    && oldsensesp->sensesp()->castSenItem()->isNever()) {
	    // Never executing.  Kill it.
	    if (oldsensesp->sensesp()->nextp()) nodep->v3fatalSrc("Never senitem should be alone, else the never should be eliminated.");
	    nodep->unlinkFrBack()->deleteTree(); nodep=NULL;
	    return;
	}

	// Read sensitivitues
	m_itemCombo = false;
	m_itemSequent = false;
	oldsensesp->iterateAndNext(*this);
	bool combo = m_itemCombo;
	bool sequent = m_itemSequent;

	if (!combo && !sequent) combo=true;	// If no list, Verilog 2000: always @ (*)
	if (combo && sequent) {
	    nodep->v3error("Unsupported: Mixed edge (pos/negedge) and activity (no edge) sensitive activity list");
	    sequent = false;
	}

	AstActive* wantactivep = NULL;
	if (combo && !sequent) {
	    // Combo:  Relink to ACTIVE(combo)
	    wantactivep = m_namer.getCActive(nodep->fileline());
	} else {
	    // Sequential: Build a ACTIVE(name)
	    // OPTIMIZE: We could substitute a constant for things in the sense list, for example
	    // always (posedge RESET) { if (RESET).... }  we know RESET is true.
	    // Summarize a long list of combo inputs as just "combo"
#ifndef __COVERITY__ // Else dead code on next line.
	    if (combo) oldsensesp->addSensesp
			   (new AstSenItem(nodep->fileline(),AstSenItem::Combo()));
#endif
	    wantactivep = m_namer.getActive(nodep->fileline(), oldsensesp);
	}

	// Delete sensitivity list
	if (oldsensesp) {
	    oldsensesp->unlinkFrBackWithNext()->deleteTree(); oldsensesp=NULL;
	}

	// Move node to new active
	nodep->unlinkFrBack();
	wantactivep->addStmtsp(nodep);

	// Warn and/or convert any delayed assignments
	if (combo && !sequent) {
	    if (kwd == VAlwaysKwd::ALWAYS_LATCH) {
		ActiveDlyVisitor dlyvisitor (nodep, ActiveDlyVisitor::CT_LATCH);
	    } else {
		ActiveDlyVisitor dlyvisitor (nodep, ActiveDlyVisitor::CT_COMBO);
	    }
	}
	else if (!combo && sequent) {
	    ActiveDlyVisitor dlyvisitor (nodep, ActiveDlyVisitor::CT_SEQ);
	}
    }
    virtual void visit(AstAlways* nodep, AstNUser*) {
	// Move always to appropriate ACTIVE based on its sense list
	UINFO(4,"    ALW   "<<nodep<<endl);
	//if (debug()>=9) nodep->dumpTree(cout,"  Alw: ");

	if (!nodep->bodysp()) {
	    // Empty always.  Kill it.
	    nodep->unlinkFrBack()->deleteTree(); nodep=NULL;
	    return;
	}
	visitAlways(nodep, nodep->sensesp(), nodep->keyword());
    }
    virtual void visit(AstAlwaysPublic* nodep, AstNUser*) {
	// Move always to appropriate ACTIVE based on its sense list
	UINFO(4,"    ALWPub   "<<nodep<<endl);
	//if (debug()>=9) nodep->dumpTree(cout,"  Alw: ");
	visitAlways(nodep, nodep->sensesp(), VAlwaysKwd::ALWAYS);
    }
    virtual void visit(AstSenGate* nodep, AstNUser*) {
	AstSenItem* subitemp = nodep->sensesp();
	if (subitemp->edgeType() != AstEdgeType::ET_ANYEDGE
	    && subitemp->edgeType() != AstEdgeType::ET_POSEDGE
	    && subitemp->edgeType() != AstEdgeType::ET_NEGEDGE) {
	    nodep->v3fatalSrc("Strange activity type under SenGate");
	}
	nodep->iterateChildren(*this);
    }
    virtual void visit(AstSenItem* nodep, AstNUser*) {
	if (nodep->edgeType() == AstEdgeType::ET_ANYEDGE) {
	    m_itemCombo = true;
	    // Delete the sensitivity
	    // We'll add it as a generic COMBO SenItem in a moment.
	    nodep->unlinkFrBack()->deleteTree(); nodep=NULL;
	} else if (nodep->varrefp()) {
	    // V3LinkResolve should have cleaned most of these up
	    if (!nodep->varrefp()->width1()) nodep->v3error("Unsupported: Non-single bit wide signal pos/negedge sensitivity: "
							    <<nodep->varrefp()->prettyName());
	    m_itemSequent = true;
	    nodep->varrefp()->varp()->usedClock(true);
	}
    }

    // Empty visitors, speed things up
    virtual void visit(AstNodeMath* nodep, AstNUser*) {}
    virtual void visit(AstVarScope* nodep, AstNUser*) {}
    //--------------------
    virtual void visit(AstNode* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
    }
public:
    // CONSTUCTORS
    ActiveVisitor(AstNetlist* nodep) {
	m_scopeFinalp = NULL;
	m_itemCombo = false;
	m_itemSequent = false;
	nodep->accept(*this);
    }
    virtual ~ActiveVisitor() {}
};

//######################################################################
// Active class functions

void V3Active::activeAll(AstNetlist* nodep) {
    UINFO(2,__FUNCTION__<<": "<<endl);
    ActiveVisitor visitor (nodep);
    V3Global::dumpCheckGlobalTree("active.tree", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}
