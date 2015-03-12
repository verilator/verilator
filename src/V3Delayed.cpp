// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Add temporaries, such as for delayed nodes
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
// V3Delayed's Transformations:
//
// Each module:
//	Replace ASSIGNDLY var, exp
//	    With   ASSIGNDLY newvar, exp
//	    At top of block:  VAR  newvar
//	    At bottom of block: ASSIGNW var newvar
//		Need _x_dly = x at top of active if "x" is not always set
//			For now we'll say it's set if at top of block (not under IF, etc)
//		Need x = _x_dly at bottom of active if "x" is never referenced on LHS
//			in the active, and above rule applies too.  (If so, use x on LHS, not _x_dly.)
//
//	If a signal is set in multiple always blocks, we need a dly read & set with
//	multiple clock sensitivities.  We have 3 options:
//	    1. When detected, make a new ACTIVE and move earlier created delayed assignment there
//	    2. Form unique ACTIVE for every multiple clocked assignment
//	    3. Predetect signals from multiple always blocks and do #2 on them
//	    Since all 3 require a top activation cleanup, we do #2 which is easiest.
//
// ASSIGNDLY (BITSEL(ARRAYSEL (VARREF(v), bits), selbits), rhs)
// ->	VAR __Vdlyvset_x
// 	VAR __Vdlyvval_x
// 	VAR __Vdlyvdim_x
// 	VAR __Vdlyvlsb_x
//	ASSIGNW (__Vdlyvset_x,0)
//	...
//	ASSIGNW (VARREF(__Vdlyvval_x), rhs)
//	ASSIGNW (__Vdlyvdim_x, dimension_number)
//	ASSIGNW (__Vdlyvset_x, 1)
//	...
//	ASSIGNW (BITSEL(ARRAYSEL(VARREF(x), __Vdlyvdim_x), __Vdlyvlsb_x), __Vdlyvval_x)
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"
#include <cstdio>
#include <cstdarg>
#include <unistd.h>
#include <algorithm>
#include <map>
#include <deque>

#include "V3Global.h"
#include "V3Delayed.h"
#include "V3Ast.h"
#include "V3Stats.h"

//######################################################################
// Delayed state, as a visitor of each AstNode

class DelayedVisitor : public AstNVisitor {
private:
    // NODE STATE
    // Cleared each module:
    //  AstVarScope::user1p()	-> AstVarScope*.  Points to temp var created.
    //  AstVarScope::user2p()	-> AstActive*.  Points to activity block of signal (valid when AstVarScope::user1p is valid)
    //  AstVarScope::user4p()	-> AstAlwaysPost*.  Post block for this variable
    //  AstVarScope::user5()	-> VarUsage. Tracks delayed vs non-delayed usage
    //  AstVar::user2()		-> bool.  Set true if already made warning
    //  AstVar::user4()		-> int.   Vector number, for assignment creation
    //  AstVarRef::user2()	-> bool.  Set true if already processed
    //  AstAlwaysPost::user2()	-> ActActive*.  Points to activity block of signal (valid when AstAlwaysPost::user4p is valid)
    //  AstAlwaysPost::user4()	-> AstIf*.  Last IF (__Vdlyvset__) created under this AlwaysPost
    // Cleared each scope/active:
    //  AstAssignDly::user3()	-> AstVarScope*.  __Vdlyvset__ created for this assign
    //  AstAlwaysPost::user3()	-> AstVarScope*.  __Vdlyvset__ last referenced in IF
    AstUser1InUse	m_inuser1;
    AstUser2InUse	m_inuser2;
    AstUser3InUse	m_inuser3;
    AstUser4InUse	m_inuser4;
    AstUser5InUse	m_inuser5;

    enum VarUsage { VU_NONE=0, VU_DLY=1, VU_NONDLY=2 };

    // STATE
    AstActive*		m_activep;	// Current activate
    AstCFunc*		m_cfuncp;	// Current public C Function
    AstAssignDly*	m_nextDlyp;	// Next delayed assignment in a list of assignments
    bool		m_inDly;	// True in delayed assignments
    bool		m_inLoop;	// True in for loops
    bool		m_inInitial;	// True in intial blocks
    typedef std::map<pair<AstNodeModule*,string>,AstVar*> VarMap;
    VarMap		m_modVarMap;	// Table of new var names created under module
    V3Double0		m_statSharedSet;// Statistic tracking


    // METHODS
    static int debug() {
	static int level = -1;
	if (VL_UNLIKELY(level < 0)) level = v3Global.opt.debugSrcLevel(__FILE__);
	return level;
    }

    void markVarUsage(AstVarScope* nodep, uint32_t flags) {
	//UINFO(4," MVU "<<flags<<" "<<nodep<<endl);
	nodep->user5( nodep->user5() | flags );
	if ((nodep->user5() & VU_DLY) && (nodep->user5() & VU_NONDLY)) {
	    nodep->v3warn(BLKANDNBLK,"Unsupported: Blocked and non-blocking assignments to same variable: "<<nodep->varp()->prettyName());
	}
    }
    AstVarScope* createVarSc(AstVarScope* oldvarscp, string name, int width/*0==fromoldvar*/, AstNodeDType* newdtypep) {
	// Because we've already scoped it, we may need to add both the AstVar and the AstVarScope
	if (!oldvarscp->scopep()) oldvarscp->v3fatalSrc("Var unscoped");
	AstVar* varp;
	AstNodeModule* addmodp = oldvarscp->scopep()->modp();
	// We need a new AstVar, but only one for all scopes, to match the new AstVarScope
	VarMap::iterator it = m_modVarMap.find(make_pair(addmodp,name));
	if (it != m_modVarMap.end()) {
	    // Created module's AstVar earlier under some other scope
	    varp = it->second;
	} else {
	    if (newdtypep) {
		varp = new AstVar (oldvarscp->fileline(), AstVarType::BLOCKTEMP, name, newdtypep);
	    } else if (width==0) {
		varp = new AstVar (oldvarscp->fileline(), AstVarType::BLOCKTEMP, name, oldvarscp->varp());
		varp->dtypeFrom(oldvarscp);
	    } else { // Used for vset and dimensions, so can zero init
		varp = new AstVar (oldvarscp->fileline(), AstVarType::BLOCKTEMP, name, VFlagBitPacked(), width);
	    }
	    addmodp->addStmtp(varp);
	    m_modVarMap.insert(make_pair(make_pair(addmodp, name), varp));
	}

	AstVarScope* varscp = new AstVarScope (oldvarscp->fileline(), oldvarscp->scopep(), varp);
	oldvarscp->scopep()->addVarp(varscp);
	return varscp;
    }

    AstActive* createActivePost(AstVarRef* varrefp) {
	AstActive* newactp = new AstActive (varrefp->fileline(), "sequentdly",
					    m_activep->sensesp());
	m_activep->addNext(newactp);
	return newactp;
    }
    void checkActivePost(AstVarRef* varrefp, AstActive* oldactivep) {
	// Check for MULTIDRIVEN, and if so make new sentree that joins old & new sentree
	if (!oldactivep) varrefp->v3fatalSrc("<= old dly assignment not put under sensitivity block");
	if (oldactivep->sensesp() != m_activep->sensesp()) {
	    if (!varrefp->varp()->fileline()->warnIsOff(V3ErrorCode::MULTIDRIVEN)
		&& !varrefp->varp()->user2()) {
		varrefp->varp()->v3warn(MULTIDRIVEN,"Signal has multiple driving blocks: "<<varrefp->varp()->prettyName()<<endl
					<<varrefp->warnMore()<<"... Location of first driving block"<<endl
					<<oldactivep->warnMore()<<"... Location of other driving block");
		varrefp->varp()->user2(true);
	    }
	    UINFO(4,"AssignDupDlyVar: "<<varrefp<<endl);
	    UINFO(4,"  Act: "<<m_activep<<endl);
	    UINFO(4,"  Act: "<<oldactivep<<endl);
	    // Make a new sensitivity list, which is the combination of both blocks
	    AstNodeSenItem* sena = m_activep->sensesp()->sensesp()->cloneTree(true);
	    AstNodeSenItem* senb = oldactivep->sensesp()->sensesp()->cloneTree(true);
	    AstSenTree* treep = new AstSenTree(m_activep->fileline(), sena);
	    if (senb) treep->addSensesp(senb);
	    if (AstSenTree* storep = oldactivep->sensesStorep()) {
		storep->unlinkFrBack();
		pushDeletep(storep);
	    }
	    oldactivep->sensesStorep(treep);
	    oldactivep->sensesp(treep);
	}
    }

    AstNode* createDlyArray(AstAssignDly* nodep, AstNode* lhsp) {
	// Create delayed assignment
	// See top of this file for transformation
	// Return the new LHS for the assignment, Null = unlink
	// Find selects
	AstNode* newlhsp = NULL;	// NULL = unlink old assign
	AstSel*  bitselp = NULL;
	AstArraySel*  arrayselp = NULL;
	if (lhsp->castSel()) {
	    bitselp = lhsp->castSel();
	    arrayselp = bitselp->fromp()->castArraySel();
	} else {
	    arrayselp = lhsp->castArraySel();
	}
	if (!arrayselp) nodep->v3fatalSrc("No arraysel under bitsel?");
	if (arrayselp->length()!=1) nodep->v3fatalSrc("ArraySel with length!=1 should have been removed in V3Slice");

	UINFO(4,"AssignDlyArray: "<<nodep<<endl);
	//
	//=== Dimensions: __Vdlyvdim__
	deque<AstNode*> dimvalp;		// Assignment value for each dimension of assignment
	AstNode* dimselp=arrayselp;
	for (; dimselp->castArraySel(); dimselp=dimselp->castArraySel()->fromp()) {
	    AstNode* valp = dimselp->castArraySel()->bitp()->unlinkFrBack();
	    dimvalp.push_front(valp);
	}
	AstVarRef* varrefp = dimselp->castVarRef();
	if (!varrefp) nodep->v3fatalSrc("No var underneath arraysels\n");
	if (!varrefp->varScopep()) varrefp->v3fatalSrc("Var didn't get varscoped in V3Scope.cpp\n");
	varrefp->unlinkFrBack();
	AstVar* oldvarp = varrefp->varp();
	int modVecNum = oldvarp->user4();  oldvarp->user4(modVecNum+1);
	//
	deque<AstNode*> dimreadps;		// Read value for each dimension of assignment
	for (unsigned dimension=0; dimension<dimvalp.size(); dimension++) {
	    AstNode* dimp = dimvalp[dimension];
	    if (dimp->castConst()) { // bit = const, can just use it
		dimreadps.push_front(dimp);
	    } else {
		string bitvarname = (string("__Vdlyvdim")+cvtToStr(dimension)
				     +"__"+oldvarp->shortName()+"__v"+cvtToStr(modVecNum));
		AstVarScope* bitvscp = createVarSc(varrefp->varScopep(), bitvarname, dimp->width(), NULL);
		AstAssign* bitassignp
		    = new AstAssign (nodep->fileline(),
				     new AstVarRef(nodep->fileline(), bitvscp, true),
				     dimp);
		nodep->addNextHere(bitassignp);
		dimreadps.push_front(new AstVarRef(nodep->fileline(), bitvscp, false));
	    }
	}
	//
	//=== Bitselect: __Vdlyvlsb__
	AstNode* bitreadp=NULL;  // Code to read Vdlyvlsb
	if (bitselp) {
	    AstNode* lsbvaluep = bitselp->lsbp()->unlinkFrBack();
	    if (bitselp->fromp()->castConst()) {// vlsb = constant, can just push constant into where we use it
		bitreadp = lsbvaluep;
	    } else {
		string bitvarname = (string("__Vdlyvlsb__")+oldvarp->shortName()+"__v"+cvtToStr(modVecNum));
		AstVarScope* bitvscp = createVarSc(varrefp->varScopep(), bitvarname, lsbvaluep->width(), NULL);
		AstAssign* bitassignp = new AstAssign (nodep->fileline(),
						       new AstVarRef(nodep->fileline(), bitvscp, true),
						       lsbvaluep);
		nodep->addNextHere(bitassignp);
		bitreadp = new AstVarRef(nodep->fileline(), bitvscp, false);
	    }
	}
	//
	//=== Value: __Vdlyvval__
	AstNode* valreadp;	// Code to read Vdlyvval
	if (nodep->rhsp()->castConst()) {	// vval = constant, can just push constant into where we use it
	    valreadp = nodep->rhsp()->unlinkFrBack();
	} else {
	    string valvarname = (string("__Vdlyvval__")+oldvarp->shortName()+"__v"+cvtToStr(modVecNum));
	    AstVarScope* valvscp = createVarSc(varrefp->varScopep(), valvarname, 0, nodep->rhsp()->dtypep());
	    newlhsp = new AstVarRef(nodep->fileline(), valvscp, true);
	    valreadp = new AstVarRef(nodep->fileline(), valvscp, false);
	}
	//
	//=== Setting/not setting boolean: __Vdlyvset__
	AstVarScope* setvscp;
	AstAssignPre* setinitp = NULL;

	if (nodep->user3p()) {
	    // Simplistic optimization.  If the previous statement in same scope was also a =>,
	    // then we told this nodep->user3 we can use its Vdlyvset rather than making a new one.
	    // This is good for code like:
	    //    for (i=0; i<5; i++)  vector[i] <= something;
	    setvscp = nodep->user3p()->castNode()->castVarScope();
	    ++m_statSharedSet;
	} else {  // Create new one
	    string setvarname = (string("__Vdlyvset__")+oldvarp->shortName()+"__v"+cvtToStr(modVecNum));
	    setvscp = createVarSc(varrefp->varScopep(), setvarname, 1, NULL);
	    setinitp = new AstAssignPre (nodep->fileline(),
					 new AstVarRef(nodep->fileline(), setvscp, true),
					 new AstConst(nodep->fileline(), 0));
	    AstAssign* setassignp
		= new AstAssign (nodep->fileline(),
				 new AstVarRef(nodep->fileline(), setvscp, true),
				 new AstConst(nodep->fileline(),
					      V3Number(nodep->fileline(),1,true)));
	    nodep->addNextHere(setassignp);
	}
	if (m_nextDlyp) {  // Tell next assigndly it can share the variable
	    m_nextDlyp->user3p(setvscp);
	}
	//
	// Create ALWAYSPOST for delayed variable
	// We add all logic to the same block if it's for the same memory
	// This insures that multiple assignments to the same memory will result
	// in correctly ordered code - the last assignment must be last.
	// It also has the nice side effect of assisting cache locality.
	AstNode* selectsp = varrefp;
	for (int dimension=int(dimreadps.size())-1; dimension>=0; --dimension) {
	    selectsp = new AstArraySel(nodep->fileline(), selectsp, dimreadps[dimension]);
	}
	if (bitselp) {
	    selectsp = new AstSel(nodep->fileline(), selectsp, bitreadp,
				  bitselp->widthp()->cloneTree(false));
	}
	// Build "IF (changeit) ...
	UINFO(9,"   For "<<setvscp<<endl);
	UINFO(9,"     & "<<varrefp<<endl);
	AstAlwaysPost* finalp = varrefp->varScopep()->user4p()->castNode()->castAlwaysPost();
	if (finalp) {
	    AstActive* oldactivep = finalp->user2p()->castNode()->castActive();
	    checkActivePost(varrefp, oldactivep);
	    if (setinitp) oldactivep->addStmtsp(setinitp);
	} else { // first time we've dealt with this memory
	    finalp = new AstAlwaysPost(nodep->fileline(), NULL/*sens*/, NULL/*body*/);
	    UINFO(9,"     Created "<<finalp<<endl);
	    AstActive* newactp = createActivePost(varrefp);
	    newactp->addStmtsp(finalp);
	    varrefp->varScopep()->user4p(finalp);
	    finalp->user2p(newactp);
	    if (setinitp) newactp->addStmtsp(setinitp);
	}
	AstIf* postLogicp;
	if (finalp->user3p()->castNode() == setvscp) {
	    // Optimize as above; if sharing Vdlyvset *ON SAME VARIABLE*,
	    // we can share the IF statement too
	    postLogicp = finalp->user4p()->castNode()->castIf();
	    if (!postLogicp) nodep->v3fatalSrc("Delayed assignment misoptimized; prev var found w/o associated IF");
	} else {
	    postLogicp = new AstIf (nodep->fileline(),
				    new AstVarRef(nodep->fileline(), setvscp, false),
				    NULL,
				    NULL);
	    UINFO(9,"     Created "<<postLogicp<<endl);
	    finalp->addBodysp(postLogicp);
	    finalp->user3p(setvscp);	// Remember IF's vset variable
	    finalp->user4p(postLogicp);	// and the associated IF, as we may be able to reuse it
	}
	postLogicp->addIfsp(new AstAssign(nodep->fileline(), selectsp, valreadp));
	return newlhsp;
    }

    // VISITORS
    virtual void visit(AstNetlist* nodep, AstNUser*) {
	//VV*****  We reset all userp() on the netlist
	m_modVarMap.clear();
	nodep->iterateChildren(*this);
    }
    virtual void visit(AstScope* nodep, AstNUser*) {
	UINFO(4," MOD   "<<nodep<<endl);
	AstNode::user3ClearTree();
	nodep->iterateChildren(*this);
    }
    virtual void visit(AstCFunc* nodep, AstNUser*) {
	m_cfuncp = nodep;
	nodep->iterateChildren(*this);
	m_cfuncp = NULL;
    }
    virtual void visit(AstActive* nodep, AstNUser*) {
	m_activep = nodep;
	bool oldinit = m_inInitial;
	m_inInitial = nodep->hasInitial();
	AstNode::user3ClearTree();  // Two sets to same variable in different actives must use different vars.
	nodep->iterateChildren(*this);
	m_inInitial = oldinit;
    }
    virtual void visit(AstAssignDly* nodep, AstNUser*) {
	m_inDly = true;
	m_nextDlyp = nodep->nextp()->castAssignDly();  // Next assignment in same block, maybe NULL.
	if (m_cfuncp) nodep->v3error("Unsupported: Delayed assignment inside public function/task");
	if (nodep->lhsp()->castArraySel()
	    || (nodep->lhsp()->castSel()
		&& nodep->lhsp()->castSel()->fromp()->castArraySel())) {
	    AstNode* lhsp = nodep->lhsp()->unlinkFrBack();
	    AstNode* newlhsp = createDlyArray(nodep, lhsp);
	    if (m_inLoop) nodep->v3warn(E_BLKLOOPINIT,"Unsupported: Delayed assignment to array inside for loops (non-delayed is ok - see docs)");
	    if (newlhsp) {
		nodep->lhsp(newlhsp);
	    } else {
		nodep->unlinkFrBack()->deleteTree(); nodep=NULL;
	    }
	    lhsp->deleteTree(); lhsp=NULL;
	}
	else {
	    nodep->iterateChildren(*this);
	}
	m_inDly = false;
	m_nextDlyp = NULL;
    }

    virtual void visit(AstVarRef* nodep, AstNUser*) {
	if (!nodep->user2Inc()) {  // Not done yet
	    if (m_inDly && nodep->lvalue()) {
		UINFO(4,"AssignDlyVar: "<<nodep<<endl);
		markVarUsage(nodep->varScopep(), VU_DLY);
		if (!m_activep) nodep->v3fatalSrc("<= not under sensitivity block");
		if (!m_activep->hasClocked()) nodep->v3error("Internal: Blocking <= assignment in non-clocked block, should have converted in V3Active");
		AstVarScope* oldvscp = nodep->varScopep();
		if (!oldvscp) nodep->v3fatalSrc("Var didn't get varscoped in V3Scope.cpp\n");
		AstVarScope* dlyvscp = oldvscp->user1p()->castNode()->castVarScope();
		if (dlyvscp) {  // Multiple use of delayed variable
		    AstActive* oldactivep = dlyvscp->user2p()->castNode()->castActive();
		    checkActivePost(nodep, oldactivep);
		}
		if (!dlyvscp) {  // First use of this delayed variable
		    string newvarname = (string("__Vdly__")+nodep->varp()->shortName());
		    dlyvscp = createVarSc(oldvscp, newvarname, 0, NULL);
		    AstNodeAssign* prep
			= new AstAssignPre (nodep->fileline(),
					    new AstVarRef(nodep->fileline(), dlyvscp, true),
					    new AstVarRef(nodep->fileline(), oldvscp, false));
		    AstNodeAssign* postp
			= new AstAssignPost (nodep->fileline(),
					     new AstVarRef(nodep->fileline(), oldvscp, true),
					     new AstVarRef(nodep->fileline(), dlyvscp, false));
		    postp->lhsp()->user2(true);	// Don't detect this assignment
		    oldvscp->user1p(dlyvscp);  // So we can find it later
		    // Make new ACTIVE with identical sensitivity tree
		    AstActive* newactp = createActivePost(nodep);
		    dlyvscp->user2p(newactp);
		    newactp->addStmtsp(prep);	// Add to FRONT of statements
		    newactp->addStmtsp(postp);
		}
		AstVarRef* newrefp = new AstVarRef(nodep->fileline(), dlyvscp, true);
		newrefp->user2(true);  // No reason to do it again
		nodep->replaceWith(newrefp); nodep->deleteTree(); nodep=NULL;
	    }
	    else if (!m_inDly && nodep->lvalue()) {
		//UINFO(9,"NBA "<<nodep<<endl);
		if (!m_inInitial) {
		    UINFO(4,"AssignNDlyVar: "<<nodep<<endl);
		    markVarUsage(nodep->varScopep(), VU_NONDLY);
		}
	    }
	}
    }

    virtual void visit(AstNodeFor* nodep, AstNUser*) {
	nodep->v3fatalSrc("For statements should have been converted to while statements in V3Begin\n");
    }
    virtual void visit(AstWhile* nodep, AstNUser*) {
	bool oldloop = m_inLoop;
	m_inLoop = true;
	nodep->iterateChildren(*this);
	m_inLoop = oldloop;
    }

    //--------------------
    // Default: Just iterate
    virtual void visit(AstNode* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
    }

public:
    // CONSTUCTORS
    DelayedVisitor(AstNetlist* nodep) {
	m_inDly = false;
	m_activep=NULL;
	m_cfuncp=NULL;
	m_nextDlyp=NULL;
	m_inLoop = false;
	m_inInitial = false;

	nodep->accept(*this);
    }
    virtual ~DelayedVisitor() {
	V3Stats::addStat("Optimizations, Delayed shared-sets", m_statSharedSet);
    }
};

//######################################################################
// Delayed class functions

void V3Delayed::delayedAll(AstNetlist* nodep) {
    UINFO(2,__FUNCTION__<<": "<<endl);
    DelayedVisitor visitor (nodep);
    V3Global::dumpCheckGlobalTree("delayed.tree", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}
