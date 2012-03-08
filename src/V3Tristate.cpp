//*************************************************************************
// DESCRIPTION: Verilator: Deals with tristate logic
//
// Code available from: http://www.veripool.org/verilator
//
// AUTHORS: Lane Brooks with Wilson Snyder, Paul Wasson, Duane Gabli
//
//*************************************************************************
//
// Copyright 2003-2012 by Wilson Snyder.  This program is free software; you can
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
// V3Tristate's Transformations:
//
//  Tristate transformations are accomplished via three operations on the tree:
//
//  1. Find 'hZ constructs and change the logic to a two state output.
//     This requires creating an __en signal for the driver resolution
//     logic to use.  This function is *not* generic right now in that
//     it can transform any logic structure.  It is currently highly
//     specialize to only work on assign structures where the 'hZ
//     assignment is in the first level.  More work needs done to make
//     this work with any logic structure.
//
//  2. While walking the tree looking for 'hZ constructs, also detect
//     any nets that have multiple LHS (left-hand side) drivers.  These
//     are the locations where driver resolution will occur.
//
//  3. Finally, make a pass through the cell pin assignments to push
//     the __en pins up the hierarchy until they are finally terminated
//     at the driver resolution stage.
//
//  Inouts are treated differently than tristates, though they are certainly
//  related.  Inouts are expanded prior to tristate expansion.  The inout
//  expansion takes each inout port and creates an new input with a name suffix
//  of __in and transforms the original port to an output port.
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"
#include <cstdio>
#include <cstdarg>
#include <unistd.h>
#include <algorithm>
#include <map>

#include "V3Global.h"
#include "V3Tristate.h"
#include "V3Ast.h"
#include "V3Stats.h"
#include "V3Inst.h"

//######################################################################

typedef std::vector<AstVar*> VarVec;
typedef std::vector<AstVarRef*> RefVec;
typedef std::map<AstVar*, RefVec*> VarMap;

//######################################################################

class TristateBaseVisitor : public AstNVisitor {
public:
    static int debug() {
	static int level = -1;
	if (VL_UNLIKELY(level < 0)) level = v3Global.opt.debugSrcLevel(__FILE__);
	return level;
    }
};

//######################################################################

class TristateExpander : public TristateBaseVisitor {
    // Finds all tristate logic and creates an __en signal and removes Z's.
    // Only supports limited assign statements initially.
    // Also detects multiple lhs var drivers.

private:
    // NODE STATE
    // Cleared on Netlist
    //   AstVarRef::user1p -> used to track any newly create __en signals
    //   AstVarRef::user2 ->  already visited
    //   AstVarRef::user3p -> a parent SEL
    //   AstVar::user1p ->    used to track any newly create __en signals
    //   AstVar::user2 ->     used for pullup/pulldown direction

    // STATE
    int		m_unique;
    AstNodeModule*	m_modp;	 // Current module
    VarMap*	m_lhsmapp;   // LHS driver map
    AstSel*	m_sel;

    virtual void visit(AstSel* nodep, AstNUser*) {
	m_sel=nodep;
	nodep->iterateChildren(*this);
	m_sel=NULL;
    }

    //*******************************************************************
    // The following visitor functions deal with detecting Z's in the
    // logic, stripping the Z's out and creating an __en signal and its
    // logic.
    //*******************************************************************
    virtual void visit(AstPull* nodep, AstNUser*) {
        // replace any pullup/pulldowns with assignw logic and an __en
        // signal just like it is any other tristate signal.  The only
        // difference is that the user2() variable on the __en signal
        // will be given a pull direction--i.e. pulldown=1, pullup=2.
        // This will signal the driver exansion logic to put a default
        // pullup or pulldown state on the tristate bus under the high-Z
        // condition when no one is driving the bus.  Given the complexity
        // of merging tristate drivers at any level, the current limitation
        // of this implementation is that a pullup/down gets applied
        // to all bits of a bus and a bus cannot have drivers in opposite
        // directions on indvidual pins.
        AstNode* outp = nodep->lhsp()->unlinkFrBack();;
        AstVarRef* outrefp = NULL;
	int width=-1;
	if (outp->castVarRef()) {
	    outrefp = outp->castVarRef();
	} else if (outp->castSel()) {
	    outrefp = outp->castSel()->fromp()->castVarRef();
	    width = outp->castSel()->widthConst();
	} else {
	    nodep->v3error("Can't find LHS varref");
	}
	outrefp->lvalue(true);
	AstVar* varp = outrefp->varp();
	if (width==-1) width=varp->width();

        V3Number num0 (nodep->fileline(), width);
	num0.setAllBits0();
	V3Number num1 (nodep->fileline(), width);
	num1.setAllBits1();

	AstConst* enrhsp = new AstConst(nodep->fileline(), num0);
	AstVar* enp = createEnableVar(outp, outrefp, enrhsp, width, "pull");
	enp->user2(nodep->direction()+1); // record the pull direction

	AstAssignW* newassp = new AstAssignW(nodep->fileline(), outp,
					     new AstConst(nodep->fileline(), nodep->direction() ? num1 : num0));
	nodep->replaceWith(newassp);
	nodep->deleteTree(); nodep=NULL;
	newassp->iterateChildren(*this);
    }

    virtual void visit(AstAssignW* nodep, AstNUser*) {
	// Note: this detects and expands tristates of the forms:
	// assign x = (OE) ?  y  : 'hZ;
	// assign x = (OE) ? 'hz :  y;

	// see if this a COND and separate out the __en logic from the output logic if it is
	if (AstCond* condp = nodep->rhsp()->castCond()) {
	    //if (debug()>=9) nodep->dumpTree(cout,"-   cond-in: ");
	    AstNode* oep = condp->condp();
	    AstNode* expr1p = condp->expr1p();
	    AstNode* expr2p = condp->expr2p();
	    AstNode* enrhsp;
	    AstNode* outrhsp;

	    if (expr1p->castConst() && expr1p->castConst()->num().isAllZ()) {
		enrhsp = new AstNot(oep->fileline(), oep->unlinkFrBack());
		outrhsp = expr2p->unlinkFrBack();
	    } else if (expr2p->castConst() && expr2p->castConst()->num().isAllZ()){
		enrhsp = oep->unlinkFrBack();
		outrhsp = expr1p->unlinkFrBack();
	    } else {
		// not a tristate or not in a form we recgonize, so exit and move on.
		return;
	    }

	    AstNode* outp = nodep->lhsp()->unlinkFrBack();;
	    AstVarRef* outrefp = NULL;
	    if (outp->castVarRef()) {
		outrefp = outp->castVarRef();
	    } else if (outp->castSel()) {
		outrefp = outp->castSel()->fromp()->castVarRef();
	    } else {
		nodep->v3error("Can't find LHS varref");
	    }

	    createEnableVar(outp, outrefp, enrhsp, outrhsp->width());

	    // replace the old assign logic with the new one
	    AstAssignW* newassp = new AstAssignW(nodep->fileline(), outp,outrhsp);
	    //if (debug()>=9) newassp->dumpTreeAndNext(cout,"-   cond-out: ");
	    nodep->replaceWith(newassp);
	    nodep->deleteTree(); nodep=NULL;
	    newassp->iterateChildren(*this);

	}
	// How about a tri gate?
	else if (AstBufIf1* bufp = nodep->rhsp()->castBufIf1()) {
	    //if (debug()>=9) nodep->dumpTree(cout,"-   tri-in : ");
	    AstNode* enrhsp = bufp->lhsp()->unlinkFrBack();
	    AstNode* outrhsp = bufp->rhsp()->unlinkFrBack();

	    AstNode* outp = nodep->lhsp()->unlinkFrBack();;
	    AstVarRef* outrefp = NULL;
	    if (outp->castVarRef()) {
		outrefp = outp->castVarRef();
	    } else if (outp->castSel()) {
		outrefp = outp->castSel()->fromp()->castVarRef();
	    } else {
		nodep->v3error("Can't find LHS varref");
	    }

	    createEnableVar(outp, outrefp, enrhsp, outrhsp->width());

	    // replace the old assign logic with the new one
	    AstAssignW* newassp = new AstAssignW(nodep->fileline(), outp,outrhsp);
	    //if (debug()>=9) newassp->dumpTreeAndNext(cout,"-   tri-out: ");
	    nodep->replaceWith(newassp);
	    nodep->deleteTree(); nodep=NULL;
	    newassp->iterateChildren(*this);
	}
	else {
	    nodep->iterateChildren(*this);
	}
    }

    AstVar* createEnableVar(AstNode* outp, AstVarRef* outrefp, AstNode* enrhsp, int width, string suffix="") {
	// this function creates an  __en Var that corresponds to
	// the outp and outrefp and creates an assignw to enrhsp
        AstVar* enp = new AstVar (outrefp->varp()->fileline(),
				  AstVarType::MODULETEMP,
				  outrefp->name() + "__en" + suffix + cvtToStr(m_unique++),
				  AstLogicPacked(), width);
	enp->varType2Out();

	if (enp->width() != enrhsp->width()) {
	    if (enrhsp->width1()) { // it seems from my futzing that the linter guarantees this condition
		enrhsp = new AstReplicate(enrhsp->fileline(), enrhsp,
					  new AstConst(enrhsp->fileline(), V3Number(enrhsp->fileline(), 32, enp->width())));
		enrhsp->width(enp->width(), enp->width());  //minwidth==width
	    } else {
		enrhsp->v3error("Don't know how to deal with selection logic wider than 1 bit");
	    }
	}

	AstNode* newassp = new AstAssignW (enp->fileline(),
					   new AstVarRef (enp->fileline(), enp, true),
					   enrhsp);
	if (debug()>=9) enp->dumpTreeAndNext(cout,"-   cev-out: ");
	if (debug()>=9) newassp->dumpTreeAndNext(cout,"-   cev-out: ");
        m_modp->addStmtp(enp);
        m_modp->addStmtp(newassp);

	outrefp->user1p(enp); // put __en signal into varref for later usage
	outrefp->varp()->user1p(enp); // put __en signal into var as well in the event this is a single lhs driver and this needs passed up one level

	return enp;
    }

    //**********************************************************************

    //**********************************************************************
    // These functions detect all var lhs drivers and add them to the
    // VarMap so that after the walk through the module we can
    // expand the driver to determine any that have multiple lhs drivers.
    //**********************************************************************

    virtual void visit(AstVarRef* nodep, AstNUser*) {
	if (nodep->lvalue() && !nodep->user2()) {
	    nodep->user2(true); // mark this ref as visited
	    AstVar* key = nodep->varp();

	    VarMap::iterator it = m_lhsmapp->find(key);
	    if (it == m_lhsmapp->end()) {
		// this key does not exist yet, so create it
		RefVec* refs = new RefVec();
		refs->push_back(nodep);
		m_lhsmapp->insert(pair<AstVar*, RefVec*>(key, refs));
	    } else {
		(*it).second->push_back(nodep);
	    }
	    nodep->user3p(m_sel); // attach the sel to this varref
	}
	nodep->iterateChildren(*this);
    }

    // Default - Iterate children to find all possible varrefs
    virtual void visit(AstNode* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
    }

public:
    TristateExpander(AstNodeModule* nodep, VarMap* lhsmapp) {
	m_modp    = nodep;
	m_lhsmapp = lhsmapp;
	m_unique  = 0;
	m_sel = NULL;
	nodep->accept(*this);       // visit eveyone
    }
    virtual ~TristateExpander() { }
};

//######################################################################

class TristateVisitor : public TristateBaseVisitor {
private:
    // NODE STATE
    // NOT Cleared on Netlist
    //   AstVarRef::user1p -> used to track any newly create __en signals
    //   AstVarRef::user3p -> a parent SEL
    //   AstVar::user1p ->    used to track any newly create __en signals
    //   AstVar::user2 ->     used for pullup/pulldown direction

    AstUser1InUse	m_inuser1;
    AstUser2InUse	m_inuser2;
    AstUser3InUse	m_inuser3;

    AstNodeModule*	m_modp;		// Current module
    AstCell* m_cellp; // current cell
    int m_unique;

    virtual void visit(AstNetlist* nodep, AstNUser*) {
	AstNode::user1ClearTree();
	nodep->iterateChildrenBackwards(*this);
    }

    virtual void visit(AstNodeModule* nodep, AstNUser*) {
	UINFO(9," MOD   "<<nodep<<endl);
	m_unique = 0;
	VarMap* lhsmapp = new VarMap();

	// expand tristate nodes and detect multiple LHS drivers for this module
	TristateExpander(nodep, lhsmapp);

	// iterate the children to grab any  __en signals from subcells
	m_modp = nodep;
	nodep->iterateChildren(*this);
	m_modp = NULL;

	// go through each multiple lhs driver & collapse it to a single driver
	for (VarMap::iterator nextit, it=lhsmapp->begin(); it != lhsmapp->end(); it=nextit) {
	    nextit = it; ++nextit;
	    m_unique = 0;
	    AstVar* lhsp = (*it).first;
	    RefVec* refs = (*it).second;
	    bool isOutput = (lhsp->varType() == AstVarType::OUTPUT) && (nodep->level() > 1); // force termination at top level

	    if (refs->size() < 2 && isOutput) {
		// if only one driver and this is an output, then exit and
		// let the driver propagate on its own.  If the signals
		// terminates at this level, then we need to let the
		// undriven state get generated.
		lhsmapp->erase(lhsp);
		delete refs;
		continue;
	    }


	    UINFO(9, "       Checking " << refs->size() << " drivers for tristates signals on net " << lhsp << endl);
	    int pull = 0;  // initially assume no pull direction

	    // Now remove and multple lhs signals that do not have __en for
	    // all possible drivers.
	    bool complete = true;
	    int found_one = 0;

	    for (RefVec::iterator ii=refs->begin(); ii != refs->end(); ++ii) {
		AstVarRef* refp = (*ii);
		if (!refp->user1p()) { // if no __en signal, then delete the entry
		    complete = false;
		} else {
		    found_one++;
		}
	    }
	    if (!complete) {
		if (found_one) {
		    UINFO(9, "       Problem mixing tristate and low-Z on " << lhsp << endl);
		    UINFO(9, "       Found " << found_one << " __en signals from of " << refs->size() << " possible drivers" << endl);
		    // not sure what I should do here other than error that they are mixing low-Z and tristate drivers.
		    // The other scenerio, and probably more likely, is that they are using a high-Z construct that
		    // is not supported.  Improving the high-Z detection logic will reduce the occurance of this failure.
		    nodep->v3error("Mixing tristate and low-Z drivers.  Perhaps you are using a high-Z construct not supported");
		} else  {
		    UINFO(9, "       No tristates found on " << lhsp <<endl);
		}
		lhsmapp->erase(lhsp);
		delete refs;
		continue;
	    }

	    UINFO(9, "       TRISTATE LHS DRIVER FOUND:" << lhsp << endl);

	    AstNode* orp = NULL,* andp = NULL,* undrivenp = NULL,* newenlogicp = NULL;

	    // loop through the lhs drivers to build the driver resolution logic
	    for (RefVec::iterator ii=refs->begin(); ii != refs->end(); ++ii) {
		AstVarRef* refp = (*ii);
		int w = lhsp->width();
		int wfill = 0; // width filler when necessary due to sels
		AstSel* selp = NULL;
		if (refp->user3p()) { // this varref has a sel
		    selp = (AstSel*) refp->user3p();
		    w = selp->widthConst();
		    wfill = lhsp->width() - w;
		}

		// create a new var for this assignment.
		AstVar* enp = (AstVar*)refp->user1p();
		AstVar* newlhsp = new AstVar(lhsp->fileline(),
					     AstVarType::MODULETEMP,
					     lhsp->name()+"__lhs"+cvtToStr(m_unique++),
					     AstLogicPacked(), w);
		nodep->addStmtp(newlhsp);

		// now append this driver to the driver logic.
		AstNode* ref1 = new AstVarRef(nodep->fileline(), newlhsp,false);
		AstNode* ref2 = new AstVarRef(nodep->fileline(), enp, false);
		andp = new AstAnd(nodep->fileline(), ref1, ref2);


		AstVar* bitselp = NULL;
		if (selp) { // this varref has a sel
		    int ws = V3Number::log2b(lhsp->width())+1;
		    bitselp = new AstVar(lhsp->fileline(),
					 AstVarType::MODULETEMP,
					 lhsp->name()+"__sel"+cvtToStr(m_unique-1),
					 AstLogicPacked(), ws);
		    //
		    nodep->addStmtp(bitselp);
		    nodep->addStmtp(new AstAssignW(lhsp->fileline(),
						   new AstVarRef(lhsp->fileline(), bitselp, true),
						   selp->lsbp()->cloneTree(false)));
		    andp = new AstShiftL(lhsp->fileline(),
					 new AstConcat(lhsp->fileline(), new AstConst(lhsp->fileline(), V3Number(lhsp->fileline(), wfill, 0)), andp),
					 new AstVarRef(lhsp->fileline(), bitselp, false),
					 lhsp->width()
			);

		    selp->replaceWith(new AstVarRef(refp->fileline(), newlhsp, true));
		    pushDeletep(selp);  // Setting selp here or deleting immediately
		    // breaks the t_tri_select test, this probably indicates a problem
		} else {
		    refp->varp(newlhsp); // assign the new var to the varref
		    refp->name(newlhsp->name());
		}

		// or this to the others
		orp = (!orp) ? andp : new AstOr(nodep->fileline(), orp, andp);

		if (isOutput) {
		    AstNode *en1p = new AstVarRef(nodep->fileline(), enp, false);
		    if (selp) {
			en1p = new AstShiftL(enp->fileline(),
					     new AstConcat(lhsp->fileline(), new AstConst(lhsp->fileline(), V3Number(lhsp->fileline(), wfill, 0)), en1p),
					     new AstVarRef(lhsp->fileline(), bitselp, false),
					     lhsp->width()
			    );
		    }
		    if (!newenlogicp) {
			newenlogicp = en1p;
		    } else {
			newenlogicp = new AstOr(nodep->fileline(), newenlogicp, en1p);
		    }
		} else {
		    if (!undrivenp) {
			undrivenp = new AstNot(nodep->fileline(), new AstVarRef(nodep->fileline(), enp, false));
			if (selp)
			    undrivenp = new AstShiftL(enp->fileline(),
						      new AstConcat(lhsp->fileline(), new AstConst(lhsp->fileline(), V3Number(lhsp->fileline(), wfill, 0)), undrivenp),
						      new AstVarRef(lhsp->fileline(), bitselp, false),
						      lhsp->width());
		    } else {
			AstNode *tmp = new AstNot(nodep->fileline(), new AstVarRef(nodep->fileline(), enp, false));
			if (selp) {
			    tmp = new AstShiftL(enp->fileline(),
						new AstConcat(lhsp->fileline(), new AstConst(lhsp->fileline(), V3Number(lhsp->fileline(), wfill, 0)), tmp),
						new AstVarRef(lhsp->fileline(), bitselp, false),
						lhsp->width());
			}
			undrivenp = new AstAnd(nodep->fileline(), tmp, undrivenp);
		    }
		}

		refp->user1p(NULL); // clear the user1p() as we done with it in the VarRef at this point

		if (enp->user2()) { // if this net is pulled up/down
		    int newpull = enp->user2();
		    if (pull == 0) {
			pull = newpull;
		    } else if (newpull != pull) {
			pull = -1; // conflict over the pull direction
		    }
		}
	    }
	    if (isOutput) {
		AstVar* newenp = new AstVar(lhsp->fileline(),
					    AstVarType::OUTPUT,
					    lhsp->name()+"__enout"+cvtToStr(m_unique++),
					    lhsp);
		nodep->addStmtp(newenp);
		nodep->addStmtp(new AstAssignW(lhsp->fileline(),
					       new AstVarRef(lhsp->fileline(), newenp, true),
					       newenlogicp));
		newenp->user2(pull); // put the pull direction in the next __en signal to pass it up
		lhsp->user1p(newenp); // put the new __en signal in the var so it can be pushed up the hierarchy.

	    } else { // this is the level where the signal terminates, we do final conflict resolution here
		UINFO(9, "       Terminating tristate logic for " << lhsp->name() << endl);
		UINFO(9, "       Pull direction is " << pull << " where -1=X, 0=Z, 1=low, 2=high." << endl);
		// figure out what to drive when no one is driving the bus
		V3Number num(nodep->fileline(), lhsp->width());
		if (pull==0) {
		    num.setAllBitsZ();
		} else if (pull==1) {
		    num.setAllBits0();
		} else if (pull==2) {
		    num.setAllBits1();
		} else {
		    num.setAllBitsX();
		}
		undrivenp = new AstAnd(nodep->fileline(), undrivenp,
				       new AstConst(nodep->fileline(), num));
		orp = new AstOr(nodep->fileline(), orp, undrivenp);
	    }
	    nodep->addStmtp(new AstAssignW(lhsp->fileline(),
					   new AstVarRef(lhsp->fileline(), lhsp, true), orp));

	    // delete the map and vector list now that we have collapsed it.
	    lhsmapp->erase(lhsp);
	    delete refs;
	}
	delete lhsmapp; // delete the map now that we are done
	nodep->user1p(NULL);
    }

    virtual void visit(AstCell* nodep, AstNUser*) {
	m_cellp = nodep;
	nodep->iterateChildren(*this);
	m_cellp = NULL;
    }

    AstVarRef* findVarRef(AstPin* nodep) {
	if (nodep->exprp()->castVarRef()) {
	    return nodep->exprp()->castVarRef();
	} else if (nodep->exprp()->castSel() && nodep->exprp()->castSel()->fromp()->castVarRef()) {
	    return nodep->exprp()->castSel()->fromp()->castVarRef();
	} else {
	    return NULL;
	}
    }

    virtual void visit(AstPin* nodep, AstNUser*) {
	// Check to see if any output pins have __en pins and create the __en pins to match
	AstVarRef* refp = findVarRef(nodep);

	if (refp && refp->lvalue() && nodep->modVarp()->user1p()) {
	    AstVar* enchildp = (AstVar*)nodep->modVarp()->user1p();
	    UINFO(9, "       Pulling __en var" << enchildp << endl);
	    AstVar* enp = new AstVar(enchildp->fileline(),
				     AstVarType::OUTPUT,
				     enchildp->name()+cvtToStr(m_unique++),
				     enchildp);
	    enp->user2(enchildp->user2());
	    m_modp->addStmtp(enp);
	    AstPin* pinp = new AstPin(nodep->fileline(),
				      nodep->pinNum(),
				      enp->name(),
				      new AstVarRef(nodep->fileline(), enp, true));
	    AstVarRef *rp = findVarRef(pinp);
	    rp->replaceWith(new AstVarRef(nodep->fileline(), enp, true));
	    rp->deleteTree(); rp=NULL;
	    pinp->width(enp->width(),enp->width());  // minwidth==width
	    pinp->modVarp(enchildp);
	    m_cellp->addPinsp(pinp);
	    refp->user1p(enp);
	    refp->varp()->user1p(enp);
	}
	// Simplify interconnect in preperation for V3Inst
	// (This could be a separate visitor, but we're in the neighborhood)
	V3Inst::pinReconnectSimple(nodep, m_cellp, m_modp);
    }

    // Default: Just iterate
    virtual void visit(AstNode* nodep, AstNUser*) {
	return; // no need to iterate further b/c AstCell and AstPin grab everything this visitor needs to hook up newly created __en pins correctly
    }

public:
    // CONSTUCTORS
    TristateVisitor(AstNode* nodep) {
	m_modp = NULL;
	m_cellp = NULL;
	m_unique = false;
	nodep->accept(*this);
    }
    virtual ~TristateVisitor() { }
};

//######################################################################

class InoutVisitor : public TristateBaseVisitor {
    // This visitor walks the tree and expands inouts into two ports.
    // The original port is switched to an output port and an additional
    // input port is created with a name suffix of __in.  All LHS logic
    // is left along connected to the original port.  All RHS varrefs
    // that point the original port are switched to point to the __in
    // input port.  The expansion is accomplished in a series of three
    // stages.  First entire hierarchy is visited and all inout vars are
    // expanded in an output and input var.  Then a second pass through
    // the hierarchy switches all the rhs varrefs to point to the newly
    // created __in vars.  Finally a third pass looks at the ports and
    // creates any needed __in ports.

private:
    // NODE STATE
    // Cleared on Netlist
    // AstVar::user1p -> a pointer to the created input port __in

    AstUser1InUse	m_inuser1;

    enum States {
	CONVERT_VARS,
	CONVERT_VARREFS,
	CONVERT_PINS
    };

    AstNodeModule*	m_modp;		// Current module
    AstCell*		m_cellp;	// Current cell
    AstNodeFTask* 	m_ftaskp;	// Current function/task
    States		m_state;

    virtual void visit(AstNetlist* nodep, AstNUser*) {
	m_state = CONVERT_VARS;
	nodep->iterateChildren(*this);
	m_state = CONVERT_VARREFS;
	nodep->iterateChildren(*this);
	m_state = CONVERT_PINS;
	nodep->iterateChildren(*this);
    }

    virtual void visit(AstNodeModule* nodep, AstNUser*) {
	m_modp = nodep;
	nodep->iterateChildren(*this);
	m_modp = NULL;
    }

    virtual void visit(AstNodeFTask* nodep, AstNUser*) {
	m_ftaskp = nodep;
	nodep->iterateChildren(*this);
	m_ftaskp = NULL;
    }

    virtual void visit(AstVar* nodep, AstNUser*) {
	if (m_state == CONVERT_VARS) {
	    if (nodep->isTristate() && !m_ftaskp) {
		// create the input var and leave the original as the output var
		AstVar* varinp = nodep->cloneTree(false)->castVar();
		varinp->name(varinp->name() + "__in");
		varinp->varType2In();

		nodep->combineType(AstVarType::OUTPUT);
		nodep->varType2Out();
		m_modp->addStmtp(varinp);
		nodep->user1p(varinp);
	    }
	}
    }

    virtual void visit(AstVarRef* nodep, AstNUser*) {
	if (m_state == CONVERT_VARREFS) {
	    if (!nodep->lvalue() && nodep->varp()->user1p()) {
		nodep->varp((AstVar*) nodep->varp()->user1p());
		nodep->name(nodep->varp()->name());
	    }
	}
    }

    virtual void visit(AstCell* nodep, AstNUser*) {
	m_cellp = nodep;
	nodep->iterateChildren(*this);
	m_cellp = NULL;
    }

    virtual void visit(AstPin* nodep, AstNUser*) {
	if (m_state == CONVERT_PINS) {
	    if (nodep->modVarp()->user1p()) {
		// create the input pin
		AstVarRef* refp = nodep->exprp()->castVarRef();
		if (!refp) nodep->v3fatal("Unsupported: Tristate pin not connected to simple net");
		AstVar* inp;
		if (refp->varp()->user1p()) { // this is a tristate
		    inp = (AstVar*) refp->varp()->user1p();
		} else {
		    inp = refp->varp();
		}
		AstPin* pinp = new AstPin(nodep->fileline(),
					  nodep->pinNum(),
					  nodep->name() + "__in",
					  new AstVarRef(nodep->fileline(), inp, false));
		m_cellp->addPinsp(pinp);

		// now link it
		pinp->modVarp((AstVar*) nodep->modVarp()->user1p());
	    }
	}
    }

    // Default: Just iterate
    virtual void visit(AstNode* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
    }

public:
    // CONSTUCTORS
    InoutVisitor(AstNode* nodep) {
	m_modp = NULL;
	m_cellp = NULL;
	m_ftaskp = NULL;
	m_state = CONVERT_VARS;
	nodep->accept(*this);
    }
    virtual ~InoutVisitor() { }
};

//######################################################################
// Tristate class functions

void V3Tristate::tristateAll(AstNetlist* nodep) {
    UINFO(2,__FUNCTION__<<": "<<endl);
    TristateVisitor visitor (nodep);
}

void V3Tristate::inoutAll(AstNetlist* nodep) {
    UINFO(2,__FUNCTION__<<": "<<endl);
    InoutVisitor visitor (nodep);
}
