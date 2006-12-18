// $Id$
//*************************************************************************
// DESCRIPTION: Verilator: Make lookup tables
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
// TABLE TRANSFORMATIONS:
//	Look at all large always and assignments.
//	Count # of input bits and # of output bits, and # of statements
//	If high # of statements relative to inpbits*outbits,
//	replace with lookup table
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"
#include <stdio.h>
#include <stdarg.h>
#include <unistd.h>
#include <math.h>
#include <deque>

#include "V3Global.h"
#include "V3Table.h"
#include "V3Stats.h"
#include "V3Ast.h"

//######################################################################
// Table class functions

// CONFIG
static const double TABLE_MAX_BYTES = 1*1024*1024;	// 1MB is max table size (better be lots of instructs to be worth it!)
static const double TABLE_TOTAL_BYTES = 64*1024*1024;	// 64MB is close to max memory of some systems (256MB or so), so don't get out of control
static const double TABLE_SPACE_TIME_MULT = 8;		// Worth 8 bytes of data to replace a instruction
static const int TABLE_MIN_NODE_COUNT = 32;	// If < 32 instructions, not worth the effort

class TableVisitor;

//######################################################################

class TableBaseVisitor : public AstNVisitor {
public:
    // Note level 8&9 include debugging each simulation value
//    int debug() { return 7; }
//    int debug() { return 9; }
};

//######################################################################

class TableSimulateVisitor : public TableBaseVisitor {
    // Simulate a node tree, returning value of variables
    // Two major operating modes:
    //   Test the tree to see if it is conformant
    //   Given a set of input values, find the output values
    // Both are done in this same visitor to reduce risk; if a visitor
    // is missing, we will simply not apply the optimization, rather then bomb.

private:
    // NODE STATE
    // Cleared on each always/assignw
    // Checking:
    //  AstVarScope::user()	-> VarUsage.  Set true to indicate tracking as lvalue/rvalue
    // Simulating:
    //  AstVarScope::user3()	-> V3Number*. Value of variable or node
    //  AstVarScope::user4()	-> V3Number*. Last value output was set to

    enum VarUsage { VU_NONE=0, VU_LV=1, VU_RV=2, VU_LVDLY=4 };

    // STATE
    bool	m_checking;		///< Checking vs. simulation mode
    // Checking:
    TableVisitor* m_cbthis;		///< Class for callback
    const char*	m_whyNotOptimizable;	///< String explaining why not optimizable or NULL to optimize
    bool	m_anyAssignDly;		///< True if found a delayed assignment
    bool	m_anyAssignComb;	///< True if found a non-delayed assignment
    bool	m_inDlyAssign;		///< Under delayed assignment
    int		m_instrCount;		///< Number of nodes
    int		m_dataCount;		///< Bytes of data
    // Simulating:
    deque<V3Number*>	m_numFreeps;	///< List of all numbers free and not in use
    deque<V3Number*>	m_numAllps; 	///< List of all numbers free and in use

    // Checking METHODS
public:
    void varRefCb(AstVarRef* nodep);	///< Call other-this function on all new var references

    void clearOptimizable(AstNode* nodep/*null ok*/, const char* why) {
	if (!m_whyNotOptimizable) {
	    if (debug()>=5) {
		UINFO(0,"Clear optimizable: "<<why);
		if (nodep) cout<<": "<<nodep;
		cout<<endl;
	    }
	    m_whyNotOptimizable = why;
	}
    }
    bool optimizable() const { return m_whyNotOptimizable==NULL; }
    bool isAssignDly() const { return m_anyAssignDly; }
    int instrCount() const { return m_instrCount; }
    int dataCount() const { return m_dataCount; }

    // Simulation METHODS
public:
    V3Number* newNumber(AstNode* nodep, uint32_t value=0) {
	// Set a constant value for this node
	if (!nodep->user3p()) {
	    // Save time - kept a list of allocated but unused V3Numbers
	    // It would be more efficient to do this by size, but the extra accounting
	    // slows things down more then we gain.
	    V3Number* nump;
	    if (!m_numFreeps.empty()) {
		//UINFO(7,"Num Reuse "<<nodep->width()<<endl);
		nump = m_numFreeps.back(); m_numFreeps.pop_back();
		nump->width(nodep->width());
		nump->fileline(nodep->fileline());
		nump->setLong(value);  // We do support more then 32 bit numbers, just valuep=0 in that case
	    } else {
		//UINFO(7,"Num New "<<nodep->width()<<endl);
		nump = new V3Number (nodep->fileline(), nodep->width(), value);
		m_numAllps.push_back(nump);
	    }
	    setNumber(nodep, nump);
	}
	return (fetchNumber(nodep));
    }
    V3Number* fetchNumberNull(AstNode* nodep) {
	return ((V3Number*)nodep->user3p());
    }
    V3Number* fetchNumber(AstNode* nodep) {
	V3Number* nump = fetchNumberNull(nodep);
	if (!nump) nodep->v3fatalSrc("No value found for node.");
	return nump;
    }
private:
    void setNumber(AstNode* nodep, const V3Number* nump) {
	UINFO(9,"     set num "<<*nump<<" on "<<nodep<<endl);
	nodep->user3p((AstNUser*)nump);
    }

    void checkNodeInfo(AstNode* nodep) {
	m_instrCount += nodep->instrCount();
	m_dataCount += nodep->width();
	if (!nodep->isPredictOptimizable()) {
	    //UINFO(9,"     !predictopt "<<nodep<<endl);
	    clearOptimizable(nodep,"!predictOptimzable");
	}
    }

    // VISITORS
    virtual void visit(AstAlways* nodep, AstNUser*) {
	if (m_checking) checkNodeInfo(nodep);
	nodep->iterateChildren(*this);
    }
    virtual void visit(AstSenTree* nodep, AstNUser*) {
	// Sensitivities aren't inputs per se; we'll keep our tree under the same sens.
    }
    virtual void visit(AstVarRef* nodep, AstNUser*) {
	AstVarScope* vscp = nodep->varScopep();
	if (!vscp) nodep->v3fatalSrc("Not linked");
	if (m_checking) {
	    if (m_checking && !optimizable()) return;  // Accelerate
	    // We can't have non-delayed assignments with same value on LHS and RHS
	    // as we don't figure out variable ordering.
	    // Delayed is OK though, as we'll decode the next state separately.
	    if (nodep->varp()->arraysp()) clearOptimizable(nodep,"Array references");
	    if (nodep->lvalue()) {
		if (m_inDlyAssign) {
		    if (!(vscp->user() & VU_LVDLY)) {
			vscp->user( vscp->user() | VU_LVDLY);
			varRefCb (nodep);
		    }
		} else { // nondly asn
		    if (!(vscp->user() & VU_LV)) {
			if (vscp->user() & VU_RV) clearOptimizable(nodep,"Var read & write");
			vscp->user( vscp->user() | VU_LV);
			varRefCb (nodep);
		    }
		}
	    } else {
		if (!(vscp->user() & VU_RV)) {
		    if (vscp->user() & VU_LV) clearOptimizable(nodep,"Var write & read");
		    vscp->user( vscp->user() | VU_RV);
		    varRefCb (nodep);
		}
	    }
	}
	else { // simulating
	    if (nodep->lvalue()) {
		nodep->v3fatalSrc("LHS varref should be handled in AstAssign visitor.");
	    } else {
		// Return simulation value
		V3Number* nump = fetchNumberNull(vscp);
		if (!nump) nodep->v3fatalSrc("Variable value should have been set before any visitor called.");
		setNumber(nodep, nump);
	    }
	}
    }
    virtual void visit(AstNodeIf* nodep, AstNUser*) {
	if (m_checking) {
	    checkNodeInfo(nodep);
	    nodep->iterateChildren(*this);
	} else {
	    nodep->condp()->iterateAndNext(*this);
	    if (fetchNumber(nodep->condp())->isNeqZero()) {
		nodep->ifsp()->iterateAndNext(*this);
	    } else {
		nodep->elsesp()->iterateAndNext(*this);
	    }
	}
    }
    virtual void visit(AstConst* nodep, AstNUser*) {
	if (m_checking) {
	    checkNodeInfo(nodep);
	} else {
	    setNumber(nodep, &(nodep->num()));
	}
    }
    virtual void visit(AstNodeUniop* nodep, AstNUser*) {
	if (m_checking) {
	    if (!optimizable()) return;  // Accelerate
	    checkNodeInfo(nodep);
	    nodep->iterateChildren(*this);
	} else {
	    nodep->iterateChildren(*this);
	    nodep->numberOperate(*newNumber(nodep), *fetchNumber(nodep->lhsp()));
	}
    }
    virtual void visit(AstNodeBiop* nodep, AstNUser*) {
	if (m_checking) {
	    if (!optimizable()) return;  // Accelerate
	    checkNodeInfo(nodep);
	    nodep->iterateChildren(*this);
	} else {
	    nodep->iterateChildren(*this);
	    nodep->numberOperate(*newNumber(nodep), *fetchNumber(nodep->lhsp()), *fetchNumber(nodep->rhsp()));
	}
    }
    virtual void visit(AstNodeTriop* nodep, AstNUser*) {
	if (m_checking) {
	    if (!optimizable()) return;  // Accelerate
	    checkNodeInfo(nodep);
	    nodep->iterateChildren(*this);
	} else {
	    nodep->iterateChildren(*this);
	    nodep->numberOperate(*newNumber(nodep),
				 *fetchNumber(nodep->lhsp()),
				 *fetchNumber(nodep->rhsp()),
				 *fetchNumber(nodep->thsp()));
	}
    }
    virtual void visit(AstNodeCond* nodep, AstNUser*) {
	// We could use above visit(AstNodeTriop), but it's slower to evaluate
	// both sides when we really only need to evaluate one side.
	if (m_checking) {
	    if (!optimizable()) return;  // Accelerate
	    checkNodeInfo(nodep);
	    nodep->iterateChildren(*this);
	} else {
	    nodep->condp()->accept(*this);
	    if (fetchNumber(nodep->condp())->isNeqZero()) {
		nodep->expr1p()->accept(*this);
		newNumber(nodep)->opAssign(*fetchNumber(nodep->expr1p()));
	    } else {
		nodep->expr2p()->accept(*this);
		newNumber(nodep)->opAssign(*fetchNumber(nodep->expr2p()));
	    }
	}
    }
    virtual void visit(AstNodeAssign* nodep, AstNUser*) {
	if (m_checking) {
	    if (!optimizable()) return;  // Accelerate
	    if (nodep->castAssignDly()) {
		if (m_anyAssignComb) clearOptimizable(nodep, "Mix of dly/non dly assigns");
		m_anyAssignDly = true;
		m_inDlyAssign = true;
	    } else {
		if (m_anyAssignDly) clearOptimizable(nodep, "Mix of dly/non dly assigns");
		m_anyAssignComb = true;
	    }
	    nodep->iterateChildren(*this);
	}
	if (!nodep->lhsp()->castVarRef()) {
	    clearOptimizable(nodep, "LHS isn't simple variable");
	}
	else if (!m_checking) {
	    nodep->rhsp()->iterateAndNext(*this);
	    AstVarScope* vscp = nodep->lhsp()->castVarRef()->varScopep();
	    setNumber(vscp, fetchNumber(nodep->rhsp()));
	}
	m_inDlyAssign = false;
    }

    virtual void visit(AstComment*, AstNUser*) {}
    // default
    // These types are definately not reducable
    //   AstCoverInc, AstNodePli, AstArraySel, AstStop, AstFinish,
    //   AstRand, AstTime, AstUCFunc, AstCCall, AstCStmt, AstUCStmt
    // In theory, we could follow the loop, but might be slow
    //   AstFor, AstWhile
    virtual void visit(AstNode* nodep, AstNUser*) {
	if (m_checking) {
	    checkNodeInfo(nodep);
	    if (optimizable()) {
		// Hmm, what is this then?
		// In production code, we'll just not optimize.  It should be fixed though.
		clearOptimizable(nodep, "Unknown node type, perhaps missing visitor in TableSimulateVisitor");
#ifdef VL_DEBUG
		UINFO(0,"Unknown node type in TableSimulateVisitor: "<<nodep->typeName()<<endl);
#endif
	    }
	} else { // simulating
	    nodep->v3fatalSrc("Optimizable should have been cleared in check step, and never reach simulation.");
	}
    }

public:
    // CONSTRUCTORS
    TableSimulateVisitor(TableVisitor* cbthis, bool checking) {
	m_cbthis = cbthis;
	m_checking = checking;
	clear(); // We reuse this structure in the main loop, so put initializers inside clear()
    }
    void clear() {
	m_whyNotOptimizable = NULL;
	m_anyAssignComb = false;
     	m_anyAssignDly = false;
	m_inDlyAssign = false;
	m_instrCount = 0;
	m_dataCount = 0;

	AstNode::userClearTree();	// userp() used on entire tree
	AstNode::user3ClearTree();	// user3p() used on entire tree
	AstNode::user4ClearTree();	// user4p() used on entire tree

	// Move all allocated numbers to the free pool
	m_numFreeps = m_numAllps;
    }
    void main (AstNode* nodep) {
	nodep->accept(*this);
    }
    virtual ~TableSimulateVisitor() {
	for (deque<V3Number*>::iterator it = m_numAllps.begin(); it != m_numAllps.end(); ++it) {
	    delete (*it);
	}
	m_numFreeps.clear();
	m_numAllps.clear();
    }
};


//######################################################################
// Table class functions

class TableVisitor : public TableBaseVisitor {
private:
    // NODE STATE
    // Cleared on each always/assignw

    // STATE
    double	m_totalBytes;		// Total bytes in tables created
    V3Double0	m_statTablesCre;	// Statistic tracking

    //  State cleared on each module
    AstModule*	m_modp;			// Current MODULE
    int		m_modTables;		// Number of tables created in this module
    deque<AstVarScope*> m_modTableVscs;	// All tables created

    //  State cleared on each scope
    AstScope*	m_scopep;		// Current SCOPE

    //  State cleared on each always/assignw
    bool	m_assignDly;		// Consists of delayed assignments instead of normal assignments
    int		m_inWidth;		// Input table width
    int		m_outWidth;		// Output table width
    deque<AstVarScope*> m_inVarps;	// Input variable list
    deque<AstVarScope*> m_outVarps;	// Output variable list
    deque<bool>    m_outNotSet;		// True if output variable is not set at some point

    // When creating a table
    deque<AstVarScope*> m_tableVarps;	// Table being created

    // METHODS
    bool treeTest(AstAlways* nodep) {
	// Process alw/assign tree
	m_inWidth = 0;
	m_outWidth = 0;
	m_inVarps.clear();
	m_outVarps.clear();
	m_outNotSet.clear();

	// Collect stats
	TableSimulateVisitor chkvis (this, true);
	chkvis.main(nodep);
	m_assignDly = chkvis.isAssignDly();
	// Also sets m_inWidth
	// Also sets m_outWidth
	// Also sets m_inVarps
	// Also sets m_outVarps

	// Calc data storage in bytes
	int chgWidth = m_outVarps.size();	// Width of one change-it-vector
	if (chgWidth<8) chgWidth = 8;
	double space = (pow((double)2,((double)(m_inWidth)))
			*(double)(m_outWidth+chgWidth));
	// Instruction count bytes (ok, it's space also not time :)
	double bytesPerInst = 4;
	double time  = (chkvis.instrCount()*bytesPerInst + chkvis.dataCount()) + 1;  // +1 so won't div by zero
	if (chkvis.instrCount() < TABLE_MIN_NODE_COUNT) {
	    chkvis.clearOptimizable(nodep,"Too few nodes involved");
	}
	if (space > TABLE_MAX_BYTES) {
	    chkvis.clearOptimizable(nodep,"Too much space");
	}
	if (space > time * TABLE_SPACE_TIME_MULT) {
	    chkvis.clearOptimizable(nodep,"Bad tradeoff");
	}
	if (m_totalBytes > TABLE_TOTAL_BYTES) {
	    chkvis.clearOptimizable(nodep,"Out of memory");
	}
	if (!m_outWidth || !m_inWidth) {
	    chkvis.clearOptimizable(nodep,"No I/O");
	}
	UINFO(4, "  Test: Opt="<<(chkvis.optimizable()?"OK":"NO")
	      <<", Instrs="<<chkvis.instrCount()<<" Data="<<chkvis.dataCount()
	      <<" inw="<<m_inWidth<<" outw="<<m_outWidth
	      <<" Spacetime="<<(space/time)<<"("<<space<<"/"<<time<<")"
	      <<": "<<nodep<<endl);
	if (chkvis.optimizable()) {
	    UINFO(3, " Table Optimize spacetime="<<(space/time)<<" "<<nodep<<endl);
	    m_totalBytes += space;
	}
	return chkvis.optimizable();
    }

public:
    void simulateVarRefCb(AstVarRef* nodep) {
	// Called by TableSimulateVisitor on each unique varref enountered
	UINFO(9,"   SimVARREF "<<nodep<<endl);
	AstVarScope* vscp = nodep->varScopep();
	if (nodep->lvalue()) {
	    m_outWidth += nodep->varp()->widthTotalBytes();
	    m_outVarps.push_back(vscp);
	} else {
	    // We'll make the table with a separate natural alignment for each
	    // output var, so always have char, 16 or 32 bit widths, so use widthTotalBytes
	    m_inWidth += nodep->varp()->width();  // Space for var
	    m_inVarps.push_back(vscp);
	}
    }

private:
    void createTable(AstAlways* nodep) {
	// We've determined this table of nodes is optimizable, do it.
	m_modTables++;
	m_statTablesCre++;

	// Index into our table
	AstVar* indexVarp = new AstVar (nodep->fileline(), AstVarType::BLOCKTEMP,
					"__Vtableidx_" + cvtToStr(m_modTables),
					new AstRange (nodep->fileline(), m_inWidth-1, 0));
	m_modp->addStmtp(indexVarp);
	AstVarScope* indexVscp = new AstVarScope (indexVarp->fileline(), m_scopep, indexVarp);
	m_scopep->addVarp(indexVscp);

	// Change it variable
	AstVar* chgVarp = new AstVar (nodep->fileline(), AstVarType::MODULETEMP,
				      "__Vtablechg_" + cvtToStr(m_modTables),
				      new AstRange (nodep->fileline(), m_outVarps.size()-1, 0),
				      new AstRange (nodep->fileline(), VL_MASK_I(m_inWidth), 0));
	chgVarp->isConst(true);
	chgVarp->initp(new AstInitArray (nodep->fileline(), NULL));
	m_modp->addStmtp(chgVarp);
	AstVarScope* chgVscp = new AstVarScope (chgVarp->fileline(), m_scopep, chgVarp);
	m_scopep->addVarp(chgVscp);

	createTableVars(nodep);
	AstNode* stmtsp = createLookupInput(nodep, indexVscp);
	createTableValues(nodep, chgVscp);

	// Collapse duplicate tables
	chgVscp = findDuplicateTable(chgVscp);
	for (deque<AstVarScope*>::iterator it = m_tableVarps.begin(); it!=m_tableVarps.end(); ++it) {
	    *it = findDuplicateTable(*it);
	}

	createOutputAssigns(nodep, stmtsp, indexVscp, chgVscp);

	// Link it in.
	if (AstAlways* nodeap = nodep->castAlways()) {
	    // Keep sensitivity list, but delete all else
	    nodeap->bodysp()->unlinkFrBackWithNext()->deleteTree();
	    nodeap->addStmtp(stmtsp);
	    if (debug()>=6) nodeap->dumpTree(cout,"  table_new: ");
	} else {
	    nodep->v3fatalSrc("Creating table under unknown node type");
	}

	// Cleanup internal structures
	m_tableVarps.clear();
    }

    void createTableVars(AstNode* nodep) {
	// Create table for each output
	for (deque<AstVarScope*>::iterator it = m_outVarps.begin(); it!=m_outVarps.end(); ++it) {
	    AstVarScope* outvscp = *it;
	    AstVar* outvarp = outvscp->varp();
	    AstVar* tablevarp
		= new AstVar (nodep->fileline(), AstVarType::MODULETEMP,
			      "__Vtable_" + cvtToStr(m_modTables) +"_"+outvarp->name(),
			      new AstRange (nodep->fileline(), outvarp->widthMin()-1, 0),
			      new AstRange (nodep->fileline(), VL_MASK_I(m_inWidth), 0));
	    tablevarp->isConst(true);
	    tablevarp->isStatic(true);
	    tablevarp->initp(new AstInitArray (nodep->fileline(), NULL));
	    m_modp->addStmtp(tablevarp);
	    AstVarScope* tablevscp = new AstVarScope(tablevarp->fileline(), m_scopep, tablevarp);
	    m_scopep->addVarp(tablevscp);
	    m_tableVarps.push_back(tablevscp);
	}
    }

    AstNode* createLookupInput(AstNode* nodep, AstVarScope* indexVscp) {
	// Concat inputs into a single temp variable (inside always)
	// First var in inVars becomes the LSB of the concat
	AstNode* concatp = NULL;
	for (deque<AstVarScope*>::iterator it = m_inVarps.begin(); it!=m_inVarps.end(); ++it) {
	    AstVarScope* invscp = *it;
	    AstVarRef* refp = new AstVarRef (nodep->fileline(), invscp, false);
	    if (concatp) {
		concatp = new AstConcat (nodep->fileline(), refp, concatp);
	    } else concatp = refp;
	}

	AstNode* stmtsp = new AstAssign
	    (nodep->fileline(),
	     new AstVarRef (nodep->fileline(), indexVscp, true),
	     concatp);
	return stmtsp;
    }

    void createTableValues(AstAlways* nodep, AstVarScope* chgVscp) {
	// Create table
	// There may be a simulation path by which the output doesn't change value.
	// We could bail on these cases, or we can have a "change it" boolean.
	// We've choosen the later route, since recirc is common in large FSMs.
	for (deque<AstVarScope*>::iterator it = m_outVarps.begin(); it!=m_outVarps.end(); ++it) {
	    m_outNotSet.push_back(false);
	}
	uint32_t inValueNextInitArray=0;
	TableSimulateVisitor simvis (this, false);
	for (uint32_t inValue=0; inValue <= VL_MASK_I(m_inWidth); inValue++) {
	    // Make a new simulation structure so we can set new input values
	    UINFO(8," Simulating "<<hex<<inValue<<endl);

	    // Above simulateVisitor clears user 3, so
	    // all outputs default to NULL to mean 'recirculating'.
	    simvis.clear();

	    // Set all inputs to the constant
	    uint32_t shift = 0;
	    for (deque<AstVarScope*>::iterator it = m_inVarps.begin(); it!=m_inVarps.end(); ++it) {
		AstVarScope* invscp = *it;
		// LSB is first variable, so extract it that way
		simvis.newNumber(invscp, VL_MASK_I(invscp->width()) & (inValue>>shift));
		shift += invscp->width();
		// We're just using32 bit arithmetic, because there's no way the input table can be 2^32 bytes!
		if (shift>31) nodep->v3fatalSrc("shift overflow");
		UINFO(8,"   Input "<<invscp->name()<<" = "<<*(simvis.fetchNumber(invscp))<<endl);
	    }

	    // Simulate
	    simvis.main(nodep);

	    // If a output changed, add it to table
	    int outnum = 0;
	    V3Number outputChgMask (nodep->fileline(), m_outVarps.size(), 0);
	    for (deque<AstVarScope*>::iterator it = m_outVarps.begin(); it!=m_outVarps.end(); ++it) {
		AstVarScope* outvscp = *it;
		V3Number* outnump = simvis.fetchNumberNull(outvscp);
		AstNode* setp;
		if (!outnump) {
		    UINFO(8,"   Output "<<outvscp->name()<<" never set\n");
		    m_outNotSet[outnum] = true;
		    // Value in table is arbitrary, but we need something
		    setp = new AstConst (outvscp->fileline(),
					 V3Number(outvscp->fileline(), outvscp->width(), 0));
		} else {
		    UINFO(8,"   Output "<<outvscp->name()<<" = "<<*outnump<<endl);
		    //  m_tableVarps[inValue] = num;
		    // Mark changed bit, too
		    outputChgMask.setBit(outnum, 1);
		    setp = new AstConst (outnump->fileline(), *outnump);
		}
		// Note InitArray requires us to have the values in inValue order
		m_tableVarps[outnum]->varp()->initp()->castInitArray()->addInitsp(setp);
		outnum++;
	    }

	    {   // Set changed table
		if (inValue != inValueNextInitArray++)
		    nodep->v3fatalSrc("InitArray requires us to have the values in inValue order");
		AstNode* setp = new AstConst (nodep->fileline(), outputChgMask);
		chgVscp->varp()->initp()->castInitArray()->addInitsp(setp);
	    }
	} // each value
    }

    AstVarScope* findDuplicateTable(AstVarScope* vsc1p) {
	// See if another table we've created is identical, if so use it for both.
	AstVar* var1p = vsc1p->varp();
	for (deque<AstVarScope*>::iterator it = m_modTableVscs.begin(); it!=m_modTableVscs.end(); ++it) {
	    AstVarScope* vsc2p= *it;
	    AstVar* var2p = vsc2p->varp();
	    if (var1p->width() == var2p->width()
		&& var1p->arrayElements() == var2p->arrayElements()) {
		AstNode* init1p = var1p->initp()->castInitArray();
		AstNode* init2p = var2p->initp()->castInitArray();
		if (init1p->sameTree(init2p)) {
		    UINFO(8,"   Duplicate table var "<<vsc2p<<" == "<<vsc1p<<endl);
		    vsc1p->unlinkFrBack()->deleteTree();
		    return vsc2p;
		}
	    }
	}
	m_modTableVscs.push_back(vsc1p);
	return vsc1p;
    }

    void createOutputAssigns(AstNode* nodep, AstNode* stmtsp, AstVarScope* indexVscp, AstVarScope* chgVscp) {
	// We walk through the changemask table, and if all ones know
	// the output is set on all branches and therefore eliminate the
	// if.  If all uses of the changemask disappear, dead code
	// elimination will remove it for us.
	// Set each output from array ref into our table
	int outnum = 0;
	for (deque<AstVarScope*>::iterator it = m_outVarps.begin(); it!=m_outVarps.end(); ++it) {
	    AstVarScope* outvscp = *it;
	    AstNode* alhsp = new AstVarRef(nodep->fileline(), outvscp, true);
	    AstNode* arhsp = new AstArraySel(nodep->fileline(),
					     new AstVarRef(nodep->fileline(), m_tableVarps[outnum], false),
					     new AstVarRef(nodep->fileline(), indexVscp, false));
	    AstNode* outasnp = (m_assignDly
				? (AstNode*)(new AstAssignDly (nodep->fileline(), alhsp, arhsp))
				: (AstNode*)(new AstAssign (nodep->fileline(), alhsp, arhsp)));
	    AstNode* outsetp = outasnp;

	    // Is the value set in only some branches of the table?
	    if (m_outNotSet[outnum]) {
		V3Number outputChgMask (nodep->fileline(), m_outVarps.size(), 0);
		outputChgMask.setBit(outnum,1);
		outsetp = new AstIf (nodep->fileline(),
				     new AstAnd(nodep->fileline(),
						new AstArraySel(nodep->fileline(),
								new AstVarRef(nodep->fileline(), chgVscp, false),
								new AstVarRef(nodep->fileline(), indexVscp, false)),
						new AstConst(nodep->fileline(), outputChgMask)),
				     outsetp, NULL);
	    }

	    stmtsp->addNext(outsetp);
	    outnum++;
	}
    }


    // VISITORS
    virtual void visit(AstNetlist* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
    }
    virtual void visit(AstModule* nodep, AstNUser*) {
	m_modTables = 0;
	m_modTableVscs.clear();
	m_modp = nodep;
	nodep->iterateChildren(*this);
	m_modp = NULL;
    }
    virtual void visit(AstScope* nodep, AstNUser*) {
	UINFO(4," SCOPE "<<nodep<<endl);
	m_scopep = nodep;
	nodep->iterateChildren(*this);
	m_scopep = NULL;
    }
    virtual void visit(AstAlways* nodep, AstNUser*) {
	UINFO(4,"  ALWAYS  "<<nodep<<endl);
	if (treeTest(nodep)) {
	    // Well, then, I'll be a memory hog.
	    createTable(nodep); nodep=NULL;
	}
    }
    virtual void visit(AstAssignAlias* nodep, AstNUser*) {}
    virtual void visit(AstAssignW* nodep, AstNUser*) {
	// It's nearly impossible to have a large enough assign to make this worthwhile
	// For now we won't bother.
	// Accelerated: no iterate
    }
    // default
    virtual void visit(AstNode* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
    }
public:
    // CONSTRUCTORS
    TableVisitor(AstNetlist* nodep) {
	m_modp = NULL;
	m_modTables = 0;
	m_scopep = NULL;
	m_assignDly = 0;
	m_inWidth = 0;
	m_outWidth = 0;
	m_totalBytes = 0;
	nodep->accept(*this);
    }
    virtual ~TableVisitor() {
	V3Stats::addStat("Optimizations, Tables created", m_statTablesCre);
    }
};

//######################################################################

void TableSimulateVisitor::varRefCb(AstVarRef* nodep) {
    // Called by checking on each new varref encountered
    // We cross-call into a TableVisitor function.
    m_cbthis->simulateVarRefCb(nodep);
}

//######################################################################
// Table class functions

void V3Table::tableAll(AstNetlist* nodep) {
    UINFO(2,__FUNCTION__<<": "<<endl);
    TableVisitor visitor (nodep);
}
