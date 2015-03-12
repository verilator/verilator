// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Make lookup tables
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
// TABLE TRANSFORMATIONS:
//	Look at all large always and assignments.
//	Count # of input bits and # of output bits, and # of statements
//	If high # of statements relative to inpbits*outbits,
//	replace with lookup table
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"
#include <cstdio>
#include <cstdarg>
#include <unistd.h>
#include <cmath>
#include <deque>

#include "V3Global.h"
#include "V3Table.h"
#include "V3Simulate.h"
#include "V3Stats.h"
#include "V3Ast.h"

//######################################################################
// Table class functions

// CONFIG
static const double TABLE_MAX_BYTES = 1*1024*1024;	// 1MB is max table size (better be lots of instructs to be worth it!)
static const double TABLE_TOTAL_BYTES = 64*1024*1024;	// 64MB is close to max memory of some systems (256MB or so), so don't get out of control
static const double TABLE_SPACE_TIME_MULT = 8;		// Worth 8 bytes of data to replace a instruction
static const int TABLE_MIN_NODE_COUNT = 32;	// If < 32 instructions, not worth the effort

//######################################################################

class TableVisitor;

class TableSimulateVisitor : public SimulateVisitor {
    // MEMBERS
    TableVisitor* m_cbthis;		///< Class for callback

public:
    virtual void varRefCb(AstVarRef* nodep);	///< Call other-this function on all new var references

    // CONSTRUCTORS
    TableSimulateVisitor(TableVisitor* cbthis) {
	m_cbthis = cbthis;
    }
    virtual ~TableSimulateVisitor() {}
};

//######################################################################
// Table class functions

class TableVisitor : public AstNVisitor {
private:
    // NODE STATE
    // Cleared on each always/assignw

    // STATE
    double	m_totalBytes;		// Total bytes in tables created
    V3Double0	m_statTablesCre;	// Statistic tracking

    //  State cleared on each module
    AstNodeModule*	m_modp;		// Current MODULE
    int			m_modTables;	// Number of tables created in this module
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
    static int debug() {
	static int level = -1;
	if (VL_UNLIKELY(level < 0)) level = v3Global.opt.debugSrcLevel(__FILE__);
	return level;
    }

    bool treeTest(AstAlways* nodep) {
	// Process alw/assign tree
	m_inWidth = 0;
	m_outWidth = 0;
	m_inVarps.clear();
	m_outVarps.clear();
	m_outNotSet.clear();

	// Collect stats
	TableSimulateVisitor chkvis (this);
	chkvis.mainTableCheck(nodep);
	m_assignDly = chkvis.isAssignDly();
	// Also sets m_inWidth
	// Also sets m_outWidth
	// Also sets m_inVarps
	// Also sets m_outVarps

	// Calc data storage in bytes
	size_t chgWidth = m_outVarps.size();	// Width of one change-it-vector
	if (chgWidth<8) chgWidth = 8;
	double space = (pow((double)2,((double)(m_inWidth)))
			*(double)(m_outWidth+chgWidth));
	// Instruction count bytes (ok, it's space also not time :)
	double bytesPerInst = 4;
	double time  = (chkvis.instrCount()*bytesPerInst + chkvis.dataCount()) + 1;  // +1 so won't div by zero
	if (chkvis.instrCount() < TABLE_MIN_NODE_COUNT) {
	    chkvis.clearOptimizable(nodep,"Table has too few nodes involved");
	}
	if (space > TABLE_MAX_BYTES) {
	    chkvis.clearOptimizable(nodep,"Table takes too much space");
	}
	if (space > time * TABLE_SPACE_TIME_MULT) {
	    chkvis.clearOptimizable(nodep,"Table has bad tradeoff");
	}
	if (m_totalBytes > TABLE_TOTAL_BYTES) {
	    chkvis.clearOptimizable(nodep,"Table out of memory");
	}
	if (!m_outWidth || !m_inWidth) {
	    chkvis.clearOptimizable(nodep,"Table has no outputs");
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
	    m_outWidth += nodep->varp()->dtypeSkipRefp()->widthTotalBytes();
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
	++m_modTables;
	++m_statTablesCre;

	// Index into our table
	AstVar* indexVarp = new AstVar (nodep->fileline(), AstVarType::BLOCKTEMP,
					"__Vtableidx" + cvtToStr(m_modTables),
					VFlagBitPacked(), m_inWidth);
	m_modp->addStmtp(indexVarp);
	AstVarScope* indexVscp = new AstVarScope (indexVarp->fileline(), m_scopep, indexVarp);
	m_scopep->addVarp(indexVscp);

	// Change it variable
	FileLine* fl = nodep->fileline();
	AstNodeArrayDType* dtypep
	    = new AstUnpackArrayDType (fl,
				       nodep->findBitDType(m_outVarps.size(),
							   m_outVarps.size(), AstNumeric::UNSIGNED),
				       new AstRange (fl, VL_MASK_I(m_inWidth), 0));
	v3Global.rootp()->typeTablep()->addTypesp(dtypep);
	AstVar* chgVarp
	    = new AstVar (fl, AstVarType::MODULETEMP,
			  "__Vtablechg" + cvtToStr(m_modTables),
			  dtypep);
	chgVarp->isConst(true);
	chgVarp->valuep(new AstInitArray (nodep->fileline(), dtypep, NULL));
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
	    FileLine* fl = nodep->fileline();
	    AstNodeArrayDType* dtypep
		= new AstUnpackArrayDType (fl, outvarp->dtypep(),
					   new AstRange (fl, VL_MASK_I(m_inWidth), 0));
	    v3Global.rootp()->typeTablep()->addTypesp(dtypep);
	    AstVar* tablevarp
		= new AstVar (fl, AstVarType::MODULETEMP,
			      "__Vtable" + cvtToStr(m_modTables) +"_"+outvarp->name(),
			      dtypep);
	    tablevarp->isConst(true);
	    tablevarp->isStatic(true);
	    tablevarp->valuep(new AstInitArray (nodep->fileline(), dtypep, NULL));
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
	TableSimulateVisitor simvis (this);
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
	    simvis.mainTableEmulate(nodep);
	    if (!simvis.optimizable()) simvis.whyNotNodep()->v3fatalSrc("Optimizable cleared, even though earlier test run said not: "<<simvis.whyNotMessage());

	    // If a output changed, add it to table
	    int outnum = 0;
	    V3Number outputChgMask (nodep->fileline(), m_outVarps.size(), 0);
	    for (deque<AstVarScope*>::iterator it = m_outVarps.begin(); it!=m_outVarps.end(); ++it) {
		AstVarScope* outvscp = *it;
		V3Number* outnump = simvis.fetchOutNumberNull(outvscp);
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
		m_tableVarps[outnum]->varp()->valuep()->castInitArray()->addInitsp(setp);
		outnum++;
	    }

	    {   // Set changed table
		if (inValue != inValueNextInitArray++)
		    nodep->v3fatalSrc("InitArray requires us to have the values in inValue order");
		AstNode* setp = new AstConst (nodep->fileline(), outputChgMask);
		chgVscp->varp()->valuep()->castInitArray()->addInitsp(setp);
	    }
	} // each value
    }

    AstVarScope* findDuplicateTable(AstVarScope* vsc1p) {
	// See if another table we've created is identical, if so use it for both.
	// (A more 'modern' way would be to instead use V3Hashed::findDuplicate)
	AstVar* var1p = vsc1p->varp();
	for (deque<AstVarScope*>::iterator it = m_modTableVscs.begin(); it!=m_modTableVscs.end(); ++it) {
	    AstVarScope* vsc2p= *it;
	    AstVar* var2p = vsc2p->varp();
	    if (var1p->width() == var2p->width()
		&& (var1p->dtypep()->arrayUnpackedElements()
		    == var2p->dtypep()->arrayUnpackedElements())) {
		AstNode* init1p = var1p->valuep()->castInitArray();
		AstNode* init2p = var2p->valuep()->castInitArray();
		if (init1p->sameGateTree(init2p)) {
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
    virtual void visit(AstNodeModule* nodep, AstNUser*) {
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
    V3Global::dumpCheckGlobalTree("table.tree", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}
