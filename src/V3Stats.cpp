// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Collect and print statistics
//
// Code available from: http://www.veripool.org/verilator
//
//*************************************************************************
//
// Copyright 2005-2015 by Wilson Snyder.  This program is free software; you can
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

#include "config_build.h"
#include "verilatedos.h"
#include <cstdio>
#include <cstdarg>
#include <unistd.h>
#include <map>
#include <iomanip>

#include "V3Global.h"
#include "V3Stats.h"
#include "V3Ast.h"
#include "V3File.h"

// This visitor does not edit nodes, and is called at error-exit, so should use constant iterators
#include "V3AstConstOnly.h"

//######################################################################
// Stats class functions

class StatsVisitor : public AstNVisitor {
private:
    // NODE STATE/TYPES

    typedef map<string,int>	NameMap;	// Number of times a name appears

    // STATE
    string	m_stage;		// Name of the stage we are scanning
    bool	m_fast;			// Counting only fastpath

    AstCFunc*	m_cfuncp;		// Current CFUNC
    V3Double0	m_statInstrLong;	// Instruction count
    bool	m_counting;		// Currently counting
    double	m_instrs;		// Current instr count

    vector<V3Double0>	m_statTypeCount;	// Nodes of given type
    V3Double0		m_statAbove[AstType::_ENUM_END][AstType::_ENUM_END];	// Nodes of given type
    V3Double0		m_statPred[AstBranchPred::_ENUM_END];	// Nodes of given type
    V3Double0		m_statInstr;		// Instruction count
    V3Double0		m_statInstrFast;	// Instruction count
    vector<V3Double0>	m_statVarWidths;	// Variables of given width
    vector<NameMap>	m_statVarWidthNames;	// Var names of given width
    V3Double0		m_statVarArray;		// Statistic tracking
    V3Double0		m_statVarBytes;		// Statistic tracking
    V3Double0		m_statVarClock;		// Statistic tracking
    V3Double0		m_statVarScpBytes;	// Statistic tracking

    // METHODS
    void allNodes(AstNode* nodep) {
	m_instrs += nodep->instrCount();
	if (m_counting) {
	    ++m_statTypeCount[nodep->type()];
	    if (nodep->firstAbovep()) { // Grab only those above, not those "back"
		++m_statAbove[nodep->firstAbovep()->type()][nodep->type()];
	    }
	    m_statInstr += nodep->instrCount();
	    if (m_cfuncp && !m_cfuncp->slow()) m_statInstrFast += nodep->instrCount();
	}
    }

    // VISITORS
    virtual void visit(AstNodeModule* nodep, AstNUser*) {
	allNodes(nodep);
	if (!m_fast) {
	    nodep->iterateChildrenConst(*this);
	} else {
	    for (AstNode* searchp = nodep->stmtsp(); searchp; searchp=searchp->nextp()) {
		if (AstCFunc* funcp = searchp->castCFunc()) {
		    if (funcp->name() == "_eval") {
			m_instrs=0;
			m_counting = true;
			funcp->iterateChildrenConst(*this);
			m_counting = false;
		    }
		}
	    }
	}
    }
    virtual void visit(AstVar* nodep, AstNUser*) {
	allNodes(nodep);
	nodep->iterateChildrenConst(*this);
	if (m_counting && nodep->dtypep()) {
	    if (nodep->isUsedClock()) ++m_statVarClock;
	    if (nodep->dtypeSkipRefp()->castUnpackArrayDType()) ++m_statVarArray;
	    else m_statVarBytes += nodep->dtypeSkipRefp()->widthTotalBytes();
	    if (int(m_statVarWidths.size()) <= nodep->width()) {
		m_statVarWidths.resize(nodep->width()+5);
		if (v3Global.opt.statsVars()) m_statVarWidthNames.resize(nodep->width()+5);
	    }
	    ++ m_statVarWidths.at(nodep->width());
	    string pn = nodep->prettyName();
	    if (v3Global.opt.statsVars()) {
		NameMap& nameMapr = m_statVarWidthNames.at(nodep->width());
		if (nameMapr.find(pn) != nameMapr.end()) {
		    nameMapr[pn]++;
		} else {
		    nameMapr[pn]=1;
		}
	    }
	}
    }
    virtual void visit(AstVarScope* nodep, AstNUser*) {
	allNodes(nodep);
	nodep->iterateChildrenConst(*this);
	if (m_counting) {
	    if (nodep->varp()->dtypeSkipRefp()->castBasicDType()) {
		m_statVarScpBytes += nodep->varp()->dtypeSkipRefp()->widthTotalBytes();
	    }
	}
    }
    virtual void visit(AstNodeIf* nodep, AstNUser*) {
	UINFO(4,"   IF "<<nodep<<endl);
	allNodes(nodep);
	// Condition is part of PREVIOUS block
	nodep->condp()->iterateAndNextConst(*this);
	// Track prediction
	if (m_counting) {
	    ++m_statPred[nodep->branchPred()];
	}
	if (!m_fast) {
	    nodep->iterateChildrenConst(*this);
	} else {
	    // See which path we want to take
	    bool takeElse = false;
	    if (!nodep->elsesp() || (nodep->branchPred()==AstBranchPred::BP_LIKELY)) {
		// Always take the if
	    } else if (!nodep->ifsp() || (nodep->branchPred()==AstBranchPred::BP_UNLIKELY)) {
		// Always take the else
	    } else {
		// Take the longer path
		bool prevCounting = m_counting;
		double prevInstr = m_instrs;
		m_counting = false;
		// Check if
		m_instrs = 0;
		nodep->ifsp()->iterateAndNextConst(*this);
		double instrIf = m_instrs;
		// Check else
		m_instrs = 0;
		nodep->elsesp()->iterateAndNextConst(*this);
		double instrElse = m_instrs;
		// Max of if or else condition
		takeElse = (instrElse > instrIf);
		// Restore
		m_counting = prevCounting;
		m_instrs = prevInstr + (takeElse?instrElse:instrIf);
	    }
	    // Count the block
	    if (m_counting) {
		if (takeElse) {
		    nodep->elsesp()->iterateAndNextConst(*this);
		} else {
		    nodep->ifsp()->iterateAndNextConst(*this);
		}
	    }
	}
    }
    // While's we assume evaluate once.
    //virtual void visit(AstWhile* nodep, AstNUser*) {

    virtual void visit(AstCCall* nodep, AstNUser*) {
	//UINFO(4,"  CCALL "<<nodep<<endl);
	allNodes(nodep);
	nodep->iterateChildrenConst(*this);
	if (m_fast) {
	    // Enter the function and trace it
	    nodep->funcp()->accept(*this);
	}
    }
    virtual void visit(AstCFunc* nodep, AstNUser*) {
	m_cfuncp = nodep;
	allNodes(nodep);
	nodep->iterateChildrenConst(*this);
	m_cfuncp = NULL;
    }
    virtual void visit(AstNode* nodep, AstNUser*) {
	allNodes(nodep);
	nodep->iterateChildrenConst(*this);
    }
public:
    // CONSTRUCTORS
    StatsVisitor(AstNetlist* nodep, const string& stage, bool fast)
	: m_stage(stage), m_fast(fast)
	{
	m_cfuncp = NULL;
	m_counting = !m_fast;
	m_instrs = 0;
	// Initialize arrays
	m_statTypeCount.resize(AstType::_ENUM_END);
	// Process
	nodep->accept(*this);
    }
    virtual ~StatsVisitor() {
	// Done. Publish statistics
	V3Stats::addStat(m_stage, "Instruction count, TOTAL", m_statInstr);
	V3Stats::addStat(m_stage, "Instruction count, fast",  m_statInstrFast);
	// Vars
	V3Stats::addStat(m_stage, "Vars, unpacked arrayed", m_statVarArray);
	V3Stats::addStat(m_stage, "Vars, clock attribute", m_statVarClock);
	V3Stats::addStat(m_stage, "Var space, non-arrays, bytes", m_statVarBytes);
	if (m_statVarScpBytes) {
	    V3Stats::addStat(m_stage, "Var space, scoped, bytes", m_statVarScpBytes);
	}
	for (unsigned i=0; i<m_statVarWidths.size(); i++) {
	    if (double count = double(m_statVarWidths.at(i))) {
		if (v3Global.opt.statsVars()) {
		    NameMap& nameMapr = m_statVarWidthNames.at(i);
		    for (NameMap::iterator it=nameMapr.begin(); it!=nameMapr.end(); ++it) {
			ostringstream os; os<<"Vars, width "<<setw(5)<<dec<<i<<" "<<it->first;
			V3Stats::addStat(m_stage, os.str(), it->second);
		    }
		} else {
		    ostringstream os; os<<"Vars, width "<<setw(5)<<dec<<i;
		    V3Stats::addStat(m_stage, os.str(), count);
		}
	    }
	}
	// Node types
	for (int type=0; type<AstType::_ENUM_END; type++) {
	    if (double count = double(m_statTypeCount.at(type))) {
		V3Stats::addStat(m_stage, string("Node count, ")+AstType(type).ascii(), count);
	    }
	}
	for (int type=0; type<AstType::_ENUM_END; type++) {
	    for (int type2=0; type2<AstType::_ENUM_END; type2++) {
		if (double count = double(m_statAbove[type][type2])) {
		    V3Stats::addStat(m_stage, string("Node pairs, ")+AstType(type).ascii()+"_"+AstType(type2).ascii(), count);
		}
	    }
	}
	// Branch pred
	for (int type=0; type<AstBranchPred::_ENUM_END; type++) {
	    if (double count = double(m_statPred[type])) {
		V3Stats::addStat(m_stage, string("Branch prediction, ")+AstBranchPred(type).ascii(), count);
	    }
	}
    }
};

//######################################################################
// Top Stats class

void V3Stats::statsStageAll(AstNetlist* nodep, const string& stage, bool fast) {
    StatsVisitor visitor (nodep, stage, fast);
}

void V3Stats::statsFinalAll(AstNetlist* nodep) {
    statsStageAll(nodep, "Final");
    statsStageAll(nodep, "Final_Fast", true);
}
