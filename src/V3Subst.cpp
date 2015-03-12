// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Substitute constants and expressions in expr temp's
//
// Code available from: http://www.veripool.org/verilator
//
//*************************************************************************
//
// Copyright 2004-2015 by Wilson Snyder.  This program is free software; you can
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
// V3Subst's Transformations:
//
// Each module:
//	Search all ASSIGN(WORDSEL(...)) and build what it's assigned to
//	Later usages of that word may then be replaced as long as
//	the RHS hasn't changed value.
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"
#include <cstdio>
#include <cstdarg>
#include <unistd.h>
#include <algorithm>
#include <vector>

#include "V3Global.h"
#include "V3Subst.h"
#include "V3Const.h"
#include "V3Stats.h"
#include "V3Ast.h"

//######################################################################
// Common debugging baseclass

class SubstBaseVisitor : public AstNVisitor {
public:
    static int debug() {
	static int level = -1;
	if (VL_UNLIKELY(level < 0)) level = v3Global.opt.debugSrcLevel(__FILE__);
	return level;
    }
};

//######################################################################
// Class for each word of a multi-word variable

class SubstVarWord {
protected:
    // MEMBERS
    AstNodeAssign*	m_assignp;	// Last assignment to each word of this var
    int			m_step;		// Step number of last assignment
    bool		m_use;		// True if each word was consumed
    bool		m_complex;	// True if each word is complex
    friend class SubstVarEntry;
    // METHODS
    void clear() {
	m_assignp = NULL;
	m_step = 0;
	m_use = false;
	m_complex = false;
    }
};

//######################################################################
// Class for every variable we may process

class SubstVarEntry {
    // MEMBERS
    AstVar*		m_varp;		// Variable this tracks
    bool		m_wordAssign;	// True if any word assignments
    bool		m_wordUse;	// True if any individual word usage
    SubstVarWord	m_whole;	// Data for whole vector used at once
    vector<SubstVarWord> m_words;	// Data for every word, if multi word variable
    int debug() { return SubstBaseVisitor::debug(); }

public:
    // CONSTRUCTORS
    SubstVarEntry (AstVar* varp) {	// Construction for when a var is used
	m_varp = varp;
	m_whole.m_use = false;
	m_wordAssign = false;
	m_wordUse = false;
	m_words.resize(varp->widthWords());
	m_whole.clear();
	for (int i=0; i<varp->widthWords(); i++) {
	    m_words[i].clear();
	}
    }
    ~SubstVarEntry() {}
private:
    // METHODS
    bool wordNumOk(int word) const {
	return word < m_varp->widthWords();
    }
    AstNodeAssign* getWordAssignp(int word) const {
	if (!wordNumOk(word)) return NULL;
	else return m_words[word].m_assignp;
    }
public:
    void assignWhole (int step, AstNodeAssign* assp) {
	if (m_whole.m_assignp) m_whole.m_complex = true;
	m_whole.m_assignp = assp;
	m_whole.m_step = step;
    }
    void assignWord (int step, int word, AstNodeAssign* assp) {
	if (!wordNumOk(word) || getWordAssignp(word) || m_words[word].m_complex) m_whole.m_complex = true;
	m_wordAssign = true;
	if (wordNumOk(word)) {
	    m_words[word].m_assignp = assp;
	    m_words[word].m_step = step;
	}
    }
    void assignWordComplex (int step, int word) {
	if (!wordNumOk(word) || getWordAssignp(word) || m_words[word].m_complex) m_whole.m_complex = true;
	m_words[word].m_complex = true;
    }
    void assignComplex(int step) {
	m_whole.m_complex = true;
    }
    void consumeWhole() {  //==consumeComplex as we don't know the difference
	m_whole.m_use = true;
    }
    void consumeWord(int word) {
	m_words[word].m_use = true;
	m_wordUse = true;
    }
    // ACCESSORS
    AstNode* substWhole(AstNode* errp) {
	if (!m_varp->isWide()
	    && !m_whole.m_complex && m_whole.m_assignp && !m_wordAssign) {
	    AstNodeAssign* assp = m_whole.m_assignp;
	    if (!assp) errp->v3fatalSrc("Reading whole that was never assigned");
	    return (assp->rhsp());
	} else {
	    return NULL;
	}
    }
    AstNode* substWord(AstNode* errp, int word) {  // Return what to substitute given word number for
	if (!m_whole.m_complex && !m_whole.m_assignp && !m_words[word].m_complex) {
	    AstNodeAssign* assp = getWordAssignp(word);
	    if (!assp) errp->v3fatalSrc("Reading a word that was never assigned, or bad word #");
	    return (assp->rhsp());
	} else {
	    return NULL;
	}
    }
    int getWholeStep() const {
	return m_whole.m_step;
    }
    int getWordStep(int word) const {
	if (!wordNumOk(word)) return 0; else return m_words[word].m_step;
    }
    void deleteAssign (AstNodeAssign* nodep) {
	UINFO(5, "Delete "<<nodep<<endl);
	nodep->unlinkFrBack()->deleteTree(); nodep=NULL;
    }
    void deleteUnusedAssign() {
	// If there are unused assignments in this var, kill them
	if (!m_whole.m_use && !m_wordUse && m_whole.m_assignp) {
	    deleteAssign (m_whole.m_assignp); m_whole.m_assignp=NULL;
	}
	for (unsigned i=0; i<m_words.size(); i++) {
	    if (!m_whole.m_use && !m_words[i].m_use && m_words[i].m_assignp && !m_words[i].m_complex) {
		deleteAssign (m_words[i].m_assignp); m_words[i].m_assignp=NULL;
	    }
	}
    }
};

//######################################################################
// See if any variables have changed value since we determined subst value, as a visitor of each AstNode

class SubstUseVisitor : public SubstBaseVisitor {
private:
    // NODE STATE
    // See SubstVisitor
    //
    // STATE
    int			m_origStep;	// Step number where subst was recorded
    bool		m_ok;		// No misassignments found

    // METHODS
    SubstVarEntry* findEntryp(AstVarRef* nodep) {
	return (SubstVarEntry*)(nodep->varp()->user1p());  // Might be NULL
    }
    // VISITORS
    virtual void visit(AstVarRef* nodep, AstNUser*) {
	SubstVarEntry* entryp = findEntryp (nodep);
	if (entryp) {
	    // Don't sweat it.  We assign a new temp variable for every new assignment,
	    // so there's no way we'd ever replace a old value.
	} else {
	    // A simple variable; needs checking.
	    if (m_origStep < nodep->varp()->user2()) {
		if (m_ok) UINFO(9,"   RHS variable changed since subst recorded: "<<nodep<<endl);
		m_ok = false;
	    }
	}
    }
    virtual void visit(AstConst* nodep, AstNUser*) {}	// Accelerate
    virtual void visit(AstNode* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
    }
public:
    // CONSTUCTORS
    SubstUseVisitor(AstNode* nodep, int origStep) {
	UINFO(9, "        SubstUseVisitor "<<origStep<<" "<<nodep<<endl);
	m_ok = true;
	m_origStep = origStep;
	nodep->accept(*this);
    }
    virtual ~SubstUseVisitor() {}
    // METHODS
    bool ok() const { return m_ok; }
};

//######################################################################
// Subst state, as a visitor of each AstNode

class SubstVisitor : public SubstBaseVisitor {
private:
    // NODE STATE
    // Passed to SubstUseVisitor
    // AstVar::user1p		-> SubstVar* for usage var, 0=not set yet
    // AstVar::user2		-> int step number for last assignment, 0=not set yet
    AstUser1InUse	m_inuser1;
    AstUser2InUse	m_inuser2;

    // STATE
    vector<SubstVarEntry*>	m_entryps;	// Nodes to delete when we are finished
    int				m_ops;		// Number of operators on assign rhs
    int				m_assignStep;	// Assignment number to determine var lifetime
    V3Double0			m_statSubsts;	// Statistic tracking

    enum { SUBST_MAX_OPS_SUBST = 30,		// Maximum number of ops to substitute in
	   SUBST_MAX_OPS_NA = 9999 };		// Not allowed to substitute

    // METHODS
    SubstVarEntry* getEntryp(AstVarRef* nodep) {
	if (!nodep->varp()->user1p()) {
	    SubstVarEntry* entryp = new SubstVarEntry (nodep->varp());
	    m_entryps.push_back(entryp);
	    nodep->varp()->user1p(entryp);
	    return entryp;
	} else {
	    SubstVarEntry* entryp = (SubstVarEntry*)(nodep->varp()->user1p());
	    return entryp;
	}
    }
    inline bool isSubstVar(AstVar* nodep) {
	return nodep->isStatementTemp() && !nodep->noSubst();
    }

    // VISITORS
    virtual void visit(AstNodeAssign* nodep, AstNUser*) {
	m_ops = 0;
	m_assignStep++;
	nodep->rhsp()->iterateAndNext(*this);
	bool hit=false;
	if (AstVarRef* varrefp = nodep->lhsp()->castVarRef()) {
	    if (isSubstVar(varrefp->varp())) {
		SubstVarEntry* entryp = getEntryp(varrefp);
		hit = true;
		if (m_ops > SUBST_MAX_OPS_SUBST) {
		    UINFO(8," ASSIGNtooDeep "<<varrefp<<endl);
		    entryp->assignComplex(m_assignStep);
		} else {
		    UINFO(8," ASSIGNwhole "<<varrefp<<endl);
		    entryp->assignWhole(m_assignStep, nodep);
		}
	    }
	}
	else if (AstWordSel* wordp = nodep->lhsp()->castWordSel()) {
	    if (AstVarRef* varrefp = wordp->lhsp()->castVarRef()) {
		if (wordp->rhsp()->castConst()
		    && isSubstVar(varrefp->varp())) {
		    int word = wordp->rhsp()->castConst()->toUInt();
		    SubstVarEntry* entryp = getEntryp(varrefp);
		    hit = true;
		    if (m_ops > SUBST_MAX_OPS_SUBST) {
			UINFO(8," ASSIGNtooDeep "<<varrefp<<endl);
			entryp->assignWordComplex(m_assignStep, word);
		    } else {
			UINFO(8," ASSIGNword"<<word<<" "<<varrefp<<endl);
			entryp->assignWord(m_assignStep, word, nodep);
		    }
		}
	    }
	}
	if (!hit) {
	    nodep->lhsp()->accept(*this);
	}
    }
    void replaceSubstEtc(AstNode* nodep, AstNode* substp) {
	if (debug()>5) nodep->dumpTree(cout,"  substw_old: ");
	AstNode* newp = substp->cloneTree(true);
	if (!nodep->isQuad() && newp->isQuad()) {
	    newp = new AstCCast (newp->fileline(), newp, nodep);
	}
	if (debug()>5)  newp->dumpTree(cout,"       w_new: ");
	nodep->replaceWith(newp);
	pushDeletep(nodep);  nodep=NULL;
	++m_statSubsts;
    }
    virtual void visit(AstWordSel* nodep, AstNUser*) {
	nodep->rhsp()->accept(*this);
	AstVarRef* varrefp = nodep->lhsp()->castVarRef();
	AstConst* constp = nodep->rhsp()->castConst();
	if (varrefp && isSubstVar(varrefp->varp())
	    && !varrefp->lvalue()
	    && constp) {
	    // Nicely formed lvalues handled in NodeAssign
	    // Other lvalues handled as unknown mess in AstVarRef
	    int word = constp->toUInt();
	    UINFO(8," USEword"<<word<<" "<<varrefp<<endl);
	    SubstVarEntry* entryp = getEntryp(varrefp);
	    if (AstNode* substp = entryp->substWord (nodep, word)) {
		// Check that the RHS hasn't changed value since we recorded it.
		SubstUseVisitor visitor (substp, entryp->getWordStep(word));
		if (visitor.ok()) {
		    replaceSubstEtc(nodep, substp); nodep=NULL;
		} else {
		    entryp->consumeWord(word);
		}
	    } else {
		entryp->consumeWord(word);
	    }
	} else {
	    nodep->lhsp()->accept(*this);
	}
    }
    virtual void visit(AstVarRef* nodep, AstNUser*) {
	// Any variable
	if (nodep->lvalue()) {
	    m_assignStep++;
	    nodep->varp()->user2(m_assignStep);
	    UINFO(9, " ASSIGNstep u2="<<nodep->varp()->user2()<<" "<<nodep<<endl);
	}
	if (isSubstVar(nodep->varp())) {
	    SubstVarEntry* entryp = getEntryp (nodep);
	    if (nodep->lvalue()) {
		UINFO(8," ASSIGNcpx "<<nodep<<endl);
		entryp->assignComplex(m_assignStep);
	    } else if (AstNode* substp = entryp->substWhole(nodep)) {
		// Check that the RHS hasn't changed value since we recorded it.
		SubstUseVisitor visitor (substp, entryp->getWholeStep());
		if (visitor.ok()) {
		    UINFO(8," USEwhole "<<nodep<<endl);
		    replaceSubstEtc(nodep, substp); nodep=NULL;
		} else {
		    UINFO(8," USEwholeButChg "<<nodep<<endl);
		    entryp->consumeWhole();
		}
	    } else {  // Consumed w/o substitute
		UINFO(8," USEwtf   "<<nodep<<endl);
		entryp->consumeWhole();
	    }
	}
    }
    virtual void visit(AstVar* nodep, AstNUser*) {}
    virtual void visit(AstConst* nodep, AstNUser*) {}
    virtual void visit(AstNode* nodep, AstNUser*) {
	m_ops++;
	if (!nodep->isSubstOptimizable()) {
	    m_ops = SUBST_MAX_OPS_NA;
	}
	nodep->iterateChildren(*this);
    }
public:
    // CONSTUCTORS
    SubstVisitor(AstNode* nodep) {
	AstNode::user1ClearTree();	// user1p() used on entire tree
	AstNode::user2ClearTree();	// user2p() used on entire tree
	m_ops = 0;
	m_assignStep = 0;
	nodep->accept(*this);
    }
    virtual ~SubstVisitor() {
	V3Stats::addStat("Optimizations, Substituted temps", m_statSubsts);
	for (vector<SubstVarEntry*>::iterator it = m_entryps.begin(); it != m_entryps.end(); ++it) {
	    (*it)->deleteUnusedAssign();
	    delete (*it);
	}
    }
};

//######################################################################
// Subst class functions

void V3Subst::substituteAll(AstNetlist* nodep) {
    UINFO(2,__FUNCTION__<<": "<<endl);
    SubstVisitor visitor (nodep);
    V3Global::dumpCheckGlobalTree("subst.tree", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}
