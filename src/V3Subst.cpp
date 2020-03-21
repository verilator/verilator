// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Substitute constants and expressions in expr temp's
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2004-2020 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
// V3Subst's Transformations:
//
// Each module:
//      Search all ASSIGN(WORDSEL(...)) and build what it's assigned to
//      Later usages of that word may then be replaced as long as
//      the RHS hasn't changed value.
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3Global.h"
#include "V3Subst.h"
#include "V3Const.h"
#include "V3Stats.h"
#include "V3Ast.h"

#include <algorithm>
#include <cstdarg>
#include <vector>

//######################################################################
// Common debugging baseclass

class SubstBaseVisitor : public AstNVisitor {
public:
    VL_DEBUG_FUNC;  // Declare debug()
};

//######################################################################
// Class for each word of a multi-word variable

class SubstVarWord {
protected:
    // MEMBERS
    AstNodeAssign*      m_assignp;      // Last assignment to each word of this var
    int                 m_step;         // Step number of last assignment
    bool                m_use;          // True if each word was consumed
    bool                m_complex;      // True if each word is complex
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
    AstVar*             m_varp;         // Variable this tracks
    bool                m_wordAssign;   // True if any word assignments
    bool                m_wordUse;      // True if any individual word usage
    SubstVarWord        m_whole;        // Data for whole vector used at once
    std::vector<SubstVarWord> m_words;  // Data for every word, if multi word variable
    int debug() { return SubstBaseVisitor::debug(); }

public:
    // CONSTRUCTORS
    explicit SubstVarEntry(AstVar* varp) {  // Construction for when a var is used
        m_varp = varp;
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
    void assignWhole(int step, AstNodeAssign* assp) {
        if (m_whole.m_assignp) m_whole.m_complex = true;
        m_whole.m_assignp = assp;
        m_whole.m_step = step;
    }
    void assignWord(int step, int word, AstNodeAssign* assp) {
        if (!wordNumOk(word) || getWordAssignp(word)
            || m_words[word].m_complex) m_whole.m_complex = true;
        m_wordAssign = true;
        if (wordNumOk(word)) {
            m_words[word].m_assignp = assp;
            m_words[word].m_step = step;
        }
    }
    void assignWordComplex(int word) {
        if (!wordNumOk(word) || getWordAssignp(word)
            || m_words[word].m_complex) m_whole.m_complex = true;
        m_words[word].m_complex = true;
    }
    void assignComplex() {
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
            UASSERT_OBJ(assp, errp, "Reading whole that was never assigned");
            return (assp->rhsp());
        } else {
            return NULL;
        }
    }
    AstNode* substWord(AstNode* errp, int word) {  // Return what to substitute given word number for
        if (!m_whole.m_complex && !m_whole.m_assignp && !m_words[word].m_complex) {
            AstNodeAssign* assp = getWordAssignp(word);
            UASSERT_OBJ(assp, errp, "Reading a word that was never assigned, or bad word #");
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
    void deleteAssign(AstNodeAssign* nodep) {
        UINFO(5, "Delete "<<nodep<<endl);
        VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
    }
    void deleteUnusedAssign() {
        // If there are unused assignments in this var, kill them
        if (!m_whole.m_use && !m_wordUse && m_whole.m_assignp) {
            VL_DO_CLEAR(deleteAssign(m_whole.m_assignp), m_whole.m_assignp = NULL);
        }
        for (unsigned i=0; i<m_words.size(); i++) {
            if (!m_whole.m_use && !m_words[i].m_use
                && m_words[i].m_assignp && !m_words[i].m_complex) {
                VL_DO_CLEAR(deleteAssign(m_words[i].m_assignp), m_words[i].m_assignp = NULL);
            }
        }
    }
};

//######################################################################
// See if any variables have changed value since we determined subst value,
// as a visitor of each AstNode

class SubstUseVisitor : public SubstBaseVisitor {
private:
    // NODE STATE
    // See SubstVisitor
    //
    // STATE
    int                 m_origStep;     // Step number where subst was recorded
    bool                m_ok;           // No misassignments found

    // METHODS
    SubstVarEntry* findEntryp(AstVarRef* nodep) {
        return reinterpret_cast<SubstVarEntry*>(nodep->varp()->user1p());  // Might be NULL
    }
    // VISITORS
    virtual void visit(AstVarRef* nodep) VL_OVERRIDE {
        SubstVarEntry* entryp = findEntryp(nodep);
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
    virtual void visit(AstConst* nodep) VL_OVERRIDE {}  // Accelerate
    virtual void visit(AstNode* nodep) VL_OVERRIDE {
        iterateChildren(nodep);
    }
public:
    // CONSTRUCTORS
    SubstUseVisitor(AstNode* nodep, int origStep) {
        UINFO(9, "        SubstUseVisitor "<<origStep<<" "<<nodep<<endl);
        m_ok = true;
        m_origStep = origStep;
        iterate(nodep);
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
    // AstVar::user1p           -> SubstVar* for usage var, 0=not set yet
    // AstVar::user2            -> int step number for last assignment, 0=not set yet
    AstUser1InUse       m_inuser1;
    AstUser2InUse       m_inuser2;

    // STATE
    std::vector<SubstVarEntry*> m_entryps;      // Nodes to delete when we are finished
    int                         m_ops;          // Number of operators on assign rhs
    int                         m_assignStep;   // Assignment number to determine var lifetime
    VDouble0                    m_statSubsts;   // Statistic tracking

    enum { SUBST_MAX_OPS_SUBST = 30,            // Maximum number of ops to substitute in
           SUBST_MAX_OPS_NA = 9999 };           // Not allowed to substitute

    // METHODS
    SubstVarEntry* getEntryp(AstVarRef* nodep) {
        if (!nodep->varp()->user1p()) {
            SubstVarEntry* entryp = new SubstVarEntry(nodep->varp());
            m_entryps.push_back(entryp);
            nodep->varp()->user1p(entryp);
            return entryp;
        } else {
            SubstVarEntry* entryp = reinterpret_cast<SubstVarEntry*>(nodep->varp()->user1p());
            return entryp;
        }
    }
    inline bool isSubstVar(AstVar* nodep) {
        return nodep->isStatementTemp() && !nodep->noSubst();
    }

    // VISITORS
    virtual void visit(AstNodeAssign* nodep) VL_OVERRIDE {
        m_ops = 0;
        m_assignStep++;
        iterateAndNextNull(nodep->rhsp());
        bool hit=false;
        if (AstVarRef* varrefp = VN_CAST(nodep->lhsp(), VarRef)) {
            if (isSubstVar(varrefp->varp())) {
                SubstVarEntry* entryp = getEntryp(varrefp);
                hit = true;
                if (m_ops > SUBST_MAX_OPS_SUBST) {
                    UINFO(8," ASSIGNtooDeep "<<varrefp<<endl);
                    entryp->assignComplex();
                } else {
                    UINFO(8," ASSIGNwhole "<<varrefp<<endl);
                    entryp->assignWhole(m_assignStep, nodep);
                }
            }
        }
        else if (AstWordSel* wordp = VN_CAST(nodep->lhsp(), WordSel)) {
            if (AstVarRef* varrefp = VN_CAST(wordp->lhsp(), VarRef)) {
                if (VN_IS(wordp->rhsp(), Const)
                    && isSubstVar(varrefp->varp())) {
                    int word = VN_CAST(wordp->rhsp(), Const)->toUInt();
                    SubstVarEntry* entryp = getEntryp(varrefp);
                    hit = true;
                    if (m_ops > SUBST_MAX_OPS_SUBST) {
                        UINFO(8," ASSIGNtooDeep "<<varrefp<<endl);
                        entryp->assignWordComplex(word);
                    } else {
                        UINFO(8," ASSIGNword"<<word<<" "<<varrefp<<endl);
                        entryp->assignWord(m_assignStep, word, nodep);
                    }
                }
            }
        }
        if (!hit) {
            iterate(nodep->lhsp());
        }
    }
    void replaceSubstEtc(AstNode* nodep, AstNode* substp) {
        if (debug()>5) nodep->dumpTree(cout, "  substw_old: ");
        AstNode* newp = substp->cloneTree(true);
        if (!nodep->isQuad() && newp->isQuad()) {
            newp = new AstCCast(newp->fileline(), newp, nodep);
        }
        if (debug()>5)  newp->dumpTree(cout, "       w_new: ");
        nodep->replaceWith(newp);
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
        ++m_statSubsts;
    }
    virtual void visit(AstWordSel* nodep) VL_OVERRIDE {
        iterate(nodep->rhsp());
        AstVarRef* varrefp = VN_CAST(nodep->lhsp(), VarRef);
        AstConst* constp = VN_CAST(nodep->rhsp(), Const);
        if (varrefp && isSubstVar(varrefp->varp())
            && !varrefp->lvalue()
            && constp) {
            // Nicely formed lvalues handled in NodeAssign
            // Other lvalues handled as unknown mess in AstVarRef
            int word = constp->toUInt();
            UINFO(8," USEword"<<word<<" "<<varrefp<<endl);
            SubstVarEntry* entryp = getEntryp(varrefp);
            if (AstNode* substp = entryp->substWord(nodep, word)) {
                // Check that the RHS hasn't changed value since we recorded it.
                SubstUseVisitor visitor (substp, entryp->getWordStep(word));
                if (visitor.ok()) {
                    VL_DO_DANGLING(replaceSubstEtc(nodep, substp), nodep);
                } else {
                    entryp->consumeWord(word);
                }
            } else {
                entryp->consumeWord(word);
            }
        } else {
            iterate(nodep->lhsp());
        }
    }
    virtual void visit(AstVarRef* nodep) VL_OVERRIDE {
        // Any variable
        if (nodep->lvalue()) {
            m_assignStep++;
            nodep->varp()->user2(m_assignStep);
            UINFO(9, " ASSIGNstep u2="<<nodep->varp()->user2()<<" "<<nodep<<endl);
        }
        if (isSubstVar(nodep->varp())) {
            SubstVarEntry* entryp = getEntryp(nodep);
            if (nodep->lvalue()) {
                UINFO(8," ASSIGNcpx "<<nodep<<endl);
                entryp->assignComplex();
            } else if (AstNode* substp = entryp->substWhole(nodep)) {
                // Check that the RHS hasn't changed value since we recorded it.
                SubstUseVisitor visitor (substp, entryp->getWholeStep());
                if (visitor.ok()) {
                    UINFO(8," USEwhole "<<nodep<<endl);
                    VL_DO_DANGLING(replaceSubstEtc(nodep, substp), nodep);
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
    virtual void visit(AstVar* nodep) VL_OVERRIDE {}
    virtual void visit(AstConst* nodep) VL_OVERRIDE {}
    virtual void visit(AstNode* nodep) VL_OVERRIDE {
        m_ops++;
        if (!nodep->isSubstOptimizable()) {
            m_ops = SUBST_MAX_OPS_NA;
        }
        iterateChildren(nodep);
    }
public:
    // CONSTRUCTORS
    explicit SubstVisitor(AstNode* nodep) {
        AstNode::user1ClearTree();  // user1p() used on entire tree
        AstNode::user2ClearTree();  // user2p() used on entire tree
        m_ops = 0;
        m_assignStep = 0;
        iterate(nodep);
    }
    virtual ~SubstVisitor() {
        V3Stats::addStat("Optimizations, Substituted temps", m_statSubsts);
        for (std::vector<SubstVarEntry*>::iterator it = m_entryps.begin();
             it != m_entryps.end(); ++it) {
            (*it)->deleteUnusedAssign();
            delete (*it);
        }
    }
};

//######################################################################
// Subst class functions

void V3Subst::substituteAll(AstNetlist* nodep) {
    UINFO(2,__FUNCTION__<<": "<<endl);
    {
        SubstVisitor visitor (nodep);
    }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("subst", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}
