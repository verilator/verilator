// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Substitute constants and expressions in expr temp's
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2004-2022 by Wilson Snyder. This program is free software; you
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

#include "V3Subst.h"

#include "V3Ast.h"
#include "V3Global.h"
#include "V3Stats.h"

#include <algorithm>
#include <vector>

//######################################################################
// Common debugging baseclass

class SubstBaseVisitor VL_NOT_FINAL : public VNVisitor {
public:
    VL_DEBUG_FUNC;  // Declare debug()
};

//######################################################################
// Class for each word of a multi-word variable

class SubstVarWord final {
protected:
    // MEMBERS
    AstNodeAssign* m_assignp;  // Last assignment to each word of this var
    int m_step;  // Step number of last assignment
    bool m_use;  // True if each word was consumed
    bool m_complex;  // True if each word is complex
    friend class SubstVarEntry;
    // METHODS
    void clear() {
        m_assignp = nullptr;
        m_step = 0;
        m_use = false;
        m_complex = false;
    }
};

//######################################################################
// Class for every variable we may process

class SubstVarEntry final {
    // MEMBERS
    AstVar* const m_varp;  // Variable this tracks
    bool m_wordAssign = false;  // True if any word assignments
    bool m_wordUse = false;  // True if any individual word usage
    SubstVarWord m_whole;  // Data for whole vector used at once
    std::vector<SubstVarWord> m_words;  // Data for every word, if multi word variable
    static int debug() { return SubstBaseVisitor::debug(); }

public:
    // CONSTRUCTORS
    explicit SubstVarEntry(AstVar* varp)
        : m_varp{varp} {  // Construction for when a var is used
        m_words.resize(varp->widthWords());
        m_whole.clear();
        for (int i = 0; i < varp->widthWords(); i++) m_words[i].clear();
    }
    ~SubstVarEntry() = default;

private:
    // METHODS
    bool wordNumOk(int word) const { return word < m_varp->widthWords(); }
    AstNodeAssign* getWordAssignp(int word) const {
        if (!wordNumOk(word)) {
            return nullptr;
        } else {
            return m_words[word].m_assignp;
        }
    }

public:
    void assignWhole(int step, AstNodeAssign* assp) {
        if (m_whole.m_assignp) m_whole.m_complex = true;
        m_whole.m_assignp = assp;
        m_whole.m_step = step;
    }
    void assignWord(int step, int word, AstNodeAssign* assp) {
        if (!wordNumOk(word) || getWordAssignp(word) || m_words[word].m_complex) {
            m_whole.m_complex = true;
        }
        m_wordAssign = true;
        if (wordNumOk(word)) {
            m_words[word].m_assignp = assp;
            m_words[word].m_step = step;
        }
    }
    void assignWordComplex(int word) {
        if (!wordNumOk(word) || getWordAssignp(word) || m_words[word].m_complex) {
            m_whole.m_complex = true;
        }
        m_words[word].m_complex = true;
    }
    void assignComplex() { m_whole.m_complex = true; }
    void consumeWhole() {  // ==consumeComplex as we don't know the difference
        m_whole.m_use = true;
    }
    void consumeWord(int word) {
        m_words[word].m_use = true;
        m_wordUse = true;
    }
    // ACCESSORS
    AstNode* substWhole(AstNode* errp) {
        if (!m_varp->isWide() && !m_whole.m_complex && m_whole.m_assignp && !m_wordAssign) {
            const AstNodeAssign* const assp = m_whole.m_assignp;
            UASSERT_OBJ(assp, errp, "Reading whole that was never assigned");
            return (assp->rhsp());
        } else {
            return nullptr;
        }
    }
    // Return what to substitute given word number for
    AstNode* substWord(AstNode* errp, int word) {
        if (!m_whole.m_complex && !m_whole.m_assignp && !m_words[word].m_complex) {
            const AstNodeAssign* const assp = getWordAssignp(word);
            UASSERT_OBJ(assp, errp, "Reading a word that was never assigned, or bad word #");
            return (assp->rhsp());
        } else {
            return nullptr;
        }
    }
    int getWholeStep() const { return m_whole.m_step; }
    int getWordStep(int word) const {
        if (!wordNumOk(word)) {
            return 0;
        } else {
            return m_words[word].m_step;
        }
    }
    void deleteAssign(AstNodeAssign* nodep) {
        UINFO(5, "Delete " << nodep << endl);
        VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
    }
    void deleteUnusedAssign() {
        // If there are unused assignments in this var, kill them
        if (!m_whole.m_use && !m_wordUse && m_whole.m_assignp) {
            VL_DO_CLEAR(deleteAssign(m_whole.m_assignp), m_whole.m_assignp = nullptr);
        }
        for (unsigned i = 0; i < m_words.size(); i++) {
            if (!m_whole.m_use && !m_words[i].m_use && m_words[i].m_assignp
                && !m_words[i].m_complex) {
                VL_DO_CLEAR(deleteAssign(m_words[i].m_assignp), m_words[i].m_assignp = nullptr);
            }
        }
    }
};

//######################################################################
// See if any variables have changed value since we determined subst value,
// as a visitor of each AstNode

class SubstUseVisitor final : public SubstBaseVisitor {
private:
    // NODE STATE
    // See SubstVisitor
    //
    // STATE
    const int m_origStep;  // Step number where subst was recorded
    bool m_ok = true;  // No misassignments found

    // METHODS
    SubstVarEntry* findEntryp(AstVarRef* nodep) {
        return reinterpret_cast<SubstVarEntry*>(nodep->varp()->user1p());  // Might be nullptr
    }
    // VISITORS
    virtual void visit(AstVarRef* nodep) override {
        const SubstVarEntry* const entryp = findEntryp(nodep);
        if (entryp) {
            // Don't sweat it.  We assign a new temp variable for every new assignment,
            // so there's no way we'd ever replace a old value.
        } else {
            // A simple variable; needs checking.
            if (m_origStep < nodep->varp()->user2()) {
                if (m_ok) {
                    UINFO(9, "   RHS variable changed since subst recorded: " << nodep << endl);
                }
                m_ok = false;
            }
        }
    }
    virtual void visit(AstConst*) override {}  // Accelerate
    virtual void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    SubstUseVisitor(AstNode* nodep, int origStep)
        : m_origStep{origStep} {
        UINFO(9, "        SubstUseVisitor " << origStep << " " << nodep << endl);
        iterate(nodep);
    }
    virtual ~SubstUseVisitor() override = default;
    // METHODS
    bool ok() const { return m_ok; }
};

//######################################################################
// Subst state, as a visitor of each AstNode

class SubstVisitor final : public SubstBaseVisitor {
private:
    // NODE STATE
    // Passed to SubstUseVisitor
    // AstVar::user1p           -> SubstVar* for usage var, 0=not set yet
    // AstVar::user2            -> int step number for last assignment, 0=not set yet
    const VNUser1InUse m_inuser1;
    const VNUser2InUse m_inuser2;

    // STATE
    std::vector<SubstVarEntry*> m_entryps;  // Nodes to delete when we are finished
    int m_ops = 0;  // Number of operators on assign rhs
    int m_assignStep = 0;  // Assignment number to determine var lifetime
    VDouble0 m_statSubsts;  // Statistic tracking

    enum {
        SUBST_MAX_OPS_SUBST = 30,  // Maximum number of ops to substitute in
        SUBST_MAX_OPS_NA = 9999
    };  // Not allowed to substitute

    // METHODS
    SubstVarEntry* getEntryp(AstVarRef* nodep) {
        if (!nodep->varp()->user1p()) {
            SubstVarEntry* const entryp = new SubstVarEntry(nodep->varp());
            m_entryps.push_back(entryp);
            nodep->varp()->user1p(entryp);
            return entryp;
        } else {
            SubstVarEntry* const entryp
                = reinterpret_cast<SubstVarEntry*>(nodep->varp()->user1p());
            return entryp;
        }
    }
    inline bool isSubstVar(AstVar* nodep) { return nodep->isStatementTemp() && !nodep->noSubst(); }

    // VISITORS
    virtual void visit(AstNodeAssign* nodep) override {
        m_ops = 0;
        m_assignStep++;
        iterateAndNextNull(nodep->rhsp());
        bool hit = false;
        if (AstVarRef* const varrefp = VN_CAST(nodep->lhsp(), VarRef)) {
            if (isSubstVar(varrefp->varp())) {
                SubstVarEntry* const entryp = getEntryp(varrefp);
                hit = true;
                if (m_ops > SUBST_MAX_OPS_SUBST) {
                    UINFO(8, " ASSIGNtooDeep " << varrefp << endl);
                    entryp->assignComplex();
                } else {
                    UINFO(8, " ASSIGNwhole " << varrefp << endl);
                    entryp->assignWhole(m_assignStep, nodep);
                }
            }
        } else if (const AstWordSel* const wordp = VN_CAST(nodep->lhsp(), WordSel)) {
            if (AstVarRef* const varrefp = VN_CAST(wordp->lhsp(), VarRef)) {
                if (VN_IS(wordp->rhsp(), Const) && isSubstVar(varrefp->varp())) {
                    const int word = VN_AS(wordp->rhsp(), Const)->toUInt();
                    SubstVarEntry* const entryp = getEntryp(varrefp);
                    hit = true;
                    if (m_ops > SUBST_MAX_OPS_SUBST) {
                        UINFO(8, " ASSIGNtooDeep " << varrefp << endl);
                        entryp->assignWordComplex(word);
                    } else {
                        UINFO(8, " ASSIGNword" << word << " " << varrefp << endl);
                        entryp->assignWord(m_assignStep, word, nodep);
                    }
                }
            }
        }
        if (!hit) iterate(nodep->lhsp());
    }
    void replaceSubstEtc(AstNode* nodep, AstNode* substp) {
        if (debug() > 5) nodep->dumpTree(cout, "  substw_old: ");
        AstNode* newp = substp->cloneTree(true);
        if (!nodep->isQuad() && newp->isQuad()) {
            newp = new AstCCast(newp->fileline(), newp, nodep);
        }
        if (debug() > 5) newp->dumpTree(cout, "       w_new: ");
        nodep->replaceWith(newp);
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
        ++m_statSubsts;
    }
    virtual void visit(AstWordSel* nodep) override {
        iterate(nodep->rhsp());
        AstVarRef* const varrefp = VN_CAST(nodep->lhsp(), VarRef);
        const AstConst* const constp = VN_CAST(nodep->rhsp(), Const);
        if (varrefp && isSubstVar(varrefp->varp()) && varrefp->access().isReadOnly() && constp) {
            // Nicely formed lvalues handled in NodeAssign
            // Other lvalues handled as unknown mess in AstVarRef
            const int word = constp->toUInt();
            UINFO(8, " USEword" << word << " " << varrefp << endl);
            SubstVarEntry* const entryp = getEntryp(varrefp);
            if (AstNode* const substp = entryp->substWord(nodep, word)) {
                // Check that the RHS hasn't changed value since we recorded it.
                const SubstUseVisitor visitor{substp, entryp->getWordStep(word)};
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
    virtual void visit(AstVarRef* nodep) override {
        // Any variable
        if (nodep->access().isWriteOrRW()) {
            m_assignStep++;
            nodep->varp()->user2(m_assignStep);
            UINFO(9, " ASSIGNstep u2=" << nodep->varp()->user2() << " " << nodep << endl);
        }
        if (isSubstVar(nodep->varp())) {
            SubstVarEntry* const entryp = getEntryp(nodep);
            if (nodep->access().isWriteOrRW()) {
                UINFO(8, " ASSIGNcpx " << nodep << endl);
                entryp->assignComplex();
            } else if (AstNode* const substp = entryp->substWhole(nodep)) {
                // Check that the RHS hasn't changed value since we recorded it.
                const SubstUseVisitor visitor{substp, entryp->getWholeStep()};
                if (visitor.ok()) {
                    UINFO(8, " USEwhole " << nodep << endl);
                    VL_DO_DANGLING(replaceSubstEtc(nodep, substp), nodep);
                } else {
                    UINFO(8, " USEwholeButChg " << nodep << endl);
                    entryp->consumeWhole();
                }
            } else {  // Consumed w/o substitute
                UINFO(8, " USEwtf   " << nodep << endl);
                entryp->consumeWhole();
            }
        }
    }
    virtual void visit(AstVar*) override {}
    virtual void visit(AstConst*) override {}
    virtual void visit(AstNode* nodep) override {
        m_ops++;
        if (!nodep->isSubstOptimizable()) m_ops = SUBST_MAX_OPS_NA;
        iterateChildren(nodep);
    }

public:
    // CONSTRUCTORS
    explicit SubstVisitor(AstNode* nodep) { iterate(nodep); }
    virtual ~SubstVisitor() override {
        V3Stats::addStat("Optimizations, Substituted temps", m_statSubsts);
        for (SubstVarEntry* ip : m_entryps) {
            ip->deleteUnusedAssign();
            delete ip;
        }
    }
};

//######################################################################
// Subst class functions

void V3Subst::substituteAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    { SubstVisitor{nodep}; }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("subst", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}
