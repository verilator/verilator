// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Substitute constants and expressions in expr temp's
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2004-2023 by Wilson Snyder. This program is free software; you
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

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Subst.h"

#include "V3Stats.h"

#include <algorithm>
#include <vector>

VL_DEFINE_DEBUG_FUNCTIONS;

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
    AstNodeExpr* substWhole(AstNode* errp) {
        if (!m_varp->isWide() && !m_whole.m_complex && m_whole.m_assignp && !m_wordAssign) {
            const AstNodeAssign* const assp = m_whole.m_assignp;
            UASSERT_OBJ(assp, errp, "Reading whole that was never assigned");
            return assp->rhsp();
        } else {
            return nullptr;
        }
    }
    // Return what to substitute given word number for
    AstNodeExpr* substWord(AstNode* errp, int word) {
        if (!m_whole.m_complex && !m_whole.m_assignp && !m_words[word].m_complex) {
            const AstNodeAssign* const assp = getWordAssignp(word);
            UASSERT_OBJ(assp, errp, "Reading a word that was never assigned, or bad word #");
            return assp->rhsp();
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

class SubstUseVisitor final : public VNVisitorConst {
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
    void visit(AstVarRef* nodep) override {
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
    void visit(AstConst*) override {}  // Accelerate
    void visit(AstNode* nodep) override {
        if (!nodep->isPure()) m_ok = false;
        iterateChildrenConst(nodep);
    }

public:
    // CONSTRUCTORS
    SubstUseVisitor(AstNode* nodep, int origStep)
        : m_origStep{origStep} {
        UINFO(9, "        SubstUseVisitor " << origStep << " " << nodep << endl);
        iterateConst(nodep);
    }
    ~SubstUseVisitor() override = default;
    // METHODS
    bool ok() const { return m_ok; }
};

//######################################################################
// Subst state, as a visitor of each AstNode

class SubstVisitor final : public VNVisitor {
    // NODE STATE
    // Passed to SubstUseVisitor
    // AstVar::user1p           -> SubstVar* for usage var, 0=not set yet. Only under CFunc.
    // AstVar::user2            -> int step number for last assignment, 0=not set yet
    const VNUser2InUse m_inuser2;

    // STATE
    std::deque<SubstVarEntry> m_entries;  // Nodes to delete when we are finished
    int m_ops = 0;  // Number of operators on assign rhs
    int m_assignStep = 0;  // Assignment number to determine var lifetime
    const AstCFunc* m_funcp = nullptr;  // Current function we are under
    VDouble0 m_statSubsts;  // Statistic tracking

    enum {
        SUBST_MAX_OPS_SUBST = 30,  // Maximum number of ops to substitute in
        SUBST_MAX_OPS_NA = 9999
    };  // Not allowed to substitute

    // METHODS
    SubstVarEntry* getEntryp(AstVarRef* nodep) {
        AstVar* const varp = nodep->varp();
        if (!varp->user1p()) {
            m_entries.emplace_back(varp);
            varp->user1p(&m_entries.back());
        }
        return varp->user1u().to<SubstVarEntry*>();
    }
    bool isSubstVar(AstVar* nodep) { return nodep->isStatementTemp() && !nodep->noSubst(); }

    // VISITORS
    void visit(AstNodeAssign* nodep) override {
        if (!m_funcp) return;
        VL_RESTORER(m_ops);
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
            if (AstVarRef* const varrefp = VN_CAST(wordp->fromp(), VarRef)) {
                if (VN_IS(wordp->bitp(), Const) && isSubstVar(varrefp->varp())) {
                    const int word = VN_AS(wordp->bitp(), Const)->toUInt();
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
    void replaceSubstEtc(AstNode* nodep, AstNodeExpr* substp) {
        if (debug() > 5) nodep->dumpTree("-  substw_old: ");
        AstNodeExpr* newp = substp->cloneTreePure(true);
        if (!nodep->isQuad() && newp->isQuad()) {
            newp = new AstCCast{newp->fileline(), newp, nodep};
        }
        if (debug() > 5) newp->dumpTree("-       w_new: ");
        nodep->replaceWith(newp);
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
        ++m_statSubsts;
    }
    void visit(AstWordSel* nodep) override {
        if (!m_funcp) return;
        iterate(nodep->bitp());
        AstVarRef* const varrefp = VN_CAST(nodep->fromp(), VarRef);
        const AstConst* const constp = VN_CAST(nodep->bitp(), Const);
        if (varrefp && isSubstVar(varrefp->varp()) && varrefp->access().isReadOnly() && constp) {
            // Nicely formed lvalues handled in NodeAssign
            // Other lvalues handled as unknown mess in AstVarRef
            const int word = constp->toUInt();
            UINFO(8, " USEword" << word << " " << varrefp << endl);
            SubstVarEntry* const entryp = getEntryp(varrefp);
            if (AstNodeExpr* const substp = entryp->substWord(nodep, word)) {
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
            iterate(nodep->fromp());
        }
    }
    void visit(AstVarRef* nodep) override {
        if (!m_funcp) return;
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
            } else if (AstNodeExpr* const substp = entryp->substWhole(nodep)) {
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
    void visit(AstVar*) override {}
    void visit(AstConst*) override {}

    void visit(AstCFunc* nodep) override {
        UASSERT_OBJ(!m_funcp, nodep, "Should not nest");
        UASSERT_OBJ(m_entries.empty(), nodep, "References outside functions");
        VL_RESTORER(m_funcp);
        m_funcp = nodep;

        const VNUser1InUse m_inuser1;
        iterateChildren(nodep);
        for (SubstVarEntry& ip : m_entries) ip.deleteUnusedAssign();
        m_entries.clear();
    }

    void visit(AstNode* nodep) override {
        ++m_ops;
        if (!nodep->isSubstOptimizable()) m_ops = SUBST_MAX_OPS_NA;
        iterateChildren(nodep);
    }

public:
    // CONSTRUCTORS
    explicit SubstVisitor(AstNode* nodep) { iterate(nodep); }
    ~SubstVisitor() override {
        V3Stats::addStat("Optimizations, Substituted temps", m_statSubsts);
        UASSERT(m_entries.empty(), "References outside functions");
    }
};

//######################################################################
// Subst class functions

void V3Subst::substituteAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    { SubstVisitor{nodep}; }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("subst", 0, dumpTreeLevel() >= 3);
}
