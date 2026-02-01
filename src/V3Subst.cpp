// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Substitute constants and expressions in expr temp's
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2004-2026 Wilson Snyder
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

#include "V3Const.h"
#include "V3Stats.h"

#include <vector>

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// Data strored for every variable that tracks assignments and usage

class SubstVarEntry final {
    friend class SubstValidVisitor;

    // SubstVarEntry contains a Record for each word, and one extra for the whole variable
    struct Record final {
        // MEMBERS
        AstNodeAssign* m_assignp;  // Last assignment to this part
        uint32_t m_step;  // Step number of last assignment. 0 means invalid entry.
        bool m_used;  // True if consumed. Can be set even if entry is invalid.
        // CONSTRUCTOR
        Record() { invalidate(); }
        // METHODS
        void invalidate() {
            m_assignp = nullptr;
            m_step = 0;
            m_used = false;
        }
    };

    // MEMBERS
    // Variable this SubstVarEntry tracks
    AstVar* const m_varp;
    // The recrod for whole variable tracking
    Record m_wholeRecord{};
    // A record for each word in the variable
    std::vector<Record> m_wordRecords{static_cast<size_t>(m_varp->widthWords()), Record{}};

    // METHDOS
    void deleteAssignmentIfUnused(Record& record, size_t& nAssignDeleted) {
        if (!record.m_assignp) return;
        if (record.m_used) return;
        ++nAssignDeleted;
        VL_DO_DANGLING(record.m_assignp->unlinkFrBack()->deleteTree(), record.m_assignp);
    }

    AstNodeExpr* substRecord(Record& record);

public:
    // CONSTRUCTORS
    explicit SubstVarEntry(AstVar* varp)
        : m_varp{varp} {}
    ~SubstVarEntry() = default;

    // Record assignment of whole variable. The given 'assp' can be null, which means
    // the variable is known to be assigned, but to an unknown value.
    void assignWhole(AstNodeAssign* assp, uint32_t step) {
        // Invalidate all word records
        for (Record& wordRecord : m_wordRecords) wordRecord.invalidate();
        // Set whole record
        m_wholeRecord.m_assignp = assp;
        m_wholeRecord.m_step = step;
        m_wholeRecord.m_used = false;
    }

    // Like assignWhole word, but records assignment to a specific word of the variable.
    void assignWord(AstNodeAssign* assp, uint32_t step, uint32_t word) {
        // Invalidate whole record
        m_wholeRecord.invalidate();
        // Set word record
        Record& wordRecord = m_wordRecords[word];
        wordRecord.m_assignp = assp;
        wordRecord.m_step = step;
        wordRecord.m_used = false;
    }

    // Mark the whole variable as used (value consumed)
    void usedWhole() {
        m_wholeRecord.m_used = true;
        for (Record& wordRecord : m_wordRecords) wordRecord.m_used = true;
    }

    // Mark the specific word as used (value consumed)
    void usedWord(uint32_t word) {
        m_wholeRecord.m_used = true;
        m_wordRecords[word].m_used = true;
    }

    // Returns substitution of whole word, or nullptr if not known/stale
    AstNodeExpr* substWhole() { return substRecord(m_wholeRecord); }
    // Returns substitution of whole word, or nullptr if not known/stale
    AstNodeExpr* substWord(uint32_t word) { return substRecord(m_wordRecords[word]); }

    void deleteUnusedAssignments(size_t& nWordAssignDeleted, size_t& nWholeAssignDeleted) {
        // Delete assignments to temporaries if they are not used
        if (!m_varp->isStatementTemp()) return;
        for (Record& wordRecord : m_wordRecords)
            deleteAssignmentIfUnused(wordRecord, nWordAssignDeleted);
        deleteAssignmentIfUnused(m_wholeRecord, nWholeAssignDeleted);
    }
};

//######################################################################
// See if any variables in the expression we are considering to
// substitute have changed value since we recorded the assignment.

class SubstValidVisitor final : public VNVisitorConst {
    // NODE STATE
    // See SubstVisitor

    // STATE
    const uint32_t m_step;  // Step number where assignment was recorded
    bool m_valid = true;  // Is the expression we are considering to substitute valid

    // METHODS
    SubstVarEntry& getEntry(AstVarRef* nodep) {
        // This vistor is always invoked on the RHS of an assignment we are considering to
        // substitute. Variable references must have all been recorded when visiting the
        // assignments RHS, so the SubstVarEntry must exist for each referenced variable.
        return *nodep->varp()->user1u().to<SubstVarEntry*>();
    }

    // VISITORS
    void visit(AstWordSel* nodep) override {
        if (!m_valid) return;

        if (AstVarRef* const refp = VN_CAST(nodep->fromp(), VarRef)) {
            if (AstConst* const idxp = VN_CAST(nodep->bitp(), Const)) {
                SubstVarEntry& entry = getEntry(refp);
                // If either the whole variable, or the indexed word was written to
                // after the original assignment was recorded, the value is invalid.
                if (m_step < entry.m_wholeRecord.m_step) m_valid = false;
                if (m_step < entry.m_wordRecords[idxp->toUInt()].m_step) m_valid = false;
                return;
            }
        }
        iterateChildrenConst(nodep);
    }

    void visit(AstVarRef* nodep) override {
        if (!m_valid) return;

        // If either the whole variable, or any of the words were written to
        // after the original assignment was recorded, the value is invalid.
        SubstVarEntry& entry = getEntry(nodep);
        if (m_step < entry.m_wholeRecord.m_step) {
            m_valid = false;
            return;
        }
        for (SubstVarEntry::Record& wordRecord : entry.m_wordRecords) {
            if (m_step < wordRecord.m_step) {
                m_valid = false;
                return;
            }
        }
    }

    void visit(AstConst*) override {}  // Accelerate

    void visit(AstNodeExpr* nodep) override {
        if (!m_valid) return;
        iterateChildrenConst(nodep);
    }

    void visit(AstNode* nodep) override { nodep->v3fatalSrc("Non AstNodeExpr under AstNodeExpr"); }

    // CONSTRUCTORS
    SubstValidVisitor(SubstVarEntry::Record& record)
        : m_step{record.m_step} {
        iterateConst(record.m_assignp->rhsp());
    }
    ~SubstValidVisitor() override = default;

public:
    static bool valid(SubstVarEntry::Record& record) {
        if (!record.m_assignp) return false;
        return SubstValidVisitor{record}.m_valid;
    }
};

AstNodeExpr* SubstVarEntry::substRecord(SubstVarEntry::Record& record) {
    if (!SubstValidVisitor::valid(record)) return nullptr;
    AstNodeExpr* const rhsp = record.m_assignp->rhsp();
    UDEBUGONLY(UASSERT_OBJ(rhsp->isPure(), record.m_assignp, "Substituting impure expression"););
    return rhsp;
}

//######################################################################
// Substitution visitor

class SubstVisitor final : public VNVisitor {
    // NODE STATE - only Under AstCFunc
    // AstVar::user1p -> SubstVarEntry* for assignment tracking. Also used by SubstValidVisitor

    // STATE
    std::deque<SubstVarEntry> m_entries;  // Storage for SubstVarEntry instances
    uint32_t m_ops = 0;  // Number of nodes on the RHS of an assignment
    uint32_t m_assignStep = 0;  // Assignment number to determine variable lifetimes
    const AstCFunc* m_funcp = nullptr;  // Current function we are under
    size_t m_nSubst = 0;  // Number of substitutions performed - for avoiding constant folding
    // Statistics
    size_t m_nWordSubstituted = 0;  // Number of words substituted
    size_t m_nWholeSubstituted = 0;  // Number of whole variables substituted
    size_t m_nWordAssignDeleted = 0;  // Number of word assignments deleted
    size_t m_nWholeAssignDeleted = 0;  // Number of whole variable assignments deleted

    static constexpr uint32_t SUBST_MAX_OPS_SUBST = 30;  // Maximum number of ops to substitute in
    static constexpr uint32_t SUBST_MAX_OPS_NA = 9999;  // Not allowed to substitute

    // METHODS
    SubstVarEntry& getEntry(AstVarRef* nodep) {
        AstVar* const varp = nodep->varp();
        if (!varp->user1p()) {
            m_entries.emplace_back(varp);
            varp->user1p(&m_entries.back());
        }
        return *varp->user1u().to<SubstVarEntry*>();
    }

    void simplify(AstNodeExpr* exprp) {
        // Often constant, so short circuit
        if (VN_IS(exprp, Const)) return;
        // Iterate expression, then constant fold it if anything changed
        const size_t nSubstBefore = m_nSubst;
        exprp = VN_AS(iterateSubtreeReturnEdits(exprp), NodeExpr);
        if (nSubstBefore != m_nSubst) V3Const::constifyEditCpp(exprp);
    }

    // The way the analysis algorithm works based on statement numbering only works
    // for variables that are written in the same basic block (ignoring AstCond) as
    // where they are consumed. The temporaries introduced in V3Premit are such, so
    // only substitute those for now.
    bool isSubstitutable(AstVar* nodep) { return nodep->isStatementTemp() && !nodep->noSubst(); }

    void substitute(AstNode* nodep, AstNodeExpr* substp) {
        AstNodeExpr* newp = substp->cloneTreePure(true);
        if (!nodep->isQuad() && newp->isQuad()) {
            newp = new AstCCast{newp->fileline(), newp, nodep};
        }
        nodep->replaceWith(newp);
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
        ++m_nSubst;
    }

    // VISITORS
    void visit(AstCFunc* nodep) override {
        UASSERT_OBJ(!m_funcp, nodep, "Should not nest");
        UASSERT_OBJ(m_entries.empty(), nodep, "Should not visit outside functions");

        // Process the function body
        {
            VL_RESTORER(m_funcp);
            m_funcp = nodep;
            const VNUser1InUse m_inuser1;
            iterateChildren(nodep);
            // Deletes unused assignments and clear entries
            for (SubstVarEntry& entry : m_entries) {
                entry.deleteUnusedAssignments(m_nWordAssignDeleted, m_nWholeAssignDeleted);
            }
            m_entries.clear();
        }

        // Constant fold here, as Ast size can likely be reduced
        if (v3Global.opt.fConstEager()) V3Const::constifyEditCpp(nodep);
    }

    void visit(AstNodeAssign* nodep) override {
        if (!m_funcp) return;

        const uint32_t ops = [&]() {
            VL_RESTORER(m_ops);
            m_ops = 0;
            // Simplify the RHS
            simplify(nodep->rhsp());
            // If the became constant, we can continue substituting it
            return VN_IS(nodep->rhsp(), Const) ? 0 : m_ops;
        }();

        // Assignment that defines the value, which is either this 'nodep',
        // or nullptr, if the value should not be substituted.
        const auto getAssignp = [&](AstVarRef* refp) -> AstNodeAssign* {
            // If too complex, don't substitute
            if (ops > SUBST_MAX_OPS_SUBST) return nullptr;
            // AstCvtPackedToArray can't be anywhere else than on the RHS of assignment
            if (VN_IS(nodep->rhsp(), CvtPackedToArray)) return nullptr;
            // If non const but want const subtitutions only
            if (refp->varp()->substConstOnly() && !VN_IS(nodep->rhsp(), Const)) return nullptr;
            // Otherwise can substitute based on the assignment
            return nodep;
        };

        // If LHS is a whole variable reference, track the whole variable
        if (AstVarRef* const refp = VN_CAST(nodep->lhsp(), VarRef)) {
            getEntry(refp).assignWhole(getAssignp(refp), ++m_assignStep);
            return;
        }

        // If LHS is a known word reference, track the word
        if (const AstWordSel* const selp = VN_CAST(nodep->lhsp(), WordSel)) {
            if (AstVarRef* const refp = VN_CAST(selp->fromp(), VarRef)) {
                // Simplify the index
                simplify(selp->bitp());
                if (const AstConst* const idxp = VN_CAST(selp->bitp(), Const)) {
                    getEntry(refp).assignWord(getAssignp(refp), ++m_assignStep, idxp->toUInt());
                    return;
                }
            }
        }

        // Not tracked, iterate LHS to simplify/reset tracking
        iterate(nodep->lhsp());
    }

    void visit(AstWordSel* nodep) override {
        if (!m_funcp) return;

        // Simplify the index
        simplify(nodep->bitp());

        // If this is a known word reference, track/substitute it
        if (AstVarRef* const refp = VN_CAST(nodep->fromp(), VarRef)) {
            if (const AstConst* const idxp = VN_CAST(nodep->bitp(), Const)) {
                SubstVarEntry& entry = getEntry(refp);
                const uint32_t word = idxp->toUInt();

                // If it's a write, reset tracking as we don't know the assigned value,
                // otherwise we would have picked it up in visit(AstNodeAssign*)
                if (refp->access().isWriteOrRW()) {
                    entry.assignWord(nullptr, ++m_assignStep, word);
                    return;
                }

                // Otherwise it's a read, substitute it if possible
                UASSERT_OBJ(refp->access().isReadOnly(), nodep, "Invalid access");
                if (isSubstitutable(refp->varp())) {
                    if (AstNodeExpr* const substp = entry.substWord(word)) {
                        ++m_nWordSubstituted;
                        substitute(nodep, substp);
                        return;
                    }
                }

                // If not substituted, mark the assignment setting this word as used
                entry.usedWord(word);
                return;
            }
        }

        // If not a known word reference, iterate fromp to simplify/reset tracking
        iterate(nodep->fromp());
    }

    void visit(AstVarRef* nodep) override {
        if (!m_funcp) return;

        SubstVarEntry& entry = getEntry(nodep);

        // If it's a write, reset tracking as we don't know the assigned value,
        // otherwise we would have picked it up in visit(AstNodeAssign*)
        if (nodep->access().isWriteOrRW()) {
            entry.assignWhole(nullptr, ++m_assignStep);
            return;
        }

        // Otherwise it's a read, substitute it if possible
        UASSERT_OBJ(nodep->access().isReadOnly(), nodep, "Invalid access");
        if (isSubstitutable(nodep->varp())) {
            if (AstNodeExpr* const substp = entry.substWhole()) {
                // Do not substitute a compound wide expression.
                // The whole point of adding temporaries is to eliminate them.
                if (!nodep->isWide() || VN_IS(substp, VarRef)) {
                    ++m_nWholeSubstituted;
                    substitute(nodep, substp);
                    return;
                }
            }
        }

        // If not substituted, mark the assignment setting this variable as used
        entry.usedWhole();
    }

    void visit(AstNodeExpr* nodep) override {
        if (!m_funcp) return;

        // Count nodes as we descend to track complexity
        ++m_ops;
        // First iterate children, this can cache child purity
        iterateChildren(nodep);
        // Do not substitute impure expressions
        if (!nodep->isPure()) m_ops = SUBST_MAX_OPS_NA;
    }

    void visit(AstVar*) override {}  // Accelerate
    void visit(AstConst*) override {}  // Accelerate

    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit SubstVisitor(AstNode* nodep) { iterate(nodep); }
    ~SubstVisitor() override {
        V3Stats::addStat("Optimizations, Substituted temps", m_nSubst);
        V3Stats::addStat("Optimizations, Whole variable assignments deleted",
                         m_nWholeAssignDeleted);
        V3Stats::addStat("Optimizations, Whole variables substituted", m_nWholeSubstituted);
        V3Stats::addStat("Optimizations, Word assignments deleted", m_nWordAssignDeleted);
        V3Stats::addStat("Optimizations, Words substituted", m_nWordSubstituted);
        UASSERT(m_entries.empty(), "Should not visit outside functions");
    }
};

//######################################################################
// Subst class functions

void V3Subst::substituteAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ":");
    { SubstVisitor{nodep}; }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("subst", 0, dumpTreeEitherLevel() >= 3);
}
