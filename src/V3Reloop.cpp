// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Recreate loops to help pack caches
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2003-2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
// V3Reloop's Transformations:
//
// Each statement list in each CFunc:
//    Look for a run of statements that are identical apart from packed
//    constants of at most 32 bits, each of which advances by a constant stride
//    from one statement to the next:
//
//      STMT(ARRAYSEL(a, 5), ARRAYSEL(b, 7), CONST(3))
//      STMT(ARRAYSEL(a, 6), ARRAYSEL(b, 6), CONST(3))
//      STMT(ARRAYSEL(a, 7), ARRAYSEL(b, 5), CONST(3))
//      ->
//      Create __Vilp local variable
//      FOR(__Vilp = 0; __Vilp < 3; ++__Vilp)
//         STMT(ARRAYSEL(a, 5 + __Vilp), ARRAYSEL(b, 7 + -1 * __Vilp), CONST(3))
//
//    Statements still execute in their original order.
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Reloop.h"

#include "V3Stats.h"

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// Collects the constants of a statement that can be replaced with a
// loop variable, and checks whether the statement can be placed in a
// new loop. Also records the types of the nodes visited, or matches
// them against those recorded for another statement, stopping at the
// first difference.

class ReloopAnalysis final : public VNVisitorConst {
    // NODE STATE
    // AstLoop::user1()     -> bool. Loop is inside the statement
    const VNUser1InUse m_user1InUse;

    // STATE
    std::vector<AstConst*>& m_consts;  // Packed constants of at most 32 bits, in visit order
    std::vector<VNType>& m_types;  // Types of the nodes visited, in visit order
    const bool m_record;  // Record 'm_types', otherwise match against it
    size_t m_typeIdx = 0;  // Next entry of 'm_types' to match
    bool m_ok = true;  // Statement can be placed in a new loop, and matches 'm_types'

    // METHODS
    // Record or match the type of 'nodep'. Returns false if the walk should stop.
    bool enter(const AstNode* nodep) {
        if (!m_ok) return false;
        if (m_record) {
            m_types.push_back(nodep->type());
        } else if (m_typeIdx == m_types.size() || m_types[m_typeIdx++] != nodep->type()) {
            m_ok = false;
        }
        return m_ok;
    }

    // VISITORS
    void visit(AstConst* nodep) override {
        if (!enter(nodep)) return;
        if (nodep->width() > 32 || nodep->num().isOpaque()) return;
        if (!nodep->dtypep()->skipRefp()->isIntegralOrPacked()) return;
        if (nodep->num().isFourState()) return;
        m_consts.push_back(nodep);
    }
    void visit(AstStreamL* nodep) override {
        if (!enter(nodep)) return;
        iterateConst(nodep->lhsp());  // Slice size 'rhsp' is emitted as a literal
    }
    void visit(AstReplicate* nodep) override {
        if (!enter(nodep)) return;
        // The count 'countp' sets widthMin, which sameNode ignores, and is emitted as a literal
        iterateConst(nodep->srcp());
    }
    void visit(AstLoop* nodep) override {
        if (!enter(nodep)) return;
        nodep->user1(true);
        iterateChildrenConst(nodep);
    }
    void visit(AstLoopTest* nodep) override {
        if (!enter(nodep)) return;
        // Emitted as 'break', so a test of an enclosing loop would break out of the new loop
        if (!nodep->loopp()->user1()) {
            m_ok = false;
            return;
        }
        iterateChildrenConst(nodep);
    }
    void visit(AstTraceDecl*) override {
        // Pointed to by AstTraceInc, and sameNode ignores what it declares
        m_ok = false;
    }
    void visit(AstNode* nodep) override {
        if (enter(nodep)) iterateChildrenConst(nodep);
    }

    // CONSTRUCTORS
    ReloopAnalysis(AstNode* nodep, std::vector<AstConst*>& consts, std::vector<VNType>& types,
                   bool record)
        : m_consts{consts}
        , m_types{types}
        , m_record{record} {
        m_consts.clear();
        if (m_record) m_types.clear();
        iterateConst(nodep);
        if (!m_record && m_typeIdx != m_types.size()) m_ok = false;
    }

public:
    // Fill 'consts' with the replaceable constants of 'nodep', and 'types' with the types of its
    // nodes. Returns true if 'nodep' can be placed in a new loop.
    static bool gather(AstNode* nodep, std::vector<AstConst*>& consts,
                       std::vector<VNType>& types) {
        return ReloopAnalysis{nodep, consts, types, true}.m_ok;
    }
    // Fill 'consts' with the replaceable constants of 'nodep'. Returns true if 'nodep' can be
    // placed in a new loop, and the types of its nodes are 'types'.
    static bool match(AstNode* nodep, std::vector<AstConst*>& consts, std::vector<VNType>& types) {
        return ReloopAnalysis{nodep, consts, types, false}.m_ok;
    }
};

//######################################################################

class ReloopVisitor final : public VNVisitor {
    // STATE
    const uint32_t m_limit = static_cast<uint32_t>(v3Global.opt.reloopLimit());  // Min run length
    AstCFunc* m_cfuncp = nullptr;  // Current function
    uint32_t m_nTemps = 0;  // Number of loop variables created in current function
    // Members to avoid reallocation
    std::vector<AstConst*> m_firstConsts;  // Replaceable constants of the first statement
    std::vector<VNType> m_firstTypes;  // Types of the nodes of the first statement
    std::vector<uint32_t> m_deltas;  // Per statement advance of 'm_firstConsts'
    std::vector<AstConst*> m_consts;  // Replaceable constants of the statement compared
    VDouble0 m_statReloops;  // Statistic tracking
    VDouble0 m_statReItems;  // Statistic tracking

    // METHODS

    // True if 'nodep' is 'firstp' with the constants 'm_firstConsts' advanced by 'm_deltas' * 'n'.
    // Arithmetic is modulo 2^32, the same as in the loop body replacing them.
    bool isStridedCopy(AstNodeStmt* firstp, AstNodeStmt* nodep, uint32_t n) {
        if (!ReloopAnalysis::match(nodep, m_consts, m_firstTypes)) return false;
        if (m_consts.size() != m_firstConsts.size()) return false;
        // Check if the constants are strided as expected
        for (size_t i = 0; i < m_consts.size(); ++i) {
            if (m_consts[i]->toUInt() != m_firstConsts[i]->toUInt() + m_deltas[i] * n) {
                return false;
            }
        }
        // Structurally identical apart from the constants. Compare in place with the constants
        // temporarily set to those of 'firstp', then restore them to 'first + delta * n'.
        for (size_t i = 0; i < m_consts.size(); ++i) {
            m_consts[i]->num().setLong(m_firstConsts[i]->toUInt());
        }
        const bool same = nodep->sameTree(firstp);
        for (size_t i = 0; i < m_consts.size(); ++i) {
            m_consts[i]->num().setLong(m_firstConsts[i]->toUInt() + m_deltas[i] * n);
        }
        return same;
    }

    // Next statement after 'stmtp', skipping comments, or nullptr if none
    static AstNodeStmt* nextStmt(AstNodeStmt* stmtp) {
        AstNode* nextp = stmtp->nextp();
        while (VN_IS(nextp, Comment)) nextp = nextp->nextp();
        return VN_CAST(nextp, NodeStmt);
    }

    // Number of statements from 'firstp' that are strided copies of it, ignoring comments, and
    // the last of them. Sets 'm_deltas' to the per statement advance of the constants
    // 'm_firstConsts'.
    std::pair<uint32_t, AstNodeStmt*> runLength(AstNodeStmt* firstp) {
        AstNodeStmt* const secondp = nextStmt(firstp);
        if (!secondp) return {1, firstp};
        if (!ReloopAnalysis::match(secondp, m_consts, m_firstTypes)) return {1, firstp};
        if (m_consts.size() != m_firstConsts.size()) return {1, firstp};
        // Calculate the per statement advance of the constants
        m_deltas.clear();
        for (size_t i = 0; i < m_firstConsts.size(); ++i) {
            m_deltas.push_back(m_consts[i]->toUInt() - m_firstConsts[i]->toUInt());
        }
        // Count the number of statements that are strided copies of 'firstp'
        uint32_t n = 1;
        AstNodeStmt* lastp = firstp;
        for (AstNodeStmt* stmtp = secondp; stmtp; stmtp = nextStmt(stmtp)) {
            if (!isStridedCopy(firstp, stmtp, n)) break;
            ++n;
            lastp = stmtp;
        }
        return {n, lastp};
    }

    // Replace constants 'm_firstConsts' with 'first + delta * itp'. On every iteration this
    // equals the replaced constant, as checked by 'isStridedCopy', so needs no masking.
    void replaceConsts(AstVar* itp) {
        for (size_t i = 0; i < m_firstConsts.size(); ++i) {
            const uint32_t delta = m_deltas[i];
            if (!delta) continue;
            AstConst* const constp = m_firstConsts[i];
            FileLine* const flp = constp->fileline();
            AstNodeExpr* valuep = new AstVarRef{flp, itp, VAccess::READ};
            if (delta != 1) valuep = new AstMul{flp, new AstConst{flp, delta}, valuep};
            if (!constp->isZero()) {
                valuep = new AstAdd{flp, new AstConst{flp, constp->toUInt()}, valuep};
            }
            valuep->dtypeFrom(constp);
            constp->replaceWith(valuep);
            VL_DO_DANGLING(pushDeletep(constp), constp);
        }
    }

    // Replace 'firstp' and the following 'n - 1' strided copies of it with a loop. Returns the
    // replacement, which is the loop initializer followed by the loop.
    AstNode* makeLoop(AstNodeStmt* firstp, uint32_t n) {
        // Remove all but the first, which becomes the loop body
        for (uint32_t i = 1; i < n;) {
            AstNode* const deadp = firstp->nextp()->unlinkFrBack();
            if (!VN_IS(deadp, Comment)) ++i;
            VL_DO_DANGLING(pushDeletep(deadp), deadp);
        }
        FileLine* const flp = firstp->fileline();
        // Create the loop variable
        AstVar* const itp
            = new AstVar{flp, VVarType::STMTTEMP, "__Vilp" + std::to_string(++m_nTemps),
                         VFlagLogicPacked{}, 32};
        m_cfuncp->addVarsp(itp);
        // Replace the constants with the loop variable
        replaceConsts(itp);
        // Create the loop initializer
        AstNode* const initp
            = new AstAssign{flp, new AstVarRef{flp, itp, VAccess::WRITE}, new AstConst{flp, 0U}};
        firstp->replaceWith(initp);
        // Create the loop
        AstLoop* const loopp = new AstLoop{flp};
        initp->addNextHere(loopp);
        // Add the loop body
        loopp->addStmtsp(firstp);
        AstNode* const incp = new AstAssign{
            flp, new AstVarRef{flp, itp, VAccess::WRITE},
            new AstAdd{flp, new AstConst{flp, 1U}, new AstVarRef{flp, itp, VAccess::READ}}};
        loopp->addStmtsp(incp);
        // Create the loop condition
        AstNodeExpr* const condp
            = new AstGt{flp, new AstConst{flp, n}, new AstVarRef{flp, itp, VAccess::READ}};
        loopp->addStmtsp(new AstLoopTest{flp, loopp, condp});
        UINFOTREE(9, initp, "", "new");
        UINFOTREE(9, loopp, "", "new");
        return initp;
    }

    // If 'startp' starts a run of statements that only differ in constants, which advance
    // by a constant per statement, reroll the run into a loop, reducing code size. Returns the
    // node now in place of 'startp', and the next statement that can start a run.
    std::pair<AstNode*, AstNode*> reroll(AstNode* startp) {
        AstNodeStmt* const firstp = VN_CAST(startp, NodeStmt);
        if (!firstp || !ReloopAnalysis::gather(firstp, m_firstConsts, m_firstTypes)) {
            return {startp, startp->nextp()};
        }
        const std::pair<uint32_t, AstNodeStmt*> run = runLength(firstp);
        const uint32_t n = run.first;
        AstNodeStmt* const lastp = run.second;
        if (n < m_limit) {
            // A run starting before 'lastp' has the same strides, so ends at the same place.
            // Skipping them makes this linear in the number of statements, not in the limit.
            return {startp, lastp != firstp ? lastp : firstp->nextp()};
        }
        UINFO(6, "Reloop items=" << n << " " << firstp);
        ++m_statReloops;
        m_statReItems += n;
        AstNode* const initp = makeLoop(firstp, n);
        return {initp, initp->nextp()->nextp()};  // Next is after the initializer and the loop
    }

    void rerollList(AstNode* headp) {
        for (AstNode* startp = headp; startp;) {
            // Outer level first, so siblings are compared before their contents are rerolled
            const std::pair<AstNode*, AstNode*> range = reroll(startp);
            for (AstNode* nodep = range.first; nodep != range.second; nodep = nodep->nextp()) {
                // Reroll children of compound statements
                if (AstIf* const ifp = VN_CAST(nodep, If)) {
                    rerollList(ifp->thensp());
                    rerollList(ifp->elsesp());
                } else if (AstLoop* const loopp = VN_CAST(nodep, Loop)) {
                    rerollList(loopp->stmtsp());
                } else if (AstJumpBlock* const blockp = VN_CAST(nodep, JumpBlock)) {
                    rerollList(blockp->stmtsp());
                } else if (AstCLocalScope* const scopep = VN_CAST(nodep, CLocalScope)) {
                    rerollList(scopep->stmtsp());
                }
            }
            startp = range.second;
        }
    }

    // VISITORS
    void visit(AstCFunc* nodep) override {
        VL_RESTORER(m_cfuncp);
        VL_RESTORER(m_nTemps);
        m_cfuncp = nodep;
        m_nTemps = 0;
        rerollList(nodep->stmtsp());
    }
    //--------------------
    void visit(AstVar*) override {}  // Accelerate
    void visit(AstNodeExpr*) override {}  // Accelerate
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit ReloopVisitor(AstNetlist* nodep) { iterate(nodep); }
    ~ReloopVisitor() override {
        V3Stats::addStat("Optimizations, Reloops", m_statReloops);
        V3Stats::addStat("Optimizations, Reloop iterations", m_statReItems);
    }
};

//######################################################################
// Reloop class functions

void V3Reloop::reloopAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ":");
    { ReloopVisitor{nodep}; }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("reloop", 0, dumpTreeEitherLevel() >= 6);
}
