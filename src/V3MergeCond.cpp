// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Merge branches/ternary ?:
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2021 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
// V3BranchMerge's Transformations:
//
//    Look for sequences of assignments with ternary conditional on the right
//    hand side with the same condition:
//      lhs0 = cond ? then0 : else0;
//      lhs1 = cond ? then1 : else1;
//      lhs2 = cond ? then2 : else2;
//
//    This seems to be a common pattern and can make the C compiler take a
//    long time when compiling it with optimization. For us it's easy and fast
//    to convert this to 'if' statements because we know the pattern is common:
//      if (cond) {
//          lhs0 = then0;
//          lhs1 = then1;
//          lhs2 = then2;
//      } else {
//          lhs0 = else0;
//          lhs1 = else1;
//          lhs2 = else2;
//      }
//
//   For 1-bit signals, we consider strength reduced forms to be conditionals,
//   but only if we already encountered a true conditional we can merge with.
//   If we did, then act as if:
//      'lhs = cond & value' is actually 'lhs = cond ? value : 1'd0'
//      'lhs = cond' is actually 'lhs = cond ? 1'd1 : 1'd0'.
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3Global.h"
#include "V3MergeCond.h"
#include "V3Stats.h"
#include "V3Ast.h"

//######################################################################

class CheckMergeableVisitor final : public AstNVisitor {
private:
    // STATE
    bool m_mergeable
        = false;  // State tracking whether tree being processed is a mergeable condition

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    void clearMergeable(const AstNode* nodep, const char* reason) {
        UASSERT_OBJ(m_mergeable, nodep, "Should have short-circuited traversal");
        m_mergeable = false;
        UINFO(9, "Clearing mergeable on " << nodep << " due to " << reason << endl);
    }

    // VISITORS
    virtual void visit(AstNode* nodep) override {
        if (!m_mergeable) return;
        // Clear if node is impure
        if (!nodep->isPure()) {
            clearMergeable(nodep, "impure");
            return;
        }
        iterateChildrenConst(nodep);
    }
    virtual void visit(AstVarRef* nodep) override {
        if (!m_mergeable) return;
        // Clear if it's an LValue referencing a marked variable
        if (nodep->access().isWriteOrRW() && nodep->varp()->user1()) {
            clearMergeable(nodep, "might modify condition");
        }
    }

public:
    CheckMergeableVisitor() = default;

    // Return false if this node should not be merged at all because:
    // - It contains an impure expression
    // - It contains an LValue referencing the condition
    bool operator()(const AstNodeAssign* node) {
        m_mergeable = true;
        iterateChildrenConst(const_cast<AstNodeAssign*>(node));
        return m_mergeable;
    }
};

class MarkVarsVisitor final : public AstNVisitor {
private:
    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    // VISITORS
    virtual void visit(AstVarRef* nodep) override { nodep->varp()->user1(1); }
    virtual void visit(AstNode* nodep) override { iterateChildrenConst(nodep); }

public:
    // Remove marks from AstVars (clear user1)
    void clear() { AstNode::user1ClearTree(); }

    // Mark all AstVars referenced by setting user1
    void mark(AstNode* node) { iterate(node); }
};

class MergeCondVisitor final : public AstNVisitor {
private:
    // NODE STATE
    // AstVar::user1 -> Flag set for variables referenced by m_mgCondp
    AstUser1InUse m_user1InUse;

    // STATE
    VDouble0 m_statMerges;  // Statistic tracking
    VDouble0 m_statMergedItems;  // Statistic tracking
    VDouble0 m_statLongestList;  // Statistic tracking

    AstNode* m_mgFirstp = nullptr;  // First node in merged sequence
    AstNode* m_mgCondp = nullptr;  // The condition of the first node
    AstNode* m_mgLastp = nullptr;  // Last node in merged sequence
    const AstNode* m_mgNextp = nullptr;  // Next node in list being examined
    uint32_t m_listLenght = 0;  // Length of current list

    CheckMergeableVisitor m_checkMergeable;  // Sub visitor for encapsulation & speed
    MarkVarsVisitor m_markVars;  // Sub visitor for encapsulation & speed

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    // This function extracts the Cond node from the RHS, if there is one and
    // it is in a supported position, which are:
    // - RHS is the Cond
    // - RHS is And(Const, Cond). This And is inserted often by V3Clean.
    AstNodeCond* extractCond(AstNode* rhsp) {
        if (AstNodeCond* const condp = VN_CAST(rhsp, NodeCond)) {
            return condp;
        } else if (AstAnd* const andp = VN_CAST(rhsp, And)) {
            if (AstNodeCond* const condp = VN_CAST(andp->rhsp(), NodeCond)) {
                if (VN_IS(andp->lhsp(), Const)) return condp;
            }
        }
        return nullptr;
    }

    // Apply (_ & 1'b1). This is necessary because this pass is after V3Clean,
    // and sometimes we have an AstAnd with a 1-bit condition on one side, but
    // a more than 1-bit value on the other side, so we need to keep only the
    // LSB. Ideally we would only do this iff the node is known not to be 1-bit
    // wide, but working that out here is a bit difficult. As this masking is
    // rarely required (only when trying to merge a "cond & value" with an
    // earlier ternary), we will just always mask it for safety.
    AstNode* maskLsb(AstNode* nodep) {
        AstNode* const maskp = new AstConst(nodep->fileline(), AstConst::BitTrue());
        return new AstAnd(nodep->fileline(), nodep, maskp);
    }

    // Fold the RHS expression assuming the given condition state. Unlink bits
    // from the RHS which is only used once, and can be reused. What remains
    // of the RHS is expected to be deleted by the caller.
    AstNode* foldAndUnlink(AstNode* rhsp, bool condTrue) {
        if (rhsp->sameTree(m_mgCondp)) {
            return new AstConst(rhsp->fileline(), AstConst::BitTrue{}, condTrue);
        } else if (AstNodeCond* const condp = extractCond(rhsp)) {
            AstNode* const resp
                = condTrue ? condp->expr1p()->unlinkFrBack() : condp->expr2p()->unlinkFrBack();
            if (condp == rhsp) {  //
                return resp;
            }
            if (AstAnd* const andp = VN_CAST(rhsp, And)) {
                UASSERT_OBJ(andp->rhsp() == condp, rhsp, "Should not try to fold this");
                return new AstAnd(andp->fileline(), andp->lhsp()->cloneTree(false), resp);
            }
        } else if (AstAnd* const andp = VN_CAST(rhsp, And)) {
            if (andp->lhsp()->sameTree(m_mgCondp)) {
                return condTrue ? maskLsb(andp->rhsp()->unlinkFrBack())
                                : new AstConst(rhsp->fileline(), AstConst::BitFalse());
            } else {
                UASSERT_OBJ(andp->rhsp()->sameTree(m_mgCondp), rhsp,
                            "AstAnd doesn't hold condition expression");
                return condTrue ? maskLsb(andp->lhsp()->unlinkFrBack())
                                : new AstConst(rhsp->fileline(), AstConst::BitFalse());
            }
        }
        rhsp->v3fatalSrc("Don't know how to fold expression");
    }

    void mergeEnd() {
        UASSERT(m_mgFirstp, "mergeEnd without list");
        // Merge if list is longer than one node
        if (m_mgFirstp != m_mgLastp) {
            UINFO(6, "MergeCond - First: " << m_mgFirstp << " Last: " << m_mgLastp << endl);
            ++m_statMerges;
            if (m_listLenght > m_statLongestList) m_statLongestList = m_listLenght;

            // Create equivalent 'if' statement and insert it before the first node
            AstIf* const ifp
                = new AstIf(m_mgCondp->fileline(), m_mgCondp->unlinkFrBack(), nullptr, nullptr);
            m_mgFirstp->replaceWith(ifp);
            ifp->addNextHere(m_mgFirstp);
            // Unzip the list and insert under branches
            AstNode* nextp = m_mgFirstp;
            do {
                // Grab next pointer and unlink
                AstNode* const currp = nextp;
                nextp = currp != m_mgLastp ? currp->nextp() : nullptr;
                currp->unlinkFrBack();
                // Skip over comments
                if (VN_IS(currp, Comment)) {
                    VL_DO_DANGLING(currp->deleteTree(), currp);
                    continue;
                }
                // Count
                ++m_statMergedItems;
                // Unlink RHS and clone to get the 2 assignments (reusing currp)
                AstNodeAssign* const thenp = VN_CAST(currp, NodeAssign);
                AstNode* const rhsp = thenp->rhsp()->unlinkFrBack();
                AstNodeAssign* const elsep = thenp->cloneTree(false);
                // Construct the new RHSs and add to branches
                thenp->rhsp(foldAndUnlink(rhsp, true));
                elsep->rhsp(foldAndUnlink(rhsp, false));
                ifp->addIfsp(thenp);
                ifp->addElsesp(elsep);
                // Cleanup
                VL_DO_DANGLING(rhsp->deleteTree(), rhsp);
            } while (nextp);
        }
        // Reset state
        m_mgFirstp = nullptr;
        m_mgCondp = nullptr;
        m_mgLastp = nullptr;
        m_mgNextp = nullptr;
        m_markVars.clear();
    }

    void addToList(AstNode* nodep, AstNode* condp) {
        // Set up head of new list if node is first in list
        if (!m_mgFirstp) {
            UASSERT_OBJ(condp, nodep, "Cannot start new list without condition");
            m_mgFirstp = nodep;
            m_mgCondp = condp;
            m_listLenght = 0;
            m_markVars.mark(condp);
        }
        // Add node
        ++m_listLenght;
        // Track end of list
        m_mgLastp = nodep;
        // Set up expected next node in list. Skip over any comments, (inserted
        // by V3Order before always blocks)
        m_mgNextp = nodep->nextp();
        while (m_mgNextp && VN_IS(m_mgNextp, Comment)) { m_mgNextp = m_mgNextp->nextp(); }
        // If last under parent, done with current list
        if (!m_mgNextp) mergeEnd();
    }

    // VISITORS
    virtual void visit(AstNodeAssign* nodep) override {
        AstNode* const rhsp = nodep->rhsp();
        if (AstNodeCond* const condp = extractCond(rhsp)) {
            if (!m_checkMergeable(nodep)) {
                // Node not mergeable.
                // If no current list, then this node is just special, move on.
                if (!m_mgFirstp) return;
                // Otherwise finish current list
                mergeEnd();
                // Finishing the list might make the node mergeable again, e.g.
                // if the reason we could not merge was due to the condition
                // being assigned, so check again and stop only if still no.
                if (!m_checkMergeable(nodep)) return;
            }
            if (m_mgFirstp && (m_mgNextp != nodep || !condp->condp()->sameTree(m_mgCondp))) {
                // Node in different list, or has different condition.
                // Finish current list, addToList will start a new one.
                mergeEnd();
            }
            // Add current node
            addToList(nodep, condp->condp());
        } else if (m_mgFirstp) {
            // RHS is not a conditional, but we already started a list.
            // If it's a 1-bit signal, and a mergeable assignment, try reduced forms
            if (m_mgNextp == nodep && rhsp->widthMin() == 1 && m_checkMergeable(nodep)) {
                // Is it a 'lhs = cond & value' or 'lhs = value & cond'?
                if (AstAnd* const andp = VN_CAST(rhsp, And)) {
                    if (andp->lhsp()->sameTree(m_mgCondp) || andp->rhsp()->sameTree(m_mgCondp)) {
                        addToList(nodep, nullptr);
                        return;
                    }
                }
                // Is it simply 'lhs = cond'?
                if (rhsp->sameTree(m_mgCondp)) {
                    addToList(nodep, nullptr);
                    return;
                }
            }
            // Not added to list, so we are done with the current list
            mergeEnd();
        }
    }
    virtual void visit(AstComment*) override {}  // Skip over comments
    // For speed, only iterate what is necessary.
    virtual void visit(AstNetlist* nodep) override { iterateAndNextNull(nodep->modulesp()); }
    virtual void visit(AstNodeModule* nodep) override { iterateAndNextNull(nodep->stmtsp()); }
    virtual void visit(AstCFunc* nodep) override {
        iterateChildren(nodep);
        // Close list, if there is one at the end of the function
        if (m_mgFirstp) mergeEnd();
    }
    virtual void visit(AstNodeStmt* nodep) override { iterateChildren(nodep); }
    virtual void visit(AstNode* nodep) override {}

public:
    // CONSTRUCTORS
    explicit MergeCondVisitor(AstNetlist* nodep) {
        m_markVars.clear();
        iterate(nodep);
    }
    virtual ~MergeCondVisitor() override {
        V3Stats::addStat("Optimizations, MergeCond merges", m_statMerges);
        V3Stats::addStat("Optimizations, MergeCond merged items", m_statMergedItems);
        V3Stats::addStat("Optimizations, MergeCond longest merge", m_statLongestList);
    }
};

//######################################################################
// MergeConditionals class functions

void V3MergeCond::mergeAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    { MergeCondVisitor visitor(nodep); }
    V3Global::dumpCheckGlobalTree("merge_cond", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 6);
}
