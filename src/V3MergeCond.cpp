// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Merge branches/ternary ?:
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2022 by Wilson Snyder. This program is free software; you
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
//  Also merges consecutive AstNodeIf statements with the same condition.
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3Global.h"
#include "V3MergeCond.h"
#include "V3Stats.h"
#include "V3Ast.h"

//######################################################################

enum class Mergeable {
    YES,  // Tree can be merged
    NO_COND_ASSIGN,  // Tree cannot be merged because it contains an assignment to a condition
    NO_IMPURE  // Tree cannot be merged because it contains an impure node
};

class CheckMergeableVisitor final : public VNVisitor {
private:
    // STATE
    bool m_condAssign = false;  // Does this tree contain an assignment to a condition variable??
    bool m_impure = false;  // Does this tree contain an impure node?

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    // VISITORS
    virtual void visit(AstNode* nodep) override {
        if (m_impure) return;
        // Clear if node is impure
        if (!nodep->isPure()) {
            UINFO(9, "Not mergeable due to impure node" << nodep << endl);
            m_impure = true;
            return;
        }
        iterateChildrenConst(nodep);
    }
    virtual void visit(AstVarRef* nodep) override {
        if (m_impure || m_condAssign) return;
        // Clear if it's an LValue referencing a marked variable
        if (nodep->access().isWriteOrRW() && nodep->varp()->user1()) {
            UINFO(9, "Not mergeable due assignment to condition" << nodep << endl);
            m_condAssign = true;
        }
    }

public:
    CheckMergeableVisitor() = default;

    // Return false if this node should not be merged at all because:
    // - It contains an impure expression
    // - It contains an LValue referencing the condition
    Mergeable operator()(const AstNode* node) {
        m_condAssign = false;
        m_impure = false;
        iterateChildrenConst(const_cast<AstNode*>(node));
        if (m_impure) {  // Impure is stronger than cond assign
            return Mergeable::NO_IMPURE;
        } else if (m_condAssign) {
            return Mergeable::NO_COND_ASSIGN;
        } else {
            return Mergeable::YES;
        }
    }
};

class MergeCondVisitor final : public VNVisitor {
private:
    // NODE STATE
    // AstVar::user1        -> Flag set for variables referenced by m_mgCondp
    // AstNode::user2       -> Flag marking node as included in merge because cheap to duplicate
    const VNUser1InUse m_user1InUse;
    const VNUser2InUse m_user2InUse;

    // STATE
    VDouble0 m_statMerges;  // Statistic tracking
    VDouble0 m_statMergedItems;  // Statistic tracking
    VDouble0 m_statLongestList;  // Statistic tracking

    AstNode* m_mgFirstp = nullptr;  // First node in merged sequence
    AstNode* m_mgCondp = nullptr;  // The condition of the first node
    const AstNode* m_mgLastp = nullptr;  // Last node in merged sequence
    const AstNode* m_mgNextp = nullptr;  // Next node in list being examined
    uint32_t m_listLenght = 0;  // Length of current list

    CheckMergeableVisitor m_checkMergeable;  // Sub visitor for encapsulation & speed

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    // This function extracts the Cond node from the RHS, if there is one and
    // it is in a supported position, which are:
    // - RHS is the Cond
    // - RHS is And(Const, Cond). This And is inserted often by V3Clean.
    static AstNodeCond* extractCond(AstNode* rhsp) {
        if (AstNodeCond* const condp = VN_CAST(rhsp, NodeCond)) {
            return condp;
        } else if (const AstAnd* const andp = VN_CAST(rhsp, And)) {
            if (AstNodeCond* const condp = VN_CAST(andp->rhsp(), NodeCond)) {
                if (VN_IS(andp->lhsp(), Const)) return condp;
            }
        }
        return nullptr;
    }

    // Predicate to check if an expression yields only 0 or 1 (i.e.: a 1-bit value)
    static bool yieldsOneOrZero(const AstNode* nodep) {
        UASSERT_OBJ(!nodep->isWide(), nodep, "Cannot handle wide nodes");
        if (const AstConst* const constp = VN_CAST(nodep, Const)) {
            return constp->num().toUQuad() <= 1;
        }
        if (const AstVarRef* const vrefp = VN_CAST(nodep, VarRef)) {
            const AstVar* const varp = vrefp->varp();
            return varp->widthMin() == 1 && !varp->dtypep()->isSigned();
        }
        if (const AstShiftR* const shiftp = VN_CAST(nodep, ShiftR)) {
            // Shift right by width - 1 or more
            if (const AstConst* const constp = VN_CAST(shiftp->rhsp(), Const)) {
                const AstVarRef* const vrefp = VN_CAST(shiftp->lhsp(), VarRef);
                const int width = vrefp && !vrefp->varp()->dtypep()->isSigned()
                                      ? vrefp->varp()->widthMin()
                                      : shiftp->width();
                if (constp->toSInt() >= width - 1) return true;
            }
            return false;
        }
        if (VN_IS(nodep, Eq) || VN_IS(nodep, Neq) || VN_IS(nodep, Lt) || VN_IS(nodep, Lte)
            || VN_IS(nodep, Gt) || VN_IS(nodep, Gte)) {
            return true;
        }
        if (const AstNodeBiop* const biopp = VN_CAST(nodep, NodeBiop)) {
            if (VN_IS(nodep, And))
                return yieldsOneOrZero(biopp->lhsp()) || yieldsOneOrZero(biopp->rhsp());
            if (VN_IS(nodep, Or) || VN_IS(nodep, Xor))
                return yieldsOneOrZero(biopp->lhsp()) && yieldsOneOrZero(biopp->rhsp());
            return false;
        }
        if (const AstNodeCond* const condp = VN_CAST(nodep, NodeCond)) {
            return yieldsOneOrZero(condp->expr1p()) && yieldsOneOrZero(condp->expr2p());
        }
        if (const AstCCast* const castp = VN_CAST(nodep, CCast)) {
            // Cast never sign extends
            return yieldsOneOrZero(castp->lhsp());
        }
        return false;
    }

    // Apply (1'b1 & _) cleaning mask if necessary. This is required because this pass is after
    // V3Clean, and sometimes we have an AstAnd with a 1-bit condition on one side, but a more
    // than 1-bit value on the other side, so we need to keep only the LSB.
    static AstNode* maskLsb(AstNode* nodep) {
        if (yieldsOneOrZero(nodep)) return nodep;
        // Otherwise apply masking
        AstNode* const maskp = new AstConst(nodep->fileline(), AstConst::BitTrue());
        // Mask on left, as conventional
        return new AstAnd(nodep->fileline(), maskp, nodep);
    }

    // Fold the RHS expression assuming the given condition state. Unlink bits
    // from the RHS which is only used once, and can be reused. What remains
    // of the RHS is expected to be deleted by the caller.
    AstNode* foldAndUnlink(AstNode* rhsp, bool condTrue) {
        if (rhsp->sameTree(m_mgCondp)) {
            return new AstConst(rhsp->fileline(), AstConst::BitTrue{}, condTrue);
        } else if (const AstNodeCond* const condp = extractCond(rhsp)) {
            AstNode* const resp
                = condTrue ? condp->expr1p()->unlinkFrBack() : condp->expr2p()->unlinkFrBack();
            if (condp == rhsp) {  //
                return resp;
            }
            if (const AstAnd* const andp = VN_CAST(rhsp, And)) {
                UASSERT_OBJ(andp->rhsp() == condp, rhsp, "Should not try to fold this");
                return new AstAnd{andp->fileline(), andp->lhsp()->cloneTree(false), resp};
            }
        } else if (const AstAnd* const andp = VN_CAST(rhsp, And)) {
            if (andp->lhsp()->sameTree(m_mgCondp)) {
                return condTrue ? maskLsb(andp->rhsp()->unlinkFrBack())
                                : new AstConst{rhsp->fileline(), AstConst::BitFalse()};
            } else {
                UASSERT_OBJ(andp->rhsp()->sameTree(m_mgCondp), rhsp,
                            "AstAnd doesn't hold condition expression");
                return condTrue ? maskLsb(andp->lhsp()->unlinkFrBack())
                                : new AstConst{rhsp->fileline(), AstConst::BitFalse()};
            }
        } else if (VN_IS(rhsp, WordSel) || VN_IS(rhsp, VarRef) || VN_IS(rhsp, Const)) {
            return rhsp->cloneTree(false);
        }
        rhsp->dumpTree("Don't know how to fold expression: ");
        rhsp->v3fatalSrc("Don't know how to fold expression");
    }

    void mergeEnd(int lineno) {
        UASSERT(m_mgFirstp, "mergeEnd without list " << lineno);
        // We might want to recursively merge an AstIf. We stash it in this variable.
        const AstNodeIf* recursivep = nullptr;
        // Drop leading cheap nodes. These were only added in the hope of finding
        // an earlier reduced form, but we failed to do so.
        while (m_mgFirstp->user2() && m_mgFirstp != m_mgLastp) {
            const AstNode* const backp = m_mgFirstp;
            m_mgFirstp = m_mgFirstp->nextp();
            --m_listLenght;
            UASSERT_OBJ(m_mgFirstp && m_mgFirstp->backp() == backp, m_mgLastp,
                        "The list should have a non-cheap element");
        }
        // Drop trailing cheap nodes. These were only added in the hope of finding
        // a later conditional to merge, but we failed to do so.
        while (m_mgLastp->user2() && m_mgFirstp != m_mgLastp) {
            const AstNode* const nextp = m_mgLastp;
            m_mgLastp = m_mgLastp->backp();
            --m_listLenght;
            UASSERT_OBJ(m_mgLastp && m_mgLastp->nextp() == nextp, m_mgFirstp,
                        "Cheap assignment should not be at the front of the list");
        }
        // Merge if list is longer than one node
        if (m_mgFirstp != m_mgLastp) {
            UINFO(6, "MergeCond - First: " << m_mgFirstp << " Last: " << m_mgLastp << endl);
            ++m_statMerges;
            if (m_listLenght > m_statLongestList) m_statLongestList = m_listLenght;

            // We need a copy of the condition in the new equivalent 'if' statement,
            // and we also need to keep track of it for comparisons later.
            m_mgCondp = m_mgCondp->cloneTree(false);
            // Create equivalent 'if' statement and insert it before the first node
            AstIf* const resultp = new AstIf(m_mgCondp->fileline(), m_mgCondp, nullptr, nullptr);
            m_mgFirstp->addHereThisAsNext(resultp);
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
                if (AstNodeAssign* const assignp = VN_CAST(currp, NodeAssign)) {
                    // Unlink RHS and clone to get the 2 assignments (reusing assignp)
                    AstNode* const rhsp = assignp->rhsp()->unlinkFrBack();
                    AstNodeAssign* const thenp = assignp;
                    AstNodeAssign* const elsep = assignp->cloneTree(false);
                    // Construct the new RHSs and add to branches
                    thenp->rhsp(foldAndUnlink(rhsp, true));
                    elsep->rhsp(foldAndUnlink(rhsp, false));
                    resultp->addIfsp(thenp);
                    resultp->addElsesp(elsep);
                    // Cleanup
                    VL_DO_DANGLING(rhsp->deleteTree(), rhsp);
                } else {
                    AstNodeIf* const ifp = VN_AS(currp, NodeIf);
                    UASSERT_OBJ(ifp, currp, "Must be AstNodeIf");
                    // Move branch contents under new if
                    if (AstNode* const listp = ifp->ifsp()) {
                        resultp->addIfsp(listp->unlinkFrBackWithNext());
                    }
                    if (AstNode* const listp = ifp->elsesp()) {
                        resultp->addElsesp(listp->unlinkFrBackWithNext());
                    }
                    // Cleanup
                    VL_DO_DANGLING(ifp->deleteTree(), ifp);
                }
            } while (nextp);
            // Recursively merge the resulting AstIf
            recursivep = resultp;
        } else if (const AstNodeIf* const ifp = VN_CAST(m_mgFirstp, NodeIf)) {
            // There was nothing to merge this AstNodeIf with, but try to merge it's branches
            recursivep = ifp;
        }
        // Reset state
        m_mgFirstp = nullptr;
        m_mgCondp = nullptr;
        m_mgLastp = nullptr;
        m_mgNextp = nullptr;
        AstNode::user1ClearTree();  // Clear marked variables
        AstNode::user2ClearTree();
        // Merge recursively within the branches
        if (recursivep) {
            iterateAndNextNull(recursivep->ifsp());
            // Close list, if there is one at the end of the then branch
            if (m_mgFirstp) mergeEnd(__LINE__);
            iterateAndNextNull(recursivep->elsesp());
            // Close list, if there is one at the end of the else branch
            if (m_mgFirstp) mergeEnd(__LINE__);
        }
    }

    // Check if the node can be simplified if included under the if
    bool isSimplifiableNode(AstNode* nodep) {
        UASSERT_OBJ(m_mgFirstp, nodep, "Cannot check with empty list");
        if (const AstNodeAssign* const assignp = VN_CAST(nodep, NodeAssign)) {
            // If it's an assignment to a 1-bit signal, try reduced forms
            if (assignp->lhsp()->widthMin() == 1) {
                // Is it a 'lhs = cond & value' or 'lhs = value & cond'?
                if (const AstAnd* const andp = VN_CAST(assignp->rhsp(), And)) {
                    if (andp->lhsp()->sameTree(m_mgCondp) || andp->rhsp()->sameTree(m_mgCondp)) {
                        return true;
                    }
                }
                // Is it 'lhs = cond'?
                if (assignp->rhsp()->sameTree(m_mgCondp)) return true;
            }
        }
        return false;
    }

    // Check if this node is cheap enough that duplicating it in two branches of an
    // AstIf and is hence not likely to cause a performance degradation if doing so.
    bool isCheapNode(AstNode* nodep) const {
        if (VN_IS(nodep, Comment)) return true;
        if (const AstNodeAssign* const assignp = VN_CAST(nodep, NodeAssign)) {
            // Check LHS
            AstNode* lhsp = assignp->lhsp();
            while (AstWordSel* const wselp = VN_CAST(lhsp, WordSel)) {
                // WordSel index is not constant, so might be expensive
                if (!VN_IS(wselp->bitp(), Const)) return false;
                lhsp = wselp->fromp();
            }
            // LHS is not a VarRef, so might be expensive
            if (!VN_IS(lhsp, VarRef)) return false;

            // Check RHS
            AstNode* rhsp = assignp->rhsp();
            while (AstWordSel* const wselp = VN_CAST(rhsp, WordSel)) {
                // WordSel index is not constant, so might be expensive
                if (!VN_IS(wselp->bitp(), Const)) return false;
                rhsp = wselp->fromp();
            }
            // RHS is not a VarRef or Constant so might be expensive
            if (!VN_IS(rhsp, VarRef) && !VN_IS(rhsp, Const)) return false;

            // Otherwise it is a cheap assignment
            return true;
        }
        return false;
    }

    void addToList(AstNode* nodep, AstNode* condp, int line) {
        // Set up head of new list if node is first in list
        if (!m_mgFirstp) {
            UASSERT_OBJ(condp, nodep, "Cannot start new list without condition " << line);
            m_mgFirstp = nodep;
            m_mgCondp = condp;
            m_listLenght = 0;
            // Mark variable references in the condition
            condp->foreach<AstVarRef>([](const AstVarRef* nodep) { nodep->varp()->user1(1); });
            // Add any preceding nodes to the list that would allow us to extend the merge range
            for (;;) {
                AstNode* const backp = m_mgFirstp->backp();
                if (!backp || backp->nextp() != m_mgFirstp) break;  // Don't move up the tree
                if (m_checkMergeable(backp) != Mergeable::YES) break;
                if (isSimplifiableNode(backp)) {
                    ++m_listLenght;
                    m_mgFirstp = backp;
                } else if (isCheapNode(backp)) {
                    backp->user2(1);
                    ++m_listLenght;
                    m_mgFirstp = backp;
                } else {
                    break;
                }
            }
        }
        // Add node
        ++m_listLenght;
        // Track end of list
        m_mgLastp = nodep;
        // Set up expected next node in list.
        m_mgNextp = nodep->nextp();
        // If last under parent, done with current list
        if (!m_mgNextp) mergeEnd(__LINE__);
    }

    // If this node is the next expected node and is helpful to add to the list, do so,
    // otherwise end the current merge. Return ture if added, false if ended merge.
    bool addIfHelpfulElseEndMerge(AstNode* nodep) {
        UASSERT_OBJ(m_mgFirstp, nodep, "List must be open");
        if (m_mgNextp == nodep) {
            if (isSimplifiableNode(nodep)) {
                addToList(nodep, nullptr, __LINE__);
                return true;
            }
            if (isCheapNode(nodep)) {
                nodep->user2(1);
                addToList(nodep, nullptr, __LINE__);
                return true;
            }
        }
        // Not added to list, so we are done with the current list
        mergeEnd(__LINE__);
        return false;
    }

    bool checkOrMakeMergeable(AstNode* nodep) {
        const Mergeable reason = m_checkMergeable(nodep);
        // If meregeable, we are done
        if (reason == Mergeable::YES) return true;
        // Node not mergeable.
        // If no current list, then this node is just special, move on.
        if (!m_mgFirstp) return false;
        // Otherwise finish current list
        mergeEnd(__LINE__);
        // If a tree was not mergeable due to an assignment to a condition,
        // then finishing the current list makes it mergeable again.
        return reason == Mergeable::NO_COND_ASSIGN;
    }

    void mergeEndIfIncompatible(AstNode* nodep, AstNode* condp) {
        if (m_mgFirstp && (m_mgNextp != nodep || !condp->sameTree(m_mgCondp))) {
            // Node in different list, or has different condition. Finish current list.
            mergeEnd(__LINE__);
        }
    }

    // VISITORS
    virtual void visit(AstNodeAssign* nodep) override {
        AstNode* const rhsp = nodep->rhsp();
        if (const AstNodeCond* const condp = extractCond(rhsp)) {
            // Check if mergeable
            if (!checkOrMakeMergeable(nodep)) return;
            // Close potentially incompatible pending merge
            mergeEndIfIncompatible(nodep, condp->condp());
            // Add current node
            addToList(nodep, condp->condp(), __LINE__);
        } else if (m_mgFirstp) {
            addIfHelpfulElseEndMerge(nodep);
        }
    }

    virtual void visit(AstNodeIf* nodep) override {
        // Check if mergeable
        if (!checkOrMakeMergeable(nodep)) {
            // If not mergeable, try to merge the branches
            iterateAndNextNull(nodep->ifsp());
            iterateAndNextNull(nodep->elsesp());
            return;
        }
        // Close potentially incompatible pending merge
        mergeEndIfIncompatible(nodep, nodep->condp());
        // Add current node
        addToList(nodep, nodep->condp(), __LINE__);
    }

    // For speed, only iterate what is necessary.
    virtual void visit(AstNetlist* nodep) override { iterateAndNextNull(nodep->modulesp()); }
    virtual void visit(AstNodeModule* nodep) override { iterateAndNextNull(nodep->stmtsp()); }
    virtual void visit(AstCFunc* nodep) override {
        iterateChildren(nodep);
        // Close list, if there is one at the end of the function
        if (m_mgFirstp) mergeEnd(__LINE__);
    }
    virtual void visit(AstNodeStmt* nodep) override {
        if (m_mgFirstp && addIfHelpfulElseEndMerge(nodep)) return;
        iterateChildren(nodep);
    }
    virtual void visit(AstNode* nodep) override {}

public:
    // CONSTRUCTORS
    explicit MergeCondVisitor(AstNetlist* nodep) { iterate(nodep); }
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
    { MergeCondVisitor{nodep}; }
    V3Global::dumpCheckGlobalTree("merge_cond", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 6);
}
