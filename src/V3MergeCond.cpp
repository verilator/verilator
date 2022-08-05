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
//  Because this optimization has notable performance impact, we go further
//  and perform code motion to try to move mergeable conditionals next to each
//  other, which in turn enable us to merge more conditionals. To do this, we
//  perform an analysis pass, followed by an optimization pass on the whole
//  AstCFunc we are optimizing.
//
//  The analysis pass gathers, for each statement in the tree, the information
//  relevant for determining whether two statements can be swapped, and some
//  other additional information that is useful during optimization.
//
//  The optimization pass tries to move conditionals near each other, first by
//  trying to move a conditional node backwards in the list, so it becomes the
//  direct successor of another earlier conditional with the same condition.
//  If this is not possible due to variable interference, then we additionally
//  try to pull earlier conditionals with the same condition closer forward to
//  be the immediate predecessor of the conditional node. We limit maximum
//  distance a node can travel to an empirically chosen but otherwise arbitrary
//  constant. This limits worst case complexity to be O(n) rather than O(n^2).
//  The worst case complexity manifests when N/2 conditionals, all with unique
//  conditions are succeeded by N/2 conditionals with the same unique
//  conditions, such that each unique condition is used by exactly 2
//  conditionals. In this case N/2 all nodes need to travel approx N/2 distance.
//  Limiting the distance bounds the latter, hence limiting complexity.
//
//  Once the analysis and optimization passes have been applied to the whole
//  function, any merged conditionals will then undergo the same analysis,
//  optimization, and merging again in their individual branches.
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3MergeCond.h"

#include "V3Ast.h"
#include "V3AstUserAllocator.h"
#include "V3DupFinder.h"
#include "V3Global.h"
#include "V3Hasher.h"
#include "V3Stats.h"

#include <queue>
#include <set>

namespace {

//######################################################################
// Utilities

// This function extracts the Cond node from the RHS of an assignment,
// if there is one and it is in a supported position, which are:
// - RHS is the Cond
// - RHS is And(Const, Cond). This And is inserted often by V3Clean.
AstNodeCond* extractCondFromRhs(AstNode* rhsp) {
    if (AstNodeCond* const condp = VN_CAST(rhsp, NodeCond)) {
        return condp;
    } else if (const AstAnd* const andp = VN_CAST(rhsp, And)) {
        if (AstNodeCond* const condp = VN_CAST(andp->rhsp(), NodeCond)) {
            if (VN_IS(andp->lhsp(), Const)) return condp;
        }
    }
    return nullptr;
}

// Predicate to check if two sets are disjoint. This is stable, as we only need
// to determine if the sets contain a shared element, which is a boolean
// property. It is also efficient as we use sorted sets, and therefore can
// enumerate elements in order (what the ordering is, is unimportant), meaning
// the worst case complexity is O(size of smaller set).
bool areDisjoint(const std::set<const AstVar*>& a, const std::set<const AstVar*>& b) {
    if (a.empty() || b.empty()) return true;
    const auto endA = a.end();
    const auto endB = b.end();
    auto itA = a.begin();
    auto itB = b.begin();
    while (true) {
        if (*itA == *itB) return false;
        if (std::less<const AstVar*>{}(*itA, *itB)) {
            itA = std::lower_bound(++itA, endA, *itB);
            if (itA == endA) return true;
        } else {
            itB = std::lower_bound(++itB, endB, *itA);
            if (itB == endB) return true;
        }
    }
}

//######################################################################
// Structure containing information required for code motion/merging

struct StmtProperties {
    AstNode* m_condp = nullptr;  // The condition expression, if a conditional node
    std::set<const AstVar*> m_rdVars;  // Variables read by this statement
    std::set<const AstVar*> m_wrVars;  // Variables writen by this statement
    bool m_isFence = false;  // Nothing should move across this statement, nor should it be merged
    AstNodeStmt* m_prevWithSameCondp = nullptr;  // Previous node in same list, with same condition
    bool writesConditionVar() const {
        // This relies on MarkVarsVisitor having been called on the condition node
        for (const AstVar* const varp : m_wrVars) {
            if (varp->user1()) return true;
        }
        return false;
    }
};

// We store the statement properties in user3 via AstUser3Allocator
using StmtPropertiesAllocator = AstUser3Allocator<AstNodeStmt, StmtProperties>;

//######################################################################
// Code motion analysis and implementation

// Pure analysis visitor that build the StmtProperties for each statement in the given
// AstNode list (following AstNode::nextp())
class CodeMotionAnalysisVisitor final : public VNVisitor {
    // NODE STATE
    // AstNodeStmt::user3   -> StmtProperties (accessed via m_stmtProperties, managed externally,
    //                         see MergeCondVisitor::process)
    // AstNode::user4       -> Used by V3Hasher
    // AstNode::user5       -> AstNode*: Set on a condition node, points to the last conditional
    //                         with that condition so far encountered in the same AstNode list

    VNUser5InUse m_user5InUse;

    StmtPropertiesAllocator& m_stmtProperties;

    // MEMBERS
    V3Hasher m_hasher;  // Used by V3DupFinder
    // Stack of a V3DupFinder used for finding identical condition expressions within one
    // statement list.
    std::vector<V3DupFinder> m_stack;
    StmtProperties* m_propsp = nullptr;  // StmtProperties structure of current AstNodeStmt

    // Extract condition expression from a megeable conditional statement, if any
    static AstNode* extractCondition(const AstNodeStmt* nodep) {
        AstNode* conditionp = nullptr;
        if (const AstNodeAssign* const assignp = VN_CAST(nodep, NodeAssign)) {
            if (AstNodeCond* const conditionalp = extractCondFromRhs(assignp->rhsp())) {
                conditionp = conditionalp->condp();
            }
        } else if (const AstNodeIf* const ifp = VN_CAST(nodep, NodeIf)) {
            conditionp = ifp->condp();
        }
        while (AstCCast* const castp = VN_CAST(conditionp, CCast)) conditionp = castp->lhsp();
        return conditionp;
    }

    void analyzeStmt(AstNodeStmt* nodep, bool tryCondMatch) {
        VL_RESTORER(m_propsp);
        // Keep hold of props of enclosing statement
        StmtProperties* const outerPropsp = m_propsp;
        // Grab the props of this statement
        m_propsp = &m_stmtProperties(nodep);

        // Extract condition from statement
        if (AstNode* const condp = extractCondition(nodep)) {
            // Remember condition node. We always need this as it is used in the later
            // traversal.
            m_propsp->m_condp = condp;
            // If this is a conditional statement, try to find an earlier one with the same
            // condition in the same list (unless we have been told not to bother because we know
            // this node is in a singleton list).
            if (tryCondMatch) {
                // Grab the duplicate finder of this list
                V3DupFinder& dupFinder = m_stack.back();
                // Find a duplicate condition
                const V3DupFinder::iterator& dit = dupFinder.findDuplicate(condp);
                if (dit == dupFinder.end()) {
                    // First time seeing this condition in the current list
                    dupFinder.insert(condp);
                    // Remember last statement with this condition (which is this statement)
                    condp->user5p(nodep);
                } else {
                    // Seen a conditional with the same condition earlier in the current list
                    AstNode* const firstp = dit->second;
                    // Add to properties for easy retrieval during optimization
                    m_propsp->m_prevWithSameCondp = static_cast<AstNodeStmt*>(firstp->user5p());
                    // Remember last statement with this condition (which is this statement)
                    firstp->user5p(nodep);
                }
            }
        }

        // Analyse this statement
        analyzeNode(nodep);

        // If there is an enclosing statement, propagate properties upwards
        if (outerPropsp) {
            // Add all rd/wr vars to outer statement
            outerPropsp->m_rdVars.insert(m_propsp->m_rdVars.cbegin(), m_propsp->m_rdVars.cend());
            outerPropsp->m_wrVars.insert(m_propsp->m_wrVars.cbegin(), m_propsp->m_wrVars.cend());
            // If this statement is impure, the enclosing statement is also impure
            if (m_propsp->m_isFence) outerPropsp->m_isFence = true;
        }
    }

    void analyzeVarRef(AstVarRef* nodep) {
        const VAccess access = nodep->access();
        AstVar* const varp = nodep->varp();
        // Gather read and written variables
        if (access.isReadOrRW()) m_propsp->m_rdVars.insert(varp);
        if (access.isWriteOrRW()) m_propsp->m_wrVars.insert(varp);
    }

    void analyzeNode(AstNode* nodep) {
        // If an impure node under a statement, mark that statement as impure
        if (m_propsp && !nodep->isPure()) m_propsp->m_isFence = true;
        // Analyze children
        iterateChildrenConst(nodep);
    }

    // VISITORS
    void visit(AstNode* nodep) override {
        // Push a new stack entry at the start of a list, but only if the list is not a
        // single element (this saves a lot of allocations in expressions)
        bool singletonListStart = false;
        if (nodep->backp()->nextp() != nodep) {  // If at head of list
            singletonListStart = nodep->nextp() == nullptr;
            if (!singletonListStart) m_stack.emplace_back(m_hasher);
        }

        // Analyse node
        if (AstNodeStmt* const stmtp = VN_CAST(nodep, NodeStmt)) {
            analyzeStmt(stmtp, /*tryCondMatch:*/ !singletonListStart);
        } else if (AstVarRef* const vrefp = VN_CAST(nodep, VarRef)) {
            analyzeVarRef(vrefp);
        } else {
            analyzeNode(nodep);
        }

        // Pop the stack at the end of a list
        if (!singletonListStart && !nodep->nextp()) m_stack.pop_back();
    }

    // CONSTRUCTOR
    CodeMotionAnalysisVisitor(AstNode* nodep, StmtPropertiesAllocator& stmtProperties)
        : m_stmtProperties(stmtProperties) {
        iterateAndNextConstNull(nodep);
    }

public:
    // Analyse the statement list starting at nodep, filling in stmtProperties.
    static void analyze(AstNode* nodep, StmtPropertiesAllocator& stmtProperties) {
        CodeMotionAnalysisVisitor{nodep, stmtProperties};
    }
};

class CodeMotionOptimizeVisitor final : public VNVisitor {
    // Do not move a node more than this many statements.
    // This bounds complexity at O(N), rather than O(N^2).
    static constexpr unsigned MAX_DISTANCE = 500;

    // NODE STATE
    // AstNodeStmt::user3   -> StmtProperties (accessed via m_stmtProperties, managed externally,
    //                         see MergeCondVisitor::process)
    // AstNodeStmt::user4   -> bool: Already processed this node

    VNUser4InUse m_user4InUse;

    const StmtPropertiesAllocator& m_stmtProperties;

    // MEMBERS

    // Predicate that checks if the order of two statements can be swapped
    bool areSwappable(const AstNodeStmt* ap, const AstNodeStmt* bp) const {
        const StmtProperties& aProps = m_stmtProperties(ap);
        const StmtProperties& bProps = m_stmtProperties(bp);
        // Don't move across fences
        if (aProps.m_isFence) return false;
        if (bProps.m_isFence) return false;
        // If either statement writes a variable that the other reads, they are not swappable
        if (!areDisjoint(aProps.m_rdVars, bProps.m_wrVars)) return false;
        if (!areDisjoint(bProps.m_rdVars, aProps.m_wrVars)) return false;
        // If they both write to the same variable, they are not swappable
        if (!areDisjoint(aProps.m_wrVars, bProps.m_wrVars)) return false;
        // Otherwise good to go
        return true;
    }

    // VISITORS
    void visit(AstNodeStmt* nodep) override {
        // Process only on first encounter
        if (nodep->user4SetOnce()) return;
        // First re-order children
        iterateChildren(nodep);
        // Grab hold of previous node with same condition
        AstNodeStmt* prevp = m_stmtProperties(nodep).m_prevWithSameCondp;
        // If no previous node with same condition, we are done
        if (!prevp) return;
#ifdef VL_DEBUG
        {  // Sanity check, only in debug build, otherwise expensive
            const AstNode* currp = prevp;
            while (currp && currp != nodep) currp = currp->nextp();
            UASSERT_OBJ(currp, nodep, "Predecessor not in same list as " << currp);
        }
#endif
        // Otherwise try to move this node backwards, as close as we can to the previous node
        // with the same condition
        if (AstNodeStmt* predp = VN_CAST(nodep->backp(), NodeStmt)) {
            // 'predp' is the newly computed predecessor node of 'nodep', which is initially
            // (without movement) the 'backp' of the node.
            for (unsigned i = MAX_DISTANCE; i; --i) {
                // If the predecessor is the previous node with the same condition, job done
                if (predp == prevp) break;
                // Don't move past a non-statement (e.g.: AstVar), or end of list
                AstNodeStmt* const backp = VN_CAST(predp->backp(), NodeStmt);
                if (!backp) break;
                // Don't swap statements if doing so would change program semantics
                if (!areSwappable(predp, nodep)) break;
                // Otherwise move 'nodep' back
                predp = backp;
            }

            // If we decided that 'nodep' should be moved back
            if (nodep->backp() != predp) {
                // Move the current node to directly follow the computed predecessor
                nodep->unlinkFrBack();
                predp->addNextHere(nodep);
                // If the predecessor is the previous node with the same condition, job done
                if (predp == prevp) return;
            }
        }
        // If we reach here, it means we were unable to move the current node all the way back
        // such that it immediately follows the previous statement with the same condition. Now
        // try to move all previous statements with the same condition forward, in the hope of
        // compacting the list further.
        for (AstNodeStmt* currp = nodep; prevp;
             currp = prevp, prevp = m_stmtProperties(currp).m_prevWithSameCondp) {
            // Move prevp (previous statement with same condition) towards currp
            if (AstNodeStmt* succp = VN_CAST(prevp->nextp(), NodeStmt)) {
                // 'succp' is the newly computed successor node of 'prevp', which is initially
                // (without movement) the 'nextp' of the node.
                for (unsigned i = MAX_DISTANCE; --i;) {
                    // If the successor of the previous statement with same condition is the
                    // target node, we are done with this predecessor
                    if (succp == currp) break;
                    // Don't move past a non-statement (e.g.: AstVar), or end of list
                    AstNodeStmt* const nextp = VN_CAST(succp->nextp(), NodeStmt);
                    if (!nextp) break;
                    // Don't swap statements if doing so would change program semantics
                    if (!areSwappable(prevp, succp)) break;
                    // Otherwise move further forward
                    succp = nextp;
                }

                // If we decided that 'prevp' should be moved forward
                if (prevp->nextp() != succp) {
                    // Move the current node to directly before the computed successor
                    prevp->unlinkFrBack();
                    succp->addHereThisAsNext(prevp);
                }
            }
        }
    }

    void visit(AstNode* nodep) override {}  // Ignore all non-statements

    // CONSTRUCTOR
    CodeMotionOptimizeVisitor(AstNode* nodep, const StmtPropertiesAllocator& stmtProperties)
        : m_stmtProperties(stmtProperties) {
        // We assert the given node is at the head of the list otherwise we might move a node
        // before the given node. This is easy to fix in the above iteration with a check on a
        // boundary node we should not move past, if we ever need to do so.
        // Note: we will do iterateAndNextNull which requires nodep->backp() != nullptr anyway
        UASSERT_OBJ(nodep->backp()->nextp() != nodep, nodep, "Must be at head of list");
        // Optimize the list
        iterateAndNextNull(nodep);
    }

public:
    // Given an AstNode list (held via AstNode::nextp()), move conditional statements as close
    // together as possible
    static AstNode* optimize(AstNode* nodep, const StmtPropertiesAllocator& stmtProperties) {
        { CodeMotionOptimizeVisitor{nodep, stmtProperties}; }
        // It is possible for the head of the list to be moved later such that it is no longer
        // in head position. If so, rewind the list and return the new head.
        while (nodep->backp()->nextp() == nodep) nodep = nodep->backp();
        return nodep;
    }
};

//######################################################################
// Conditional merging

class MergeCondVisitor final : public VNVisitor {
private:
    // NODE STATE
    // AstVar::user1        -> bool: Set for variables referenced by m_mgCondp
    //                         (Only below MergeCondVisitor::process).
    // AstNode::user2       -> bool: Marking node as included in merge because cheap to
    //                         duplicate
    //                         (Only below MergeCondVisitor::process).
    // AstNodeStmt::user3   -> StmtProperties
    //                         (Only below MergeCondVisitor::process).
    // AstNode::user4       -> See CodeMotionAnalysisVisitor/CodeMotionOptimizeVisitor
    // AstNode::user5       -> See CodeMotionAnalysisVisitor

    // STATE
    VDouble0 m_statMerges;  // Statistic tracking
    VDouble0 m_statMergedItems;  // Statistic tracking
    VDouble0 m_statLongestList;  // Statistic tracking

    AstNode* m_mgFirstp = nullptr;  // First node in merged sequence
    AstNode* m_mgCondp = nullptr;  // The condition of the first node
    const AstNode* m_mgLastp = nullptr;  // Last node in merged sequence
    const AstNode* m_mgNextp = nullptr;  // Next node in list being examined
    uint32_t m_listLenght = 0;  // Length of current list

    std::queue<AstNode*>* m_workQueuep = nullptr;  // Node lists (via AstNode::nextp()) to merge
    // Statement properties for code motion and merging
    StmtPropertiesAllocator* m_stmtPropertiesp = nullptr;

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    // Function that processes a whole sub-tree
    void process(AstNode* nodep) {
        // Set up work queue
        std::queue<AstNode*> workQueue;
        m_workQueuep = &workQueue;
        m_workQueuep->push(nodep);

        do {
            // Set up user* for this iteration
            const VNUser1InUse user1InUse;
            const VNUser2InUse user2InUse;
            const VNUser3InUse user3InUse;
            // Statement properties only preserved for this iteration,
            // then memory is released immediately.
            StmtPropertiesAllocator stmtProperties;
            m_stmtPropertiesp = &stmtProperties;

            // Pop off current work item
            AstNode* currp = m_workQueuep->front();
            m_workQueuep->pop();

            // Analyse sub-tree list for code motion and conditional merging
            CodeMotionAnalysisVisitor::analyze(currp, stmtProperties);
            // Perform the code motion within the whole sub-tree list
            if (v3Global.opt.fMergeCondMotion()) {
                currp = CodeMotionOptimizeVisitor::optimize(currp, stmtProperties);
            }

            // Merge conditionals in the whole sub-tree list (this might create new work items)
            iterateAndNextNull(currp);

            // Close pending merge, if there is one at the end of the whole sub-tree list
            if (m_mgFirstp) mergeEnd();
        } while (!m_workQueuep->empty());
    }

    // Skip past AstArraySel and AstWordSel with const index
    static AstNode* skipConstSels(AstNode* nodep) {
        while (const AstArraySel* const aselp = VN_CAST(nodep, ArraySel)) {
            // ArraySel index is not constant, so might be expensive
            if (!VN_IS(aselp->bitp(), Const)) return nodep;
            nodep = aselp->fromp();
        }
        while (const AstWordSel* const wselp = VN_CAST(nodep, WordSel)) {
            // WordSel index is not constant, so might be expensive
            if (!VN_IS(wselp->bitp(), Const)) return nodep;
            nodep = wselp->fromp();
        }
        return nodep;
    }

    // Check if this node is cheap enough that duplicating it in two branches of an
    // AstIf is not likely to cause a performance degradation.
    static bool isCheapNode(AstNode* nodep) {
        // Comments are cheap
        if (VN_IS(nodep, Comment)) return true;
        // So are some assignments
        if (const AstNodeAssign* const assignp = VN_CAST(nodep, NodeAssign)) {
            // Check LHS
            AstNode* const lhsp = skipConstSels(assignp->lhsp());
            // LHS is not a VarRef, so might be expensive
            if (!VN_IS(lhsp, VarRef)) return false;

            // Check RHS
            AstNode* const rhsp = skipConstSels(assignp->rhsp());
            // RHS is not a VarRef or Constant so might be expensive
            if (!VN_IS(rhsp, VarRef) && !VN_IS(rhsp, Const)) return false;

            // Otherwise it is a cheap assignment
            return true;
        }
        // Others are not
        return false;
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
        AstNode* const maskp = new AstConst{nodep->fileline(), AstConst::BitTrue()};
        // Mask on left, as conventional
        return new AstAnd{nodep->fileline(), maskp, nodep};
    }

    // Fold the RHS expression of an assignment assuming the given condition state.
    // Unlink bits from the RHS which is only used once, and can be reused (is an unomdified
    // sub-tree). What remains of the RHS is expected to be deleted by the caller.
    AstNode* foldAndUnlink(AstNode* rhsp, bool condTrue) {
        if (rhsp->sameTree(m_mgCondp)) {
            return new AstConst{rhsp->fileline(), AstConst::BitTrue{}, condTrue};
        } else if (const AstNodeCond* const condp = extractCondFromRhs(rhsp)) {
            AstNode* const resp
                = condTrue ? condp->expr1p()->unlinkFrBack() : condp->expr2p()->unlinkFrBack();
            if (condp == rhsp) return resp;
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
        } else if (VN_IS(rhsp, ArraySel) || VN_IS(rhsp, WordSel) || VN_IS(rhsp, VarRef)
                   || VN_IS(rhsp, Const)) {
            return rhsp->cloneTree(false);
        }
        // LCOV_EXCL_START
        if (debug()) rhsp->dumpTree("Don't know how to fold expression: ");
        rhsp->v3fatalSrc("Should not try to fold this during conditional merging");
        // LCOV_EXCL_STOP
    }

    void mergeEnd() {
        UASSERT(m_mgFirstp, "mergeEnd without list");
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
                        "Cheap statement should not be at the front of the list");
        }
        // If the list contains a single AstNodeIf, we will want to merge its branches.
        // If so, keep hold of the AstNodeIf in this variable.
        AstNodeIf* recursivep = nullptr;
        // Merge if list is longer than one node
        if (m_mgFirstp != m_mgLastp) {
            UINFO(6, "MergeCond - First: " << m_mgFirstp << " Last: " << m_mgLastp << endl);
            ++m_statMerges;
            if (m_listLenght > m_statLongestList) m_statLongestList = m_listLenght;

            // We need a copy of the condition in the new equivalent 'if' statement,
            // and we also need to keep track of it for comparisons later.
            m_mgCondp = m_mgCondp->cloneTree(false);
            // Create equivalent 'if' statement and insert it before the first node
            AstIf* const resultp = new AstIf{m_mgCondp->fileline(), m_mgCondp};
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
            // Merge the branches of the resulting AstIf after re-analysis
            if (resultp->ifsp()) m_workQueuep->push(resultp->ifsp());
            if (resultp->elsesp()) m_workQueuep->push(resultp->elsesp());
        } else if (AstNodeIf* const ifp = VN_CAST(m_mgFirstp, NodeIf)) {
            // There was nothing to merge this AstNodeIf with, so try to merge its branches.
            // No re-analysis is required for this, so do it directly below
            recursivep = ifp;
        }
        // Reset state
        m_mgFirstp = nullptr;
        m_mgCondp = nullptr;
        m_mgLastp = nullptr;
        m_mgNextp = nullptr;
        AstNode::user1ClearTree();  // Clear marked variables
        AstNode::user2ClearTree();
        // Merge recursively within the branches of an un-merged AstNodeIF
        if (recursivep) {
            iterateAndNextNull(recursivep->ifsp());
            iterateAndNextNull(recursivep->elsesp());
            // Close a pending merge to ensure merge state is
            // reset as expected at the end of this function
            if (m_mgFirstp) mergeEnd();
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

    bool addToList(AstNodeStmt* nodep, AstNode* condp) {
        // Set up head of new list if node is first in list
        if (!m_mgFirstp) {
            UASSERT_OBJ(condp, nodep, "Cannot start new list without condition");
            // Mark variable references in the condition
            condp->foreach<AstVarRef>([](const AstVarRef* nodep) { nodep->varp()->user1(1); });
            // Now check again if mergeable. We need this to pick up assignments to conditions,
            // e.g.: 'c = c ? a : b' at the beginning of the list, which is in fact not mergeable
            // because it updates the condition. We simply bail on these.
            if ((*m_stmtPropertiesp)(nodep).writesConditionVar()) {
                // Clear marked variables
                AstNode::user1ClearTree();
                // We did not add to the list
                return false;
            }
            m_mgFirstp = nodep;
            m_mgCondp = condp;
            m_listLenght = 0;
            // Add any preceding nodes to the list that would allow us to extend the merge
            // range
            while (true) {
                AstNodeStmt* const backp = VN_CAST(m_mgFirstp->backp(), NodeStmt);
                if (!backp || backp->nextp() != m_mgFirstp) break;  // Don't move up the tree
                const StmtProperties& props = (*m_stmtPropertiesp)(backp);
                if (props.m_isFence || props.writesConditionVar()) break;
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
        if (!m_mgNextp) mergeEnd();
        // We did add to the list
        return true;
    }

    // If this node is the next expected node and is helpful to add to the list, do so,
    // otherwise end the current merge. Return ture if added, false if ended merge.
    bool addIfHelpfulElseEndMerge(AstNodeStmt* nodep) {
        UASSERT_OBJ(m_mgFirstp, nodep, "List must be open");
        if (!checkOrMakeMergeable(nodep)) return false;
        if (!m_mgFirstp) return false;  // If 'checkOrMakeMergeable' closed the list
        if (m_mgNextp == nodep) {
            if (isSimplifiableNode(nodep)) {
                if (addToList(nodep, nullptr)) return true;
            } else if (isCheapNode(nodep)) {
                nodep->user2(1);
                if (addToList(nodep, nullptr)) return true;
            }
        }
        // Not added to list, so we are done with the current list
        mergeEnd();
        return false;
    }

    bool checkOrMakeMergeable(const AstNodeStmt* nodep) {
        const StmtProperties& props = (*m_stmtPropertiesp)(nodep);
        if (props.m_isFence) return false;  // Fence node never mergeable
        // If the statement writes a condition variable of a pending merge,
        // we must end the pending merge
        if (m_mgFirstp && props.writesConditionVar()) mergeEnd();
        return true;  // Now surely mergeable
    }

    void mergeEndIfIncompatible(const AstNode* nodep, const AstNode* condp) {
        if (m_mgFirstp && (m_mgNextp != nodep || !condp->sameTree(m_mgCondp))) {
            // Node in different list, or has different condition. Finish current list.
            mergeEnd();
        }
    }

    // VISITORS
    virtual void visit(AstNodeAssign* nodep) override {
        if (AstNode* const condp = (*m_stmtPropertiesp)(nodep).m_condp) {
            // Check if mergeable
            if (!checkOrMakeMergeable(nodep)) return;
            // Close potentially incompatible pending merge
            mergeEndIfIncompatible(nodep, condp);
            // Add current node
            addToList(nodep, condp);
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
        addToList(nodep, nodep->condp());
    }

    virtual void visit(AstNodeStmt* nodep) override {
        if (m_mgFirstp && addIfHelpfulElseEndMerge(nodep)) return;
        iterateChildren(nodep);
    }

    virtual void visit(AstCFunc* nodep) override {
        // Merge function body
        if (nodep->stmtsp()) process(nodep->stmtsp());
    }

    // For speed, only iterate what is necessary.
    virtual void visit(AstNetlist* nodep) override { iterateAndNextNull(nodep->modulesp()); }
    virtual void visit(AstNodeModule* nodep) override { iterateAndNextNull(nodep->stmtsp()); }
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

}  // namespace

//######################################################################
// MergeConditionals class functions

void V3MergeCond::mergeAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    { MergeCondVisitor{nodep}; }
    V3Global::dumpCheckGlobalTree("merge_cond", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 6);
}
