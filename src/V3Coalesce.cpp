// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Coalesce variables connected by single assignments
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
// V3Coalesce's Transformations:
//
// A continuous assignment of one whole variable to another, 'assign a = b', makes
// 'a' nothing but a copy of 'b'. Redirect every reference to 'a' at 'b', so the
// two are a single signal as far as the rest of the compiler is concerned. This is
// done transitively, so a chain of copies collapses onto the signal at the end of
// it in one pass.
//
// The assignment itself is kept, so 'a' still holds the value, and remains
// traceable and visible via the VPI.
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Coalesce.h"

#include "V3Stats.h"

#include <unordered_map>
#include <unordered_set>
#include <vector>

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################

class CoalesceVisitor final : public VNVisitorConst {
    // NODE STATE
    // Cleared on netlist
    //  AstVarScope::user1p()  -> AstVarScope*. The signal this one is a copy of
    //  AstVarScope::user2()   -> uint64_t. Number of references that write it
    //  AstVarScope::user3()   -> bool. Used in a sensitivity list
    //  AstVarScope::user4p()  -> AstConst*. The constant assigned to it, if any
    const VNUser1InUse m_user1InUse;
    const VNUser2InUse m_user2InUse;
    const VNUser3InUse m_user3InUse;
    const VNUser4InUse m_user4InUse;

    // STATE
    std::vector<AstNodeVarRef*> m_refps;  // All references, to redirect at the end
    VDouble0 m_nCoalesced;  // Number of coalesced variables, for statistics
    VDouble0 m_nReplaced;  // Number of redirected references, for statistics

    // METHODS
    // Whether the given variable can be replaced by whatever is driving it
    static bool isCoalescible(const AstVarScope* vscp) {
        const AstVar* const varp = vscp->varp();
        if (varp->dtypep()->skipRefp()->isCompound()) return false;
        if (varp->delayp()) return false;
        if (varp->isForced()) return false;
        if (varp->isSigUserRWPublic()) return false;
        // The user asked for it to be split, which needs the variable itself
        if (varp->attrSplitVar()) return false;
        if (varp->isSc()) return false;
        if (const AstIface* const ifacep = VN_CAST(vscp->scopep()->modp(), Iface)) {
            if (ifacep->hasVirtualRef()) return false;
        }
        return true;
    }

    static void noteCopy(const AstNodeAssign* nodep) {
        // Don't do it if there is a timing control
        if (nodep->timingControlp()) return;
        // Must be a whole variable assigned from a whole variable
        const AstVarRef* const lhsp = VN_CAST(nodep->lhsp(), VarRef);
        if (!lhsp) return;
        if (AstConst* const constp = VN_CAST(nodep->rhsp(), Const)) {
            lhsp->varScopep()->user4p(constp);
            return;
        }
        const AstVarRef* const rhsp = VN_CAST(nodep->rhsp(), VarRef);
        if (!rhsp) return;
        // Check types: plain vectors of the same width, or the same type. A copy that
        // reshapes a packed struct or array is kept, as V3Decompose splits along its shape.
        const AstNodeDType* const lDtp = lhsp->dtypep()->skipRefp();
        const AstNodeDType* const rDtp = rhsp->dtypep()->skipRefp();
        if (VN_IS(lDtp, BasicDType) && VN_IS(rDtp, BasicDType)) {
            UASSERT_OBJ(lDtp->width() == rDtp->width(), nodep, "Malformed assignment");
        } else if (!lDtp->sameTree(rDtp)) {
            return;
        }
        // Both sides must be compatible
        AstVarScope* const lVscp = lhsp->varScopep();
        if (!isCoalescible(lVscp)) return;
        AstVarScope* const rVscp = rhsp->varScopep();
        if (!isCoalescible(rVscp)) return;
        // Note the replacement
        lVscp->user1p(rVscp);
    }

    using ConstCache = std::unordered_map<const AstVarScope*, const AstConst*>;

    // Resolve each copy-chain suffix once, including nonconstant and cyclic suffixes
    static const AstConst* constOf(const AstVarScope* vscp, ConstCache& cache) {
        std::vector<const AstVarScope*> path;
        const AstConst* constp = nullptr;
        // A null entry also breaks cycles while this path is being visited
        while (!constp && vscp && vscp->user2() == 1 && cache.emplace(vscp, nullptr).second) {
            path.push_back(vscp);
            constp = VN_CAST(vscp->user4p(), Const);
            vscp = VN_CAST(vscp->user1p(), VarScope);
        }
        // Stopped at a variable resolved before
        if (!constp && vscp) {
            const ConstCache::const_iterator it = cache.find(vscp);
            if (it != cache.end()) constp = it->second;
        }
        for (const AstVarScope* const seenp : path) cache[seenp] = constp;
        return constp;
    }

    // A kept port that gets the same constant in every instance has no logic to share, so
    // it is not kept, and the constant can be folded into the instances
    void releaseConstPorts() {
        ConstCache cache;
        // The constant of each kept port in all its instances so far, nullptr if they differ
        std::unordered_map<AstVar*, const AstConst*> consts;
        std::unordered_set<const AstVarScope*> seen;
        for (const AstNodeVarRef* const refp : m_refps) {
            const AstVarScope* const vscp = refp->varScopep();
            if (!vscp->varp()->keepPort() || !seen.insert(vscp).second) continue;
            const AstConst* const constp = constOf(vscp, cache);
            const auto pair = consts.emplace(vscp->varp(), constp);
            const AstConst*& seenp = pair.first->second;
            if (!pair.second && seenp && !(constp && constp->sameTree(seenp))) seenp = nullptr;
        }
        for (const auto& pair : consts) {
            if (pair.second) pair.first->keepPort(false);
        }
    }

    // The signal the given one is a copy of, or nullptr if it is not a copy of one
    static AstVarScope* driverOf(AstVarScope* vscp) {
        // Don't substitute if written more than once
        if (vscp->user2() != 1) return nullptr;
        // A port V3Inst kept for an instance that remains a module stays a variable of its
        // own, so the module's instances can share code. With several threads, a clock is
        // coalesced instead, as it would otherwise add serial trigger work.
        if (vscp->varp()->keepPort() && !(v3Global.opt.mtasks() && vscp->user3())) return nullptr;
        return VN_AS(vscp->user1p(), VarScope);
    }

    // The signal the given one is ultimately a copy of, or nullptr if no such signal.
    // This compresses the chain of copies as it goes so amortized cost to O(1) in practice.
    static AstVarScope* findEquivalent(AstVarScope* vscp) {
        // Walk to the end of the chain, pointing each variable at its grandparent on the
        // way, so the chain halves in length on every walk of it. A cycle halves the
        // same way until it is a variable pointing at itself, which is how it's found.
        for (AstVarScope *midp = driverOf(vscp), *nextp; midp; vscp = midp, midp = nextp) {
            // Don't do it if circular (or driven from a cycle)
            if (midp == vscp) return nullptr;
            nextp = driverOf(midp);
            if (!nextp) return midp;  // 'midp' is the end of the chain
            vscp->user1p(nextp);
        }
        // 'vscp' is not a copy of anything
        return nullptr;
    }

    // VISITORS
    void visit(AstNodeVarRef* nodep) override {
        m_refps.push_back(nodep);
        if (nodep->access().isWriteOrRW()) nodep->varScopep()->user2Inc();
    }
    void visit(AstSenItem* nodep) override {
        iterateChildrenConst(nodep);
        if (const AstNodeVarRef* const refp = nodep->varrefp()) refp->varScopep()->user3(true);
    }
    void visit(AstAssignW* nodep) override {
        iterateChildrenConst(nodep);
        // continuous assignment
        noteCopy(nodep);
    }
    void visit(AstAlways* nodep) override {
        iterateChildrenConst(nodep);
        // always_comb with single assignment
        if (nodep->keyword() != VAlwaysKwd::ALWAYS_COMB) return;
        const AstAssign* const assignp = VN_CAST(nodep->stmtsp(), Assign);
        if (!assignp || assignp->nextp()) return;
        noteCopy(assignp);
    }
    void visit(AstNode* nodep) override { iterateChildrenConst(nodep); }

    // CONSTRUCTORS
    explicit CoalesceVisitor(AstNetlist* nodep) {
        // Gather the references and the copy assignments
        iterateConst(nodep);
        releaseConstPorts();

        // Redirect the references at the signal each chain of copies ends on
        for (AstNodeVarRef* const refp : m_refps) {
            AstVarScope* const vscp = refp->varScopep();
            AstVarScope* const rootp = findEquivalent(vscp);
            if (!rootp) continue;
            // A reference redirected to another scope makes the code of this scope specific
            // to that instance, so its instances can't share it. Only a clock port, whose
            // copy costs trigger work, is redirected across scopes.
            if (rootp->scopep() != vscp->scopep()
                && !(vscp->varp()->direction() == VDirection::INPUT && vscp->user3())) {
                continue;
            }
            // A kept clock is coalesced, so it is no longer kept
            vscp->varp()->keepPort(false);
            // The sole write of a copy is the copy assignment itself, keep it
            if (refp->access().isWriteOrRW()) {
                ++m_nCoalesced;
                continue;
            }
            // Redirect reference
            rootp->varp()->propagateAttrFrom(vscp->varp());
            refp->varp(rootp->varp());
            refp->varScopep(rootp);
            ++m_nReplaced;
        }

        V3Stats::addStat("Optimizations, Coalesced references", m_nReplaced);
        V3Stats::addStat("Optimizations, Coalesced variables", m_nCoalesced);
    }
    ~CoalesceVisitor() override = default;

public:
    static void apply(AstNetlist* nodep) { CoalesceVisitor{nodep}; }
};

//######################################################################
// V3Coalesce class functions

void V3Coalesce::coalesceAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ":");
    CoalesceVisitor::apply(nodep);
    V3Global::dumpCheckGlobalTree("coalesce", 0, dumpTreeEitherLevel() >= 3);
}
