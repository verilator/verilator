// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Split packed variables into bit ranges
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
// V3BitBlast replaces a packed variable with one variable per bit range,
// called a fragment. This avoids false combinational loops (UNOPTFLAT) through
// the bits of a variable, and lets downstream passes optimize each fragment
// separately.
//
// A variable is split if all its references are either:
//  - constant bit selects,
//  - whole,
// and either:
//   - it is marked with split_var
//   - all its references are constant bit selects, which are either disjoint
//     or identical (i.e.: non-overlapping)
// The fragments are the ranges between the boundaries of the bit ranges
// written, and the edges of the range of bits referenced by any read or write,
// so unused bits at the edges are dropped. A write then assigns whole
// fragments, and a read selects from, or concatenates the fragments it
// overlaps.
//
// A write to multiple fragments must be an assignment LHS, which is expanded
// into assignments to each fragment. This only happens for split_var
// variables, e.g.:
//
//   logic [7:0] x /* verilator split_var */;
//   always_comb begin
//     x[3:0] = a;
//     x[7:4] = b;
//     x = {x[3:0], x[7:4]};
//   end
//   assign out = x[5:2];
//
// Becomes, with fragments 'x_7_4' and 'x_3_0' for 'x[7:4]' and 'x[3:0]':
//
//   always_comb begin
//     x_3_0 = a;
//     x_7_4 = b;
//     tmp = {x_3_0, x_7_4};
//     x_3_0 = tmp[3:0];
//     x_7_4 = tmp[7:4];
//   end
//   assign out = {x_7_4[1:0], x_3_0[3:2]};
//
// The RHS of an assignment to multiple fragments is assigned to a temporary
// first, so it is evaluated once, and reads the fragments before any of them is
// written. A constant, a variable, or a constant select of a variable is
// selected from directly instead.
//
// The pass records all references in a single traversal, decides which
// variables to split, then replaces the references. The decision is made for
// each AstVarScope separately. AstVarScopes of the same variable with the same
// fragment share the AstVar of the fragment.
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3BitBlast.h"

#include "V3AstUserAllocator.h"
#include "V3SharedTmps.h"
#include "V3Stats.h"

#include <algorithm>

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################

class BitBlastVisitor final : public VNVisitorConst, public VNDeleter {
    // TYPES

    // A read of a variable: a constant bit select or a whole VarRef
    struct RdRef final {
        AstNodeExpr* exprp;  // Sel, or the VarRef if whole
        int lsb;  // First bit read
        int msb;  // Last bit read
    };

    // A write of a variable: a constant bit select or a whole VarRef
    struct WrRef final {
        AstNodeExpr* exprp;  // The Sel, or the VarRef if whole
        AstNodeAssign* assignp;  // The assignment, if it can be expanded
        int lsb;  // The first bit written
        int msb;  // The last bit written
    };

    // A fragment of a split AstVarScope
    struct Fragment final {
        int lsb;  // The first bit in the variable
        int msb;  // The last bit in the variable
        AstVarScope* vscp;  // The AstVarScope of the fragment
    };

    // The information about an AstVarScope of an eligible variable
    struct VscpInfo final {
        std::vector<RdRef> rdRefs;  // The reads of the AstVarScope
        std::vector<WrRef> wrRefs;  // The writes of the AstVarScope
        std::vector<Fragment> fragments;  // The fragments in LSB order, empty if not split
        bool blocked = false;  // Referenced other than by an RdRef or WrRef
    };

    // NODE STATE
    //  AstVar::user1()             -> int: bit 0: eligible, bit 1: evaluated, see isEligible
    //  AstVarScope::user1()        -> VscpInfo, via m_vscpInfos
    //  AstVar::user2()             -> Fragment AstVars by LSB and MSB, via m_fragmentVarps
    //  AstScope::user2p()          -> AstActive*: combinational active, see comboActive
    const VNUser1InUse m_user1InUse;
    const VNUser2InUse m_user2InUse;

    // STATE
    // The fragment AstVars created so far, by LSB and MSB. AstVarScopes with the same
    // fragment share its AstVar.
    AstUser2Allocator<AstVar, std::map<std::pair<int, int>, AstVar*>> m_fragmentVarps;
    AstUser1Allocator<AstVarScope, VscpInfo> m_vscpInfos;
    std::vector<AstVarScope*> m_vscps;  // AstVarScopes of eligible variables, in encounter order
    AstNodeAssign* m_assignp = nullptr;  // The enclosing assignment, if it can be expanded
    V3SharedTmps m_tmps{"__VbitblastTmp", VVarType::MODULETEMP};  // Temporaries of RHSs
    VDouble0 m_statSplitAttr;  // AstVarScopes split only due to split_var
    VDouble0 m_statSplitAuto;  // AstVarScopes split automatically
    VDouble0 m_statFragments;  // Fragment AstVarScopes created
    VDouble0 m_statTmps;  // Assignments to multiple fragments through a temporary

    // METHODS

    // Warn that splitting requested via split_var cannot be done, because of 'reasonp'
    static void warnNoSplit(AstVar* varp, const AstNode* wherep, const char* reasonp) {
        // Only warn if user requested splitting
        if (!varp->attrSplitVar()) return;
        wherep->v3warn(SPLITVAR, varp->prettyNameQ()
                                     << " marked split_var but will not be split because "
                                     << reasonp);
        wherep->fileline()->modifyWarnOff(V3ErrorCode::SPLITVAR, true);  // Warn only once
    }

    // Is the variable eligible for splitting by its type and properties. Note this might be
    // overridden by a visit to an unsupported construct, so it is not completely determined
    // until the whole netlist is visited.
    static bool isEligible(AstVar* varp) {
        // Compute and cache eligibility on first encounter
        if (!varp->user1()) {
            const bool eligible = [&]() {
                const AstNodeDType* const dtypep = varp->dtypep()->skipRefp();
                // Packed types only
                if (!dtypep->isIntegralOrPacked()) return false;
                // Wider than one bit
                if (dtypep->width() <= 1) return false;
                // Check properties
                const char* const reasonp = varp->cannotSplitKindReason();
                // Warn that it cannot be split if user explicitly requested splitting
                if (reasonp) warnNoSplit(varp, varp, reasonp);
                // Eligible if no refusal reason returned
                return !reasonp;
            }();
            varp->user1(2 | eligible);
        }
        // Return the cached result
        return varp->user1() & 1;
    }

    // The VscpInfo of the AstVarScope of an eligible variable
    VscpInfo& vscpInfoOf(AstVarScope* vscp) {
        if (VscpInfo* const infop = m_vscpInfos.tryGet(vscp)) return *infop;
        // Also record on first encounter
        m_vscps.push_back(vscp);
        return m_vscpInfos(vscp);
    }

    // Record step methods

    // Block splitting of the AstVarScope, due to the construct in 'wherep'
    static void block(AstVar* varp, VscpInfo& info, const AstNode* wherep) {
        warnNoSplit(varp, wherep, "it is referenced in an unsupported way");
        if (info.blocked) return;
        info.blocked = true;
        info.rdRefs.clear();
        info.wrRefs.clear();
    }

    // Record the reference 'exprp' of bits 'lsb' to 'msb' through 'refp'
    void record(AstNodeExpr* exprp, AstVarRef* refp, int lsb, int msb) {
        AstVar* const varp = refp->varp();
        if (!isEligible(varp)) return;
        VscpInfo& info = vscpInfoOf(refp->varScopep());
        // RW reference blocks splitting
        if (refp->access().isRW()) block(varp, info, exprp);
        // Don't recod if blocked (due to RW above, or any other reason from elsewhere)
        if (info.blocked) return;
        // Record reference
        if (refp->access().isReadOnly()) {
            info.rdRefs.push_back({exprp, lsb, msb});
            return;
        }
        // A write as an assignment LHS can be expanded into assignments to multiple fragments
        const bool canExpand = m_assignp && exprp == m_assignp->lhsp();
        info.wrRefs.push_back({exprp, canExpand ? m_assignp : nullptr, lsb, msb});
    }

    // Assignment visitor, shared by the assignment types that can be expanded
    void visitAssignment(AstNodeAssign* nodep) {
        VL_RESTORER(m_assignp);
        // Not with timing control, but always needs visiting
        m_assignp = nodep->timingControlp() ? nullptr : nodep;
        iterateChildrenConst(nodep);
    }

    // Decision step methods

    // The AstVar of the fragment of 'varp' of bits 'lsb' to 'msb', created on first use
    AstVar* fragmentVarp(AstVar* varp, int lsb, int msb) {
        AstVar*& fragVarpr = m_fragmentVarps(varp)[{lsb, msb}];
        if (fragVarpr) return fragVarpr;
        const int width = msb - lsb + 1;
        std::string name = varp->name() + "__BRA__" + AstNode::encodeNumber(msb);
        if (width > 1) name += AstNode::encodeName(":") + AstNode::encodeNumber(lsb);
        name += "__KET__";
        AstNodeDType* const dtypep = varp->dtypep()->isFourstate()
                                         ? varp->findLogicDType(width, width, VSigning::UNSIGNED)
                                         : varp->findBitDType(width, width, VSigning::UNSIGNED);
        fragVarpr = new AstVar{varp->fileline(), varp->varType(), name, dtypep};
        fragVarpr->propagateSplitAttrFrom(varp);
        varp->addHereThisAsNext(fragVarpr);
        return fragVarpr;
    }

    // Decide whether to split the AstVarScope, and if so, create its fragments
    void decide(AstVarScope* vscp, VscpInfo& info) {
        if (info.blocked) return;
        AstVar* const varp = vscp->varp();
        // Split automatically if all references are disjoint or identical bit selects
        const bool isAuto = [&]() {
            std::vector<std::pair<int, int>> ranges;  // [lsb, msb] inclusive
            for (const RdRef& ref : info.rdRefs) {
                if (VN_IS(ref.exprp, VarRef)) return false;
                ranges.emplace_back(ref.lsb, ref.msb);
            }
            for (const WrRef& ref : info.wrRefs) {
                if (VN_IS(ref.exprp, VarRef)) return false;
                ranges.emplace_back(ref.lsb, ref.msb);
            }
            std::sort(ranges.begin(), ranges.end());
            for (size_t i = 0; i + 1 < ranges.size(); ++i) {
                const std::pair<int, int>& a = ranges[i];
                const std::pair<int, int>& b = ranges[i + 1];
                if (a != b && a.second >= b.first) return false;
            }
            return true;
        }();
        // Otherwise only if requested
        if (!isAuto && !varp->attrSplitVar()) return;
        // The fragment boundaries are the boundaries of the ranges written,
        // and of the range referenced, as bits outside of it are not used
        int lsb = varp->width();
        int msb = -1;
        for (const RdRef& ref : info.rdRefs) {
            lsb = std::min(lsb, ref.lsb);
            msb = std::max(msb, ref.msb);
        }
        std::vector<int> bounds;
        for (const WrRef& ref : info.wrRefs) {
            lsb = std::min(lsb, ref.lsb);
            msb = std::max(msb, ref.msb);
            bounds.push_back(ref.lsb);
            bounds.push_back(ref.msb + 1);
        }
        bounds.push_back(lsb);
        bounds.push_back(msb + 1);
        std::sort(bounds.begin(), bounds.end());
        bounds.erase(std::unique(bounds.begin(), bounds.end()), bounds.end());
        // Nothing to do if the only fragment is the whole variable
        if (bounds.size() == 2 && lsb == 0 && msb == varp->width() - 1) return;
        // Writes that cannot be expanded must write one fragment
        for (const WrRef& ref : info.wrRefs) {
            // On the LHS of assignment it can be expanded
            if (ref.assignp) continue;
            // If write is to a whole fragment, it can be replaced
            if (*std::upper_bound(bounds.begin(), bounds.end(), ref.lsb) == ref.msb + 1) {
                continue;
            }
            // Otherwise can't split
            warnNoSplit(varp, ref.exprp, "it is written in an unsupported way");
            return;
        }

        // Splitting this variable
        ++(isAuto ? m_statSplitAuto : m_statSplitAttr);

        // Create the fragment AstVarScopes
        for (size_t i = 0; i + 1 < bounds.size(); ++i) {
            const int lsb = bounds[i];
            const int msb = bounds[i + 1] - 1;
            AstVar* const fragVarp = fragmentVarp(varp, lsb, msb);
            AstVarScope* const newp = new AstVarScope{vscp->fileline(), vscp->scopep(), fragVarp};
            vscp->addHereThisAsNext(newp);
            info.fragments.push_back({lsb, msb, newp});
            ++m_statFragments;
        }
    }

    // Rewrite step methods

    // Index of the fragment containing bit 'bit'
    static size_t fragmentIndex(const VscpInfo& info, int bit) {
        const auto it = std::upper_bound(info.fragments.begin(), info.fragments.end(), bit,
                                         [](int b, const Fragment& fragment) {  //
                                             return b <= fragment.msb;
                                         });
        return it - info.fragments.begin();
    }

    // Replace the read 'ref' with the bits of the fragments it overlaps
    void rewriteRead(const RdRef& ref, const VscpInfo& info) {
        FileLine* const flp = ref.exprp->fileline();
        AstNodeExpr* resultp = nullptr;
        for (size_t i = fragmentIndex(info, ref.lsb); i < info.fragments.size(); ++i) {
            const Fragment& fragment = info.fragments[i];
            if (fragment.lsb > ref.msb) break;
            const int partLsb = std::max(ref.lsb, fragment.lsb);
            const int partMsb = std::min(ref.msb, fragment.msb);
            AstNodeExpr* bitsp = new AstVarRef{flp, fragment.vscp, VAccess::READ};
            if (partLsb != fragment.lsb || partMsb != fragment.msb) {
                bitsp = new AstSel{flp, bitsp, partLsb - fragment.lsb, partMsb - partLsb + 1};
            }
            // Higher bits go to the left
            resultp = resultp ? new AstConcat{flp, bitsp, resultp} : bitsp;
        }
        ref.exprp->replaceWith(resultp);
        VL_DO_DANGLING(pushDeletep(ref.exprp), ref.exprp);
    }

    // Can the bits of the RHS of an assignment to multiple fragments be selected directly for
    // each fragment. It must be pure and cheap, and must not read a fragment being written, which
    // it cannot, as it is wider than one fragment, and its reads were rewritten into fragments.
    static bool isSelectable(const AstNodeExpr* nodep) {
        if (VN_IS(nodep, Const)) return true;
        if (const AstSel* const selp = VN_CAST(nodep, Sel)) {
            if (!VN_IS(selp->lsbp(), Const)) return false;
            nodep = selp->fromp();
        }
        const AstVarRef* const refp = VN_CAST(nodep, VarRef);
        if (!refp) return false;
        // Not a forced variable (trips several bugs in V3Force)
        if (refp->varp()->isForced()) return false;
        // Not a SystemC variable, which can only be accessed whole, not selected from.
        return !refp->varp()->isSc();
    }

    // Replace the write 'ref' with the fragments it covers
    void rewriteWrite(AstScope* scopep, const WrRef& ref, const VscpInfo& info) {
        FileLine* const flp = ref.exprp->fileline();
        const size_t first = fragmentIndex(info, ref.lsb);
        const size_t last = fragmentIndex(info, ref.msb);
        UASSERT_OBJ(info.fragments[first].lsb == ref.lsb, ref.exprp,
                    "Write not at fragment boundary");
        // If one fragment, write it instead
        if (first == last) {
            ref.exprp->replaceWith(new AstVarRef{flp, info.fragments[first].vscp, VAccess::WRITE});
            VL_DO_DANGLING(pushDeletep(ref.exprp), ref.exprp);
            return;
        }
        // Otherwise it must be an assignment LHS: expand the assignment into
        // an assignment to each fragment
        AstNodeAssign* const origp = ref.assignp;
        AstNodeExpr* rhsp = origp->rhsp()->unlinkFrBack();
        // Unless its bits can be selected directly, assign the RHS to a temporary first, so it
        // is evaluated once, and reads the fragments before any of them is written
        if (!isSelectable(rhsp)) {
            ++m_statTmps;
            AstVarScope* const tmpp = m_tmps.make(flp, scopep, rhsp->dtypep());
            AstVarRef* const tmpRefp = new AstVarRef{flp, tmpp, VAccess::WRITE};
            origp->addHereThisAsNext(new AstAssign{flp, tmpRefp, rhsp});
            rhsp = new AstVarRef{flp, tmpp, VAccess::READ};
        }
        // Assign each fragment its bits of the RHS
        for (size_t i = first; i <= last; ++i) {
            const Fragment& fragment = info.fragments[i];
            const int lsb = fragment.lsb - ref.lsb;  // LSB of the fragment's bits in the RHS
            const int width = fragment.msb - fragment.lsb + 1;
            AstVarRef* const lhsp = new AstVarRef{flp, fragment.vscp, VAccess::WRITE};
            AstSel* const selp = new AstSel{flp, rhsp->cloneTreePure(false), lsb, width};
            origp->addHereThisAsNext(origp->cloneType(lhsp, selp));
        }
        VL_DO_DANGLING(pushDeletep(rhsp), rhsp);
        VL_DO_DANGLING(pushDeletep(origp->unlinkFrBack()), origp);
    }

    // The combinational AstActive of the scope, cached
    static AstActive* comboActive(AstScope* scopep) {
        if (!scopep->user2p()) scopep->user2p(scopep->comboActivep(true));
        return VN_AS(scopep->user2p(), Active);
    }

    // VISITORS
    void visit(AstNodeDType*) override {}  // No references in data types
    void visit(AstNode* nodep) override { iterateChildrenConst(nodep); }
    void visit(AstAssign* nodep) override { visitAssignment(nodep); }
    void visit(AstAssignW* nodep) override { visitAssignment(nodep); }
    void visit(AstAssignDly* nodep) override { visitAssignment(nodep); }
    void visit(AstSel* nodep) override {
        AstVarRef* const refp = VN_CAST(nodep->fromp(), VarRef);
        if (!refp || !isEligible(refp->varp())) {
            iterateChildrenConst(nodep);
            return;
        }
        // Must be constant and in range. V3Unknown only guards the LSB, so a select with
        // the LSB in range, but the MSB beyond the variable can reach here.
        const AstConst* const lsbp = VN_CAST(nodep->lsbp(), Const);
        if (!lsbp || lsbp->toSInt() + nodep->widthConst() > refp->varp()->width()) {
            block(refp->varp(), vscpInfoOf(refp->varScopep()), refp);
            iterateConst(nodep->lsbp());
            return;
        }
        // Record partial access
        record(nodep, refp, lsbp->toSInt(), lsbp->toSInt() + nodep->widthConst() - 1);
    }
    void visit(AstVarRef* nodep) override {
        // Record whole access
        record(nodep, nodep, 0, nodep->varp()->width() - 1);
    }
    void visit(AstMemberSel* nodep) override {
        iterateChildrenConst(nodep);
        // The AstVarScope is not known, so all of them are blocked, by making it ineligible
        AstVar* const varp = nodep->varp();
        if (!isEligible(varp)) return;
        varp->user1(2);  // Mark not eligible
        warnNoSplit(varp, nodep, "it is referenced in an unsupported way");
    }

    // CONSTRUCTORS
    explicit BitBlastVisitor(AstNetlist* netlistp) {
        // Record the references
        iterateConst(netlistp);

        // Decide which AstVarScopes are split, unless the variable became ineligible
        for (AstVarScope* const vscp : m_vscps) {
            if (isEligible(vscp->varp())) decide(vscp, m_vscpInfos(vscp));
        }

        // Rewrite the reads, then the writes, which might move the reads in their RHS
        for (AstVarScope* const vscp : m_vscps) {
            const VscpInfo& info = m_vscpInfos(vscp);
            if (info.fragments.empty()) continue;
            for (const RdRef& ref : info.rdRefs) rewriteRead(ref, info);
        }
        for (AstVarScope* const vscp : m_vscps) {
            const VscpInfo& info = m_vscpInfos(vscp);
            if (info.fragments.empty()) continue;
            for (const WrRef& ref : info.wrRefs) rewriteWrite(vscp->scopep(), ref, info);
        }

        // Drive variables that must be kept from their fragments
        for (AstVarScope* const vscp : m_vscps) {
            const VscpInfo& info = m_vscpInfos(vscp);
            if (info.fragments.empty()) continue;
            if (!(vscp->varp()->isTrace() && vscp->isTrace())
                && !vscp->varp()->isVpiLazyCombWhole())
                continue;
            AstActive* const activep = comboActive(vscp->scopep());
            FileLine* const flp = vscp->fileline();
            for (const Fragment& fragment : info.fragments) {
                AstVarRef* const lhsRefp = new AstVarRef{flp, vscp, VAccess::WRITE};
                const int width = fragment.msb - fragment.lsb + 1;
                AstSel* const lhsp = new AstSel{flp, lhsRefp, fragment.lsb, width};
                AstVarRef* const rhsp = new AstVarRef{flp, fragment.vscp, VAccess::READ};
                activep->addStmtsp(new AstAlways{new AstAssignW{flp, lhsp, rhsp}});
            }
        }

        V3Stats::addStat("Optimizations, Bitblast, variables split due to attribute",
                         m_statSplitAttr);
        V3Stats::addStat("Optimizations, Bitblast, variables split automatically",
                         m_statSplitAuto);
        V3Stats::addStat("Optimizations, Bitblast, fragments created", m_statFragments);
        V3Stats::addStat("Optimizations, Bitblast, assignments through temporary", m_statTmps);
    }

public:
    static void apply(AstNetlist* netlistp) { BitBlastVisitor{netlistp}; }
};

//######################################################################
// V3BitBlast class functions

void V3BitBlast::bitBlastAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ":");
    BitBlastVisitor::apply(nodep);
    V3Global::dumpCheckGlobalTree("bitblast", 0, dumpTreeEitherLevel() >= 3);
}
