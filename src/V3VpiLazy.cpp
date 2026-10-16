// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Reconstruct optimizer-eliminated VPI signals
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
//
// V3VpiLazy implements --vpi-lazy: VPI access to combinational signals the
// optimizer eliminates, at no cost to the hot eval path. LinkParse marks every
// VPI-accessible variable isSigVpiLazyCandidate(), which unlike --public-flat-rw
// does not block optimization; this pass then gives each signal one of three
// outcomes:
//
//   reconstructed - no storage, recomputed on demand by a cold function
//   copied        - no storage, its own shadow refreshed by a memcpy on read
//   retained      - ordinary storage, as --public-flat-rw would give it
//
// Anything the first two cannot claim is retained, so the VPI-visible set is
// never smaller than --public-flat-rw's (the completeness floor).
//
// UNIT OF RECONSTRUCTION
//
// Post-V3Active every combinational driver is an AstAlways under a combo
// AstActive (a continuous assign being an AstAlways{CONT_ASSIGN} wrapping one
// AstAssignW), so the unit is one such block: a "group". Continuous assigns
// writing disjoint constant ranges or constant-index elements of one variable
// merge into one group, assembled in its shadow. A group's targets are the
// VPI-visible variables it solely drives, its other written variables temp
// shadows. Its statements are cloned into a cold loose function with every
// written variable redirected to a "shadow", leaving the originals deletable.
// Operands belonging to another group are rewired to that group's shadows,
// keeping reconstruction O(N); other "boundary" operands keep their storage so
// the cone has something to read: retained if VPI-visible, else pinned with no
// row, as a compiler temporary has no RTL name.
//
// A group is claimed only if one ordered walk over its statements proves that
// every read of a group variable's bits follows a write of them on every path,
// that every statement is pure and of a modelled kind, and that every target
// is written on all paths. Groups in a dependency cycle merge into one, its
// blocks in encounter order, and are claimed if that walk proves the merged
// group. Otherwise its targets are retained, and Bail records why for --stats.
//
// PHASES, in the fixed order run() lists
//
//   classifyCombDriven                       the bits a VPI put may not change
//   findHelperCandidates                     vars a copy needs promoted to a target
//   formGroups, analyseGroups                form, then prove or bail
//   anchorConsumersOfAnchored                anchor shared cones reading an anchored one
//   buildDependencyGraph, splitCyclesRetainCores, topoOrderSurvivors
//                                            retain cycle cores, order the rest
//   copyStoredSources                        copy rows: the source holds storage
//   foldTrivialCopyGroups                    fold rows: the source is another cone
//   emitReconstructions                      emit the funcs and shadows
//   retainCompletenessFloor                  retain what is left
//
// COPY AND FOLD
//
// A group whose whole body is `target = u;` needs no cone, costing no function
// and no epoch slot. copyStoredSources takes a u that holds storage: the row
// keeps a shadow of its own, refreshed by memcpy from u. foldTrivialCopyGroups
// takes a u that is another live cone's target: the row is that cone's shadow,
// its read that cone's, and it has no member of its own (isLazyShadowAlias).
//
// A copy of stored state keeps its own shadow, as each alias has storage of
// its own under --public-flat-rw: after a put into u and before the next eval,
// the copy must still read u's last-eval value, which the undo log swaps in
// around its memcpy. A fold's source is itself rebuilt under the undo log, and
// no put reaches it, so sharing its shadow reads exactly what a copy would.
//
// WRITABILITY
//
// A put is accepted where a --public-flat-rw put would persist: into bits that
// hold their value without a driver, as flops, latches, undriven or
// initial-only storage and top-level inputs do. classifyCombDriven unions per
// instance the bits each combinational block writes: a constant select or
// element names its own, any other write the whole variable. Latch bits
// contribute nothing: all of an always_latch's, else those a walk of the
// block's if-tree proves unassigned on some path, per bit, as full-width and
// constant-select assigns define them. The walk reads only control flow, and
// folds constant conditions itself, so how V3Split, V3Case or V3Const reshaped
// the block does not change its answer. A target written under a loop or jump,
// or through any other lvalue, is not proven, so each of its writes counts as
// combinational. A variable driven whole is read-only; one driven in part
// keeps its storage and a mask of the bits a put may not change. Assembled
// from constant-select assigns, and read in the design and in cones only in
// the bits they drive, it is reconstructed instead: its shadow holds the
// undriven bits, which the cone never writes, and takes the mask. Instances of
// one AstVar, as a non-inlined module's or an interface's are, can differ,
// driven from their parents: the variable is then PARTIAL, keeping its
// storage, and each instance's row takes its own class, so writability follows
// the RTL and not inlining. Explicit public_flat_rw and forceable signals keep
// --public-flat-rw semantics.
//
// RUNTIME
//
// A reconstructed row's datap is a VerilatedVarLazyDatap {refreshp, selfp,
// offsets}. A read calls refreshp, which compares the group's stamp in its
// module's epoch array against vlSymsp->__Vm_lazy.epoch, recomputes the cone
// if stale, and restamps; eval() bumps the epoch, so a cone is recomputed at most
// once per eval step however many of its signals are read. The epoch is odd
// during eval(), and a read then moves it first, so a read from DPI or a
// callback mid-eval never trusts a memo.
//
// Reconstructed, copied and wholly combinational rows are read-only, and a put
// into a masked row keeps the masked bits, changing nothing if it changes no
// other bit. A put logs the bytes it overwrites, which a read swaps back in
// around a reconstruction until the next eval, so a put reaches a rebuilt
// dependant when it would reach a --public-flat-rw one. A put into a retained
// signal also sets vlSymsp->__Vm_lazy.written, so the next eval re-runs the
// settle region once to propagate it.
//
// A lazy read is thus model code that writes model state - the shadow and the
// memo stamps - from whatever thread called VPI, and those stamps are plain
// words. A read racing eval() is therefore a user error, as it is under --vpi
// and --public-flat-rw; VPI's answer, a synch callback, is dispatched on the
// eval thread, and this pass emits nothing thread-aware.
//
// One function serves every instance of a module, so it must read variables
// rather than instance-specific driver expressions; AstCFunc::vpiLazyReconstruct
// tells V3Gate and V3Dfg to leave those reads alone. A group writing outside the
// scope that authored it is anchored in the written scope if that has one
// instance, else in the top scope: one function per instance, addressing every
// variable absolute, which a row in another module reaches through a stub. So is
// a shared group reading an anchored one, as a shared function cannot call one
// instance's. An anchored group's instance may thus be claimed while another of
// its variable is retained: the variable keeps its role and storage for the
// retained instances, and the claimed ones move to an unflagged twin the
// optimiser is free to eliminate, so storage is kept per instance.
//
// Determinism: pointer-keyed maps are never iterated where order reaches
// output; iteration always walks a companion vector in tree-encounter order.
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3VpiLazy.h"

#include "V3Ast.h"
#include "V3Global.h"
#include "V3Graph.h"
#include "V3Sched.h"
#include "V3Stats.h"

#include <algorithm>
#include <array>
#include <cstring>
#include <limits>
#include <map>
#include <memory>
#include <set>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

VL_DEFINE_DEBUG_FUNCTIONS;

static const char* const RECONSTRUCT_FUNC_NAME = "__Vlazy_reconstruct";
static const char* const SHADOW_PREFIX = "__Vlazyrecon__";
static const char* const EPOCH_NAME = "__Vlazyepoch";
static const char* const RECONSTRUCT_BODY_FUNC_NAME = "__Vlazy_reconstruct_body";
static const char* const RECONSTRUCT_INST_FUNC_NAME = "__Vlazy_reconstruct_inst";

//######################################################################
class V3VpiLazyContext final {
public:
    // PARTIAL variable -> its masked bits, where every instance agrees
    std::map<const AstVar*, std::vector<V3VpiLazy::CombRun>> m_combRuns;
    // One instance of a PARTIAL variable whose instances differ.
    struct InstComb final {
        VVpiLazyComb m_comb;  // This instance's class
        std::vector<V3VpiLazy::CombRun> m_runs;  // Its masked bits, if PARTIAL
    };
    std::map<std::pair<std::string, const AstVar*>, InstComb> m_instComb;  // By scope name
    // Refresh func of a shadow's row in a scope other than its group's; see rowStub()
    std::map<std::pair<std::string, const AstVar*>, const AstCFunc*> m_rowRefresh;
    // A split variable's or its shadow's instances held by the other; see splitKeptInstances()
    std::set<std::pair<std::string, const AstVar*>> m_noRow;

    VVpiLazyComb combOf(const std::string& scopeName, const AstVar* varp) const {
        if (!varp->isVpiLazyCombPartial()) return varp->vpiLazyComb();
        const auto it = m_instComb.find({scopeName, varp});
        return it == m_instComb.end() ? VVpiLazyComb{VVpiLazyComb::PARTIAL} : it->second.m_comb;
    }
    const std::vector<V3VpiLazy::CombRun>& combRunsOf(const std::string& scopeName,
                                                      const AstVar* varp) const {
        const auto it = m_instComb.find({scopeName, varp});
        if (it != m_instComb.end()) return it->second.m_runs;
        const auto rit = m_combRuns.find(varp);
        UASSERT_OBJ(rit != m_combRuns.end(), varp, "--vpi-lazy masked variable has no runs");
        return rit->second;
    }
};

V3VpiLazyContext* V3VpiLazy::newContext() { return new V3VpiLazyContext; }
void V3VpiLazy::deleteContext(V3VpiLazyContext* ctxp) { delete ctxp; }

//######################################################################

namespace {

using InstComb = V3VpiLazyContext::InstComb;

bool storagePinnedElsewhere(const AstVar* varp) {
    if (varp->isPrimaryIO()) return true;
    if (varp->isForceable()) return true;
    return varp->isReadByDpi() || varp->isWrittenByDpi();
}

bool reconstructableKind(const AstVar* varp) {
    if (storagePinnedElsewhere(varp)) return false;
    AstNodeDType* leafp = varp->dtypeSkipRefp();
    while (AstUnpackArrayDType* const adtypep = VN_CAST(leafp, UnpackArrayDType)) {
        leafp = adtypep->subDTypep()->skipRefp();
    }
    return VN_IS(leafp, BasicDType) || leafp->isIntegralOrPacked();
}

// One partial write's footprint; idxs order need only be consistent between parts.
struct PartExtent final {
    std::vector<int32_t> idxs;  // Constant unpacked indices, last first
    int lsb = 0;  // First bit written within the element
    int width = 0;  // Bits written from lsb
};

// One combinational block as LazyGatherVisitor found it, before any optimisation.
struct CombBlock final {
    AstAlways* m_alwaysp = nullptr;  // The combo block
    AstScope* m_scopep = nullptr;  // Scope that authored the block
    AstAssignW* m_assignwp = nullptr;  // Lone AstAssignW of a CONT_ASSIGN block
    std::vector<AstVarScope*> m_targets;  // Written vars, encounter order
    std::unordered_map<const AstVarScope*, int> m_writeCount;  // Writes within this block
    std::vector<AstVarRef*> m_writeRefs;  // Its writing refs, encounter order
    // Constant-select footprint of each assign's LHS base ref, where partialLhsRef finds one
    std::unordered_map<const AstVarRef*, PartExtent> m_partialExts;
    std::vector<AstVarScope*> m_reads;  // Vars it reads, first-occurrence pre-order
    bool m_impure = false;  // Some node in it is unsafeToReexecute
};

class GroupVertex;

// See UNIT OF RECONSTRUCTION above.
struct Group final {
    AstScope* scopep = nullptr;  // Scope that authored the statements, unless anchored elsewhere
    std::vector<const CombBlock*> blockps;  // Its blocks, encounter order
    std::vector<AstVarScope*> targets;  // VPI candidates this group defines, encounter order
    std::vector<AstVarScope*> temps;  // Other variables it writes, encounter order
    std::unordered_set<AstVarScope*> members;  // targets and temps, for lookup
    std::vector<AstVarScope*> zeroInitps;  // Partial assembly: zero these shadows first
    AstVarScope* copyFromp = nullptr;  // Converted: refresh by copying this variable instead
    // targets[0]->varp(), cross-instance group identity; targets[0] itself if anchored elsewhere
    const AstNode* keyp = nullptr;
    AstCFunc* funcp = nullptr;  // Its reconstruct func, shared by every instance of keyp
    bool live = true;  // Cleared when the group is abandoned and its targets retained
    GroupVertex* vtxp = nullptr;  // Its vertex in the dependency graph, null once dead
};

class GroupVertex final : public V3GraphVertex {
    VL_RTTI_IMPL(GroupVertex, V3GraphVertex)
    Group* const m_groupp;  // The group this vertex orders

public:
    GroupVertex(V3Graph* graphp, Group* groupp)
        : V3GraphVertex{graphp}
        , m_groupp{groupp} {}
    Group* groupp() const { return m_groupp; }
};

// One constant-selected partial `assign` of a variable
struct PartWrite final {
    const CombBlock* m_blockp = nullptr;  // Its CONT_ASSIGN block
    PartExtent m_ext;  // The bits it writes
};

// Base and footprint of a constant-selected partial write (`base[3][c +: w] = rhs;`), else null.
AstVarRef* partialLhsRef(AstNodeExpr* lhsp, PartExtent& extr) {
    AstNodeExpr* nodep = lhsp;
    bool anySel = false;
    // Nested, as V3Const has not flattened them under -fno-const-before-dfg
    while (AstSel* const selp = VN_CAST(nodep, Sel)) {
        if (!VN_IS(selp->lsbp(), Const)) return nullptr;
        extr.lsb += selp->lsbConst();
        if (!anySel) extr.width = selp->widthConst();
        nodep = selp->fromp();
        anySel = true;
    }
    while (AstArraySel* const aselp = VN_CAST(nodep, ArraySel)) {
        const AstConst* const idxp = VN_CAST(aselp->bitp(), Const);
        if (!idxp) return nullptr;
        extr.idxs.push_back(static_cast<int32_t>(idxp->toSInt()));
        nodep = aselp->fromp();
        anySel = true;
    }
    if (!anySel) return nullptr;
    AstVarRef* const refp = VN_CAST(nodep, VarRef);
    if (!refp) return nullptr;
    if (!extr.width) extr.width = lhsp->dtypep()->skipRefp()->width();
    return refp;
}

AstVarScope* partialLhs(AstNodeExpr* lhsp, PartExtent& extr) {
    AstVarRef* const refp = partialLhsRef(lhsp, extr);
    return refp ? refp->varScopep() : nullptr;
}

// 'partialr' if a select leaves untouched bits, which are then read. Null if not a select chain.
AstVarRef* lhsBaseRef(AstNodeExpr* lhsp, bool& partialr) {
    partialr = false;
    for (AstNodeExpr* nodep = lhsp;;) {
        if (AstVarRef* const refp = VN_CAST(nodep, VarRef)) return refp;
        if (AstSel* const selp = VN_CAST(nodep, Sel)) {
            partialr = true;
            nodep = selp->fromp();
        } else if (AstArraySel* const aselp = VN_CAST(nodep, ArraySel)) {
            partialr = true;
            nodep = aselp->fromp();
        } else {
            return nullptr;
        }
    }
}

// Calls are exempt: isPredictOptimizable() is false for every AstNodeCCall only as V3Simulate
// cannot call one.
bool unsafeToReexecute(AstNode* nodep) {
    if (!nodep->isPure()) return true;
    return !nodep->isPredictOptimizable() && !VN_IS(nodep, NodeCCall);
}

// Some bits of one instance of a variable: flat element -> {lsb, width}
struct CombFootprint final {
    bool whole = false;  // Every bit; runsOf is then empty
    std::map<int32_t, std::vector<std::pair<int, int>>> runsOf;  // Else the bits, per element
};

// A mask names bits of a table row's integral elements; any other kind is all or nothing.
bool combMaskable(const AstVar* varp, std::vector<int32_t>& dimsr, int& elemWidthr) {
    const AstNodeDType* dtypep = varp->dtypeSkipRefp();
    while (const AstUnpackArrayDType* const adtypep = VN_CAST(dtypep, UnpackArrayDType)) {
        dimsr.push_back(adtypep->elementsConst());
        dtypep = adtypep->subDTypep()->skipRefp();
    }
    if (!dtypep->isIntegralOrPacked()) return false;
    elemWidthr = dtypep->width();
    return true;
}

// Row-major, as the storage is laid out; false unless the select names bits of one element.
bool combElement(const AstVar* varp, const PartExtent& ext, int32_t& elemr) {
    std::vector<int32_t> dims;
    int elemWidth = 0;
    if (!combMaskable(varp, dims, elemWidth)) return false;
    if (ext.idxs.size() != dims.size()) return false;
    if (ext.lsb < 0 || ext.width <= 0 || ext.lsb + ext.width > elemWidth) return false;
    int64_t flat = 0;
    for (size_t k = 0; k < dims.size(); ++k) {
        const int32_t idx = ext.idxs[dims.size() - 1 - k];
        if (idx < 0 || idx >= dims[k]) return false;
        flat = flat * dims[k] + idx;
        if (flat > std::numeric_limits<int32_t>::max()) return false;
    }
    elemr = static_cast<int32_t>(flat);
    return true;
}

// Keeps an element's runs sorted, disjoint and non-adjacent, as intersectBits needs.
void addBits(CombFootprint& fp, int32_t elem, int lsb, int width) {
    if (fp.whole) return;
    std::vector<std::pair<int, int>>& runs = fp.runsOf[elem];
    int lo = lsb;
    int hi = lsb + width;
    // Disjoint runs have ascending ends too
    const auto firstIt = std::lower_bound(
        runs.begin(), runs.end(), lsb,
        [](const std::pair<int, int>& run, int bit) { return run.first + run.second < bit; });
    auto lastIt = firstIt;
    for (; lastIt != runs.end() && lastIt->first <= hi; ++lastIt) {
        lo = std::min(lo, lastIt->first);
        hi = std::max(hi, lastIt->first + lastIt->second);
    }
    if (firstIt == lastIt) {
        runs.emplace(firstIt, lo, hi - lo);
        return;
    }
    *firstIt = {lo, hi - lo};
    runs.erase(firstIt + 1, lastIt);
}

// addBits keeps runs disjoint and non-adjacent, so a defined range lies within one run.
bool bitsDefined(const CombFootprint& fp, int32_t elem, int lsb, int width) {
    if (fp.whole) return true;
    const auto it = fp.runsOf.find(elem);
    if (it == fp.runsOf.end()) return false;
    return std::any_of(it->second.begin(), it->second.end(), [&](const std::pair<int, int>& run) {
        return run.first <= lsb && lsb + width <= run.first + run.second;
    });
}

// Pre-optimization walk: write/read counts per VarScope, and per-block write info.
class LazyGatherVisitor final : public VNVisitor {
    // NODE STATE
    //  AstVarScope::user1()  -> bool. Already in the current block's m_reads
public:
    // STATE
    std::unordered_map<const AstVarScope*, int> m_writeCount;  // Writes per var
    std::vector<AstVarScope*> m_writtenOrder;  // Vars with >=1 write, encounter order
    std::vector<CombBlock> m_combBlocks;  // Combo blocks, encounter order
    std::unordered_map<const AstVar*, std::vector<AstVarScope*>> m_vscpsOf;  // Its instances
    std::unordered_map<const AstVarScope*, std::vector<AstVarRef*>> m_refsOf;  // Its refs
    // Every VarScope in tree-encounter order; iterated by the completeness floor.
    std::vector<AstVarScope*> m_vscOrder;
    // Bits of VPI candidates any read may reach
    std::unordered_map<const AstVarScope*, CombFootprint> m_readBits;

private:
    AstScope* m_scopep = nullptr;  // Scope currently being descended
    CombBlock* m_blockp = nullptr;  // Block being gathered, while inside a combo always body
    const AstVarRef* m_selRefp = nullptr;  // Read whose constant select is being visited

    void checkPure(AstNode* nodep) {
        if (m_blockp && unsafeToReexecute(nodep)) m_blockp->m_impure = true;
    }

    // VISITORS
    void visit(AstVarRef* nodep) override {
        checkPure(nodep);
        AstVarScope* const vscp = nodep->varScopep();
        m_refsOf[vscp].push_back(nodep);
        if (!nodep->access().isReadOnly()) {
            if (m_writeCount[vscp]++ == 0) m_writtenOrder.push_back(vscp);
            if (m_blockp) {
                if (m_blockp->m_writeCount[vscp]++ == 0) m_blockp->m_targets.push_back(vscp);
                m_blockp->m_writeRefs.push_back(nodep);
            }
        }
        if (!nodep->access().isWriteOnly()) {
            if (nodep != m_selRefp && vscp->varp()->isSigVpiLazyCandidate()) {
                CombFootprint& fp = m_readBits[vscp];
                fp.whole = true;
                fp.runsOf.clear();
            }
            if (m_blockp && !vscp->user1SetOnce()) m_blockp->m_reads.push_back(vscp);
        }
        iterateChildren(nodep);
    }
    void visit(AstNodeAssign* nodep) override {
        checkPure(nodep);
        if (m_blockp) {
            PartExtent ext;
            if (const AstVarRef* const refp = partialLhsRef(nodep->lhsp(), ext))
                m_blockp->m_partialExts.emplace(refp, std::move(ext));
        }
        iterateChildren(nodep);
    }
    void visitSel(AstNodeExpr* nodep) {
        checkPure(nodep);
        PartExtent ext;
        const AstVarRef* const refp = partialLhsRef(nodep, ext);
        VL_RESTORER(m_selRefp);
        // An inner select of the same chain reads no less than this one
        if (refp && refp != m_selRefp && refp->access().isReadOnly()
            && refp->varp()->isSigVpiLazyCandidate()) {
            int32_t elem = 0;
            if (combElement(refp->varp(), ext, elem)) {
                m_selRefp = refp;
                addBits(m_readBits[refp->varScopep()], elem, ext.lsb, ext.width);
            }
        }
        iterateChildren(nodep);
    }
    void visit(AstSel* nodep) override { visitSel(nodep); }
    void visit(AstArraySel* nodep) override { visitSel(nodep); }
    void visit(AstActive* nodep) override {
        if (!nodep->hasCombo()) {
            iterateChildren(nodep);
            return;
        }
        // Same descent as the global counts, keeping the sole-driver equality exact.
        for (AstNode* stmtp = nodep->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
            AstAlways* const alwaysp = VN_CAST(stmtp, Always);
            if (!alwaysp) {  // e.g. AstCoverToggle under --coverage: not a lazy driver
                iterate(stmtp);
                continue;
            }
            // V3Active moved the sensitivity to the AstActive, so the body is all there is
            UASSERT_OBJ(!alwaysp->sentreep(), alwaysp, "--vpi-lazy combo block has a sentree");
            CombBlock block;
            block.m_alwaysp = alwaysp;
            block.m_scopep = m_scopep;
            {
                VL_RESTORER(m_blockp);
                m_blockp = &block;
                AstNode::user1ClearTree();
                iterateChildren(alwaysp);
            }
            if (block.m_targets.empty()) continue;
            if (alwaysp->keyword() == VAlwaysKwd::CONT_ASSIGN) {
                AstAssignW* const awp = VN_CAST(alwaysp->stmtsp(), AssignW);
                if (awp && !awp->nextp() && !awp->timingControlp()) block.m_assignwp = awp;
            }
            m_combBlocks.push_back(std::move(block));
        }
    }
    void visit(AstScope* nodep) override {
        VL_RESTORER(m_scopep);
        m_scopep = nodep;
        iterateChildren(nodep);
    }
    void visit(AstVarScope* nodep) override {
        m_vscpsOf[nodep->varp()].push_back(nodep);
        m_vscOrder.push_back(nodep);
        iterateChildren(nodep);
    }
    void visit(AstNode* nodep) override {
        checkPure(nodep);
        iterateChildren(nodep);
    }

public:
    // CONSTRUCTORS
    explicit LazyGatherVisitor(AstNetlist* nodep) {
        const VNUser1InUse user1InUse;
        iterate(nodep);
    }
};

class VpiLazyPreparer final {
    using Defined = std::unordered_set<AstVarScope*>;

    // STATE
    AstScope* const m_topScopep;  // Scope of the top module, which anchors cross-scope groups
    V3VpiLazyContext& m_ctx;  // Classification shared with V3EmitCSyms
    LazyGatherVisitor m_gather;  // The one netlist walk's findings

    int m_combBailRetained = 0;  // Group-bail / non-sole-driver / cycle retains

    std::vector<std::unique_ptr<Group>> m_groups;  // Formation order (deterministic)
    // Group::keyp -> the groups sharing it, one per instance
    std::unordered_map<const AstNode*, std::vector<Group*>> m_groupsOfKey;
    // Instances keeping their storage: RETAINED if VPI candidates, else PINNED (splitKept...)
    std::unordered_set<const AstVarScope*> m_kept;
    std::unordered_map<AstVarScope*, Group*> m_groupOf;  // Solely-written var -> its group
    // Group target -> its group and index in its 'targets'
    std::unordered_map<AstVarScope*, std::pair<Group*, size_t>> m_targetOf;
    // Copy sources promoted from temp to target; per AstVar, so every instance forms one shape
    std::unordered_set<const AstVar*> m_helperCandVars;
    std::unordered_set<const AstVarScope*> m_helperTargets;  // Committed helper targets
    int m_helperCount = 0;  // Helper targets reconstructed, per instance
    std::vector<Group*> m_copyGroups;  // Copies of a variable that holds storage
    std::vector<Group*> m_foldedCopies;  // Copies of another cone's target, sharing its shadow
    int m_foldedCount = 0;  // Folded copy rows, per instance, for stats
    int m_copyCount = 0;  // Copy descriptors, per instance, for stats
    // Converted target -> the variable its row copies, for cone operand substitution.
    std::unordered_map<AstVarScope*, AstVarScope*> m_retargetSrcOf;

    V3Graph m_depGraph;  // u -> v where v reads a variable u defines; vertices are GroupVertex

    std::vector<Group*> m_ordered;  // Topological order of reconstructed survivor groups
    std::vector<AstCFunc*> m_splitFuncps;  // Entry and body funcs, emission order

    FileLine* m_funcFlp = nullptr;  // Of every node emitted, the top scope's
    int m_reconstructed = 0;  // Reconstructed signals (per instance)
    int m_fallback = 0;  // Retained with storage (incl. group bails), snapshotted pre-emission
    uint32_t m_boundaryStorage = 0;  // Pinned only to feed a reconstruct function
    // Why each retained signal missed reconstruction.
    enum class Bail : uint8_t {
        MULTIDRIVEN,  // Written by more than one group, or outside any group
        DTYPE,  // Kind reconstruction cannot express (unpacked aggregate)
        PARTIAL_MIXED_WRITE,  // Partial-write target also has a full/comb/impure/var-lsb write
        PARTIAL_OVERLAP,  // Partial writes overlap, so no unambiguous assembly
        PARTIAL_GAP,  // Partial writes leave bits undriven, which a VPI put may write
        READ_BEFORE_WRITE,  // A group var is read before an unconditional full-width write
        LATCH,  // A target is not written on every path through the block
        IMPURE,  // The block has a side effect reconstruction must not repeat
        UNSUPPORTED_STMT,  // A statement kind the ordered walk does not model
        UNSUPPORTED_LVALUE,  // A continuous write whose shape a shadow cannot mirror
        COMB_CYCLE,  // Genuine combinational cycle (SCC member)
        COMPLETENESS_FLOOR,  // No classification path claimed it; retained so VPI still sees it
        BOUNDARY_COMB_DTYPE,  // Comb boundary operand of a kind reconstruction cannot express
        _COUNT
    };
    // METHODS
    // Returns 'cond', so a caller bails and returns in one line
    static bool bailIf(Bail& whyr, Bail why, bool cond) {
        if (cond) whyr = why;
        return cond;
    }
    static const char* bailName(Bail b) {
        static const char* const names[] = {"multidriven",
                                            "dtype",
                                            "partial mixed write",
                                            "partial overlap",
                                            "partial gap",
                                            "read before write",
                                            "latch",
                                            "impure",
                                            "unsupported statement",
                                            "unsupported lvalue",
                                            "comb cycle",
                                            "completeness floor",
                                            "boundary comb (dtype)"};
        static_assert(sizeof(names) / sizeof(names[0]) == static_cast<size_t>(Bail::_COUNT),
                      "Bail name table out of sync with enum");
        return names[static_cast<size_t>(b)];
    }
    std::array<int, static_cast<size_t>(Bail::_COUNT)> m_bailCount{};
    std::unordered_set<const AstVarScope*> m_combTargets;  // Built by hasCombDriver()
    bool m_combTargetsBuilt = false;  // m_combTargets is empty for a design with no comb block
    // Per-module member + per-instance VarScope, else N identically-named members collide.
    std::unordered_map<AstVar*, AstVar*> m_shadowVarOfOrig;  // per-module member dedup
    std::unordered_map<AstVarScope*, AstVarScope*> m_shadowOf;  // per-instance VarScope
    // One stamp-array member per module, not one apiece for thousands of groups.
    std::unordered_map<const AstNodeModule*, AstVar*> m_epochVarOfMod;  // makeStampVar
    std::unordered_map<const AstScope*, AstVarScope*> m_epochOfScope;  // stampFor
    // Per group key, so shared by every instance of its module.
    struct KeyInfo final {
        int gid = -1;  // Design-global id naming the emitted artefacts (gidOf)
        AstCFunc* funcp = nullptr;  // Reconstruct func shared by every instance
        int epochSlot = -1;  // Index into the module's stamp array (assignEpochSlots)
    };
    std::unordered_map<const AstNode*, KeyInfo> m_keyInfo;
    std::unordered_map<const Group*, AstCFunc*> m_instStubOf;  // instanceCallee
    std::map<std::pair<const AstNodeModule*, const Group*>, AstCFunc*> m_rowStubOf;  // rowStub
    int m_nextGid = 0;  // Next KeyInfo::gid
    int m_nextTempIdx = 0;  // Next temp shadow's name suffix

    std::map<std::string, int> m_floorReason;  // Floor residual shape -> instances, for stats
    std::unordered_map<const AstVarScope*, CombFootprint> m_combFootOf;
    std::unordered_set<const AstVar*> m_combFootVars;  // Variables of m_combFootOf keys
    std::vector<AstVar*> m_combFootOrder;  // m_combFootVars, encounter order
    int m_combWhole = 0;  // Read-only variables, per instance
    int m_combPartial = 0;  // Masked variables, per instance
    // Assembled from constant-select assigns, whose undriven bits only a VPI read reaches
    std::unordered_set<const AstVar*> m_gapVars;

public:
    VpiLazyPreparer(AstNetlist* nodep, AstScope* topScopep, V3VpiLazyContext& ctx)
        : m_topScopep{topScopep}
        , m_ctx{ctx}
        , m_gather{nodep} {}

    const std::vector<AstCFunc*>& splitFuncps() const { return m_splitFuncps; }
    void classifyOnly() { classifyCombDriven(); }

    void run() {
        classifyCombDriven();
        findHelperCandidates();
        formGroups();
        analyseGroups();
        anchorConsumersOfAnchored();
        buildDependencyGraph();
        splitCyclesRetainCores();
        topoOrderSurvivors();
        copyStoredSources();
        foldTrivialCopyGroups();
        emitReconstructions();
        retainCompletenessFloor();
        reportStats();
    }

private:
    // METHODS
    int instancesOf(const AstVar* varp) const {
        const auto it = m_gather.m_vscpsOf.find(varp);
        return it != m_gather.m_vscpsOf.end() ? static_cast<int>(it->second.size()) : 1;
    }

    int keyInstances(const Group* g) const {
        const AstVar* const varp = VN_CAST(g->keyp, Var);
        return varp ? instancesOf(varp) : 1;
    }

    int writeCountOf(const AstVarScope* vscp) const {
        const auto it = m_gather.m_writeCount.find(vscp);
        return it == m_gather.m_writeCount.end() ? 0 : it->second;
    }

    // Shadow member and lazy flag are per module: a shape is taken for every instance or none.
    bool claimPerVar(const std::unordered_map<const AstVar*, int>& tally,
                     const AstVar* varp) const {
        const auto it = tally.find(varp);
        return it != tally.end() && it->second == instancesOf(varp);
    }

    // After topoOrderSurvivors, only a copy or a fold clears 'live'.
    void dropFromOrdered() {
        m_ordered.erase(
            std::remove_if(m_ordered.begin(), m_ordered.end(), [](Group* g) { return !g->live; }),
            m_ordered.end());
    }

    Group* liveGroupOf(AstVarScope* u) const {
        const auto it = m_groupOf.find(u);
        if (it == m_groupOf.end()) return nullptr;
        return it->second->live ? it->second : nullptr;
    }

    // A converted target has no storage, so a cone reading it reads what its row copies. Both
    // conversions take a source of the target's layout and scope, which a multi-instance
    // group's reads are confined to, so the substitute is valid wherever the target is read.
    AstVarScope* retargetSubstituteFor(AstVarScope* u) const {
        const auto it = m_retargetSrcOf.find(u);
        return it == m_retargetSrcOf.end() ? nullptr : it->second;
    }

    bool hasCombDriver(AstVarScope* vscp) {
        if (!m_combTargetsBuilt) {
            for (const CombBlock& b : m_gather.m_combBlocks)
                for (AstVarScope* const t : b.m_targets) m_combTargets.insert(t);
            m_combTargetsBuilt = true;
        }
        return m_combTargets.count(vscp) != 0;
    }

    bool kept(const AstVarScope* vscp) const { return m_kept.count(vscp); }
    bool candidate(const AstVarScope* vscp) const {
        return vscp->varp()->isSigVpiLazyCandidate() && !kept(vscp);
    }

    void retainTarget(AstVarScope* target, Bail why) {
        // Holding storage regardless, or no VPI row to keep
        if (!target->varp()->isSigVpiLazyCandidate() || storagePinnedElsewhere(target->varp()))
            return;
        if (!m_kept.insert(target).second) return;
        UINFO(9, "vpi-lazy retained: " << bailName(why) << " " << target->name());
        ++m_combBailRetained;
        ++m_bailCount[static_cast<size_t>(why)];
    }

    // Returns 'cond', so a caller retains and returns in one line
    bool retainIf(AstVarScope* target, Bail why, bool cond) {
        if (cond) retainTarget(target, why);
        return cond;
    }

    // All-or-nothing per module: the func is shared, so a survivor gets the wrong instance.
    void killGroupsOfKey(const AstNode* keyp, Bail why) {
        const auto git = m_groupsOfKey.find(keyp);
        UASSERT_OBJ(git != m_groupsOfKey.end(), keyp, "--vpi-lazy group key has no groups");
        for (Group* const g : git->second) {
            if (!g->live) continue;
            g->live = false;
            for (AstVarScope* const t : g->targets) retainTarget(t, why);
        }
    }

    // METHODS - Writability

    // Explicit public_flat_rw, forceable and top-level input signals keep flat-rw semantics.
    static bool combCandidate(const AstVar* varp) {
        return varp->isSigVpiLazyCandidate() && !varp->isForceable() && !varp->isPrimaryInish();
    }

    CombFootprint& combFootprint(const AstVarScope* vscp) {
        AstVar* const varp = vscp->varp();
        const auto pr = m_combFootOf.emplace(vscp, CombFootprint{});
        if (pr.second && m_combFootVars.insert(varp).second) m_combFootOrder.push_back(varp);
        return pr.first->second;
    }

    // Null 'extp': a write the footprint cannot narrow, so the whole variable.
    void addCombWrite(const AstVarScope* vscp, const PartExtent* extp) {
        CombFootprint& fp = combFootprint(vscp);
        if (fp.whole) return;
        int32_t elem = 0;
        if (!extp || !combElement(vscp->varp(), *extp, elem)) {
            fp.whole = true;
            fp.runsOf.clear();
            return;
        }
        fp.runsOf[elem].emplace_back(extp->lsb, extp->width);
    }

    void addCombBits(const AstVarScope* vscp, const CombFootprint& bits) {
        CombFootprint& fp = combFootprint(vscp);
        if (fp.whole) return;
        if (bits.whole) {
            fp.whole = true;
            fp.runsOf.clear();
            return;
        }
        for (const auto& pr : bits.runsOf)
            for (const std::pair<int, int>& run : pr.second) fp.runsOf[pr.first].push_back(run);
    }

    // 1 or 0 if 'condp' is constant, else -1: what V3Const folds before prepare() unless
    // -fno-const-before-dfg, and V3Case's grouped `if (a | ... | 1'b1)`.
    static int constTruth(const AstNodeExpr* condp) {
        if (const AstVarRef* const refp = VN_CAST(condp, VarRef)) {
            const AstConst* const valuep = VN_CAST(refp->varp()->valuep(), Const);
            if (refp->varp()->isParam() && valuep) condp = valuep;
        }
        if (const AstConst* const constp = VN_CAST(condp, Const)) return constp->isZero() ? 0 : 1;
        if (condp->width() != 1) return -1;
        if (VN_IS(condp, Not) || VN_IS(condp, LogNot)) {
            const int truth = constTruth(VN_AS(condp, NodeUniop)->lhsp());
            return truth < 0 ? -1 : !truth;
        }
        const AstNodeBiop* const biopp = VN_CAST(condp, NodeBiop);
        if (!biopp) return -1;
        const int lhs = constTruth(biopp->lhsp());
        const int rhs = constTruth(biopp->rhsp());
        if (VN_IS(condp, Or) || VN_IS(condp, LogOr)) {
            if (lhs == 1 || rhs == 1) return 1;
            return lhs == 0 && rhs == 0 ? 0 : -1;
        }
        if (VN_IS(condp, And) || VN_IS(condp, LogAnd)) {
            if (lhs == 0 || rhs == 0) return 0;
            return lhs == 1 && rhs == 1 ? 1 : -1;
        }
        return -1;
    }

    static void unionBits(CombFootprint& dst, const CombFootprint& src) {
        if (dst.whole) return;
        if (src.whole) {
            dst.whole = true;
            dst.runsOf.clear();
            return;
        }
        for (const auto& pr : src.runsOf) {
            for (const std::pair<int, int>& run : pr.second)
                addBits(dst, pr.first, run.first, run.second);
        }
    }

    static CombFootprint intersectBits(const CombFootprint& a, const CombFootprint& b) {
        if (a.whole) return b;
        if (b.whole) return a;
        CombFootprint both;
        for (const auto& pr : a.runsOf) {
            const auto it = b.runsOf.find(pr.first);
            if (it == b.runsOf.end()) continue;
            std::vector<std::pair<int, int>> runs;
            auto xIt = pr.second.begin();
            auto yIt = it->second.begin();
            while (xIt != pr.second.end() && yIt != it->second.end()) {
                const int xEnd = xIt->first + xIt->second;
                const int yEnd = yIt->first + yIt->second;
                const int lo = std::max(xIt->first, yIt->first);
                const int hi = std::min(xEnd, yEnd);
                if (lo < hi) runs.emplace_back(lo, hi - lo);
                if (xEnd < yEnd) {
                    ++xIt;
                } else {
                    ++yIt;
                }
            }
            if (!runs.empty()) both.runsOf.emplace(pr.first, std::move(runs));
        }
        return both;
    }

    using DefinedBits = std::unordered_map<AstVarScope*, CombFootprint>;

    static DefinedBits intersectDefined(const DefinedBits& a, const DefinedBits& b) {
        const bool aSmaller = a.size() <= b.size();
        const DefinedBits& smallr = aSmaller ? a : b;
        const DefinedBits& larger = aSmaller ? b : a;
        DefinedBits both;
        for (const auto& pr : smallr) {
            const auto it = larger.find(pr.first);
            if (it == larger.end()) continue;
            CombFootprint bits = intersectBits(pr.second, it->second);
            if (bits.whole || !bits.runsOf.empty()) both.emplace(pr.first, std::move(bits));
        }
        return both;
    }

    static void unionDefined(DefinedBits& dst, DefinedBits&& src) {
        if (dst.empty()) {
            dst = std::move(src);
            return;
        }
        for (const auto& pr : src) unionBits(dst[pr.first], pr.second);
    }

    // Finds the bits every path through a block assigns. Arms only add, so
    // (D | then) & (D | else) == D | (then & else): each arm is walked from empty.
    // Both arms of a constant 'if' are walked, so a V3Const-folded branch reads the same.
    class LazyLatchVisitor final : public VNVisitorConst {
    public:
        DefinedBits m_defined;  // Bits assigned on every path so far
        // Full-width and constant-select assigns reached through ifs alone, the only writes
        // it decides
        std::unordered_set<const AstVarRef*> m_modelled;

    private:
        DefinedBits walkArm(AstNode* stmtsp) {
            VL_RESTORER_CLEAR(m_defined);
            iterateAndNextConstNull(stmtsp);
            DefinedBits armDefined;
            armDefined.swap(m_defined);
            return armDefined;
        }

        // VISITORS
        void visit(AstNodeAssign* nodep) override {
            PartExtent ext;
            int32_t elem = 0;
            if (AstVarRef* const refp = VN_CAST(nodep->lhsp(), VarRef)) {
                m_modelled.insert(refp);
                CombFootprint& fp = m_defined[refp->varScopep()];
                fp.whole = true;
                fp.runsOf.clear();
            } else if (AstVarRef* const prefp = partialLhsRef(nodep->lhsp(), ext)) {
                if (combElement(prefp->varp(), ext, elem)) {
                    m_modelled.insert(prefp);
                    addBits(m_defined[prefp->varScopep()], elem, ext.lsb, ext.width);
                }
            }
        }
        void visit(AstNodeIf* nodep) override {
            // An else-if chain is folded from its last 'else' up, iteratively
            std::vector<AstNodeIf*> chain{nodep};
            while (AstNodeIf* const nextp = VN_CAST(chain.back()->elsesp(), NodeIf)) {
                if (nextp->nextp()) break;
                chain.push_back(nextp);
            }
            DefinedBits delta = walkArm(chain.back()->elsesp());
            for (auto it = chain.rbegin(); it != chain.rend(); ++it) {
                DefinedBits thenDelta = walkArm((*it)->thensp());
                const int truth = constTruth((*it)->condp());
                if (truth == 1) {
                    delta = std::move(thenDelta);
                } else if (truth < 0) {
                    delta = intersectDefined(thenDelta, delta);
                }
            }
            unionDefined(m_defined, std::move(delta));
        }
        void visit(AstNode*) override {}  // Writes under any other statement stay unmodelled

    public:
        explicit LazyLatchVisitor(AstNode* stmtsp) { iterateAndNextConstNull(stmtsp); }
    };

    struct LatchProof final {
        DefinedBits defined;  // Bits assigned on every path; a target's others are a latch's
        Defined unprovable;  // Targets whose every write is combinational
    };

    // Purity and read order do not matter here, so the answer does not depend on how V3Split
    // partitioned the block. A target written any other way, as under a loop or jump, is not
    // proven: the safe direction.
    static LatchProof proveLatches(const CombBlock& b) {
        LatchProof proof;
        const VAlwaysKwd kwd = b.m_alwaysp->keyword();
        if (kwd == VAlwaysKwd::ALWAYS_LATCH) return proof;
        LazyLatchVisitor latch{kwd == VAlwaysKwd::CONT_ASSIGN ? nullptr : b.m_alwaysp->stmtsp()};
        proof.defined = std::move(latch.m_defined);
        for (const AstVarRef* const refp : b.m_writeRefs)
            if (!latch.m_modelled.count(refp)) proof.unprovable.insert(refp->varScopep());
        return proof;
    }

    // See WRITABILITY above.
    void classifyCombDriven() {
        for (const AstVarScope* const vscp : m_gather.m_vscOrder)
            vscp->varp()->vpiLazyComb(VVpiLazyComb::NONE);
        for (const CombBlock& b : m_gather.m_combBlocks) {
            if (std::none_of(b.m_targets.begin(), b.m_targets.end(),
                             [](const AstVarScope* t) { return combCandidate(t->varp()); }))
                continue;
            const LatchProof proof = proveLatches(b);
            Defined proven;
            for (AstVarRef* const refp : b.m_writeRefs) {
                AstVarScope* const vscp = refp->varScopep();
                if (!combCandidate(vscp->varp())) continue;
                if (proof.unprovable.count(vscp)) {
                    const auto it = b.m_partialExts.find(refp);
                    addCombWrite(vscp, it == b.m_partialExts.end() ? nullptr : &it->second);
                    continue;
                }
                // Every bit defined on every path has a write, so the union of writes is these
                const auto it = proof.defined.find(vscp);
                if (it != proof.defined.end() && proven.insert(vscp).second)
                    addCombBits(vscp, it->second);
            }
        }
        // V3Const made 'assign v = CONST' an initial plus a decl value, but it still drives v
        for (const AstVarScope* const vscp : m_gather.m_vscOrder) {
            AstVar* const varp = vscp->varp();
            if (combCandidate(varp) && varp->isContinuously() && varp->isConst() && varp->valuep()
                && !varp->isParam())
                addCombWrite(vscp, nullptr);
        }
        for (AstVar* const varp : m_combFootOrder)
            finishCombFootprint(varp, m_gather.m_vscpsOf.at(varp));
    }

    // Merged runs covering every bit of every element are the whole variable, and have none.
    static InstComb mergedFootprint(const AstVar* varp, CombFootprint& fp) {
        std::vector<V3VpiLazy::CombRun> runs;
        if (!fp.whole) {
            std::vector<int32_t> dims;
            int elemWidth = 0;
            combMaskable(varp, dims, elemWidth);
            uint64_t elements = 1;
            for (const int32_t d : dims) {
                elements *= static_cast<uint64_t>(d);
                if (elements > fp.runsOf.size()) break;
            }
            bool full = elements == fp.runsOf.size();
            for (auto& pr : fp.runsOf) {
                std::vector<std::pair<int, int>>& parts = pr.second;
                std::sort(parts.begin(), parts.end());
                const size_t first = runs.size();
                for (const std::pair<int, int>& part : parts) {
                    const uint32_t lsb = static_cast<uint32_t>(part.first);
                    const uint32_t width = static_cast<uint32_t>(part.second);
                    V3VpiLazy::CombRun* const lastp = runs.size() > first ? &runs.back() : nullptr;
                    if (lastp && lsb <= lastp->lsb + lastp->width) {
                        lastp->width = std::max(lastp->width, lsb + width - lastp->lsb);
                    } else {
                        runs.push_back({static_cast<uint32_t>(pr.first), lsb, width});
                    }
                }
                if (runs.size() != first + 1 || runs.back().lsb != 0
                    || runs.back().width != static_cast<uint32_t>(elemWidth))
                    full = false;
            }
            fp.whole = full;
        }
        if (fp.whole) return InstComb{VVpiLazyComb::WHOLE, {}};
        return InstComb{VVpiLazyComb::PARTIAL, std::move(runs)};
    }

    void countComb(VVpiLazyComb comb, int instances) {
        if (comb == VVpiLazyComb::WHOLE) m_combWhole += instances;
        if (comb == VVpiLazyComb::PARTIAL) m_combPartial += instances;
    }

    // Instances alike share the variable's class. Otherwise each keeps its own, as each has its
    // own row, and PARTIAL keeps the storage the writable ones need.
    void finishCombFootprint(AstVar* varp, const std::vector<AstVarScope*>& vscps) {
        std::vector<InstComb> insts;
        for (const AstVarScope* const vscp : vscps) {
            const auto it = m_combFootOf.find(vscp);
            insts.push_back(it == m_combFootOf.end() ? InstComb{VVpiLazyComb::NONE, {}}
                                                     : mergedFootprint(varp, it->second));
        }
        const InstComb& firstr = insts.front();
        if (std::all_of(insts.begin(), insts.end(), [&](const InstComb& ic) {
                return ic.m_comb == firstr.m_comb && ic.m_runs == firstr.m_runs;
            })) {
            varp->vpiLazyComb(firstr.m_comb);
            countComb(firstr.m_comb, instancesOf(varp));
            if (firstr.m_comb == VVpiLazyComb::PARTIAL)
                m_ctx.m_combRuns.emplace(varp, std::move(insts.front().m_runs));
            return;
        }
        varp->vpiLazyComb(VVpiLazyComb::PARTIAL);
        for (size_t i = 0; i < vscps.size(); ++i) {
            countComb(insts[i].m_comb, 1);
            m_ctx.m_instComb.emplace(std::make_pair(vscps[i]->scopep()->name(), varp),
                                     std::move(insts[i]));
        }
    }

    VVpiLazyComb combOf(const AstVarScope* vscp) const {
        return m_ctx.combOf(vscp->scopep()->name(), vscp->varp());
    }

    // METHODS - Group formation

    static AstVarScope* partialWriteBase(const CombBlock& b, PartExtent& extr) {
        if (!b.m_assignwp) return nullptr;
        if (!b.m_assignwp->rhsp()->isPure()) return nullptr;
        return partialLhs(b.m_assignwp->lhsp(), extr);
    }

    // A write from another scope is one instance's own; the module's own code is every one's.
    bool multidriven(const std::unordered_set<const AstVarScope*>& notSole, AstVarScope* w,
                     const AstScope* writerp) const {
        if (w->scopep() != writerp) return notSole.count(w);
        const std::vector<AstVarScope*>& vscps = m_gather.m_vscpsOf.at(w->varp());
        return std::any_of(vscps.begin(), vscps.end(),
                           [&](AstVarScope* vscp) { return notSole.count(vscp); });
    }

    Group* makeGroup(AstScope* scopep, std::vector<const CombBlock*>&& blockps,
                     const std::vector<AstVarScope*>& written,
                     const std::unordered_map<const AstVarScope*, int>& groupWrites,
                     const std::unordered_set<const AstVarScope*>& notSole) {
        // Writes into one other, single-instance scope, but for the writer's own temps, anchor the
        // group there: its one func reads the writer's variables absolute. Any other write outside
        // the writer, or a read outside one with several instances, anchors it in the top scope,
        // which addresses them all absolute, and a row elsewhere refreshes through a rowStub().
        AstScope* const writerp = scopep;
        const auto foreign = [&](const AstVarScope* vscp) { return vscp->scopep() != writerp; };
        const auto it = std::find_if(written.begin(), written.end(), foreign);
        if (it == written.end()) {
            if (instancesOf(written[0]->varp()) > 1
                && std::any_of(blockps.begin(), blockps.end(), [&](const CombBlock* bp) {
                       return std::any_of(bp->m_reads.begin(), bp->m_reads.end(), foreign);
                   }))
                scopep = m_topScopep;
        } else {
            AstScope* const anchorp = (*it)->scopep();
            const auto writerTemp = [&](AstVarScope* w) {
                return w->scopep() == writerp && !candidate(w)
                       && !m_helperCandVars.count(w->varp());
            };
            scopep = std::all_of(written.begin(), written.end(),
                                 [&](AstVarScope* w) {
                                     return writerTemp(w)
                                            || (w->scopep() == anchorp
                                                && instancesOf(w->varp()) == 1);
                                 })
                         ? anchorp
                         : m_topScopep;
        }
        std::vector<AstVarScope*> targets;
        std::vector<AstVarScope*> temps;
        std::vector<AstVarScope*> soleTemps;
        for (AstVarScope* const w : written) {
            AstVar* const varp = w->varp();
            const auto wit = groupWrites.find(w);
            UASSERT_OBJ(wit != groupWrites.end(), w,
                        "--vpi-lazy group writes a variable it did not count");
            const bool sole = writeCountOf(w) == wit->second;
            if (multidriven(notSole, w, writerp)) {
                retainTarget(w, Bail::MULTIDRIVEN);
            } else if (!candidate(w)) {
                // A temp, unless a VPI-visible copy reads it: then a "helper target" with a
                // shadow, and no row of its own.
                if (m_helperCandVars.count(varp)) {
                    targets.push_back(w);
                    m_helperTargets.insert(w);
                    continue;
                }
            } else if (!reconstructableKind(varp)) {
                retainTarget(w, Bail::DTYPE);
            } else {
                targets.push_back(w);
                continue;
            }
            temps.push_back(w);
            if (sole) soleTemps.push_back(w);
        }
        if (targets.empty()) return nullptr;
        auto ownp = std::make_unique<Group>();
        Group* const g = ownp.get();
        g->scopep = scopep;
        g->blockps = std::move(blockps);
        g->targets = targets;
        g->temps = temps;
        g->members.insert(targets.begin(), targets.end());
        g->members.insert(temps.begin(), temps.end());
        g->keyp = targets[0]->varp();
        if (std::any_of(targets.begin(), targets.end(),
                        [&](const AstVarScope* t) { return t->scopep() != scopep; }))
            g->keyp = targets[0];
        for (size_t i = 0; i < targets.size(); ++i) {
            m_groupOf[targets[i]] = g;
            m_targetOf[targets[i]] = {g, i};
        }
        // Only a solely-written temp may be read through another group's shadow copy.
        for (AstVarScope* const t : soleTemps) m_groupOf.emplace(t, g);
        m_groups.push_back(std::move(ownp));
        m_groupsOfKey[g->keyp].push_back(g);
        return g;
    }

    // A parameter is a static member, which a row cannot address by offset.
    static bool canCopyFrom(const AstVarScope* dstp, const AstVarScope* srcp) {
        return dstp->scopep() == srcp->scopep() && reconstructableKind(dstp->varp())
               && !srcp->varp()->isParam() && sameLayout(dstp, srcp);
    }

    // A group temp has no shadow, so another block reading it pins its storage; a helper target
    // gives it one. Not a block's own temps: promoting a conditionally written one bails a latch.
    void findHelperCandidates() {
        for (const CombBlock& b : m_gather.m_combBlocks) {
            for (const AstVarScope* const r : b.m_reads) {
                const AstVar* const varp = r->varp();
                if (varp->isSigVpiLazyCandidate()) continue;
                if (b.m_writeCount.count(r)) continue;
                if (reconstructableKind(varp)) m_helperCandVars.insert(varp);
            }
        }
    }

    void formGroups() {
        const std::vector<CombBlock>& blocks = m_gather.m_combBlocks;
        // Pass 1: partial-write sets, and (per AstVar, so instances agree) the multi-group writes.
        std::unordered_map<AstVarScope*, std::vector<PartWrite>> partsOf;
        struct WInfo final {
            int m_blocks = 0;  // Blocks writing this var
            int m_sum = 0;  // Their combined write count
            bool m_allParts = true;  // Every one is a partial write of this var
        };
        std::unordered_map<const AstVarScope*, WInfo> winfo;
        std::vector<AstVarScope*> partialBase(blocks.size(), nullptr);
        for (size_t i = 0; i < blocks.size(); ++i) {
            const CombBlock& b = blocks[i];
            PartExtent ext;
            AstVarScope* const basep = partialWriteBase(b, ext);
            partialBase[i] = basep;
            if (basep) partsOf[basep].push_back(PartWrite{&b, std::move(ext)});
            for (AstVarScope* const w : b.m_targets) {
                const auto cit = b.m_writeCount.find(w);
                UASSERT_OBJ(cit != b.m_writeCount.end(), w,
                            "--vpi-lazy block target has no write count");
                WInfo& wi = winfo[w];
                ++wi.m_blocks;
                wi.m_sum += cit->second;
                if (basep != w) wi.m_allParts = false;
            }
        }
        std::unordered_set<const AstVarScope*> notSole;
        for (const auto& pr : winfo) {
            const WInfo& wi = pr.second;
            const bool sole
                = wi.m_sum == writeCountOf(pr.first) && (wi.m_blocks == 1 || wi.m_allParts);
            if (!sole) notSole.insert(pr.first);
        }
        // Anything written outside a combinational block entirely has no group to define it.
        for (AstVarScope* const w : m_gather.m_writtenOrder)
            if (!winfo.count(w)) notSole.insert(w);

        // Pass 2: form the groups, in block-encounter order.
        const std::unordered_set<const AstVar*> gapRead = gapReadVars();
        std::unordered_set<AstVarScope*> partialDone;
        for (size_t i = 0; i < blocks.size(); ++i) {
            const CombBlock& b = blocks[i];
            if (AstVarScope* const basep = partialBase[i]) {
                if (!partialDone.insert(basep).second) continue;  // merged at first encounter
                const auto pit = partsOf.find(basep);
                UASSERT_OBJ(pit != partsOf.end(), basep,
                            "--vpi-lazy partial-write base has no recorded parts");
                formPartialGroup(basep, pit->second, b.m_scopep, notSole, gapRead);
                continue;
            }
            if (AstAssignW* const awp = b.m_assignwp) {
                AstNodeExpr* const lhsp = awp->lhsp();
                if (VN_IS(lhsp, VarRef)) {
                    makeGroup(b.m_scopep, {&b}, b.m_targets, b.m_writeCount, notSole);
                    continue;
                }
                // A write shape the shadow cannot mirror: retain rather than let it be dropped.
                bool partial = false;
                if (const AstVarRef* const basep2 = lhsBaseRef(lhsp, partial))
                    retainTarget(basep2->varScopep(), Bail::UNSUPPORTED_LVALUE);
                continue;
            }
            makeGroup(b.m_scopep, {&b}, b.m_targets, b.m_writeCount, notSole);
        }
    }

    // Masked variables some read, in the design or a cone, may reach the undriven bits of.
    // Per variable, as the shadow and its row are per module.
    std::unordered_set<const AstVar*> gapReadVars() const {
        std::unordered_set<const AstVar*> readVars;
        for (const auto& pr : m_gather.m_readBits) {
            const AstVar* const varp = pr.first->varp();
            if (!varp->isVpiLazyCombPartial() || readVars.count(varp)) continue;
            const auto cit = m_ctx.m_combRuns.find(varp);
            if (pr.second.whole || cit == m_ctx.m_combRuns.end()) {  // Or instances differ
                readVars.insert(varp);
                continue;
            }
            CombFootprint driven;
            for (const V3VpiLazy::CombRun& run : cit->second)
                addBits(driven, static_cast<int32_t>(run.elem), static_cast<int>(run.lsb),
                        static_cast<int>(run.width));
            for (const auto& epr : pr.second.runsOf) {
                for (const std::pair<int, int>& run : epr.second)
                    if (!bitsDefined(driven, epr.first, run.first, run.second))
                        readVars.insert(varp);
            }
        }
        return readVars;
    }

    // Disjoint partial `assign`s have no full-width driver but assemble exactly. Bits none drives
    // stay in the shadow, holding a put, unless a read other than VPI's may reach them.
    void formPartialGroup(AstVarScope* basep, const std::vector<PartWrite>& parts,
                          AstScope* scopep, const std::unordered_set<const AstVarScope*>& notSole,
                          const std::unordered_set<const AstVar*>& gapRead) {
        AstVar* const varp = basep->varp();
        if (!candidate(basep) && !m_helperCandVars.count(varp)) return;
        if (retainIf(basep, Bail::DTYPE, !reconstructableKind(varp))) return;
        // A full / procedural / impure / variable-range write exists too.
        if (retainIf(basep, Bail::PARTIAL_MIXED_WRITE,
                     static_cast<int>(parts.size()) != writeCountOf(basep)
                         || multidriven(notSole, basep, scopep)))
            return;
        // Overlapping writes are multidriven: assembly would depend on encounter order. Bucketed
        // by element index, then LSB-sorted so only adjacent pairs need testing.
        const size_t depth = parts[0].m_ext.idxs.size();
        std::map<std::vector<int32_t>, std::vector<const PartExtent*>> byElem;
        for (const PartWrite& pw : parts) {
            UASSERT_OBJ(pw.m_ext.idxs.size() == depth, basep,
                        "--vpi-lazy: V3Slice leaves partial writes at one depth");
            byElem[pw.m_ext.idxs].push_back(&pw.m_ext);
        }
        for (auto& pr : byElem) {
            std::vector<const PartExtent*>& bucket = pr.second;
            std::sort(
                bucket.begin(), bucket.end(),
                [](const PartExtent* ap, const PartExtent* bp) { return ap->lsb < bp->lsb; });
            for (size_t i = 1; i < bucket.size(); ++i) {
                if (retainIf(basep, Bail::PARTIAL_OVERLAP,
                             bucket[i]->lsb < bucket[i - 1]->lsb + bucket[i - 1]->width))
                    return;
            }
        }
        if (combOf(basep) == VVpiLazyComb::PARTIAL) {
            if (retainIf(basep, Bail::PARTIAL_GAP, gapRead.count(varp))) return;
            m_gapVars.insert(varp);
        }
        const std::unordered_map<const AstVarScope*, int> groupWrites{
            {basep, static_cast<int>(parts.size())}};
        std::vector<const CombBlock*> blockps;
        blockps.reserve(parts.size());
        for (const PartWrite& pw : parts) blockps.push_back(pw.m_blockp);
        makeGroup(scopep, std::move(blockps), {basep}, groupWrites, notSole);
    }

    // METHODS - Group analysis

    // True if 'fp' names every bit of 'varp'; then remembered as whole, so decided once.
    static bool fullyDefined(CombFootprint& fp, const AstVar* varp) {
        if (fp.whole) return true;
        std::vector<int32_t> dims;
        int elemWidth = 0;
        if (!combMaskable(varp, dims, elemWidth)) return false;
        uint64_t elements = 1;
        for (const int32_t d : dims) elements *= static_cast<uint64_t>(d);
        if (fp.runsOf.size() != elements) return false;
        for (const auto& pr : fp.runsOf) {
            if (pr.second.size() != 1 || pr.second[0].first != 0
                || pr.second[0].second != elemWidth)
                return false;
        }
        fp.whole = true;
        fp.runsOf.clear();
        return true;
    }

    // One ordered walk over a group's statements: see UNIT OF RECONSTRUCTION above. Per bit, so
    // `a[1] = f(a[0])` reads only what it already wrote.
    class LazyReadOrderVisitor final : public VNVisitorConst {
        using ArmDefs = std::vector<std::pair<AstVarScope*, CombFootprint>>;

        const Group* const m_groupp;  // Group whose statements are walked
        // Group var bits the prefix wrote on every path; conditionals intersect
        DefinedBits& m_definedr;
        Bail& m_whyr;  // Why the walk failed, its first failure only
        ArmDefs m_undo;  // Each var the current arm changed, as it was before the arm
        std::unordered_set<const AstVarScope*> m_undoSet;  // m_undo's vars, for lookup
        const AstVarRef* m_skipp = nullptr;  // An assignment's LHS base ref, checked apart
        bool m_inExpr = false;  // Scanning an expression's reads, not walking statements

    public:
        bool m_ok = true;  // No statement bailed
        std::vector<AstVarScope*> m_assembledps;  // Vars first defined in part, encounter order

    private:
        // Records the first failure; returns 'cond', so a caller bails and returns in one line
        bool bailIf(Bail why, bool cond) {
            if (cond && m_ok) {
                m_ok = false;
                m_whyr = why;
            }
            return cond;
        }
        CombFootprint& changing(AstVarScope* vscp) {
            CombFootprint& fp = m_definedr[vscp];
            if (m_undoSet.insert(vscp).second) m_undo.emplace_back(vscp, fp);
            return fp;
        }
        void defineWhole(AstVarScope* vscp) {
            CombFootprint& fp = changing(vscp);
            fp.whole = true;
            fp.runsOf.clear();
        }
        void defineBits(AstVarScope* vscp, int32_t elem, int lsb, int width) {
            CombFootprint& fp = changing(vscp);
            if (!fp.whole && fp.runsOf.empty()
                && std::find(m_assembledps.begin(), m_assembledps.end(), vscp)
                       == m_assembledps.end())
                m_assembledps.push_back(vscp);
            addBits(fp, elem, lsb, width);
        }
        bool member(const AstVarRef* refp) const {
            return m_groupp->members.count(refp->varScopep()) != 0;
        }
        void scanReads(AstNode* nodep) {
            VL_RESTORER(m_inExpr);
            m_inExpr = true;
            iterateAndNextConstNull(nodep);
        }
        // Walks the arm from what the prefix defined, then restores that and returns what the
        // arm left defined of each var it changed, so an if costs its arms' writes alone.
        ArmDefs walkArm(AstNode* stmtsp, AstNode* contsp = nullptr) {
            VL_RESTORER_CLEAR(m_undo);
            VL_RESTORER_CLEAR(m_undoSet);
            iterateAndNextConstNull(stmtsp);
            iterateAndNextConstNull(contsp);
            for (std::pair<AstVarScope*, CombFootprint>& pr : m_undo)
                std::swap(m_definedr[pr.first], pr.second);
            ArmDefs armDefs;
            armDefs.swap(m_undo);
            return armDefs;
        }
        // A constant select of a group var reads only its own bits.
        void visitSel(AstNodeExpr* nodep) {
            if (!m_ok) return;
            PartExtent ext;
            int32_t elem = 0;
            const AstVarRef* const refp = partialLhsRef(nodep, ext);
            if (refp && refp != m_skipp && !refp->access().isWriteOnly() && member(refp)
                && combElement(refp->varp(), ext, elem)) {
                bailIf(Bail::READ_BEFORE_WRITE,
                       !bitsDefined(m_definedr[refp->varScopep()], elem, ext.lsb, ext.width));
                return;
            }
            iterateChildrenConst(nodep);
        }

        // VISITORS
        void visit(AstNodeAssign* nodep) override {
            if (!m_ok) return;  // The first failure decides; the rest is not worth walking
            UASSERT_OBJ(!m_inExpr, nodep,
                        "--vpi-lazy: V3LiftExpr leaves no assignment in an expression");
            // V3Active rewrote '<=' and V3Force lowered AssignForce; only blocking/cont remain.
            UASSERT_OBJ(VN_IS(nodep, Assign) || VN_IS(nodep, AssignW), nodep,
                        "--vpi-lazy: unexpected assignment kind in a combinational block");
            // Only --timing keeps a delay this far, and such a block never terminates: untested.
            if (bailIf(Bail::UNSUPPORTED_STMT, VL_UNCOVERABLE(nodep->timingControlp())))
                return;  // LCOV_EXCL_LINE
            bool partial = false;
            AstVarRef* const baserefp = lhsBaseRef(nodep->lhsp(), partial);
            if (bailIf(Bail::UNSUPPORTED_STMT, !baserefp)) return;
            AstVarScope* const basep = baserefp->varScopep();
            // The gather counted every write under this block, so its write set is members
            UASSERT_OBJ(m_groupp->members.count(basep), nodep,
                        "--vpi-lazy: group members miss a write of their own block");
            {
                VL_RESTORER(m_skipp);
                m_skipp = baserefp;
                scanReads(nodep->rhsp());
                scanReads(nodep->lhsp());
            }
            PartExtent ext;
            int32_t elem = 0;
            if (!partial) {
                defineWhole(basep);
            } else if (partialLhsRef(nodep->lhsp(), ext)
                       && combElement(basep->varp(), ext, elem)) {
                defineBits(basep, elem, ext.lsb, ext.width);
            }  // Else no bit is provably defined; the untouched ones keep what they had
        }
        void visit(AstVarRef* nodep) override {
            if (!m_ok || nodep == m_skipp || nodep->access().isWriteOnly() || !member(nodep))
                return;
            bailIf(Bail::READ_BEFORE_WRITE,
                   !fullyDefined(m_definedr[nodep->varScopep()], nodep->varp()));
        }
        void visit(AstSel* nodep) override { visitSel(nodep); }
        void visit(AstArraySel* nodep) override { visitSel(nodep); }
        void visit(AstNodeIf* nodep) override {
            if (!m_ok) return;
            scanReads(nodep->condp());
            const ArmDefs thenDefs = walkArm(nodep->thensp());
            const ArmDefs elseDefs = walkArm(nodep->elsesp());
            std::unordered_map<const AstVarScope*, const CombFootprint*> elseOf;
            for (const auto& pr : elseDefs) elseOf.emplace(pr.first, &pr.second);
            for (const auto& pr : thenDefs) {
                const auto it = elseOf.find(pr.first);
                if (it != elseOf.end()) changing(pr.first) = intersectBits(pr.second, *it->second);
            }
        }
        // May run zero times, so it defines nothing on exit.
        void visit(AstLoop* nodep) override { walkArm(nodep->stmtsp(), nodep->contsp()); }
        void visit(AstLoopTest* nodep) override { scanReads(nodep->condp()); }
        // A jump may skip the tail: define nothing
        void visit(AstJumpBlock* nodep) override { walkArm(nodep->stmtsp()); }
        void visit(AstJumpGo*) override {}
        void visit(AstComment*) override {}
        void visit(AstNode* nodep) override {
            // V3Table and friends may leave odd shapes
            if (bailIf(Bail::UNSUPPORTED_STMT, !m_inExpr)) return;
            iterateChildrenConst(nodep);
        }

    public:
        LazyReadOrderVisitor(const Group* groupp, DefinedBits& definedr, Bail& whyr)
            : m_groupp{groupp}
            , m_definedr{definedr}
            , m_whyr{whyr} {
            for (const CombBlock* const bp : groupp->blockps)
                iterateAndNextConstNull(bp->m_alwaysp->stmtsp());
        }
    };

    bool definesDriven(CombFootprint& fp, const AstVar* varp) const {
        if (!m_gapVars.count(varp)) return fullyDefined(fp, varp);
        const std::vector<V3VpiLazy::CombRun>& runs = m_ctx.m_combRuns.at(varp);
        return std::all_of(runs.begin(), runs.end(), [&](const V3VpiLazy::CombRun& run) {
            return bitsDefined(fp, static_cast<int32_t>(run.elem), static_cast<int>(run.lsb),
                               static_cast<int>(run.width));
        });
    }

    // A var first defined in part is assembled into a zeroed shadow, but for its undriven bits.
    bool analyseGroup(Group* g, Bail& whyr) const {
        for (const CombBlock* const bp : g->blockps)
            if (bailIf(whyr, Bail::IMPURE, bp->m_impure)) return false;
        DefinedBits defined;
        LazyReadOrderVisitor walk{g, defined, whyr};
        if (!walk.m_ok) return false;
        for (AstVarScope* const t : g->targets) {
            // Not written on every path
            if (bailIf(whyr, Bail::LATCH, !definesDriven(defined[t], t->varp()))) return false;
        }
        for (AstVarScope* const u : walk.m_assembledps)
            if (!m_gapVars.count(u->varp())) g->zeroInitps.push_back(u);
        return true;
    }

    void analyseGroups() {
        for (const auto& ownp : m_groups) {
            Group* const g = ownp.get();
            if (!g->live) continue;
            Bail why = Bail::UNSUPPORTED_STMT;
            if (!analyseGroup(g, why)) killGroupsOfKey(g->keyp, why);
        }
    }

    // METHODS - Scheduling

    // A func shared by every instance cannot call the one instance's func that an operand group
    // anchored elsewhere has, so is anchored in the top scope too: one func per instance.
    void anchorConsumersOfAnchored() {
        for (bool changed = true; changed;) {
            changed = false;
            for (const auto& ownp : m_groups) {
                const Group* const g = ownp.get();
                if (!g->live || keyInstances(g) <= 1) continue;
                const auto elsewhere = [&](AstVarScope* vscp) {
                    const Group* const ugp = liveGroupOf(vscp);
                    return ugp && ugp->scopep != g->scopep;
                };
                bool bad = false;
                for (const CombBlock* const bp : g->blockps)
                    bad = bad || std::any_of(bp->m_reads.begin(), bp->m_reads.end(), elsewhere);
                if (!bad) continue;
                const auto kit = m_groupsOfKey.find(g->keyp);
                const std::vector<Group*> groups = std::move(kit->second);
                m_groupsOfKey.erase(kit);
                for (Group* const instp : groups) {
                    instp->scopep = m_topScopep;
                    instp->keyp = instp->targets[0];
                    m_groupsOfKey[instp->keyp].push_back(instp);
                }
                changed = true;
            }
        }
    }

    // u defines a variable v reads: edge u -> v.
    void buildDependencyGraph() {
        for (const auto& ownp : m_groups) {
            Group* const g = ownp.get();
            g->vtxp = g->live ? new GroupVertex{&m_depGraph, g} : nullptr;
        }
        for (const auto& ownp : m_groups) {
            Group* const g = ownp.get();
            if (!g->live) continue;
            for (const CombBlock* const bp : g->blockps) {
                for (AstVarScope* const u : bp->m_reads) {
                    if (g->members.count(u)) continue;
                    Group* const ugp = liveGroupOf(u);
                    if (!ugp || ugp == g) continue;
                    new V3GraphEdge{&m_depGraph, ugp->vtxp, g->vtxp, 1};
                }
            }
        }
        m_depGraph.removeRedundantEdgesMax(&V3GraphEdge::followAlwaysTrue);
    }

    // A cycle between groups need not be one between bits. Merged into the first, its blocks run
    // in encounter order, and analyseGroup proves every read follows its write.
    bool mergeCycle(const std::vector<Group*>& sccps) {
        Group* const g = sccps[0];
        Group merged;
        merged.scopep = g->scopep;
        size_t members = 0;
        for (const Group* const ugp : sccps) {
            if (ugp->scopep != g->scopep) return false;  // One func addresses one scope
            merged.blockps.insert(merged.blockps.end(), ugp->blockps.begin(), ugp->blockps.end());
            merged.targets.insert(merged.targets.end(), ugp->targets.begin(), ugp->targets.end());
            merged.members.insert(ugp->members.begin(), ugp->members.end());
            members += ugp->members.size();
        }
        // A var two of them write has no one order the model is known to share
        if (merged.members.size() != members) return false;
        // Every CombBlock is an element of one vector, so address order is encounter order
        std::sort(merged.blockps.begin(), merged.blockps.end());
        Bail why = Bail::COMB_CYCLE;
        if (!analyseGroup(&merged, why)) return false;
        g->blockps = std::move(merged.blockps);
        g->members = std::move(merged.members);
        g->zeroInitps = std::move(merged.zeroInitps);
        for (size_t i = 1; i < sccps.size(); ++i) {
            Group* const ugp = sccps[i];
            for (AstVarScope* const t : ugp->targets) {
                m_targetOf[t] = {g, g->targets.size()};
                m_groupOf[t] = g;
                g->targets.push_back(t);
            }
            for (AstVarScope* const t : ugp->temps) {
                const auto it = m_groupOf.find(t);
                if (it != m_groupOf.end() && it->second == ugp) it->second = g;
                g->temps.push_back(t);
            }
            ugp->live = false;
        }
        return true;
    }

    // Greedy feedback vertex: the member on the most paths through its SCC
    static Group* cycleCut(const std::vector<Group*>& sccps) {
        Group* cutp = nullptr;
        size_t best = 0;
        for (Group* const g : sccps) {
            const uint32_t color = g->vtxp->color();
            size_t in = 0;
            size_t out = 0;
            for (const V3GraphEdge& edge : g->vtxp->inEdges())
                in += edge.fromp()->color() == color;
            for (const V3GraphEdge& edge : g->vtxp->outEdges())
                out += edge.top()->color() == color;
            if (!cutp || in * out > best) {
                cutp = g;
                best = in * out;
            }
        }
        return cutp;
    }

    // A group downstream of a cycle still reconstructs cold, so only SCC members are retained.
    // An SCC that does not merge loses one group, retained, and what remains is retried.
    void splitCyclesRetainCores() {
        while (true) {
            m_depGraph.stronglyConnected(&V3GraphEdge::followAlwaysTrue);
            std::map<uint32_t, std::vector<Group*>> sccOf;  // Non-zero color: a multi-group SCC
            for (const auto& ownp : m_groups) {
                Group* const g = ownp.get();
                if (g->live && g->vtxp->color() != 0) sccOf[g->vtxp->color()].push_back(g);
            }
            if (sccOf.empty()) return;
            for (const auto& pr : sccOf) {
                const std::vector<Group*>& sccps = pr.second;
                if (!mergeCycle(sccps)) killGroupsOfKey(cycleCut(sccps)->keyp, Bail::COMB_CYCLE);
            }
            // Merged and killed groups leave the graph
            m_depGraph.clear();
            buildDependencyGraph();
        }
    }

    // Kahn topo-sort, preferring a ready group in the previous group's scope. Not GraphStream: it
    // resumes after the last returned vertex, not the newest ready group; order names the shadows.
    void topoOrderSurvivors() {
        std::vector<Group*> live;
        for (const auto& ownp : m_groups)
            if (ownp->live) live.push_back(ownp.get());
        std::unordered_map<Group*, size_t> inDegree;
        for (Group* const g : live) inDegree[g] = g->vtxp->inEdges().size();
        std::unordered_map<const AstScope*, std::vector<Group*>> readyOf;  // lookup only
        std::vector<AstScope*> scopeQueue;  // Scopes that (re)gained ready groups, encounter order
        const auto pushReady = [&](Group* g) {
            std::vector<Group*>& stack = readyOf[g->scopep];
            if (stack.empty()) scopeQueue.push_back(g->scopep);
            stack.push_back(g);
        };
        for (Group* const g : live)
            if (inDegree[g] == 0) pushReady(g);
        const AstScope* curScopep = nullptr;
        size_t scopeQi = 0;
        while (true) {
            Group* up = nullptr;
            if (curScopep) {
                std::vector<Group*>& stack = readyOf[curScopep];
                if (!stack.empty()) {
                    up = stack.back();
                    stack.pop_back();
                }
            }
            if (!up) {
                while (scopeQi < scopeQueue.size() && readyOf[scopeQueue[scopeQi]].empty())
                    ++scopeQi;
                if (scopeQi == scopeQueue.size()) break;
                curScopep = scopeQueue[scopeQi];
                std::vector<Group*>& stack = readyOf[curScopep];
                up = stack.back();
                stack.pop_back();
            }
            m_ordered.push_back(up);
            for (const V3GraphEdge& edge : up->vtxp->outEdges()) {
                Group* const v = static_cast<const GroupVertex*>(edge.top())->groupp();
                if (--inDegree[v] == 0) pushReady(v);
            }
        }
        // splitCyclesRetainCores() left a DAG of live vertices only
        for (Group* const g : live) {
            UASSERT_OBJ(!inDegree[g], g->keyp, "--vpi-lazy group left unordered");
        }
    }

    // Commits to a storage variable, not a group, so no later phase can invalidate it.
    void copyStoredSources() {
        std::vector<Group*> cand;
        std::unordered_map<const AstVar*, int> candInstances;
        // Recorded even when refused, so a refused link does not hide that storage from below.
        std::unordered_map<const Group*, AstVarScope*> chainEnd;
        // Topological order, so a source's own chain is resolved before anything reads it.
        for (Group* const g : m_ordered) {
            AstVarScope* u = soleCopySource(g);
            if (!u) continue;
            AstVarScope* const targetp = g->targets[0];
            // A helper target's cone exists only to be copied; converting it leaves it unread.
            if (m_helperTargets.count(targetp)) continue;
            const auto tit = m_targetOf.find(u);
            if (tit != m_targetOf.end()) {
                const auto cit = chainEnd.find(tit->second.first);
                if (cit != chainEnd.end()) u = cit->second;
            }
            // The source must hold storage, and nothing in a live group does.
            if (liveGroupOf(u)) continue;
            chainEnd.emplace(g, u);
            if (u == targetp || !canCopyFrom(targetp, u)) continue;
            cand.push_back(g);
            ++candInstances[targetp->varp()];
        }
        for (Group* const g : cand) {
            AstVarScope* const targetp = g->targets[0];
            if (!claimPerVar(candInstances, targetp->varp())) continue;
            const auto cit = chainEnd.find(g);
            UASSERT_OBJ(cit != chainEnd.end(), targetp->varp(),
                        "--vpi-lazy copy candidate has no resolved source");
            g->copyFromp = cit->second;
            g->live = false;
            m_retargetSrcOf.emplace(targetp, g->copyFromp);
            m_copyGroups.push_back(g);
        }
        dropFromOrdered();
    }

    // Reads pre-optimisation statements, so a width change appears as a Cast/Extend and is
    // refused: memcpy cannot convert.
    AstVarScope* soleCopySource(const Group* g) const {
        if (g->targets.size() != 1 || !g->temps.empty() || g->blockps.size() != 1) return nullptr;
        // Another scope's write may differ per instance
        if (g->blockps[0]->m_scopep != g->targets[0]->scopep()) return nullptr;
        const AstNodeAssign* const asgnp = VN_CAST(g->blockps[0]->m_alwaysp->stmtsp(), NodeAssign);
        if (!asgnp || asgnp->nextp()) return nullptr;
        const AstVarRef* const lhsp = VN_CAST(asgnp->lhsp(), VarRef);
        const AstVarRef* const rhsp = VN_CAST(asgnp->rhsp(), VarRef);
        if (!lhsp || !rhsp || lhsp->varScopep() != g->targets[0]) return nullptr;
        return rhsp->varScopep();
    }

    // Layouts must match exactly: the descriptor refreshes by memcpy of totalSize() bytes.
    // entSize() has no width for VLVT_REAL or VLVT_STRING, so such a row would copy nothing,
    // and a std::string could not be raw-copied even if it did; those stay cones.
    static bool sameLayout(const AstVarScope* a, const AstVarScope* b) {
        const AstNodeDType* const adtp = a->varp()->dtypep()->skipRefp();
        const AstNodeDType* const bdtp = b->varp()->dtypep()->skipRefp();
        return !a->varp()->isDouble() && !a->varp()->isString()
               && a->varp()->vlEnumType() == b->varp()->vlEnumType()
               && adtp->widthTotalBytes() == bdtp->widthTotalBytes()
               && (adtp->similarDType(bdtp)
                   // `bit` and `logic` of one width are stored alike
                   || (VN_IS(adtp, BasicDType) && VN_IS(bdtp, BasicDType)
                       && adtp->width() == bdtp->width()));
    }

    void foldTrivialCopyGroups() {
        // Topological order, so a chain resolves to a source that is not itself folded.
        std::unordered_map<const AstVar*, int> foldable;  // Instances of a key that can fold
        for (Group* const g : m_ordered) {
            AstVarScope* u = soleCopySource(g);
            if (!u) continue;
            if (AstVarScope* const srcp = retargetSubstituteFor(u)) u = srcp;
            const Group* const ugp = liveGroupOf(u);
            // m_groupOf covers temps too, and only a target has a shadow with a func to call
            if (!ugp || ugp == g || !m_targetOf.count(u)) continue;
            if (ugp->copyFromp) u = ugp->copyFromp;  // Source folded too; chase it
            // srcOffset is from the target's own selfp, so the source must be the same instance.
            if (!sameLayout(g->targets[0], u) || u->scopep() != g->targets[0]->scopep()) continue;
            ++foldable[g->targets[0]->varp()];
            g->copyFromp = u;
        }
        // m_ordered order, not foldable's, so what is emitted does not depend on pointer hashing
        for (Group* const g : m_ordered) {
            if (!g->copyFromp) continue;
            // One instance could not fold: none may. Instances fold alike, so this is untested.
            // LCOV_EXCL_START
            if (VL_UNCOVERABLE(!claimPerVar(foldable, g->targets[0]->varp()))) {
                g->copyFromp = nullptr;
                continue;
            }  // LCOV_EXCL_STOP
            // Killing it makes the retarget safe: a consumer that cannot substitute pins instead.
            m_retargetSrcOf.emplace(g->targets[0], g->copyFromp);
            m_foldedCopies.push_back(g);
            g->live = false;
        }
        dropFromOrdered();
    }

    // METHODS - Emission

    // Design-global group id, shared by every instance of the group's module.
    int gidOf(const Group* g) {
        int& gid = m_keyInfo[g->keyp].gid;
        if (gid < 0) gid = m_nextGid++;
        return gid;
    }

    std::string reconFuncName(const Group* g) {
        return std::string{RECONSTRUCT_FUNC_NAME} + "__" + std::to_string(gidOf(g));
    }

    std::string reconBodyFuncName(const Group* g) {
        return std::string{RECONSTRUCT_BODY_FUNC_NAME} + "__" + std::to_string(gidOf(g));
    }

    // tableFacing: its address goes in a VlLazyReconEntry, whose refreshp is void(*)(void*), so
    // it takes the self pointer untyped. Not isStatic: V3Descope reads that as "no self pointer"
    // and would descope every reference absolutely, pinning one instance into a shared func.
    AstCFunc* newReconFunc(AstScope* scopep, const std::string& name, bool tableFacing) const {
        AstCFunc* const funcp = new AstCFunc{m_funcFlp, name, scopep, ""};
        funcp->isStatic(false);
        funcp->isLoose(true);
        if (tableFacing) funcp->voidSelf(true);
        funcp->slow(true);
        // A table-facing func's only caller is the syms recon-fn array, which no pass can see.
        funcp->entryPoint(true);
        // One func serves every instance: V3Gate/V3Dfg must not substitute instance expressions.
        funcp->vpiLazyReconstruct(true);
        funcp->declPrivate(false);
        scopep->addBlocksp(funcp);
        return funcp;
    }

    AstCFunc* newCallStub(AstScope* scopep, const Group* g) {
        AstCFunc* const stubp = newReconFunc(
            scopep, std::string{RECONSTRUCT_INST_FUNC_NAME} + "__" + std::to_string(gidOf(g)),
            true);
        AstCCall* const callp = new AstCCall{m_funcFlp, g->funcp};
        callp->dtypeSetVoid();
        stubp->addStmtsp(callp->makeStmt());
        return stubp;
    }

    // V3Descope takes a call's self pointer from its callee's scope, which for a shared func is
    // the representative's. A stub in the operand's own scope gets the call that instance's
    // self pointer; V3Descope then points the call at the shared func and deletes the stub.
    AstCFunc* instanceCallee(const Group* ugp) {
        if (ugp->funcp->scopep() == ugp->scopep) return ugp->funcp;
        AstCFunc*& stubp = m_instStubOf[ugp];
        if (!stubp) {
            stubp = newCallStub(ugp->scopep, ugp);
            stubp->vpiLazyInstStub(true);
        }
        return stubp;
    }

    // A row is refreshed with its own instance's self pointer, so a row outside an anchored
    // group's scope calls a stub of its own module, which calls the func absolute.
    AstCFunc* rowStub(AstScope* scopep, const Group* g) {
        AstCFunc*& stubp = m_rowStubOf[{scopep->modp(), g}];
        if (!stubp) stubp = newCallStub(scopep, g);
        return stubp;
    }

    // Slots per module over m_ordered; arrays are created in first-encounter module order.
    void assignEpochSlots() {
        std::unordered_map<const AstNodeModule*, size_t> idxOfMod;
        std::vector<std::pair<AstNodeModule*, int>> slotsOfMod;
        for (Group* const g : m_ordered) {
            AstNodeModule* const modp = g->scopep->modp();
            const auto pair = idxOfMod.emplace(modp, slotsOfMod.size());
            if (pair.second) slotsOfMod.emplace_back(modp, 0);
            int& slot = m_keyInfo[g->keyp].epochSlot;
            if (slot < 0) slot = slotsOfMod[pair.first->second].second++;
        }
        for (const auto& pr : slotsOfMod) pr.first->addStmtsp(makeStampVar(pr.first, pr.second));
    }

    // Freshness stamps, per instance: a shared slot would mark instance B fresh after A ran.
    // MODULETEMP being isTemp() is what forces the zero initializer, even under
    // --x-initial unique.
    AstVar* makeStampVar(AstNodeModule* modp, int slots) {
        FileLine* const flp = modp->fileline();
        AstUnpackArrayDType* const dtypep = new AstUnpackArrayDType{
            flp, modp->findUInt64DType(), new AstRange{flp, slots - 1, 0}};
        v3Global.rootp()->typeTablep()->addTypesp(dtypep);
        AstVar* const varp = new AstVar{flp, VVarType::MODULETEMP, EPOCH_NAME, dtypep};
        varp->trace(false);
        varp->vpiLazyRole(VVpiLazyRole::STAMP);
        m_epochVarOfMod.emplace(modp, varp);
        return varp;
    }

    // Per-instance VarScope for the stamp array, so the guard can reference it as an AstVarRef.
    AstVarScope* stampFor(Group* g) {
        AstScope* const scopep = g->scopep;
        const auto it = m_epochOfScope.find(scopep);
        if (it != m_epochOfScope.end()) return it->second;
        const auto mit = m_epochVarOfMod.find(scopep->modp());
        UASSERT_OBJ(mit != m_epochVarOfMod.end(), scopep->modp(),
                    "--vpi-lazy module has no stamp array");
        AstVar* const varp = mit->second;
        AstVarScope* const vscp = new AstVarScope{varp->fileline(), scopep, varp};
        scopep->addVarsp(vscp);
        m_epochOfScope.emplace(scopep, vscp);
        return vscp;
    }

    AstNodeExpr* newStaleCheck(AstVarScope* epochVscp, int slot) {
        AstCExpr* const exprp = new AstCExpr{m_funcFlp, "vlSymsp->__Vm_lazy.stale(", 1};
        exprp->add(new AstArraySel{m_funcFlp,
                                   new AstVarRef{m_funcFlp, epochVscp, VAccess::READWRITE}, slot});
        exprp->add(")");
        return exprp;
    }

    AstVarScope* attachShadow(AstVarScope* origp, AstVar* shadowVarp, bool isNew) {
        if (isNew) {
            shadowVarp->trace(false);
            // A VPI-facing shadow stays a member; V3Localize may take a temp
            if (!shadowVarp->isLazyReconstructTemp()) shadowVarp->sigPublic(true);
            origp->scopep()->modp()->addStmtsp(shadowVarp);
            m_shadowVarOfOrig.emplace(origp->varp(), shadowVarp);
        }
        // One shadow VarScope per instance scope, sharing the module's member.
        AstVarScope* const shadowVscp
            = new AstVarScope{origp->varp()->fileline(), origp->scopep(), shadowVarp};
        origp->scopep()->addVarsp(shadowVscp);
        m_shadowOf.emplace(origp, shadowVscp);
        return shadowVscp;
    }

    // origp's shadow, else its module's shadow member attached to origp's scope, else null.
    AstVarScope* reuseShadow(AstVarScope* origp) {
        const auto it = m_shadowOf.find(origp);
        if (it != m_shadowOf.end()) return it->second;
        const auto vit = m_shadowVarOfOrig.find(origp->varp());
        return vit != m_shadowVarOfOrig.end() ? attachShadow(origp, vit->second, false) : nullptr;
    }

    AstVarScope* shadowForTarget(Group* g, size_t slot) {
        const int gid = gidOf(g);
        AstVarScope* const origp = g->targets[slot];
        if (AstVarScope* const vscp = reuseShadow(origp)) return vscp;
        return newTargetShadow(origp,
                               SHADOW_PREFIX + std::to_string(gid) + "_" + std::to_string(slot));
    }

    AstVarScope* newTargetShadow(AstVarScope* origp, const std::string& name) {
        AstVar* const origVarp = origp->varp();
        AstVar* const shadowVarp
            = new AstVar{origVarp->fileline(), VVarType::MODULETEMP, name, origVarp->dtypep()};
        shadowVarp->origName(origVarp->name());  // VPI-facing name
        // A helper target emits no VPI row of its own, only a shadow for its copies to read.
        shadowVarp->vpiLazyRole(m_helperTargets.count(origp) ? VVpiLazyRole::SHADOW_HELPER
                                                             : VVpiLazyRole::SHADOW);
        // Read-safe metadata only: the RW/lazy/forceable flags change how passes treat the shadow.
        shadowVarp->direction(origVarp->direction());
        shadowVarp->declDirection(origVarp->declDirection());
        shadowVarp->isContinuously(origVarp->isContinuously());
        shadowVarp->lazyShadowNet(origVarp->isNet());
        return attachShadow(origp, shadowVarp, true);
    }

    // Shadow of a non-target group variable: plain cold storage, no origName, so no VPI row.
    AstVarScope* shadowForTemp(AstVarScope* origp) {
        if (AstVarScope* const vscp = reuseShadow(origp)) return vscp;
        AstVar* const origVarp = origp->varp();
        AstVar* const shadowVarp
            = new AstVar{origVarp->fileline(), VVarType::MODULETEMP,
                         std::string{SHADOW_PREFIX} + "t" + std::to_string(m_nextTempIdx++),
                         origVarp->dtypep()};
        shadowVarp->vpiLazyRole(VVpiLazyRole::SHADOW_TEMP);
        return attachShadow(origp, shadowVarp, true);
    }

    // A target is written by its own group alone, so the map names the right group.
    AstVarScope* shadowForMember(AstVarScope* u) {
        const auto it = m_targetOf.find(u);
        return it != m_targetOf.end() ? shadowForTarget(it->second.first, it->second.second)
                                      : shadowForTemp(u);
    }

    // An AstAssignW must never sit under a CFunc, so continuous assigns are cloned as blocking.
    static AstNode* cloneBody(const Group* g) {
        AstNode* bodyp = nullptr;
        for (const CombBlock* const bp : g->blockps) {
            for (AstNode* stmtp = bp->m_alwaysp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
                AstNode* clonep;
                if (const AstAssignW* const awp = VN_CAST(stmtp, AssignW)) {
                    clonep = new AstAssign{awp->fileline(), awp->lhsp()->cloneTree(false),
                                           awp->rhsp()->cloneTree(false)};
                } else {
                    clonep = stmtp->cloneTree(false);
                }
                bodyp = AstNode::addNext(bodyp, clonep);
            }
        }
        return bodyp;
    }

    // The cone must read the variable, not a driver expression: every instance's if 'shared' by
    // them, else only u, as a func anchored elsewhere reads it absolute.
    void pinBoundary(AstVarScope* u, bool shared) {
        AstVar* const uVarp = u->varp();
        if (uVarp->isPrimaryIO() || uVarp->isSigUserRWPublic() || kept(u)) return;
        if (uVarp->isSigUserRdPublic()) {
            // Retaining would arm the write gate on a row that refuses writes.
            UASSERT_OBJ(!uVarp->isSigVpiLazyCandidate(), uVarp, "public_flat_rd is still lazy");
            return;
        }
        const bool cand = uVarp->isSigVpiLazyCandidate();
        // Holds storage regardless, so the completeness floor retains it.
        if (cand && !hasCombDriver(u)) return;
        for (AstVarScope* const vscp :
             shared ? m_gather.m_vscpsOf.at(uVarp) : std::vector<AstVarScope*>{u}) {
            if (!m_kept.insert(vscp).second) continue;
            if (!cand) {  // No RTL name, so no row: --public-flat-rw would not have one either.
                ++m_boundaryStorage;
                continue;
            }
            // A bailed group's targets are retained and a converted one is substituted
            UASSERT_OBJ(!reconstructableKind(uVarp), u,
                        "--vpi-lazy comb boundary operand no skip path explains");
            const Bail why = Bail::BOUNDARY_COMB_DTYPE;
            UINFO(9, "vpi-lazy retained: " << bailName(why) << " " << vscp->name());
            ++m_fallback;
            ++m_bailCount[static_cast<size_t>(why)];
        }
    }

    // Redirects a group's body to shadows; no re-typing, a shadow keeps its dtype. Pre-order, so
    // the cone operands are refreshed in the order the body first reads them.
    class LazyConeRewireVisitor final : public VNVisitor {
        VpiLazyPreparer& m_prep;  // Owns the shadows and group maps
        Group* const m_groupp;  // Group whose cloned body is rewired
        std::unordered_set<Group*> m_seenOps;  // m_coneOps, for lookup

    public:
        std::vector<Group*> m_coneOps;  // Reconstructed operand groups, first-read order

    private:
        void redirect(AstVarRef* refp, AstVarScope* vscp) {
            refp->varScopep(vscp);
            refp->varp(vscp->varp());
        }

        // VISITORS
        void visit(AstVarRef* nodep) override {
            AstVarScope* u = nodep->varScopep();
            if (m_groupp->members.count(u)) {  // Read or written by this group
                redirect(nodep, m_prep.shadowForMember(u));
                return;
            }
            if (AstVarScope* const srcp = m_prep.retargetSubstituteFor(u)) {
                u = srcp;
                redirect(nodep, srcp);
            }
            Group* const ugp = m_prep.liveGroupOf(u);
            if (ugp && ugp != m_groupp) {
                // Operand is reconstructed too: read its shadow, calling its func to freshen.
                UASSERT_OBJ(ugp->funcp, m_groupp->keyp,
                            "--vpi-lazy cone operand ordered after its consumer");
                redirect(nodep, m_prep.shadowForMember(u));
                if (m_seenOps.insert(ugp).second) m_coneOps.push_back(ugp);
                return;
            }
            m_prep.pinBoundary(u, m_prep.keyInstances(m_groupp) > 1);
        }
        void visit(AstNode* nodep) override { iterateChildren(nodep); }

    public:
        LazyConeRewireVisitor(VpiLazyPreparer& prep, Group* groupp, AstNode* bodyp)
            : m_prep{prep}
            , m_groupp{groupp} {
            // The body is a detached list, and iterateAndNext needs its head to have a back
            for (AstNode* stmtp = bodyp; stmtp; stmtp = stmtp->nextp()) iterate(stmtp);
        }
    };

    // Added to the tree at once, so remapped clones' dtypep() links survive V3Dead's dtype GC.
    void emitReconstructions() {
        m_fallback = m_combBailRetained;
        m_funcFlp = m_topScopep->fileline();
        assignEpochSlots();
        // Every instance needs its own shadow VarScope for its descriptor.
        for (Group* const g : m_ordered) {
            for (size_t slot = 0; slot < g->targets.size(); ++slot) shadowForTarget(g, slot);
        }
        for (Group* const g : m_ordered) {
            KeyInfo& key = m_keyInfo[g->keyp];
            if (key.funcp) {
                g->funcp = key.funcp;
                continue;  // non-representative instance: share the func
            }
            emitReconFunc(g, key);
        }
        emitCopyRows(m_copyGroups, false);
        emitCopyRows(m_foldedCopies, true);
    }

    void emitReconFunc(Group* g, KeyInfo& key) {
        AstCFunc* const funcp = newReconFunc(g->scopep, reconFuncName(g), true);
        g->funcp = funcp;
        key.funcp = funcp;
        m_splitFuncps.push_back(funcp);
        bindRowRefresh(g, funcp);
        AstNode* const bodyp = cloneBody(g);
        const LazyConeRewireVisitor rewire{*this, g, bodyp};
        AstIf* const guardp = newEpochGuard(g, key.epochSlot);
        funcp->addStmtsp(guardp);
        AstCFunc* const bodyFuncp = splitBodyFunc(g, guardp, bodyp);
        const auto addBodyStmt = [&](AstNode* stmtp) {
            if (bodyFuncp) {
                bodyFuncp->addStmtsp(stmtp);
            } else {
                guardp->addThensp(stmtp);
            }
        };
        // Refresh the operand cone; topo order guarantees each operand's func exists.
        for (Group* const ugp : rewire.m_coneOps) {
            AstCCall* const callp = new AstCCall{m_funcFlp, instanceCallee(ugp)};
            callp->dtypeSetVoid();
            addBodyStmt(callp->makeStmt());
        }
        for (AstVarScope* const u : g->zeroInitps) addBodyStmt(newZeroShadow(u));
        addBodyStmt(bodyp);
        moveRowsToShadows(g);
    }

    // What V3EmitCSyms routes a row's refreshp to, here and on any fold of this shadow
    void bindRowRefresh(Group* g, AstCFunc* funcp) {
        for (AstVarScope* const t : g->targets) {
            const auto tit = m_shadowOf.find(t);
            UASSERT_OBJ(tit != m_shadowOf.end(), t->varp(),
                        "--vpi-lazy reconstruct target has no shadow");
            AstVar* const shadowVarp = tit->second->varp();
            if (t->scopep() == g->scopep) {
                shadowVarp->lazyReconFuncp(funcp);
            } else {
                m_ctx.m_rowRefresh.emplace(std::make_pair(t->scopep()->name(), shadowVarp),
                                           rowStub(t->scopep(), g));
            }
        }
    }

    // Not an early return: split-cfuncs may move the body elsewhere.
    AstIf* newEpochGuard(Group* g, int epochSlot) {
        return new AstIf{m_funcFlp, newStaleCheck(stampFor(g), epochSlot)};
    }

    // The guard cannot move with the body, so a large body moves to a func the guard calls;
    // /4 slack for the optimizer growing it. Returns that func, or nullptr if not split.
    AstCFunc* splitBodyFunc(Group* g, AstIf* guardp, const AstNode* bodyp) {
        const int splitAt = v3Global.opt.outputSplitCFuncs();
        if (!splitAt) return nullptr;
        int nodes = 0;
        for (const AstNode* sp = bodyp; sp; sp = sp->nextp()) nodes += sp->nodeCount();
        if (nodes < splitAt / 4) return nullptr;
        AstCFunc* const bodyFuncp = newReconFunc(g->scopep, reconBodyFuncName(g), false);
        m_splitFuncps.push_back(bodyFuncp);
        AstCCall* const bodyCallp = new AstCCall{m_funcFlp, bodyFuncp};
        bodyCallp->dtypeSetVoid();
        guardp->addThensp(bodyCallp->makeStmt());
        return bodyFuncp;
    }

    // A partial assembly builds its shadow up from zero
    AstAssign* newZeroShadow(AstVarScope* u) {
        AstVarScope* const shadowp = shadowForMember(u);
        AstVar* const shadowVarp = shadowp->varp();
        AstNodeDType* const dtypep = shadowVarp->dtypep();
        AstNodeExpr* zerop;
        if (VN_IS(dtypep->skipRefp(), UnpackArrayDType)) {
            // No whole-array Const exists; CReset is V3's array clear.
            zerop = new AstCReset{m_funcFlp, shadowVarp, /*constructing*/ false};
        } else {
            AstConst* const constp
                = new AstConst{m_funcFlp, V3Number{m_funcFlp, dtypep->width(), 0}};
            constp->dtypep(dtypep);
            zerop = constp;
        }
        return new AstAssign{m_funcFlp, new AstVarRef{m_funcFlp, shadowp, VAccess::WRITE}, zerop};
    }

    // The shadows carry the original signals' VPI presence.
    void moveRowsToShadows(Group* g) {
        for (AstVarScope* const t : g->targets) {
            if (m_helperTargets.count(t)) {
                ++m_helperCount;  // Never lazy-flagged; read only by the copies of it
                continue;
            }
            if (m_gapVars.count(t->varp())) moveMaskToShadow(t);
            m_reconstructed += keyInstances(g);
        }
    }

    // The undriven bits a put may write are now the shadow's.
    void moveMaskToShadow(AstVarScope* t) {
        AstVar* const varp = t->varp();
        AstVar* const shadowVarp = m_shadowOf.at(t)->varp();
        if (shadowVarp->isVpiLazyCombPartial()) return;  // Another instance moved it
        shadowVarp->vpiLazyComb(VVpiLazyComb::PARTIAL);
        m_ctx.m_combRuns.emplace(shadowVarp, m_ctx.m_combRuns.at(varp));
    }

    // Copy rows: a shadow and a descriptor source, no func, no epoch slot. A copy names the
    // stored source; a fold's shadow aliases the source cone's, whose func its row calls.
    void emitCopyRows(const std::vector<Group*>& groups, bool folded) {
        for (Group* const g : groups) {
            UASSERT_OBJ(!kept(g->targets[0]), g->targets[0],
                        "--vpi-lazy converted target pinned, not substituted");
            AstVar* srcVarp;
            if (folded) {
                const auto sit = m_shadowOf.find(g->copyFromp);
                UASSERT_OBJ(sit != m_shadowOf.end(), g->copyFromp->varp(),
                            "--vpi-lazy folded copy source has no shadow");
                srcVarp = sit->second->varp();
                UASSERT_OBJ(
                    srcVarp->lazyReconFuncp()
                        || m_ctx.m_rowRefresh.count({g->copyFromp->scopep()->name(), srcVarp}),
                    srcVarp, "--vpi-lazy folded copy source has no reconstruct func");
                ++m_foldedCount;
            } else {
                pinBoundary(g->copyFromp, false);  // As the cone this row replaced would have
                srcVarp = g->copyFromp->varp();
                ++m_copyCount;
            }
            AstVar* const shadowVarp = shadowForTarget(g, 0)->varp();
            UASSERT_OBJ(!shadowVarp->lazyCopySrc() || shadowVarp->lazyCopySrc() == srcVarp,
                        shadowVarp, "--vpi-lazy copy instances disagree on their source");
            shadowVarp->lazyCopySrc(srcVarp);
            if (shadowVarp->isLazyShadowAlias()) shadowVarp->noReset(true);  // No member to reset
            ++m_reconstructed;  // Each instance is its own group
        }
    }

    // A still-flagged VarScope is a residual: retain it, keeping the VPI set a superset of
    // --public-flat-rw's. Kind exclusions govern what may be reconstructed, not what may be
    // retained: else V3Gate substitutes the driver away and the row reads zero for ever.
    void retainCompletenessFloor() {
        for (AstVarScope* const vscp : m_gather.m_vscOrder) {
            AstVar* const varp = vscp->varp();
            if (!candidate(vscp) || m_shadowOf.count(vscp)) continue;  // Retained, or has a row
            // Its row keeps --public-flat-rw semantics, so give it that flag: V3Force pins a
            // forceable net's force vars, not the net itself, and DFG may alias it away.
            if (storagePinnedElsewhere(varp)) {
                varp->sigUserRWPublic(true);
                varp->vpiLazyRole(VVpiLazyRole::NONE);
                const bool dpi = varp->isReadByDpi() || varp->isWrittenByDpi();
                m_floorReason[dpi ? "storage pinned (DPI)" : "storage pinned"]
                    += instancesOf(varp);
            } else {
                ++m_floorReason[floorReason(vscp)];
                UINFO(9, "vpi-lazy floor: " << floorReason(vscp) << " " << vscp->name());
                retainTarget(vscp, Bail::COMPLETENESS_FLOOR);
            }
        }
        splitKeptInstances();
        for (AstVarScope* const vscp : m_gather.m_vscOrder) {
            // A VPI write into a writable retained signal is propagated by re-running 'settle'
            // on the next eval.
            if (vscp->varp()->isSigVpiLazyRetained() && !vscp->varp()->isVpiLazyCombWhole())
                v3Global.setHasVpiLazyRetained();
        }
    }

    // The lazy role is per variable, but storage is kept per instance: instances not kept move
    // to a twin with no role, which the optimiser is free to eliminate.
    void splitKeptInstances() {
        for (AstVarScope* const vscp : m_gather.m_vscOrder) {
            AstVar* const varp = vscp->varp();
            const auto vit = m_gather.m_vscpsOf.find(varp);
            if (vit == m_gather.m_vscpsOf.end()) continue;  // A twin made below
            const std::vector<AstVarScope*>& vscps = vit->second;
            if (vscp != vscps.front()) continue;
            const bool cand = varp->isSigVpiLazyCandidate();
            std::vector<AstVarScope*> freed;
            for (AstVarScope* const instp : vscps)
                if (!kept(instp)) freed.push_back(instp);
            if (freed.size() == vscps.size()) {
                if (!cand) continue;
                // Every instance's VPI presence moved to a shadow, its undriven bits too.
                UASSERT_OBJ(!varp->isVpiLazyCombPartial() || m_gapVars.count(varp), varp,
                            "--vpi-lazy drops the storage of a variable with undriven bits");
                varp->vpiLazyRole(VVpiLazyRole::NONE);
                varp->vpiLazyComb(VVpiLazyComb::NONE);
                continue;
            }
            varp->vpiLazyRole(cand ? VVpiLazyRole::RETAINED : VVpiLazyRole::PINNED);
            if (freed.empty()) continue;
            AstVar* const twinp = varp->cloneTree(false);
            twinp->name(varp->name() + "__Vlazyfreed");
            twinp->vpiLazyRole(VVpiLazyRole::NONE);
            twinp->vpiLazyComb(VVpiLazyComb::NONE);
            varp->addNextHere(twinp);
            // Refs cloned since the gather read only shadows or kept instances; see pinBoundary()
            for (AstVarScope* const instp : freed) {
                m_ctx.m_noRow.emplace(instp->scopep()->name(), varp);
                instp->varp(twinp);
                for (AstVarRef* const refp : m_gather.m_refsOf[instp]) refp->varp(twinp);
            }
            const auto sit = m_shadowVarOfOrig.find(varp);
            if (sit != m_shadowVarOfOrig.end()) {
                for (AstVarScope* const instp : vscps)
                    if (kept(instp)) m_ctx.m_noRow.emplace(instp->scopep()->name(), sit->second);
            }
        }
    }

    // A floor residual is one no classifier claimed, so no bail count records its shape.
    const char* floorReason(AstVarScope* vscp) {
        const AstVar* const varp = vscp->varp();
        if (varp->isIO()) return hasCombDriver(vscp) ? "port (comb-driven)" : "port (other)";
        if (!reconstructableKind(varp)) return "dtype";
        const int writes = writeCountOf(vscp);
        if (writes == 0) return "undriven";
        // Several writes to a flop are its NBA branches; only a comb driver can be multidriven.
        if (!hasCombDriver(vscp)) return "sequential";
        return writes > 1 ? "multidriven" : "comb (unclaimed)";
    }

    void reportStats() {
        const size_t reconstructedMembers = m_shadowVarOfOrig.size();
        const int floorRetained = m_bailCount[static_cast<size_t>(Bail::COMPLETENESS_FLOOR)];
        UINFO(3, "vpi-lazy: reconstructed="
                     << m_reconstructed << " groups=" << m_ordered.size()
                     << " members=" << reconstructedMembers << " fallback=" << m_fallback
                     << " copyGroups=" << m_copyCount << " foldedCopies=" << m_foldedCount
                     << " helpers=" << m_helperCount << " floorRetained=" << floorRetained);
        if (v3Global.opt.stats()) {
            V3Stats::addStat("VPI, lazy reconstructed", m_reconstructed);
            V3Stats::addStat("VPI, lazy groups", m_ordered.size());
            V3Stats::addStat("VPI, lazy reconstructed members", reconstructedMembers);
            V3Stats::addStat("VPI, lazy fallback retained", m_fallback);
            V3Stats::addStat("VPI, lazy boundary storage pinned", m_boundaryStorage);
            V3Stats::addStat("VPI, lazy copy descriptors", m_copyCount);
            V3Stats::addStat("VPI, lazy folded copy cones", m_foldedCount);
            V3Stats::addStat("VPI, lazy helper targets", m_helperCount);
            V3Stats::addStat("VPI, lazy floor retained", floorRetained);
            V3Stats::addStat("VPI, lazy comb read-only", m_combWhole);
            V3Stats::addStat("VPI, lazy comb masked", m_combPartial);
            for (const auto& pr : m_floorReason)
                V3Stats::addStat(std::string{"VPI, lazy floor residual, "} + pr.first, pr.second);
            for (size_t i = 0; i < static_cast<size_t>(Bail::_COUNT); ++i) {
                if (m_bailCount[i] && static_cast<Bail>(i) != Bail::COMPLETENESS_FLOOR) {
                    V3Stats::addStat(std::string{"VPI, lazy group bail, "}
                                         + bailName(static_cast<Bail>(i)),
                                     m_bailCount[i]);
                }
            }
        }
    }
};

}  // namespace

//######################################################################

void V3VpiLazy::prepare(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ":");
    V3VpiLazyContext& ctx = nodep->createVpiLazyContext();
    AstScope* const topScopep = nodep->topScopep() ? nodep->topScopep()->scopep() : nullptr;
    if (!topScopep) return;
    std::vector<AstCFunc*> splitFuncps;
    {
        VpiLazyPreparer preparer{nodep, topScopep, ctx};
        preparer.run();
        splitFuncps = preparer.splitFuncps();
    }

    // Per --output-split-cfuncs. splitCheck moves whole top-level statements, so an entry func's
    // epoch guard stays whole. Instance stubs are left whole for V3Descope.
    for (AstCFunc* const funcp : splitFuncps) V3Sched::util::splitCheck(funcp);

    V3Global::dumpCheckGlobalTree("vpi-lazy-prepare", 0, dumpTreeEitherLevel() >= 3);
}

void V3VpiLazy::classifyComb(AstNetlist* nodep) {
    AstScope* const topScopep = nodep->topScopep() ? nodep->topScopep()->scopep() : nullptr;
    if (!topScopep) return;
    V3VpiLazyContext ctx;
    VpiLazyPreparer{nodep, topScopep, ctx}.classifyOnly();
}

VVpiLazyComb V3VpiLazy::combOf(const AstNetlist* nodep, const AstScope* scopep,
                               const AstVar* varp) {
    if (!varp->isVpiLazyCombPartial()) return varp->vpiLazyComb();
    const V3VpiLazyContext* const ctxp = nodep->vpiLazyContextp();
    UASSERT_OBJ(ctxp, varp, "--vpi-lazy comb mask without a context");
    return ctxp->combOf(scopep->name(), varp);
}

const std::vector<V3VpiLazy::CombRun>&
V3VpiLazy::combRuns(const AstNetlist* nodep, const AstScope* scopep, const AstVar* varp) {
    const V3VpiLazyContext* const ctxp = nodep->vpiLazyContextp();
    UASSERT_OBJ(ctxp, varp, "--vpi-lazy comb mask without a context");
    return ctxp->combRunsOf(scopep->name(), varp);
}

bool V3VpiLazy::hasRow(const AstNetlist* nodep, const AstScope* scopep, const AstVar* varp) {
    const V3VpiLazyContext* const ctxp = nodep->vpiLazyContextp();
    return !ctxp || !ctxp->m_noRow.count({scopep->name(), varp});
}

const AstCFunc* V3VpiLazy::refreshFuncp(const AstNetlist* nodep, const AstScope* scopep,
                                        const AstVar* shadowVarp) {
    const V3VpiLazyContext* const ctxp = nodep->vpiLazyContextp();
    UASSERT_OBJ(ctxp, shadowVarp, "--vpi-lazy row without a context");
    const auto it = ctxp->m_rowRefresh.find({scopep->name(), shadowVarp});
    return it != ctxp->m_rowRefresh.end() ? it->second : shadowVarp->lazyReconFuncp();
}
