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
// VPI-accessible variable isSigVpiLazyRWPublic(), which unlike --public-flat-rw
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
// merge into one group, assembled from a zero base. A group's targets are the
// VPI-visible variables it solely drives, its other written variables temp
// shadows. Its statements are cloned into a cold loose function with every
// written variable redirected to a "shadow", leaving the originals deletable.
// Operands belonging to another group are rewired to that group's shadows,
// keeping reconstruction O(N); other "boundary" operands are pinned with
// sigUserRWPublic so the cone has real storage to read.
//
// A group is claimed only if one ordered walk over its statements proves that
// every read of a group variable follows an unconditional full-width write of
// it, that every statement is pure and of a modelled kind, and that every
// target is written on all paths. Otherwise its targets are retained, and Bail
// records why for --stats.
//
// PHASES, in the fixed order run() lists
//
//   findHelperCandidates                     vars a copy needs promoted to a target
//   findCrossScopeCopyCandidates             `otherScope.dst = u;` targets formGroups must not
//                                            retain, so crossScopeCopySources may claim them
//   formGroups, analyseGroups                form, then prove or bail
//   restrictMultiInstanceToLocalCones        retain cones not class-internal
//   buildDependencyGraph, splitCyclesRetainCores, topoOrderSurvivors
//                                            retain cycle cores, order the rest
//   copyStoredSources                        copy rows: the source holds storage
//   crossScopeCopySources                    copy rows whose source is in another scope
//   pruneBodies                              backward liveness over the clones
//   foldTrivialCopyGroups                    fold rows: the source is another cone
//   emitReconstructions                      emit the funcs and shadows
//   retainWriteOnlySequential, retainCompletenessFloor   retain what is left
//
// COPY AND FOLD
//
// A group whose whole body is `target = u;` needs no cone: its descriptor
// refreshes by memcpy from u, costing no function and no epoch slot.
// copyStoredSources takes a u that holds storage and names it directly;
// foldTrivialCopyGroups takes a u that is another live cone's target, and
// names that cone's shadow, calling its function first.
//
// crossScopeCopySources is copyStoredSources for the shape that never forms a
// group at all: a continuous `otherScope.dst = u;`, as an SV interface port
// driven from its parent is. Its descriptor's source is in another scope, and
// so addressed relative to the Syms object both scopes are members of.
//
// Every converted row keeps its own shadow: --public-flat-rw is the
// reference, and there two aliases of one net are distinct nets, so two rows
// naming one storage location would leak a deposit from one into the other.
//
// RUNTIME
//
// A reconstructed row's datap is a VerilatedVarLazyDatap {refreshp, selfp,
// offsets}. A read calls refreshp, which compares the group's stamp in its
// module's epoch array against vlSymsp->__Vm_lazyEpoch, recomputes the cone if
// stale, and restamps; eval() bumps the epoch, so a cone is recomputed at most
// once per eval step however many of its signals are read.
//
// A vpi_put_value into a reconstructed signal refreshes the row, stores, and
// stamps the row's word in the module's __Vlazydep array with
// vlSymsp->__Vm_lazyDepStamp. Two things follow, and they are what IEEE
// 1800-2023 38.34 asks of a deposit into a net. The put also bumps the epoch,
// so every memoised cone misses and the signals that resolve from this one
// re-resolve; and each cone body tests the deposit word before committing to
// a row, so the rebuild recomputes that row's siblings and dependents while
// leaving the deposited row alone. Both retire together at evalEnd (see
// VerilatedSyms::lazyEvalEnd), which is over-eager - the LRM would hold the
// override until a driver of that net changed - but per-net driver tracking is
// the work this pass exists to avoid. A put into a retained signal instead sets
// __Vm_vpiLazyWritten, and the next eval re-runs the settle region once to
// propagate it.
//
// A lazy read is thus model code that writes model state - the shadow and the
// memo stamps - from whatever thread called VPI, and those stamps are plain
// words. A read racing eval() is therefore a user error, as it is under --vpi
// and --public-flat-rw; VPI's answer, a synch callback, is dispatched on the
// eval thread, and this pass emits nothing thread-aware.
//
// One function serves every instance of a module, so it must read variables
// rather than instance-specific driver expressions; AstCFunc::vpiLazyReconstruct
// tells V3Gate and V3Dfg to leave those reads alone.
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
static const char* const DEP_NAME = "__Vlazydep";
static const char* const RECONSTRUCT_BODY_FUNC_NAME = "__Vlazy_reconstruct_body";

//######################################################################
class V3VpiLazyContext final {
public:
    // Names survive the intervening optimisation passes.
    struct CrossScopeSrcNames final {
        std::string m_dstScopeName;
        std::string m_dstVarName;
        std::string m_srcScopeName;
        std::string m_srcVarName;
    };

    std::set<std::string> m_residualNames;
    std::vector<CrossScopeSrcNames> m_crossScopeSrcs;
    std::map<std::pair<const AstScope*, const AstVar*>, V3VpiLazy::CrossScopeSrc>
        m_crossScopeResolved;
    bool m_crossScopeResolvedDone = false;
    std::unordered_map<std::string, int> m_depSlotOfShadowName;
    std::map<const AstVar*, V3VpiLazy::DepWord> m_depWordResolved;
    // Guards emitted, against which finalize() checks that the optimizer did not fold them away.
    int m_depGuards = 0;
};

V3VpiLazyContext* V3VpiLazy::newContext() { return new V3VpiLazyContext; }
void V3VpiLazy::deleteContext(V3VpiLazyContext* ctxp) { delete ctxp; }

//######################################################################

namespace {

using CrossScopeSrcNames = V3VpiLazyContext::CrossScopeSrcNames;

bool storagePinnedElsewhere(const AstVar* varp) {
    if (varp->isPrimaryIO()) return true;
    if (varp->isForceable()) return true;
    if (varp->isReadByDpi() || varp->isWrittenByDpi()) return true;
    if (varp->isSigModPublic()) return true;
    return false;
}

// Dims past VPI_TABLE_MAX_DIMS are rejected: the shadow must fit a VlVarTableEntry row.
bool copyTargetKind(const AstVar* varp) {
    if (storagePinnedElsewhere(varp)) return false;
    AstNodeDType* const dtypep = varp->dtypeSkipRefp();
    AstNodeDType* leafp = dtypep;
    while (AstUnpackArrayDType* const adtypep = VN_CAST(leafp, UnpackArrayDType)) {
        leafp = adtypep->subDTypep()->skipRefp();
    }
    if (!(VN_IS(leafp, BasicDType) || leafp->isIntegralOrPacked())) return false;
    const std::pair<uint32_t, uint32_t> dims = dtypep->dimensions(/*includeBasic*/ true);
    return dims.first + dims.second <= static_cast<uint32_t>(V3VpiLazy::VPI_TABLE_MAX_DIMS);
}

// A port is excluded: one loose func serves every instance, named from its target's module, so a
// port written from its parent has nowhere to put one. A copy row has no func, so may claim it.
bool reconstructableKind(const AstVar* varp) {
    if (varp->isIO()) return false;
    return copyTargetKind(varp);
}

class GroupVertex;

// See UNIT OF RECONSTRUCTION above.
struct Group final {
    AstScope* scopep = nullptr;  // Scope that authored the statements (see restrictMulti...)
    AstAlways* alwaysp = nullptr;  // Procedural block, or null for an assign group
    std::vector<AstAssignW*> partialps;  // Continuous assigns; empty unless an assign group
    std::vector<AstVarScope*> targets;  // VPI candidates this group defines, encounter order
    std::vector<AstVarScope*> temps;  // Other variables it writes, encounter order
    std::unordered_set<AstVarScope*> members;
    std::unordered_map<AstVarScope*, size_t> slotOf;  // target -> index in 'targets'
    std::vector<AstVarScope*> zeroInitps;  // Partial assembly: zero these shadows first
    AstVarScope* copyFromp = nullptr;  // Converted: refresh by copying this variable instead
    AstVar* keyp = nullptr;  // targets[0]->varp(): cross-instance group identity
    AstCFunc* funcp = nullptr;
    int epochSlot = -1;  // Index into the module's stamp array (assignEpochSlots)
    // Per target, its index into the module's deposit array, or -1 for a helper target, which
    // has no VPI row and so can never be deposited into (assignDepSlots)
    std::vector<int> depSlots;
    bool live = true;  // Cleared when the group is abandoned and its targets retained
    GroupVertex* vtxp = nullptr;  // Its vertex in the dependency graph, null once dead
    AstVarScope* copySrcp = nullptr;  // soleCopySource() memo
    bool copySrcValid = false;
    // Representatives only: the pruned statement clone and the group vars it still produces.
    AstNode* bodyp = nullptr;
    std::unordered_set<AstVarScope*> neededps;
};

class GroupVertex final : public V3GraphVertex {
    VL_RTTI_IMPL(GroupVertex, V3GraphVertex)
    Group* const m_groupp;

public:
    GroupVertex(V3Graph* graphp, Group* groupp)
        : V3GraphVertex{graphp}
        , m_groupp{groupp} {}
    Group* groupp() const { return m_groupp; }
    string name() const override { return m_groupp->keyp->name(); }
};

// One partial write's footprint; idxs order need only be consistent between parts.
struct PartExtent final {
    std::vector<int32_t> idxs;
    int lsb = 0;
    int width = 0;
};

struct PartWrite final {
    AstAssignW* m_awp = nullptr;
    PartExtent m_ext;
};

// Base and footprint of a constant-selected partial write (`base[3][c +: w] = rhs;`), else null.
AstVarScope* partialLhs(AstNodeExpr* lhsp, PartExtent& extr) {
    AstNodeExpr* nodep = lhsp;
    bool anySel = false;
    if (AstSel* const selp = VN_CAST(nodep, Sel)) {
        if (!VN_IS(selp->lsbp(), Const)) return nullptr;
        extr.lsb = selp->lsbConst();
        extr.width = selp->widthConst();
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
    return refp->varScopep();
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

// Pre-optimization walk: write/read counts per VarScope, and per-block write info.
class LazyGatherVisitor final : public VNVisitor {
public:
    struct CombBlock final {
        AstAlways* m_alwaysp = nullptr;
        AstScope* m_scopep = nullptr;  // Scope that authored the block
        AstAssignW* m_assignwp = nullptr;  // Lone AstAssignW of a CONT_ASSIGN block
        std::vector<AstVarScope*> m_targets;  // Written vars, encounter order
        std::unordered_map<const AstVarScope*, int> m_writeCount;  // Writes within this block
    };
    // STATE
    std::unordered_map<const AstVarScope*, int> m_writeCount;
    std::vector<AstVarScope*> m_writtenOrder;  // Vars with >=1 write, encounter order
    std::unordered_map<const AstVarScope*, int> m_readCount;  // Reads (RW counts as read)
    std::vector<CombBlock> m_combBlocks;
    // Per-AstVar VarScope count == instance count; keeps retain stats in per-instance units.
    std::unordered_map<const AstVar*, int> m_instanceCount;
    // Every VarScope in tree-encounter order; iterated by the completeness floor and by
    // prepare()'s residual scan.
    std::vector<AstVarScope*> m_vscOrder;

private:
    AstScope* m_scopep = nullptr;  // Scope currently being descended
    AstAlways* m_comboAlwaysp = nullptr;  // Non-null while inside a combo always body
    std::unordered_map<const AstVarScope*, int> m_blockWrites;  // Writes of the current block
    std::vector<AstVarScope*> m_blockWriteOrder;  // Vars written in this block, encounter order

    void bumpWrite(AstVarScope* vscp) {
        if (m_writeCount[vscp]++ == 0) m_writtenOrder.push_back(vscp);
        if (m_comboAlwaysp) {
            if (m_blockWrites[vscp]++ == 0) m_blockWriteOrder.push_back(vscp);
        }
    }

    // VISITORS
    void visit(AstVarRef* nodep) override {
        if (!nodep->access().isReadOnly()) bumpWrite(nodep->varScopep());
        if (!nodep->access().isWriteOnly()) ++m_readCount[nodep->varScopep()];
        iterateChildren(nodep);
    }
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
            VL_RESTORER_CLEAR(m_blockWrites);
            VL_RESTORER_CLEAR(m_blockWriteOrder);
            VL_RESTORER(m_comboAlwaysp);
            m_comboAlwaysp = alwaysp;
            iterateChildren(alwaysp);
            if (m_blockWriteOrder.empty()) continue;
            CombBlock block;
            block.m_alwaysp = alwaysp;
            block.m_scopep = m_scopep;
            block.m_targets = m_blockWriteOrder;
            block.m_writeCount = m_blockWrites;
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
        ++m_instanceCount[nodep->varp()];
        m_vscOrder.push_back(nodep);
        iterateChildren(nodep);
    }
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit LazyGatherVisitor(AstNetlist* nodep) { iterate(nodep); }
};

class VpiLazyPreparer final {
    using CombBlock = LazyGatherVisitor::CombBlock;
    using Defined = std::unordered_set<AstVarScope*>;

    // STATE
    AstScope* const m_topScopep;
    V3VpiLazyContext& m_ctx;
    LazyGatherVisitor m_gather;

    int m_combBailRetained = 0;  // Group-bail / non-sole-driver / cycle retains

    std::vector<std::unique_ptr<Group>> m_groups;  // Formation order (deterministic)
    std::unordered_map<AstVar*, std::vector<Group*>> m_groupsOfKey;
    std::unordered_map<AstVarScope*, Group*> m_groupOf;  // Solely-written var -> its group
    std::unordered_map<AstVarScope*, Group*> m_targetOf;  // Group target -> its group
    // Copy sources promoted from temp to target; per AstVar, so every instance forms one shape
    std::unordered_set<const AstVar*> m_helperCandVars;
    std::unordered_set<const AstVarScope*> m_helperTargets;  // Committed helper targets
    int m_helperCount = 0;  // Helper targets reconstructed, per instance
    std::vector<Group*> m_copyGroups;  // Copies of a variable that holds storage
    std::vector<Group*> m_foldedCopies;  // Cones folded to a descriptor memcpy
    int m_foldedCount = 0;
    int m_copyCount = 0;
    // Converted target -> the variable its row copies, for cone operand substitution.
    std::unordered_map<AstVarScope*, AstVarScope*> m_retargetSrcOf;
    // Cross-scope copy candidates found before grouping: target -> its local source
    std::unordered_map<AstVarScope*, AstVarScope*> m_xscopeSrcOf;
    std::vector<AstVarScope*> m_xscopeOrder;  // m_xscopeSrcOf keys, encounter order
    std::vector<AstVarScope*> m_crossScopeCopyTargets;  // Claimed, awaiting emit
    std::unordered_map<const AstVar*, int> m_xscopeShadowIdx;

    V3Graph m_depGraph;  // u -> v where v reads a variable u defines; vertices are GroupVertex

    std::vector<Group*> m_ordered;  // Topological order of reconstructed survivor groups

    FileLine* m_funcFlp = nullptr;
    int m_reconstructed = 0;  // Reconstructed signals (per instance)
    int m_fallback = 0;  // Retained with storage (incl. group bails), snapshotted pre-emission
    uint32_t m_boundaryStorage = 0;  // Pinned only to feed a reconstruct function
    // Why each retained signal missed reconstruction.
    enum class Bail : uint8_t {
        MULTIDRIVEN,  // Written by more than one group, or outside any group
        DTYPE,  // Kind reconstruction cannot express (unpacked aggregate, over dim cap)
        PARTIAL_MIXED_WRITE,  // Partial-write target also has a full/comb/impure/var-lsb write
        PARTIAL_OVERLAP,  // Partial writes overlap, so no unambiguous assembly
        READ_BEFORE_WRITE,  // A group var is read before an unconditional full-width write
        LATCH,  // A target is not written on every path through the block
        IMPURE,  // The block has a side effect reconstruction must not repeat
        UNSUPPORTED_STMT,  // A statement kind the ordered walk does not model
        UNSUPPORTED_LVALUE,  // A continuous write whose shape a shadow cannot mirror
        CROSS_SCOPE_WRITE,  // Writes a variable outside the scope that authored the statements
        CROSS_SCOPE_CONE,  // Multi-instance cone reading outside its scope; one func cannot serve
        COMB_CYCLE,  // Genuine combinational cycle (SCC member or self-loop)
        TOPO_LEFTOVER,  // Unordered by Kahn's despite being a DAG; indicates a bug
        COMPLETENESS_FLOOR,  // No classification path claimed it; retained so VPI still sees it
        BOUNDARY_COMB_DTYPE,  // Comb boundary operand of a kind reconstruction cannot express
        BOUNDARY_COMB_COPY,  // Comb boundary operand whose own row copies another variable
        BOUNDARY_COMB_UNKNOWN,  // Comb boundary operand no skip path explains
        BOUNDARY_OPERAND_SEQ,  // Read by another cone, no comb driver: sequential/undriven
        _COUNT
    };
    // METHODS
    static const char* bailName(Bail b) {
        static const char* const names[] = {"multidriven",
                                            "dtype",
                                            "partial mixed write",
                                            "partial overlap",
                                            "read before write",
                                            "latch",
                                            "impure",
                                            "unsupported statement",
                                            "unsupported lvalue",
                                            "cross-scope write",
                                            "cross-scope cone",
                                            "comb cycle",
                                            "topo leftover",
                                            "completeness floor",
                                            "boundary comb (dtype)",
                                            "boundary comb (copy)",
                                            "boundary comb (unexplained)",
                                            "boundary operand (seq)"};
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
    struct StampArray final {
        std::unordered_map<const AstNodeModule*, AstVar*> varOfMod;
        std::unordered_map<const AstScope*, AstVarScope*> ofScope;
    };
    StampArray m_epoch;
    StampArray m_dep;
    std::unordered_map<AstVar*, AstCFunc*> m_funcOfKey;
    // Short names for the emitted artefacts; ids are design-global (gidOf).
    std::unordered_map<const AstVar*, int> m_gidOfKey;
    std::unordered_map<const AstVar*, int> m_tempIdxOfVar;
    int m_nextGid = 0;
    int m_nextTempIdx = 0;

    int m_prunedStmts = 0;  // Cloned statements dropped as dead (pruneBodies)
    int m_floorRetained = 0;
    std::map<std::string, int> m_floorReason;  // Floor residual shape -> instances, for stats
    int m_crossScopeCopies = 0;  // Copy rows whose source is in another scope

public:
    VpiLazyPreparer(AstNetlist* nodep, AstScope* topScopep, V3VpiLazyContext& ctx)
        : m_topScopep{topScopep}
        , m_ctx{ctx}
        , m_gather{nodep} {}

    // Pre-run VarScope order; run() adds shadow and stamp VarScopes, which carry no lazy role
    const std::vector<AstVarScope*>& vscOrder() const { return m_gather.m_vscOrder; }

    void run() {
        findHelperCandidates();
        findCrossScopeCopyCandidates();
        formGroups();
        analyseGroups();
        restrictMultiInstanceToLocalCones();
        buildDependencyGraph();
        splitCyclesRetainCores();
        topoOrderSurvivors();
        copyStoredSources();
        crossScopeCopySources();
        pruneBodies();
        foldTrivialCopyGroups();
        emitReconstructions();
        retainCompletenessFloor();
        reportStats();
    }

private:
    // METHODS
    int instancesOf(const AstVar* varp) const {
        const auto it = m_gather.m_instanceCount.find(varp);
        return it != m_gather.m_instanceCount.end() ? it->second : 1;
    }

    int writeCountOf(const AstVarScope* vscp) const {
        const auto it = m_gather.m_writeCount.find(vscp);
        return it == m_gather.m_writeCount.end() ? 0 : it->second;
    }

    int readCountOf(const AstVarScope* vscp) const {
        const auto it = m_gather.m_readCount.find(vscp);
        return it == m_gather.m_readCount.end() ? 0 : it->second;
    }

    // Shadow member and lazy flag are per module: a shape is taken for every instance or none.
    bool claimPerVar(const std::unordered_map<const AstVar*, int>& tally,
                     const AstVar* varp) const {
        const auto it = tally.find(varp);
        return it != tally.end() && it->second == instancesOf(varp);
    }

    void dropFromOrdered(const std::unordered_set<Group*>& dropped) {
        if (dropped.empty()) return;
        m_ordered.erase(std::remove_if(m_ordered.begin(), m_ordered.end(),
                                       [&](Group* g) { return dropped.count(g) != 0; }),
                        m_ordered.end());
    }

    Group* liveGroupOf(AstVarScope* u) const {
        const auto it = m_groupOf.find(u);
        if (it == m_groupOf.end()) return nullptr;
        return it->second->live ? it->second : nullptr;
    }

    template <typename T_Callable>
    void forEachStmt(const Group* g, T_Callable&& f) const {
        if (g->alwaysp) {
            for (AstNode* sp = g->alwaysp->stmtsp(); sp; sp = sp->nextp()) f(sp);
        } else {
            for (AstAssignW* const awp : g->partialps) f(static_cast<AstNode*>(awp));
        }
    }

    template <typename T_Callable>
    bool existsInStmt(const Group* g, T_Callable&& p) const {
        if (g->alwaysp) {
            for (AstNode* sp = g->alwaysp->stmtsp(); sp; sp = sp->nextp())
                if (sp->exists(p)) return true;
        } else {
            for (AstAssignW* const awp : g->partialps)
                if (awp->exists(p)) return true;
        }
        return false;
    }

    Bail combBoundaryReason(AstVarScope* u) {
        if (!reconstructableKind(u->varp())) return Bail::BOUNDARY_COMB_DTYPE;
        if (m_retargetSrcOf.count(u)) return Bail::BOUNDARY_COMB_COPY;
        // Catch-all: what is left is a variable a bailed group wrote, reached as a copy's source.
        return Bail::BOUNDARY_COMB_UNKNOWN;
    }

    // A converted target has no storage, so a cone reading it reads what its row copies.
    AstVarScope* retargetSubstituteFor(AstVarScope* u, const Group* g) const {
        const auto it = m_retargetSrcOf.find(u);
        if (it == m_retargetSrcOf.end()) return nullptr;
        AstVarScope* const srcp = it->second;
        if (!u->varp()->dtypep()->similarDType(srcp->varp()->dtypep())) return nullptr;
        if (instancesOf(g->keyp) > 1 && srcp->scopep() != g->scopep) return nullptr;
        return srcp;
    }

    bool hasCombDriver(AstVarScope* vscp) {
        if (!m_combTargetsBuilt) {
            for (const CombBlock& b : m_gather.m_combBlocks)
                for (AstVarScope* const t : b.m_targets) m_combTargets.insert(t);
            m_combTargetsBuilt = true;
        }
        return m_combTargets.count(vscp) != 0;
    }

    void retainTarget(AstVarScope* target, Bail why) {
        AstVar* const varp = target->varp();
        if (!varp->isSigVpiLazyRWPublic()) return;  // already reconstructed / retained
        varp->vpiLazyRole(VVpiLazyRole::RETAINED);
        m_combBailRetained += instancesOf(varp);
        m_bailCount[static_cast<size_t>(why)] += instancesOf(varp);
    }

    // All-or-nothing per module: flag and func are shared, so a survivor gets the wrong instance.
    void killGroupsOfKey(AstVar* keyp, Bail why) {
        const auto git = m_groupsOfKey.find(keyp);
        UASSERT_OBJ(git != m_groupsOfKey.end(), keyp, "--vpi-lazy group key has no groups");
        for (Group* const g : git->second) {
            if (!g->live) continue;
            g->live = false;
            for (AstVarScope* const t : g->targets) retainTarget(t, why);
        }
    }

    // METHODS - Group formation

    static AstVarScope* partialWriteBase(const CombBlock& b, PartExtent& extr) {
        if (!b.m_assignwp) return nullptr;
        if (!b.m_assignwp->rhsp()->isPure()) return nullptr;
        return partialLhs(b.m_assignwp->lhsp(), extr);
    }

    Group* makeGroup(AstScope* scopep, AstAlways* alwaysp, std::vector<AstAssignW*>&& parts,
                     const std::vector<AstVarScope*>& written,
                     const std::unordered_map<const AstVarScope*, int>& groupWrites,
                     const std::unordered_set<const AstVar*>& notSole, bool zeroInit) {
        // V3EmitCSyms names the func from the target shadow's module: all group vars share it.
        for (AstVarScope* const w : written) {
            if (w->scopep() == scopep) continue;
            for (AstVarScope* const t : written) {
                if (m_xscopeSrcOf.count(t)) continue;  // crossScopeCopySources() may claim it
                if (t->varp()->isSigVpiLazyRWPublic() && !storagePinnedElsewhere(t->varp()))
                    retainTarget(t, Bail::CROSS_SCOPE_WRITE);
            }
            return nullptr;
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
            if (notSole.count(varp)) {
                // Multidriven in some instance: never a target, the choice being per module.
                if (varp->isSigVpiLazyRWPublic() && !storagePinnedElsewhere(varp))
                    retainTarget(w, Bail::MULTIDRIVEN);
            } else if (!varp->isSigVpiLazyRWPublic()) {
                // A temp, unless a VPI-visible copy reads it: then a "helper target" with a
                // shadow, and no row of its own.
                if (m_helperCandVars.count(varp) && reconstructableKind(varp)) {
                    targets.push_back(w);
                    m_helperTargets.insert(w);
                    continue;
                }
            } else if (!reconstructableKind(varp)) {
                if (!storagePinnedElsewhere(varp)) retainTarget(w, Bail::DTYPE);
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
        g->alwaysp = alwaysp;
        g->partialps = std::move(parts);
        g->targets = targets;
        g->temps = temps;
        g->members.insert(targets.begin(), targets.end());
        g->members.insert(temps.begin(), temps.end());
        if (zeroInit) g->zeroInitps = targets;
        g->keyp = targets[0]->varp();
        for (size_t i = 0; i < targets.size(); ++i) {
            g->slotOf.emplace(targets[i], i);
            m_groupOf[targets[i]] = g;
            m_targetOf[targets[i]] = g;
        }
        // Only a solely-written temp may be read through another group's shadow copy.
        for (AstVarScope* const t : soleTemps)
            if (t) m_groupOf.emplace(t, g);
        m_groups.push_back(std::move(ownp));
        m_groupsOfKey[g->keyp].push_back(g);
        return g;
    }

    static bool canCopyFrom(const AstVarScope* dstp, const AstVarScope* srcp) {
        return dstp->scopep() == srcp->scopep() && reconstructableKind(dstp->varp())
               && sameLayout(dstp, srcp);
    }

    template <typename T_Callable>
    void forEachCopyAssign(T_Callable&& f) const {
        for (const CombBlock& b : m_gather.m_combBlocks) {
            if (!b.m_assignwp) continue;
            const AstVarRef* const dstRefp = VN_CAST(b.m_assignwp->lhsp(), VarRef);
            const AstVarRef* const srcRefp = VN_CAST(b.m_assignwp->rhsp(), VarRef);
            if (!dstRefp || !srcRefp || !srcRefp->access().isReadOnly()) continue;
            f(b, dstRefp->varScopep(), srcRefp->varScopep());
        }
    }

    // A copy whose source is a group temp has no shadow to read; a helper target gives it one.
    void findHelperCandidates() {
        forEachCopyAssign([&](const CombBlock&, AstVarScope* dstp, AstVarScope* srcp) {
            if (!dstp->varp()->isSigVpiLazyRWPublic() || writeCountOf(dstp) != 1) return;
            if (srcp->varp()->isSigVpiLazyRWPublic()) return;
            if (!reconstructableKind(srcp->varp())) return;
            if (!canCopyFrom(dstp, srcp)) return;
            m_helperCandVars.insert(srcp->varp());
        });
    }

    // `otherScope.dst = u;` can never be a cone, makeGroup refusing a write outside the authoring
    // scope, but it is a copy row: record it here so makeGroup does not retain it instead.
    void findCrossScopeCopyCandidates() {
        std::unordered_map<const AstVar*, int> instances;
        std::vector<std::pair<AstVarScope*, AstVarScope*>> cand;
        forEachCopyAssign([&](const CombBlock& b, AstVarScope* dstp, AstVarScope* srcp) {
            if (dstp->scopep() == b.m_scopep) return;  // copyStoredSources' shape
            // pinBoundary reasons within one scope, and that is the scope V3EmitCSyms addresses.
            if (srcp->scopep() != b.m_scopep) return;
            if (!dstp->varp()->isSigVpiLazyRWPublic()) return;
            if (writeCountOf(dstp) != 1) return;
            if (!copyTargetKind(dstp->varp()) || !sameLayout(dstp, srcp)) return;
            cand.emplace_back(dstp, srcp);
            ++instances[dstp->varp()];
        });
        for (const auto& pr : cand) {
            if (!claimPerVar(instances, pr.first->varp())) continue;
            if (m_xscopeSrcOf.emplace(pr.first, pr.second).second)
                m_xscopeOrder.push_back(pr.first);
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
            if (basep) partsOf[basep].push_back(PartWrite{b.m_assignwp, std::move(ext)});
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
        std::unordered_set<const AstVar*> notSole;
        for (const auto& pr : winfo) {
            const WInfo& wi = pr.second;
            const bool sole
                = wi.m_sum == writeCountOf(pr.first) && (wi.m_blocks == 1 || wi.m_allParts);
            if (!sole) notSole.insert(pr.first->varp());
        }
        // Anything written outside a combinational block entirely has no group to define it.
        for (AstVarScope* const w : m_gather.m_writtenOrder)
            if (!winfo.count(w)) notSole.insert(w->varp());

        // Pass 2: form the groups, in block-encounter order.
        std::unordered_set<AstVarScope*> partialDone;
        for (size_t i = 0; i < blocks.size(); ++i) {
            const CombBlock& b = blocks[i];
            if (AstVarScope* const basep = partialBase[i]) {
                if (!partialDone.insert(basep).second) continue;  // merged at first encounter
                const auto pit = partsOf.find(basep);
                UASSERT_OBJ(pit != partsOf.end(), basep,
                            "--vpi-lazy partial-write base has no recorded parts");
                formPartialGroup(basep, pit->second, b.m_scopep, notSole);
                continue;
            }
            if (AstAssignW* const awp = b.m_assignwp) {
                AstNodeExpr* const lhsp = awp->lhsp();
                if (VN_IS(lhsp, VarRef)) {
                    makeGroup(b.m_scopep, nullptr, {awp}, b.m_targets, b.m_writeCount, notSole,
                              /*zeroInit*/ false);
                    continue;
                }
                // A write shape the shadow cannot mirror: retain rather than let it be dropped.
                bool partial = false;
                if (const AstVarRef* const basep2 = lhsBaseRef(lhsp, partial)) {
                    AstVar* const varp = basep2->varScopep()->varp();
                    if (varp->isSigVpiLazyRWPublic() && !storagePinnedElsewhere(varp))
                        retainTarget(basep2->varScopep(), Bail::UNSUPPORTED_LVALUE);
                }
                continue;
            }
            makeGroup(b.m_scopep, b.m_alwaysp, {}, b.m_targets, b.m_writeCount, notSole,
                      /*zeroInit*/ false);
        }
    }

    // Disjoint partial `assign`s have no full-width driver but assemble exactly from a zero base.
    void formPartialGroup(AstVarScope* basep, const std::vector<PartWrite>& parts,
                          AstScope* scopep, const std::unordered_set<const AstVar*>& notSole) {
        AstVar* const varp = basep->varp();
        if (!varp->isSigVpiLazyRWPublic()) return;
        if (!reconstructableKind(varp)) {
            if (!storagePinnedElsewhere(varp)) retainTarget(basep, Bail::DTYPE);
            return;
        }
        if (static_cast<int>(parts.size()) != writeCountOf(basep) || notSole.count(varp)) {
            // A full / procedural / impure / variable-range write exists too.
            retainTarget(basep, Bail::PARTIAL_MIXED_WRITE);
            return;
        }
        // Overlapping writes are multidriven: assembly would depend on encounter order. Bucketed
        // by element index, then LSB-sorted so only adjacent pairs need testing.
        const size_t depth = parts[0].m_ext.idxs.size();
        std::map<std::vector<int32_t>, std::vector<const PartExtent*>> byElem;
        for (const PartWrite& pw : parts) {
            // V3Slice leaves parts at one depth; degraded not asserted, a wrong guess miscompiles
            if (pw.m_ext.idxs.size() != depth) {
                // LCOV_EXCL_START
                retainTarget(basep, Bail::PARTIAL_OVERLAP);
                return;
                // LCOV_EXCL_STOP
            }
            byElem[pw.m_ext.idxs].push_back(&pw.m_ext);
        }
        for (auto& pr : byElem) {
            std::vector<const PartExtent*>& bucket = pr.second;
            std::sort(
                bucket.begin(), bucket.end(),
                [](const PartExtent* ap, const PartExtent* bp) { return ap->lsb < bp->lsb; });
            for (size_t i = 1; i < bucket.size(); ++i) {
                if (bucket[i]->lsb < bucket[i - 1]->lsb + bucket[i - 1]->width) {
                    retainTarget(basep, Bail::PARTIAL_OVERLAP);
                    return;
                }
            }
        }
        const std::unordered_map<const AstVarScope*, int> groupWrites{
            {basep, static_cast<int>(parts.size())}};
        std::vector<AstAssignW*> assignps;
        assignps.reserve(parts.size());
        for (const PartWrite& pw : parts) assignps.push_back(pw.m_awp);
        makeGroup(scopep, nullptr, std::move(assignps), {basep}, groupWrites, notSole,
                  /*zeroInit*/ true);
    }

    // METHODS - Group analysis

    // Calls are exempt: isPredictOptimizable() is false for every AstNodeCCall only as V3Simulate
    // cannot call one.
    static bool unsafeToReexecute(AstNode* nodep) {
        if (!nodep->isPure()) return true;
        return !nodep->isPredictOptimizable() && !VN_IS(nodep, NodeCCall);
    }

    // Asked per root statement: exists() does not follow nextp() from its root.
    static bool impure(AstNode* stmtp) {
        return stmtp->exists([](AstNode* nodep) { return unsafeToReexecute(nodep); });
    }

    // 'skipp' is an assignment's LHS base ref, whose read is checked apart.
    static bool readsUndefined(AstNode* nodep, const AstVarRef* skipp, const Group* g,
                               const Defined& defined) {
        bool bad = false;
        nodep->foreach([&](AstVarRef* refp) {
            if (refp == skipp || refp->access().isWriteOnly()) return;
            AstVarScope* const u = refp->varScopep();
            if (g->members.count(u) && !defined.count(u)) bad = true;
        });
        return bad;
    }

    bool walkStmts(AstNode* stmtsp, const Group* g, Defined& defined, Bail& whyr) const {
        for (AstNode* sp = stmtsp; sp; sp = sp->nextp())
            if (!walkStmt(sp, g, defined, whyr)) return false;
        return true;
    }

    // 'defined': group vars the prefix wrote unconditionally full-width; conditionals intersect.
    bool walkStmt(AstNode* stmtp, const Group* g, Defined& defined, Bail& whyr) const {
        if (VN_IS(stmtp, Comment) || VN_IS(stmtp, JumpGo)) return true;
        if (AstNodeAssign* const asgnp = VN_CAST(stmtp, NodeAssign)) {
            // V3Active rewrote '<=' and V3Force lowered AssignForce; only blocking/cont remain.
            UASSERT_OBJ(VN_IS(stmtp, Assign) || VN_IS(stmtp, AssignW), stmtp,
                        "--vpi-lazy: unexpected assignment kind in a combinational block");
            // Only --timing keeps a delay this far, and such a block never terminates: untested.
            if (asgnp->timingControlp()) {  // LCOV_EXCL_START
                whyr = Bail::UNSUPPORTED_STMT;
                return false;
            }  // LCOV_EXCL_STOP
            bool partial = false;
            AstVarRef* const baserefp = lhsBaseRef(asgnp->lhsp(), partial);
            if (!baserefp) {
                whyr = Bail::UNSUPPORTED_STMT;
                return false;
            }
            AstVarScope* const basep = baserefp->varScopep();
            // The gather counted every write under this block, so its write set is g->members
            UASSERT_OBJ(g->members.count(basep), stmtp,
                        "--vpi-lazy: group members miss a write of their own block");
            if (readsUndefined(asgnp, baserefp, g, defined)) {
                whyr = Bail::READ_BEFORE_WRITE;
                return false;
            }
            if (partial) {
                // The untouched bits keep their prior value, so the shadow must already hold it.
                if (!defined.count(basep)) {
                    whyr = Bail::READ_BEFORE_WRITE;
                    return false;
                }
            } else {
                defined.insert(basep);
            }
            return true;
        }
        if (AstNodeIf* const ifp = VN_CAST(stmtp, NodeIf)) {
            if (readsUndefined(ifp->condp(), nullptr, g, defined)) {
                whyr = Bail::READ_BEFORE_WRITE;
                return false;
            }
            Defined thenDef = defined;
            Defined elseDef = defined;
            if (!walkStmts(ifp->thensp(), g, thenDef, whyr)) return false;
            if (!walkStmts(ifp->elsesp(), g, elseDef, whyr)) return false;
            for (AstVarScope* const v : thenDef)
                if (elseDef.count(v)) defined.insert(v);
            return true;
        }
        if (AstLoop* const loopp = VN_CAST(stmtp, Loop)) {
            // May run zero times, so it defines nothing on exit.
            Defined body = defined;
            if (!walkStmts(loopp->stmtsp(), g, body, whyr)) return false;
            return walkStmts(loopp->contsp(), g, body, whyr);
        }
        if (AstLoopTest* const testp = VN_CAST(stmtp, LoopTest)) {
            if (readsUndefined(testp->condp(), nullptr, g, defined)) {
                whyr = Bail::READ_BEFORE_WRITE;
                return false;
            }
            return true;
        }
        if (AstJumpBlock* const jblockp = VN_CAST(stmtp, JumpBlock)) {
            Defined inner = defined;  // A jump may skip the tail: define nothing
            return walkStmts(jblockp->stmtsp(), g, inner, whyr);
        }
        whyr = Bail::UNSUPPORTED_STMT;  // V3Table and friends may leave odd shapes
        return false;
    }

    // No part of a continuous-assign group may read the target: shadow-reads-shadow reads stale.
    bool analyseAssignGroup(const Group* g, Bail& whyr) const {
        for (AstAssignW* const awp : g->partialps) {
            if (impure(awp)) {
                whyr = Bail::IMPURE;
                return false;
            }
            bool selfRead = false;
            awp->rhsp()->foreach([&](AstVarRef* refp) {
                if (g->members.count(refp->varScopep())) selfRead = true;
            });
            if (selfRead) {
                whyr = Bail::READ_BEFORE_WRITE;
                return false;
            }
        }
        return true;
    }

    // An unpacked array covered by unconditional constant-index element assigns, and never
    // read, is defined whatever the order: seed it defined, zeroing the shadow to assemble into.
    void seedElementWrittenArrays(Group* g, Defined& defined) const {
        // Walked once and shared: each element-written array grows this same block, so
        // re-walking it per candidate would be quadratic in the block size.
        struct RefInfo final {
            bool anyRead = false;
            int writes = 0;
        };
        struct ElemInfo final {
            std::map<std::vector<int32_t>, std::vector<PartExtent>> byElem;
            int matched = 0;
            size_t depth = 0;
            bool mixedDepth = false;
        };
        std::unordered_map<const AstVarScope*, RefInfo> refs;
        g->alwaysp->foreach([&](AstVarRef* refp) {
            const AstVarScope* const u = refp->varScopep();
            if (!VN_IS(u->varp()->dtypeSkipRefp(), UnpackArrayDType)) return;
            RefInfo& ri = refs[u];
            if (!refp->access().isWriteOnly()) ri.anyRead = true;
            if (!refp->access().isReadOnly()) ++ri.writes;
        });
        std::unordered_map<const AstVarScope*, ElemInfo> elems;
        for (AstNode* sp = g->alwaysp->stmtsp(); sp; sp = sp->nextp()) {
            AstNodeAssign* const asgnp = VN_CAST(sp, NodeAssign);
            if (!asgnp) continue;
            PartExtent ext;
            const AstVarScope* const u = partialLhs(asgnp->lhsp(), ext);
            if (!u || ext.idxs.empty() || !refs.count(u)) continue;
            ElemInfo& ei = elems[u];
            if (ei.mixedDepth) continue;
            if (!ei.matched) ei.depth = ext.idxs.size();
            if (ext.idxs.size() != ei.depth) {
                ei.mixedDepth = true;
                continue;
            }
            ei.byElem[ext.idxs].push_back(ext);
            ++ei.matched;
        }

        const auto trySeed = [&](AstVarScope* u) {
            const auto rit = refs.find(u);
            if (rit == refs.end()) return;
            if (rit->second.anyRead || !rit->second.writes) return;
            const auto eit = elems.find(u);
            if (eit == elems.end() || eit->second.mixedDepth) return;
            if (eit->second.matched != rit->second.writes) return;  // Nested or variable-indexed
            const size_t depth = eit->second.depth;
            std::map<std::vector<int32_t>, std::vector<PartExtent>>& byElem = eit->second.byElem;
            // An element this block never writes has no driver at all, so zeroing the shadow
            // would invent a value the model's own storage does not hold. Prove full coverage.
            AstNodeDType* dtypep = u->varp()->dtypeSkipRefp();
            size_t elements = 1;
            std::vector<int32_t> dimElements;  // Outermost first; idxs is innermost first
            for (size_t d = 0; d < depth; ++d) {
                const AstUnpackArrayDType* const adtypep = VN_CAST(dtypep, UnpackArrayDType);
                if (!adtypep) return;
                const size_t extent = static_cast<size_t>(adtypep->elementsConst());
                // A wrapped product would prove coverage of an element count nobody has
                if (extent && elements > std::numeric_limits<size_t>::max() / extent) return;
                dimElements.push_back(adtypep->elementsConst());
                elements *= extent;
                dtypep = adtypep->subDTypep()->skipRefp();
            }
            // A select shallower than the array leaves the sub-array's own extent unproven
            if (VN_IS(dtypep, UnpackArrayDType)) return;
            if (byElem.size() != elements) return;
            const int elemWidth = dtypep->width();
            // Per bucket, LSB-sorted so one walk proves contiguous coverage from bit 0
            for (auto& pr : byElem) {
                for (size_t k = 0; k < depth; ++k) {
                    const int32_t idx = pr.first[depth - 1 - k];
                    if (idx < 0 || idx >= dimElements[k]) return;
                }
                std::vector<PartExtent>& bucket = pr.second;
                std::sort(bucket.begin(), bucket.end(),
                          [](const PartExtent& a, const PartExtent& b) { return a.lsb < b.lsb; });
                int covered = 0;
                for (const PartExtent& ext : bucket) {
                    if (ext.lsb != covered) return;  // A gap, or an overlap
                    covered += ext.width;
                }
                if (covered != elemWidth) return;
            }
            defined.insert(u);
            g->zeroInitps.push_back(u);
        };
        for (AstVarScope* const t : g->targets) trySeed(t);
        for (AstVarScope* const t : g->temps) trySeed(t);
    }

    bool analyseBlockGroup(Group* g, Bail& whyr) const {
        for (AstNode* sp = g->alwaysp->stmtsp(); sp; sp = sp->nextp()) {
            if (impure(sp)) {
                whyr = Bail::IMPURE;
                return false;
            }
        }
        Defined defined;
        seedElementWrittenArrays(g, defined);
        if (!walkStmts(g->alwaysp->stmtsp(), g, defined, whyr)) return false;
        for (AstVarScope* const t : g->targets) {
            if (!defined.count(t)) {
                whyr = Bail::LATCH;  // Not written on every path
                return false;
            }
        }
        return true;
    }

    void analyseGroups() {
        for (const auto& ownp : m_groups) {
            Group* const g = ownp.get();
            if (!g->live) continue;
            Bail why = Bail::UNSUPPORTED_STMT;
            const bool ok = g->alwaysp ? analyseBlockGroup(g, why) : analyseAssignGroup(g, why);
            if (!ok) killGroupsOfKey(g->keyp, why);
        }
    }

    // METHODS - Scheduling

    // One loose vlSelf-relative func per instance, and a cross-scope VarRef descopes absolute.
    void restrictMultiInstanceToLocalCones() {
        std::unordered_set<const AstVar*> unshareable;
        for (const auto& ownp : m_groups) {
            const Group* const g = ownp.get();
            if (!g->live || instancesOf(g->keyp) <= 1) continue;
            bool bad = false;
            for (AstVarScope* const t : g->targets)
                if (t->scopep() != g->scopep) bad = true;
            if (!bad) {
                bad = existsInStmt(g, [&](const AstVarRef* refp) {
                    return refp->varScopep()->scopep() != g->scopep;
                });
            }
            if (bad) unshareable.insert(g->keyp);
        }
        for (const auto& ownp : m_groups) {
            Group* const g = ownp.get();
            if (g->live && unshareable.count(g->keyp))
                killGroupsOfKey(g->keyp, Bail::CROSS_SCOPE_CONE);
        }
    }

    // u defines a variable v reads: edge u -> v.
    void buildDependencyGraph() {
        for (const auto& ownp : m_groups) {
            Group* const g = ownp.get();
            if (!g->live) continue;
            g->vtxp = new GroupVertex{&m_depGraph, g};
        }
        for (const auto& ownp : m_groups) {
            Group* const g = ownp.get();
            if (!g->live) continue;
            forEachStmt(g, [&](AstNode* sp) {
                sp->foreach([&](AstVarRef* refp) {
                    if (refp->access().isWriteOnly()) return;
                    AstVarScope* u = refp->varScopep();
                    if (g->members.count(u)) return;
                    if (AstVarScope* const srcp = retargetSubstituteFor(u, g)) u = srcp;
                    Group* const ugp = liveGroupOf(u);
                    if (!ugp || ugp == g) return;
                    new V3GraphEdge{&m_depGraph, ugp->vtxp, g->vtxp, 1};
                });
            });
        }
        m_depGraph.removeRedundantEdgesMax(&V3GraphEdge::followAlwaysTrue);
    }

    // Edges into a killed group must stop counting against its consumers' in-degree.
    void dropDeadVertices() {
        for (const auto& ownp : m_groups) {
            Group* const g = ownp.get();
            if (g->live || !g->vtxp) continue;
            VL_DO_DANGLING(g->vtxp->unlinkDelete(&m_depGraph), g->vtxp);
            g->vtxp = nullptr;
        }
    }

    // A group downstream of a cycle still reconstructs cold, so only SCC members are retained.
    void splitCyclesRetainCores() {
        m_depGraph.stronglyConnected(&V3GraphEdge::followAlwaysTrue);
        for (const auto& ownp : m_groups) {
            Group* const g = ownp.get();
            // Non-zero color = a real comb cycle (multi-node SCC or self-loop): retain it.
            if (g->live && g->vtxp->color() != 0) killGroupsOfKey(g->keyp, Bail::COMB_CYCLE);
        }
        dropDeadVertices();
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
        // Survivors are a DAG, so a leftover is a bug: retain it rather than let V3Dead drop it.
        const std::unordered_set<Group*> ordered{m_ordered.begin(), m_ordered.end()};
        for (Group* const g : live) {
            if (g->live && !ordered.count(g)) killGroupsOfKey(g->keyp, Bail::TOPO_LEFTOVER);
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
            if (!g->live) continue;
            AstVarScope* u = soleCopySource(g);
            if (!u) continue;
            AstVarScope* const targetp = g->targets[0];
            // A helper target's cone exists only to be copied; converting it leaves it unread.
            if (m_helperTargets.count(targetp)) continue;
            const auto tit = m_targetOf.find(u);
            if (tit != m_targetOf.end()) {
                const auto cit = chainEnd.find(tit->second);
                if (cit != chainEnd.end()) u = cit->second;
            }
            // The source must hold storage, and nothing in a live group does.
            if (liveGroupOf(u)) continue;
            chainEnd.emplace(g, u);
            if (u == targetp || !canCopyFrom(targetp, u)) continue;
            cand.push_back(g);
            ++candInstances[targetp->varp()];
        }
        std::unordered_set<Group*> dropped;
        for (Group* const g : cand) {
            AstVarScope* const targetp = g->targets[0];
            if (!claimPerVar(candInstances, targetp->varp())) continue;
            const auto cit = chainEnd.find(g);
            UASSERT_OBJ(cit != chainEnd.end(), targetp->varp(),
                        "--vpi-lazy copy candidate has no resolved source");
            g->copyFromp = cit->second;
            g->live = false;
            dropped.insert(g);
            m_retargetSrcOf.emplace(targetp, g->copyFromp);
            m_copyGroups.push_back(g);
        }
        dropFromOrdered(dropped);
    }

    // Runs after copyStoredSources, so liveGroupOf() already says what kept its storage.
    void crossScopeCopySources() {
        std::unordered_map<const AstVar*, int> viable;
        std::vector<AstVarScope*> cand;
        for (AstVarScope* const dstp : m_xscopeOrder) {
            AstVarScope* const srcp = m_xscopeSrcOf.at(dstp);
            if (!dstp->varp()->isSigVpiLazyRWPublic()) continue;  // retained meanwhile
            if (m_groupOf.count(dstp)) continue;  // a group writes it too
            if (liveGroupOf(srcp) || m_retargetSrcOf.count(srcp)) continue;  // no own storage
            cand.push_back(dstp);
            ++viable[dstp->varp()];
        }
        std::unordered_set<const AstVar*> claimed;
        for (AstVarScope* const dstp : cand)
            if (claimPerVar(viable, dstp->varp())) claimed.insert(dstp->varp());
        // Claiming a target costs it its storage, so one that is also some other candidate's
        // source must not be claimed. Dropping only ever removes sources, so one pass suffices.
        for (AstVarScope* const dstp : cand)
            if (claimed.count(dstp->varp())) claimed.erase(m_xscopeSrcOf.at(dstp)->varp());
        for (AstVarScope* const dstp : cand) {
            if (!claimed.count(dstp->varp())) continue;
            // The retarget is what keeps a cone reading this target off pinBoundary().
            m_retargetSrcOf.emplace(dstp, m_xscopeSrcOf.at(dstp));
            m_crossScopeCopyTargets.push_back(dstp);
        }
    }

    // Cross-scope copies: a shadow and a Syms-relative descriptor source, no func, no epoch slot.
    void emitCrossScopeCopies() {
        for (AstVarScope* const dstp : m_crossScopeCopyTargets) {
            if (dstp->varp()->isSigUserRWPublic() || dstp->varp()->isSigVpiLazyRetained())
                continue;
            AstVarScope* const srcp = m_xscopeSrcOf.at(dstp);
            pinBoundary(srcp);
            AstVarScope* const shadowp = crossScopeShadow(dstp);
            m_ctx.m_crossScopeSrcs.push_back(
                CrossScopeSrcNames{dstp->scopep()->name(), shadowp->varp()->name(),
                                   srcp->scopep()->name(), srcp->varp()->name()});
            dstp->varp()->vpiLazyRole(VVpiLazyRole::NONE);
            ++m_reconstructed;
            ++m_crossScopeCopies;
        }
    }

    // Reads pre-optimisation statements, so a width change appears as a Cast/Extend and is
    // refused: memcpy cannot convert.
    AstVarScope* soleCopySource(Group* g) const {
        if (g->copySrcValid) return g->copySrcp;
        g->copySrcValid = true;
        g->copySrcp = soleCopySourceCalc(g);
        return g->copySrcp;
    }

    AstVarScope* soleCopySourceCalc(const Group* g) const {
        if (g->targets.size() != 1 || !g->temps.empty()) return nullptr;
        AstNode* onlyp = nullptr;
        size_t n = 0;
        forEachStmt(g, [&](AstNode* sp) {
            onlyp = sp;
            ++n;
        });
        if (n != 1) return nullptr;
        const AstNodeAssign* const asgnp = VN_CAST(onlyp, NodeAssign);
        if (!asgnp) return nullptr;
        const AstVarRef* const lhsp = VN_CAST(asgnp->lhsp(), VarRef);
        const AstVarRef* const rhsp = VN_CAST(asgnp->rhsp(), VarRef);
        if (!lhsp || !rhsp || lhsp->varScopep() != g->targets[0]) return nullptr;
        return rhsp->varScopep();
    }

    // Layouts must match exactly: the descriptor refreshes by memcpy of totalSize() bytes.
    // entSize() has no width for VLVT_REAL or VLVT_STRING, so such a row would copy nothing,
    // and a std::string could not be raw-copied even if it did; those stay cones.
    static bool sameLayout(const AstVarScope* a, const AstVarScope* b) {
        return !a->varp()->isDouble() && !a->varp()->isString()
               && a->varp()->vlEnumType() == b->varp()->vlEnumType()
               && a->varp()->dtypep()->widthTotalBytes() == b->varp()->dtypep()->widthTotalBytes()
               && a->varp()->dtypep()->similarDType(b->varp()->dtypep());
    }

    void foldTrivialCopyGroups() {
        // Topological order, so a chain resolves to a source that is not itself folded.
        std::unordered_map<const Group*, AstVarScope*> resolvedSrc;
        std::unordered_map<const AstVar*, int> foldable;  // Instances of a key that can fold
        for (Group* const g : m_ordered) {
            if (!g->live) continue;
            AstVarScope* u = soleCopySource(g);
            if (u) {
                if (AstVarScope* const srcp = retargetSubstituteFor(u, g)) u = srcp;
                Group* const ugp = liveGroupOf(u);
                // m_groupOf covers temps too, and only a target has a shadow with a func to call
                if (!ugp || ugp == g || !ugp->slotOf.count(u)) {
                    u = nullptr;
                } else {
                    const auto rit = resolvedSrc.find(ugp);
                    if (rit != resolvedSrc.end()) u = rit->second;  // Source folded too; chase it
                    if (u && !sameLayout(g->targets[0], u)) u = nullptr;
                }
            }
            if (!u) continue;
            resolvedSrc.emplace(g, u);
            ++foldable[g->keyp];
            g->copyFromp = u;
        }
        // m_ordered order, not foldable's, so what is emitted does not depend on pointer hashing
        std::unordered_set<Group*> dropped;
        for (Group* const g : m_ordered) {
            if (!g->copyFromp) continue;
            if (!claimPerVar(foldable, g->keyp)) {  // One instance could not fold: none may
                g->copyFromp = nullptr;
                continue;
            }
            // srcOffset is from the target's own selfp, so the source must be the same instance.
            if (g->copyFromp->scopep() != g->targets[0]->scopep()) {
                g->copyFromp = nullptr;
                continue;
            }
            // The source must still emit a cone of its own, else there is no shadow to copy
            const Group* const srcGroupp = liveGroupOf(g->copyFromp);
            if (!srcGroupp || dropped.count(const_cast<Group*>(srcGroupp))) {
                g->copyFromp = nullptr;
                continue;
            }
            // Killing it makes the retarget safe: a consumer that cannot substitute pins instead.
            m_retargetSrcOf.emplace(g->targets[0], g->copyFromp);
            m_foldedCopies.push_back(g);
            g->live = false;
            if (g->bodyp) VL_DO_DANGLING(g->bodyp->deleteTree(), g->bodyp);
            dropped.insert(g);
        }
        dropFromOrdered(dropped);
    }

    // METHODS - Emission

    // Design-global group id, shared by every instance of the group's module.
    int gidOf(const Group* g) {
        const auto it = m_gidOfKey.find(g->keyp);
        if (it != m_gidOfKey.end()) return it->second;
        const int gid = m_nextGid++;
        m_gidOfKey.emplace(g->keyp, gid);
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
        if (tableFacing) {
            funcp->voidSelfArg(true);
            funcp->argTypes("void* voidSelf");
        }
        funcp->slow(true);
        // Called only via the syms recon-fn array, an out-of-tree address-take no pass can see.
        funcp->entryPoint(true);
        // One func serves every instance: V3Gate/V3Dfg must not substitute instance expressions.
        funcp->vpiLazyReconstruct(true);
        funcp->declPrivate(false);
        scopep->addBlocksp(funcp);
        return funcp;
    }

    void assignEpochSlots() {
        std::unordered_map<const AstVar*, int> slotOfKey;
        std::unordered_map<AstNodeModule*, int> slotsOfMod;
        std::vector<AstNodeModule*> modOrder;  // Deterministic AstVar creation order
        for (Group* const g : m_ordered) {
            AstNodeModule* const modp = g->scopep->modp();
            UASSERT_OBJ(g->targets[0]->scopep()->modp() == modp, g->keyp,
                        "Lazy group key variable outside the group scope's module");
            const auto mpair = slotsOfMod.emplace(modp, 0);
            if (mpair.second) modOrder.push_back(modp);
            int& slots = mpair.first->second;
            const auto pair = slotOfKey.emplace(g->keyp, slots);
            if (pair.second) ++slots;
            g->epochSlot = pair.first->second;
        }
        for (AstNodeModule* const modp : modOrder) {
            const auto mit = slotsOfMod.find(modp);
            UASSERT_OBJ(mit != slotsOfMod.end(), modp,
                        "--vpi-lazy module has no epoch slot count");
            modp->addStmtsp(makeStampVar(m_epoch, modp, mit->second, EPOCH_NAME, false));
        }
    }

    // Deposit generations, per guarded row per instance. Assigned after the shadows exist, and
    // keyed by the shadow variable, so every instance of a module shares the numbering and the
    // runtime can turn a slot into one byte offset from any instance's base.
    void assignDepSlots() {
        std::unordered_map<const AstVar*, int> slotOfShadow;
        std::unordered_map<AstNodeModule*, int> slotsOfMod;
        std::vector<AstNodeModule*> modOrder;  // Deterministic AstVar creation order
        for (Group* const g : m_ordered) {
            AstNodeModule* const modp = g->scopep->modp();
            const auto mpair = slotsOfMod.emplace(modp, 0);
            if (mpair.second) modOrder.push_back(modp);
            int& slots = mpair.first->second;
            g->depSlots.assign(g->targets.size(), -1);
            for (size_t slot = 0; slot < g->targets.size(); ++slot) {
                AstVarScope* const t = g->targets[slot];
                // A helper target emits no VPI row, so nothing can deposit into it
                if (m_helperTargets.count(t)) continue;
                const auto sit = m_shadowOf.find(t);
                UASSERT_OBJ(sit != m_shadowOf.end(), t->varp(),
                            "--vpi-lazy deposit slot before the target's shadow");
                AstVar* const shadowVarp = sit->second->varp();
                const auto pair = slotOfShadow.emplace(shadowVarp, slots);
                if (pair.second) {
                    ++slots;
                    m_ctx.m_depSlotOfShadowName.emplace(shadowVarp->name(), pair.first->second);
                }
                g->depSlots[slot] = pair.first->second;
            }
        }
        for (AstNodeModule* const modp : modOrder) {
            const auto mit = slotsOfMod.find(modp);
            UASSERT_OBJ(mit != slotsOfMod.end(), modp, "--vpi-lazy module has no deposit count");
            if (!mit->second) continue;
            AstVar* const depVarp = makeStampVar(m_dep, modp, mit->second, DEP_NAME, true);
            // Next to __Vlazyepoch, so the two cold words share a line rather than sit
            // among signals
            const auto eit = m_epoch.varOfMod.find(modp);
            UASSERT_OBJ(eit != m_epoch.varOfMod.end(), modp,
                        "--vpi-lazy module has deposit slots but no epoch stamp array");
            eit->second->addNextHere(depVarp);
        }
    }

    // Freshness and deposit stamps, per instance: a shared slot would mark instance B fresh
    // after A ran. MODULETEMP being isTemp() is what forces the zero initializer, even under
    // --x-initial unique; a zero slot is even, so it can never equal the odd __Vm_lazyDepStamp.
    AstVar* makeStampVar(StampArray& arr, AstNodeModule* modp, int slots, const string& name,
                         bool pub) {
        FileLine* const flp = modp->fileline();
        AstUnpackArrayDType* const dtypep = new AstUnpackArrayDType{
            flp, modp->findUInt64DType(), new AstRange{flp, slots - 1, 0}};
        v3Global.rootp()->typeTablep()->addTypesp(dtypep);
        AstVar* const varp = new AstVar{flp, VVarType::MODULETEMP, name, dtypep};
        UASSERT_OBJ(varp->varType().isTemp(), varp, "Stamp array must be zero-initialized");
        varp->trace(false);
        // Only the VPI runtime writes the deposit array, through a byte offset no pass can see,
        // so without this the guards read a variable nothing assigns and are foldable.
        if (pub) varp->sigPublic(true);
        arr.varOfMod.emplace(modp, varp);
        return varp;
    }

    // Per-instance VarScope for the stamp array, so the guard can reference it as an AstVarRef.
    AstVarScope* stampFor(StampArray& arr, Group* g) {
        AstScope* const scopep = g->scopep;
        const auto it = arr.ofScope.find(scopep);
        if (it != arr.ofScope.end()) return it->second;
        const auto mit = arr.varOfMod.find(scopep->modp());
        UASSERT_OBJ(mit != arr.varOfMod.end(), scopep->modp(),
                    "--vpi-lazy module has no stamp array");
        AstVar* const varp = mit->second;
        AstVarScope* const vscp = new AstVarScope{varp->fileline(), scopep, varp};
        scopep->addVarsp(vscp);
        arr.ofScope.emplace(scopep, vscp);
        return vscp;
    }

    AstNodeExpr* newEpochSel(AstVarScope* epochVscp, int slot, VAccess access) {
        return new AstArraySel{m_funcFlp, new AstVarRef{m_funcFlp, epochVscp, access}, slot};
    }
    AstNodeExpr* newModelEpoch() { return new AstCExpr{m_funcFlp, "vlSymsp->__Vm_lazyEpoch", 64}; }

    AstNodeExpr* newDepSel(AstVarScope* depVscp, int slot) {
        return new AstArraySel{m_funcFlp, new AstVarRef{m_funcFlp, depVscp, VAccess::READ}, slot};
    }
    AstNodeExpr* newDepStamp() {
        return new AstCExpr{m_funcFlp, "vlSymsp->__Vm_lazyDepStamp", 64};
    }

    // The deposit slot a statement commits to, or -1 if it must always run. Only a statement
    // whose single written variable is a guarded row of this group qualifies: a write this scan
    // cannot see, or that a temp another cone reads shares, must never be suppressed.
    static int wrappableDepSlot(const std::unordered_map<const AstVarScope*, int>& slotOfShadow,
                                AstNode* stmtp) {
        AstVarScope* writtenp = nullptr;
        bool opaque = false;
        stmtp->foreach([&](AstNode* nodep) {
            if (opaque) return;
            if (AstVarRef* const refp = VN_CAST(nodep, VarRef)) {
                // An AstCReset names no variable of its own; its assign's lvalue is this ref
                if (refp->access().isReadOnly()) return;
                if (writtenp && writtenp != refp->varScopep()) opaque = true;
                writtenp = refp->varScopep();
            } else if (VN_IS(nodep, NodeCCall) || VN_IS(nodep, CStmt)) {
                opaque = true;  // May write rows this scan cannot enumerate
            }
        });
        if (opaque || !writtenp) return -1;
        const auto it = slotOfShadow.find(writtenp);
        return it == slotOfShadow.end() ? -1 : it->second;
    }

    // Guard each run of statements committing to one deposited row, so a deposit survives the
    // rebuild that every deposit forces on every cone (IEEE 1800-2023 38.34). Per row, not per
    // function: a cone writes up to four rows, and suppressing the function would freeze the
    // deposited row's siblings. 'headp' is already linked under its owner.
    void guardDepositedWrites(Group* g, const std::unordered_map<const AstVarScope*, int>& slots,
                              AstNode* headp) {
        AstNode* stmtp = headp;
        while (stmtp) {
            const int slot = wrappableDepSlot(slots, stmtp);
            if (slot < 0) {
                // A mixed statement still guards what it holds: a conditional overwrite of one
                // row is wrapped whole above, and only one that also writes a temp gets here.
                for (AstNode* const childp :
                     {stmtp->op1p(), stmtp->op2p(), stmtp->op3p(), stmtp->op4p()}) {
                    if (childp && VN_IS(childp, NodeStmt)) guardDepositedWrites(g, slots, childp);
                }
                stmtp = stmtp->nextp();
                continue;
            }
            AstNode* lastp = stmtp;
            while (lastp->nextp() && wrappableDepSlot(slots, lastp->nextp()) == slot) {
                lastp = lastp->nextp();
            }
            AstNode* const contp = lastp->nextp();
            AstIf* const guardp
                = new AstIf{m_funcFlp, new AstNeq{m_funcFlp, newDepSel(stampFor(m_dep, g), slot),
                                                  newDepStamp()}};
            stmtp->addHereThisAsNext(guardp);  // Takes the run's place in the list
            if (contp) contp->unlinkFrBackWithNext();
            guardp->addThensp(stmtp->unlinkFrBackWithNext());
            if (contp) guardp->addNextHere(contp);
            ++m_ctx.m_depGuards;
            stmtp = contp;
        }
    }

    AstVarScope* attachShadow(AstVarScope* origp, AstVar* shadowVarp, bool isNew) {
        // prepare() scans the pre-run VarScope order, which no shadow is in. A lazy role here
        // would go uncounted, and with it the retained re-settle path
        UASSERT_OBJ(!shadowVarp->isSigVpiLazyRWPublic() && !shadowVarp->isSigVpiLazyRetained(),
                    shadowVarp, "--vpi-lazy shadow must carry no lazy role");
        if (isNew) {
            shadowVarp->trace(false);
            shadowVarp->sigPublic(true);  // Keep as a struct member; don't optimize/localize
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

    AstVarScope* shadowForTarget(Group* g, size_t slot) {
        return targetShadow(g->targets[slot],
                            SHADOW_PREFIX + std::to_string(gidOf(g)) + "_" + std::to_string(slot));
    }

    // Shadow of a cross-scope copy target, which belongs to no group and so has no group id.
    AstVarScope* crossScopeShadow(AstVarScope* origp) {
        const int idx
            = m_xscopeShadowIdx.emplace(origp->varp(), m_xscopeShadowIdx.size()).first->second;
        return targetShadow(origp, std::string{SHADOW_PREFIX} + "x" + std::to_string(idx));
    }

    AstVarScope* targetShadow(AstVarScope* origp, const std::string& name) {
        const auto it = m_shadowOf.find(origp);
        if (it != m_shadowOf.end()) return it->second;
        AstVar* const origVarp = origp->varp();
        const auto vit = m_shadowVarOfOrig.find(origVarp);
        if (vit != m_shadowVarOfOrig.end()) return attachShadow(origp, vit->second, false);
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
        const auto it = m_shadowOf.find(origp);
        if (it != m_shadowOf.end()) return it->second;
        AstVar* const origVarp = origp->varp();
        const auto vit = m_shadowVarOfOrig.find(origVarp);
        if (vit != m_shadowVarOfOrig.end()) return attachShadow(origp, vit->second, false);
        const auto iit = m_tempIdxOfVar.find(origVarp);
        const int idx = iit != m_tempIdxOfVar.end() ? iit->second : m_nextTempIdx++;
        m_tempIdxOfVar.emplace(origVarp, idx);
        AstVar* const shadowVarp = new AstVar{
            origVarp->fileline(), VVarType::MODULETEMP,
            std::string{SHADOW_PREFIX} + "t" + std::to_string(idx), origVarp->dtypep()};
        shadowVarp->vpiLazyRole(VVpiLazyRole::SHADOW_TEMP);
        return attachShadow(origp, shadowVarp, true);
    }

    AstVarScope* shadowForMember(Group* g, AstVarScope* u) {
        const auto it = g->slotOf.find(u);
        return it != g->slotOf.end() ? shadowForTarget(g, it->second) : shadowForTemp(u);
    }

    // An AstAssignW must never sit under a CFunc, so continuous assigns are cloned as blocking.
    static AstNode* cloneBody(const Group* g) {
        AstNode* bodyp = nullptr;
        if (g->alwaysp) {
            bodyp = g->alwaysp->stmtsp()->cloneTree(true);
        } else {
            for (AstAssignW* const awp : g->partialps)
                bodyp = AstNode::addNext(bodyp, static_cast<AstNode*>(awp->cloneTree(false)));
        }
        std::vector<AstAssignW*> contps;
        bodyp->foreachAndNext([&](AstAssignW* nodep) { contps.push_back(nodep); });
        for (AstAssignW* const contp : contps) {
            AstAssign* const asgnp = new AstAssign{
                contp->fileline(), contp->lhsp()->unlinkFrBack(), contp->rhsp()->unlinkFrBack()};
            if (contp->backp()) {
                contp->replaceWith(asgnp);
            } else {  // The detached list head has no back to replace through
                UASSERT_OBJ(contp == bodyp, contp, "detached assign is not the body root");
                bodyp = asgnp;
                if (AstNode* const nextp = contp->nextp()) {
                    nextp->unlinkFrBackWithNext();
                    bodyp = AstNode::addNext(bodyp, nextp);
                }
            }
            VL_DO_DANGLING(contp->deleteTree(), contp);
        }
        return bodyp;
    }

    // The cone is shared by every instance, so it must read the variable, not a driver expression.
    void pinBoundary(AstVarScope* u) {
        AstVar* const uVarp = u->varp();
        if (uVarp->isPrimaryIO() || uVarp->isSigUserRWPublic() || uVarp->isSigVpiLazyRetained())
            return;
        if (uVarp->isSigUserRdPublic()) {
            // Retaining would arm the write gate on a row that refuses deposits.
            UASSERT_OBJ(!uVarp->isSigVpiLazyRWPublic(), uVarp, "public_flat_rd is still lazy");
            return;
        }
        if (uVarp->isSigVpiLazyRWPublic()) {
            m_fallback += instancesOf(uVarp);
            // Sequential/undriven operands hold storage regardless, so pinning them is free.
            const Bail why = hasCombDriver(u) ? combBoundaryReason(u) : Bail::BOUNDARY_OPERAND_SEQ;
            m_bailCount[static_cast<size_t>(why)] += instancesOf(uVarp);
        } else {
            // Storage kept only so a reconstruct function can read it.
            m_boundaryStorage += instancesOf(uVarp);
        }
        uVarp->vpiLazyRole(VVpiLazyRole::RETAINED);
    }

    // METHODS - Liveness prune

    // The group variables one statement reads (its own subtree only: foreach ignores nextp()).
    static void stmtRefs(AstNode* nodep, Defined& readsr) {
        nodep->foreach([&](AstVarRef* refp) {
            if (!refp->access().isWriteOnly()) readsr.insert(refp->varScopep());
        });
    }

    static std::vector<AstNode*> splitList(AstNode* listp) {
        std::vector<AstNode*> stmtps;
        while (listp) {
            AstNode* const nextp = listp->nextp();
            if (nextp) nextp->unlinkFrBackWithNext();
            stmtps.push_back(listp);
            listp = nextp;
        }
        return stmtps;
    }

    // 'neededr' only grows, so one backward pass suffices; no dead-store elimination.
    AstNode* pruneList(AstNode* listp, Defined& neededr) {
        std::vector<AstNode*> stmtps = splitList(listp);
        std::vector<bool> keep(stmtps.size(), true);
        for (size_t i = stmtps.size(); i-- > 0;) keep[i] = pruneStmt(stmtps[i], neededr);
        AstNode* newp = nullptr;
        for (size_t i = 0; i < stmtps.size(); ++i) {
            if (keep[i]) {
                newp = AstNode::addNext(newp, stmtps[i]);
            } else {
                ++m_prunedStmts;
                VL_DO_DANGLING(stmtps[i]->deleteTree(), stmtps[i]);
            }
        }
        return newp;
    }

    // Prunes inside 'stmtp' too; everything is pure, so a drop shows only through what it writes.
    bool pruneStmt(AstNode* stmtp, Defined& neededr) {
        if (VN_IS(stmtp, Comment)) return false;
        if (VN_IS(stmtp, JumpGo)) return true;
        if (AstNodeAssign* const asgnp = VN_CAST(stmtp, NodeAssign)) {
            bool live = false;
            asgnp->lhsp()->foreach([&](AstVarRef* refp) {
                if (!refp->access().isReadOnly() && neededr.count(refp->varScopep())) live = true;
            });
            if (!live) return false;
            stmtRefs(asgnp, neededr);
            return true;
        }
        if (AstNodeIf* const ifp = VN_CAST(stmtp, NodeIf)) {
            AstNode* thensp = ifp->thensp();
            if (thensp) thensp->unlinkFrBackWithNext();
            AstNode* elsesp = ifp->elsesp();
            if (elsesp) elsesp->unlinkFrBackWithNext();
            thensp = pruneList(thensp, neededr);
            elsesp = pruneList(elsesp, neededr);
            if (!thensp && !elsesp) return false;
            if (thensp) ifp->addThensp(thensp);
            if (elsesp) ifp->addElsesp(elsesp);
            stmtRefs(ifp->condp(), neededr);
            return true;
        }
        if (AstJumpBlock* const jblockp = VN_CAST(stmtp, JumpBlock)) {
            AstNode* stmtsp = jblockp->stmtsp();
            if (stmtsp) stmtsp->unlinkFrBackWithNext();
            stmtsp = pruneList(stmtsp, neededr);
            if (!stmtsp) return false;
            jblockp->addStmtsp(stmtsp);
            return true;
        }
        stmtRefs(stmtp, neededr);  // Loops and any unmodelled shape: keep whole
        return true;
    }

    // Before operand rewiring, so the cone refresh calls follow the pruned reads. REVERSE topo
    // order makes temp liveness exact: every consumer is pruned first.
    void pruneBodies() {
        std::vector<Group*> repps;
        std::unordered_set<AstVar*> seenKeys;
        for (Group* const g : m_ordered)
            if (seenKeys.insert(g->keyp).second) repps.push_back(g);
        std::unordered_set<const AstVar*> liveReads;  // What a pruned body still reads
        for (size_t i = repps.size(); i-- > 0;) {
            Group* const g = repps[i];
            g->neededps.insert(g->targets.begin(), g->targets.end());
            for (AstVarScope* const u : g->temps)
                if (liveReads.count(u->varp())) g->neededps.insert(u);
            g->bodyp = pruneList(cloneBody(g), g->neededps);
            UASSERT_OBJ(g->bodyp, g->keyp, "--vpi-lazy pruned a group's whole body");
            // Mirrors emitReconstructions's rewiring: a read on another group's shadow counts.
            g->bodyp->foreachAndNext([&](AstVarRef* refp) {
                if (refp->access().isWriteOnly()) return;
                AstVarScope* u = refp->varScopep();
                if (g->members.count(u)) return;
                if (AstVarScope* const srcp = retargetSubstituteFor(u, g)) u = srcp;
                const Group* const ugp = liveGroupOf(u);
                if (!ugp || ugp == g) return;
                liveReads.insert(u->varp());
            });
        }
    }

    // Added to the tree at once, so remapped clones' dtypep() links survive V3Dead's dtype GC.
    void emitReconstructions() {
        m_fallback = m_combBailRetained;
        m_funcFlp = m_topScopep->fileline();
        assignEpochSlots();
        // Every instance needs its own shadow VarScope for its descriptor, and a deposit slot is
        // keyed by the shadow, so every shadow exists before any slot or statement is made.
        for (Group* const g : m_ordered) {
            for (size_t slot = 0; slot < g->targets.size(); ++slot) shadowForTarget(g, slot);
        }
        assignDepSlots();
        for (Group* const g : m_ordered) {
            const auto fit = m_funcOfKey.find(g->keyp);
            if (fit != m_funcOfKey.end()) {
                g->funcp = fit->second;
                continue;  // non-representative instance: share the func
            }
            AstCFunc* const funcp = newReconFunc(g->scopep, reconFuncName(g), true);
            g->funcp = funcp;
            m_funcOfKey.emplace(g->keyp, funcp);
            // What V3EmitCSyms routes a row's refreshp to, here and on any fold of this shadow
            for (AstVarScope* const t : g->targets) {
                const auto tit = m_shadowOf.find(t);
                UASSERT_OBJ(tit != m_shadowOf.end(), t->varp(),
                            "--vpi-lazy reconstruct target has no shadow");
                tit->second->varp()->lazyReconFuncp(funcp);
            }

            // Redirect group variables to their shadows; no re-typing, a shadow keeps its dtype.
            AstNode* const bodyp = g->bodyp;
            std::unordered_set<Group*> seenOps;
            std::vector<Group*> coneOps;
            bodyp->foreachAndNext([&](AstVarRef* refp) {
                AstVarScope* u = refp->varScopep();
                if (g->members.count(u)) {  // Read or written by this group
                    AstVarScope* const shadowp = shadowForMember(g, u);
                    refp->varScopep(shadowp);
                    refp->varp(shadowp->varp());
                    return;
                }
                if (AstVarScope* const srcp = retargetSubstituteFor(u, g)) {
                    u = srcp;
                    refp->varScopep(srcp);
                    refp->varp(srcp->varp());
                    refp->dtypeFrom(srcp->varp());
                }
                Group* const ugp = liveGroupOf(u);
                if (ugp && ugp != g) {
                    // Operand is reconstructed too: read its shadow, calling its func to freshen.
                    UASSERT_OBJ(ugp->funcp, g->keyp,
                                "--vpi-lazy cone operand ordered after its consumer");
                    AstVarScope* const shadowp = shadowForMember(ugp, u);
                    refp->varScopep(shadowp);
                    refp->varp(shadowp->varp());
                    if (seenOps.insert(ugp).second) coneOps.push_back(ugp);
                    return;
                }
                pinBoundary(u);
            });

            // (1) epoch guard. Not an early return: split-cfuncs may move the body elsewhere.
            AstVarScope* const epochVscp = stampFor(m_epoch, g);
            AstIf* const guardp = new AstIf{
                m_funcFlp,
                new AstNeq{m_funcFlp, newEpochSel(epochVscp, g->epochSlot, VAccess::READ),
                           newModelEpoch()}};
            funcp->addStmtsp(guardp);
            guardp->addThensp(new AstAssign{
                m_funcFlp, newEpochSel(epochVscp, g->epochSlot, VAccess::WRITE), newModelEpoch()});
            // The guard cannot move with the body; /4 slack for the optimizer growing it.
            AstCFunc* bodyFuncp = nullptr;
            if (const int splitAt = v3Global.opt.outputSplitCFuncs()) {
                int nodes = 0;
                for (AstNode* sp = bodyp; sp; sp = sp->nextp()) nodes += sp->nodeCount();
                if (nodes >= splitAt / 4) {
                    bodyFuncp = newReconFunc(g->scopep, reconBodyFuncName(g), false);
                    AstCCall* const bodyCallp = new AstCCall{m_funcFlp, bodyFuncp};
                    bodyCallp->dtypeSetVoid();
                    guardp->addThensp(bodyCallp->makeStmt());
                }
            }
            const auto addBodyStmt = [&](AstNode* stmtp) {
                if (bodyFuncp) {
                    bodyFuncp->addStmtsp(stmtp);
                } else {
                    guardp->addThensp(stmtp);
                }
            };
            // (2) refresh the operand cone; topo order guarantees each operand's func exists.
            for (Group* const ugp : coneOps) {
                AstCCall* const callp = new AstCCall{m_funcFlp, ugp->funcp};
                callp->dtypeSetVoid();
                addBodyStmt(callp->makeStmt());
            }
            // (3) zero the shadows a partial assembly builds up, then (4) run its statements.
            for (AstVarScope* const u : g->zeroInitps) {
                if (!g->neededps.count(u)) continue;  // Its element writes were pruned away
                AstVarScope* const shadowp = shadowForMember(g, u);
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
                addBodyStmt(new AstAssign{
                    m_funcFlp, new AstVarRef{m_funcFlp, shadowp, VAccess::WRITE}, zerop});
            }
            addBodyStmt(bodyp);

            // (5) after the body is final, because the zero-initializers need guarding too or
            // a partially assembled row would be zeroed out from under a deposit
            std::unordered_map<const AstVarScope*, int> slotOfShadow;
            for (size_t slot = 0; slot < g->targets.size(); ++slot) {
                if (g->depSlots[slot] >= 0) {
                    slotOfShadow.emplace(shadowForTarget(g, slot), g->depSlots[slot]);
                }
            }
            if (!slotOfShadow.empty()) {
                guardDepositedWrites(g, slotOfShadow,
                                     bodyFuncp ? bodyFuncp->stmtsp() : guardp->thensp());
            }

            // The original signals' VPI presence now comes from the shadows.
            for (AstVarScope* const t : g->targets) {
                if (m_helperTargets.count(t)) {
                    ++m_helperCount;  // Never lazy-flagged; read only by the copies of it
                    continue;
                }
                t->varp()->vpiLazyRole(VVpiLazyRole::NONE);
                m_reconstructed += instancesOf(t->varp());
            }
        }
        emitCopyGroups();
        emitFoldedCopies();
        emitCrossScopeCopies();
    }

    // A shadow row on top of the retained row a consumer pinned would name the signal twice.
    static bool targetPinnedAlready(const Group* g) {
        const AstVar* const varp = g->targets[0]->varp();
        return varp->isSigUserRWPublic() || varp->isSigVpiLazyRetained();
    }

    void bindCopyRow(Group* g, AstVar* srcVarp) {
        AstVar* const shadowVarp = shadowForTarget(g, 0)->varp();
        if (AstVar* const prevp = shadowVarp->lazyCopySrc()) {
            UASSERT_OBJ(prevp == srcVarp, shadowVarp,
                        "--vpi-lazy copy instances disagree on their source");
        } else {
            shadowVarp->lazyCopySrc(srcVarp);
        }
        AstVar* const targetVarp = g->targets[0]->varp();
        targetVarp->vpiLazyRole(VVpiLazyRole::NONE);
        m_reconstructed += instancesOf(targetVarp);
    }

    // Folded cones: a shadow pointed at the source's, whose func the descriptor calls.
    void emitFoldedCopies() {
        for (Group* const g : m_foldedCopies) {
            if (targetPinnedAlready(g)) continue;
            const auto sit = m_shadowOf.find(g->copyFromp);
            UASSERT_OBJ(sit != m_shadowOf.end(), g->copyFromp->varp(),
                        "--vpi-lazy folded copy source has no shadow");
            AstVar* const srcShadowVarp = sit->second->varp();
            UASSERT_OBJ(srcShadowVarp->lazyReconFuncp(), srcShadowVarp,
                        "--vpi-lazy folded copy source has no reconstruct func");
            bindCopyRow(g, srcShadowVarp);
            ++m_foldedCount;
        }
    }

    // Copies of a stored variable: a shadow and a descriptor source, no func, no epoch slot.
    void emitCopyGroups() {
        for (Group* const g : m_copyGroups) {
            if (targetPinnedAlready(g)) continue;
            pinBoundary(g->copyFromp);  // The cone this row replaced would have pinned it too
            bindCopyRow(g, g->copyFromp->varp());
            ++m_copyCount;
        }
    }

    // A still-flagged VarScope is a residual: retain it, keeping the VPI set a superset of
    // --public-flat-rw's. Kind exclusions govern what may be reconstructed, not what may be
    // retained: else V3Gate substitutes the driver away and the row reads zero for ever.
    void retainCompletenessFloor() {
        for (AstVarScope* const vscp : m_gather.m_vscOrder) {
            AstVar* const varp = vscp->varp();
            if (!varp->isSigVpiLazyRWPublic()) continue;  // reconstructed / retained already
            if (storagePinnedElsewhere(varp)) continue;  // only exclusions bail
            const int insts = instancesOf(varp);
            m_floorReason[floorReason(vscp)] += insts;
            UINFO(9, "vpi-lazy floor: " << floorReason(vscp) << " " << vscp->name());
            retainTarget(vscp, Bail::COMPLETENESS_FLOOR);  // flips the shared AstVar flag once
            m_floorRetained += insts;  // counted once per AstVar (guard above)
        }
    }

    // A floor residual is one no classifier claimed, so no bail count records its shape.
    const char* floorReason(AstVarScope* vscp) {
        const AstVar* const varp = vscp->varp();
        if (varp->isIO()) return hasCombDriver(vscp) ? "port (comb-driven)" : "port (other)";
        if (!reconstructableKind(varp)) return "dtype";
        const int writes = writeCountOf(vscp);
        if (writes == 0) return "undriven";
        // A comb driver means V3Inline moved the readers to the source net, not that none exist.
        if (readCountOf(vscp) == 0 && !hasCombDriver(vscp)) return "sequential";
        if (writes > 1) return "multidriven";
        return hasCombDriver(vscp) ? "comb (unclaimed)" : "sequential";
    }

    void reportStats() {
        const size_t reconstructedMembers = m_shadowVarOfOrig.size();
        UINFO(3, "vpi-lazy: reconstructed="
                     << m_reconstructed << " groups=" << m_ordered.size()
                     << " members=" << reconstructedMembers << " fallback=" << m_fallback
                     << " copyGroups=" << m_copyCount << " crossScopeCopies=" << m_crossScopeCopies
                     << " foldedCopies=" << m_foldedCount << " prunedStmts=" << m_prunedStmts
                     << " helpers=" << m_helperCount << " floorRetained=" << m_floorRetained);
        if (v3Global.opt.stats()) {
            V3Stats::addStat("VPI, lazy reconstructed", m_reconstructed);
            V3Stats::addStat("VPI, lazy groups", m_ordered.size());
            V3Stats::addStat("VPI, lazy reconstructed members", reconstructedMembers);
            V3Stats::addStat("VPI, lazy fallback retained", m_fallback);
            V3Stats::addStat("VPI, lazy boundary storage pinned", m_boundaryStorage);
            V3Stats::addStat("VPI, lazy copy descriptors", m_copyCount);
            V3Stats::addStat("VPI, lazy cross-scope copy descriptors", m_crossScopeCopies);
            V3Stats::addStat("VPI, lazy folded copy cones", m_foldedCount);
            V3Stats::addStat("VPI, lazy helper targets", m_helperCount);
            V3Stats::addStat("VPI, lazy pruned statements", m_prunedStmts);
            V3Stats::addStat("VPI, lazy floor retained", m_floorRetained);
            for (const auto& pr : m_floorReason)
                V3Stats::addStat(std::string{"VPI, lazy floor residual, "} + pr.first, pr.second);
            for (size_t i = 0; i < static_cast<size_t>(Bail::_COUNT); ++i) {
                if (m_bailCount[i]) {
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
    {
        VpiLazyPreparer preparer{nodep, topScopep, ctx};
        preparer.run();

        // Residuals by name, not pointer: V3Dead may delete the AstVar, and a freed slot can be
        // reused. Both roles are only ever set through a scoped variable the gather walk already
        // saw, so its order holds every one of them.
        bool anyRetained = false;
        for (const AstVarScope* const vscp : preparer.vscOrder()) {
            const AstVar* const varp = vscp->varp();
            if (varp->isSigVpiLazyRWPublic()) ctx.m_residualNames.emplace(vscp->name());
            if (varp->isSigVpiLazyRetained()) anyRetained = true;
        }
        // A deposit into a retained signal is propagated by re-running 'settle' on the next eval.
        if (anyRetained) v3Global.setHasVpiLazyRetained();
    }

    if (v3Global.opt.stats()) {
        V3Stats::addStat("VPI, lazy residual un-retained", ctx.m_residualNames.size());
    }

    V3Global::dumpCheckGlobalTree("vpi-lazy-prepare", 0, dumpTreeEitherLevel() >= 3);
}

//######################################################################

namespace {

// Everything resolveCrossScopeSrcs() needs from the tree, in one walk: the AstScope of each
// wanted scope name, the module-level AstVar of each wanted variable name, and each module's
// deposit array and reconstruct shadows.
class CrossScopeGatherVisitor final : public VNVisitorConst {
    // STATE
    V3VpiLazyContext& m_ctx;
    const std::set<std::string>& m_wantScopes;
    const std::set<std::string>& m_wantVars;
    const bool m_wantDepWords;
    const AstNodeModule* m_modp = nullptr;
    bool m_modLevel = false;  // Directly under a module's stmtsp
    const AstVar* m_depVarp = nullptr;
    std::vector<const AstVar*> m_shadowps;

public:
    std::map<std::string, const AstScope*> m_scopeps;
    std::map<std::pair<const AstNodeModule*, std::string>, const AstVar*> m_varps;

private:
    // Bind the deposit slots emitReconstructions() recorded by name to the surviving tree. A
    // cone row's descriptor carries the byte offset of its word, so V3EmitCSyms needs the
    // module's array member (for offsetof, under its protected name) as well as the slot.
    void resolveDepWords() {
        for (const AstVar* const shadowVarp : m_shadowps) {
            const auto it = m_ctx.m_depSlotOfShadowName.find(shadowVarp->name());
            if (it == m_ctx.m_depSlotOfShadowName.end()) continue;  // Copy, fold or cross-scope
            // Without the array there is no word for the runtime to stamp, and the row would
            // silently go back to being recomputed out from under a deposit
            UASSERT_OBJ(m_depVarp, shadowVarp,
                        "--vpi-lazy row has a deposit slot but its module has no " << DEP_NAME);
            m_ctx.m_depWordResolved.emplace(shadowVarp, V3VpiLazy::DepWord{m_depVarp, it->second});
        }
    }

    // VISITORS
    void visit(AstNodeModule* nodep) override {
        VL_RESTORER(m_modp);
        VL_RESTORER(m_modLevel);
        VL_RESTORER(m_depVarp);
        VL_RESTORER_CLEAR(m_shadowps);
        m_modp = nodep;
        m_modLevel = true;
        m_depVarp = nullptr;
        iterateChildrenConst(nodep);
        if (m_wantDepWords) resolveDepWords();
    }
    void visit(AstScope* nodep) override {
        // Not folded into the module stmtsp walk: the top scope is op2 of an AstTopScope, one
        // level deeper than a direct stmtsp child
        if (m_wantScopes.count(nodep->name())) {
            const bool inserted = m_scopeps.emplace(nodep->name(), nodep).second;
            // A collision would bind a row to the wrong instance, which is what naming avoids
            UASSERT_OBJ(inserted, nodep, "Duplicate scope name '" << nodep->name() << "'");
        }
        VL_RESTORER(m_modLevel);
        m_modLevel = false;
        iterateChildrenConst(nodep);
    }
    void visit(AstVar* nodep) override {
        if (!m_modLevel) return;
        if (m_wantDepWords) {
            if (nodep->name() == DEP_NAME) {
                m_depVarp = nodep;
            } else if (nodep->isLazyReconstructShadow()) {
                m_shadowps.push_back(nodep);
            }
        }
        if (!m_wantVars.count(nodep->name())) return;
        const bool inserted = m_varps.emplace(std::make_pair(m_modp, nodep->name()), nodep).second;
        UASSERT_OBJ(inserted, nodep,
                    "Duplicate module-level variable name in " << m_modp->prettyNameQ());
    }
    // Module-level vars only: V3Descope moves CFuncs up but leaves their locals inside
    void visit(AstCFunc*) override {}
    // Skipped whole: its scope is named "TOP" like the real top scope, and its module hangs off
    // it rather than the netlist, so neither was ever collected
    void visit(AstConstPool*) override {}
    void visit(AstNode* nodep) override {
        VL_RESTORER(m_modLevel);
        m_modLevel = false;
        iterateChildrenConst(nodep);
    }

public:
    // CONSTRUCTORS
    CrossScopeGatherVisitor(AstNetlist* nodep, V3VpiLazyContext& ctx,
                            const std::set<std::string>& wantScopes,
                            const std::set<std::string>& wantVars, bool wantDepWords)
        : m_ctx{ctx}
        , m_wantScopes{wantScopes}
        , m_wantVars{wantVars}
        , m_wantDepWords{wantDepWords} {
        iterateConst(nodep);
    }
};

}  // namespace

const V3VpiLazy::DepWord* V3VpiLazy::depWordOf(const AstNetlist* nodep, const AstVar* shadowVarp) {
    // Most rows on most designs are cones, so this runs per lazy descriptor slot
    const V3VpiLazyContext* const ctxp = nodep->vpiLazyContextp();
    if (!ctxp || ctxp->m_depSlotOfShadowName.empty()) return nullptr;
    UASSERT(ctxp->m_crossScopeResolvedDone,
            "depWordOf() before V3VpiLazy::resolveCrossScopeSrcs()");
    const auto it = ctxp->m_depWordResolved.find(shadowVarp);
    return it == ctxp->m_depWordResolved.end() ? nullptr : &it->second;
}

void V3VpiLazy::resolveCrossScopeSrcs(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ":");
    V3VpiLazyContext* const ctxp = nodep->vpiLazyContextp();
    if (!ctxp) return;
    ctxp->m_crossScopeResolvedDone = true;
    ctxp->m_depWordResolved.clear();
    // Two independent jobs, one walk: the deposit slots are bound whenever any row has one,
    // the name maps built only for the rows that name another scope.
    const bool wantDepWords = !ctxp->m_depSlotOfShadowName.empty();
    const bool wantCrossScope = !ctxp->m_crossScopeSrcs.empty();
    if (!wantDepWords && !wantCrossScope) return;

    // Only the names rows actually reference are looked up, so only those are collected and
    // only their uniqueness is asserted: a duplicate elsewhere is no business of this pass.
    std::set<std::string> wantScopes;
    std::set<std::string> wantVars;
    for (const CrossScopeSrcNames& names : ctxp->m_crossScopeSrcs) {
        wantScopes.emplace(names.m_dstScopeName);
        wantScopes.emplace(names.m_srcScopeName);
        wantVars.emplace(names.m_dstVarName);
        wantVars.emplace(names.m_srcVarName);
    }
    const CrossScopeGatherVisitor gather{nodep, *ctxp, wantScopes, wantVars, wantDepWords};
    if (!wantCrossScope) return;

    const auto findScope = [&gather](const std::string& name) -> const AstScope* {
        const auto it = gather.m_scopeps.find(name);
        return it == gather.m_scopeps.end() ? nullptr : it->second;
    };
    const auto findVar
        = [&gather](const AstScope* scopep, const std::string& varName) -> const AstVar* {
        if (!scopep) return nullptr;
        const auto it = gather.m_varps.find(std::make_pair(scopep->modp(), varName));
        return it == gather.m_varps.end() ? nullptr : it->second;
    };

    for (const CrossScopeSrcNames& names : ctxp->m_crossScopeSrcs) {
        const AstScope* const dstScopep = findScope(names.m_dstScopeName);
        const AstVar* const dstVarp = findVar(dstScopep, names.m_dstVarName);
        // Shadow, or the scope holding it, went away: no descriptor row can ask for its source
        if (!dstVarp) continue;
        const AstScope* const srcScopep = findScope(names.m_srcScopeName);
        const AstVar* const srcVarp = findVar(srcScopep, names.m_srcVarName);
        if (!srcVarp) {
            v3fatalSrc("--vpi-lazy cross-scope copy source '"
                       << names.m_srcScopeName << "." << names.m_srcVarName
                       << "' did not survive; its VPI row would copy garbage");
        }
        // pinBoundary() promised this source keeps its storage; a dead member would copy garbage.
        UASSERT_OBJ(srcVarp->isSigVpiLazyRetained() || srcVarp->isSigUserRWPublic()
                        || srcVarp->isSigUserRdPublic() || srcVarp->isPrimaryIO(),
                    srcVarp, "--vpi-lazy cross-scope copy source was not pinned");
        const bool inserted
            = ctxp->m_crossScopeResolved
                  .emplace(std::make_pair(dstScopep, dstVarp), CrossScopeSrc{srcScopep, srcVarp})
                  .second;
        UASSERT_OBJ(inserted, dstVarp,
                    "Duplicate --vpi-lazy cross-scope copy row in " << dstScopep->prettyNameQ());
    }
}

const V3VpiLazy::CrossScopeSrc* V3VpiLazy::crossScopeCopySrc(const AstNetlist* nodep,
                                                             const AstScope* scopep,
                                                             const AstVar* shadowVarp) {
    // Most designs have no cross-scope row at all, and this runs per lazy descriptor slot
    const V3VpiLazyContext* const ctxp = nodep->vpiLazyContextp();
    if (!ctxp || ctxp->m_crossScopeSrcs.empty()) return nullptr;
    UASSERT(ctxp->m_crossScopeResolvedDone,
            "crossScopeCopySrc() before V3VpiLazy::resolveCrossScopeSrcs()");
    const auto it = ctxp->m_crossScopeResolved.find(std::make_pair(scopep, shadowVarp));
    return it == ctxp->m_crossScopeResolved.end() ? nullptr : &it->second;
}

//######################################################################

namespace {

// Everything finalize() needs from the tree, in one walk: the role assert, which reconstruct
// func (if only one) uses each temp shadow, the surviving deposit guards, and the reconstruct
// funcs to split.
class FinalizeVisitor final : public VNVisitorConst {
public:
    struct Use final {
        AstCFunc* m_funcp = nullptr;  // Null once a second func, or no func at all, uses it
        AstNode* m_firstUsep = nullptr;  // First top-level statement of m_funcp using it
    };
    // STATE
    std::vector<AstVar*> m_order;  // Temp shadows in encounter order (determinism)
    std::unordered_map<AstVar*, Use> m_useOf;
    std::vector<AstCFunc*> m_reconFuncps;  // Encounter order (determinism)
    int m_depGuardsSurvived = 0;

private:
    AstCFunc* m_funcp = nullptr;  // Func currently being descended, null outside one
    AstNode* m_stmtp = nullptr;  // Top-level statement of m_funcp->stmtsp() being descended
    bool m_inReconFunc = false;

    void visit(AstCFunc* nodep) override {
        VL_RESTORER(m_funcp);
        VL_RESTORER(m_stmtp);
        VL_RESTORER(m_inReconFunc);
        m_funcp = nodep;
        m_stmtp = nullptr;
        m_inReconFunc = nodep->vpiLazyReconstruct();
        if (m_inReconFunc) m_reconFuncps.push_back(nodep);
        iterateAndNextConstNull(nodep->argsp());
        iterateAndNextConstNull(nodep->varsp());
        iterateConstNull(nodep->scopeNamep());
        // By hand: the declaration goes before a top-level statement, so only those count.
        for (AstNode* stmtp = nodep->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
            m_stmtp = stmtp;
            iterateConst(stmtp);
        }
    }
    void visit(AstVar* nodep) override {
        // prepare() clears the lazy flag whenever it retains, so the two are disjoint.
        UASSERT_OBJ(!nodep->isSigVpiLazyRetained() || !nodep->isSigVpiLazyRWPublic(), nodep,
                    "--vpi-lazy signal is both retained and lazy");
        iterateChildrenConst(nodep);
    }
    void visit(AstNodeVarRef* nodep) override {
        AstVar* const varp = nodep->varp();
        if (m_inReconFunc && VN_IS(nodep, VarRef) && varp->name() == DEP_NAME) {
            ++m_depGuardsSurvived;
        }
        if (varp->isLazyReconstructTemp()) {
            const auto pair = m_useOf.emplace(varp, Use{m_funcp, m_stmtp});
            if (pair.second) {
                m_order.push_back(varp);
            } else if (pair.first->second.m_funcp != m_funcp) {
                pair.first->second.m_funcp = nullptr;
            } else if (!pair.first->second.m_firstUsep) {
                // Only if first mentioned outside stmtsp, and shadow refs are statement-only
                pair.first->second.m_firstUsep = m_stmtp;  // LCOV_EXCL_LINE
            }
        }
        iterateChildrenConst(nodep);
    }
    void visit(AstNode* nodep) override { iterateChildrenConst(nodep); }

public:
    explicit FinalizeVisitor(AstNetlist* nodep) { iterateConst(nodep); }
};

// A temp shadow only one reconstruct func touches needs no per-instance member. Not V3Localize's
// job: it runs after finalize() has split, and it skips the isSigPublic() attachShadow sets.
int localizeTempShadows(const FinalizeVisitor& uses) {
    int localized = 0;
    for (AstVar* const varp : uses.m_order) {
        const auto uit = uses.m_useOf.find(varp);
        UASSERT_OBJ(uit != uses.m_useOf.end(), varp, "--vpi-lazy temp shadow has no recorded use");
        const FinalizeVisitor::Use& use = uit->second;
        AstCFunc* const funcp = use.m_funcp;
        if (!funcp) continue;
        if (!funcp->vpiLazyReconstruct()) continue;
        if (!use.m_firstUsep) continue;
        varp->unlinkFrBack();
        varp->funcLocal(true);
        varp->sigPublic(false);  // Was set only to hold it as a member
        use.m_firstUsep->addHereThisAsNext(varp);
        ++localized;
    }
    return localized;
}

// Which variables the surviving tree writes, and every un-retained lazy VarScope left in it.
class RetentionGatherVisitor final : public VNVisitorConst {
public:
    // STATE
    std::unordered_set<const AstVar*> m_writtenps;
    std::vector<const AstVarScope*> m_lazyVscps;  // Encounter order (determinism)

private:
    // VISITORS
    void visit(AstNodeVarRef* nodep) override {
        if (!nodep->access().isReadOnly()) m_writtenps.emplace(nodep->varp());
        iterateChildrenConst(nodep);
    }
    void visit(AstVarScope* nodep) override {
        if (nodep->varp()->isSigVpiLazyRWPublic()) m_lazyVscps.push_back(nodep);
        iterateChildrenConst(nodep);
    }
    void visit(AstNode* nodep) override { iterateChildrenConst(nodep); }

public:
    // CONSTRUCTORS
    explicit RetentionGatherVisitor(AstNetlist* nodep) { iterateConst(nodep); }
};

}  // namespace

// prepare() runs before V3Gate and V3Dead, so storagePinnedElsewhere() is a forecast. A wrong one
// is silent: a VPI row pointing at storage nothing writes, reading zero for ever.
void V3VpiLazy::verifyRetention(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ":");
    const V3VpiLazyContext* const ctxp = nodep->vpiLazyContextp();
    if (!ctxp || ctxp->m_residualNames.empty()) return;

    const RetentionGatherVisitor gather{nodep};

    std::set<std::string> livenames;
    for (const AstVarScope* const vscp : gather.m_lazyVscps) {
        const AstVar* const varp = vscp->varp();
        livenames.emplace(vscp->name());
        // A primary port is written by the model's caller, not through any VarRef in here.
        if (varp->isPrimaryIO()) continue;
        if (gather.m_writtenps.count(varp)) continue;
        varp->v3fatalSrc("--vpi-lazy left '"
                         << vscp->name()
                         << "' un-retained, but its driver did not survive: its VPI row would"
                            " read zero for ever. storagePinnedElsewhere() over-promised.");
    }

    for (const std::string& name : ctxp->m_residualNames) {
        if (livenames.count(name)) continue;
        v3fatalSrc("--vpi-lazy left '" << name
                                       << "' un-retained, but its storage did not survive:"
                                          " its VPI row is lost. storagePinnedElsewhere()"
                                          " over-promised.");
    }
}

//######################################################################

void V3VpiLazy::finalize(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ":");

    const FinalizeVisitor visitor{nodep};

    const int localized = localizeTempShadows(visitor);
    if (v3Global.opt.stats()) V3Stats::addStat("VPI, lazy localized temps", localized);

    // A guard reads a variable nothing in the tree assigns - only the VPI runtime writes the
    // deposit array - so an optimizer may fold the guards away and silently restore the defect
    // they fix. Counted, not matched one for one: V3Const may merge two adjacent guards.
    const V3VpiLazyContext* const ctxp = nodep->vpiLazyContextp();
    if (ctxp && ctxp->m_depGuards) {
        const int survived = visitor.m_depGuardsSurvived;
        if (!survived) {
            v3fatalSrc("--vpi-lazy emitted " << ctxp->m_depGuards
                                             << " deposit guards and none survived: a VPI"
                                                " deposit into a reconstructed signal would be"
                                                " recomputed away");
        }
        UINFO(3, "vpi-lazy: deposit guards emitted=" << ctxp->m_depGuards
                                                     << " survived=" << survived);
        if (v3Global.opt.stats()) { V3Stats::addStat("VPI, lazy deposit guards", survived); }
    }

    // Split oversized reconstruction funcs per --output-split-cfuncs, their size now settled.
    // prepare()'s pointers do not survive the intervening passes, so the walk above found the
    // funcs by their flag. splitCheck moves whole top-level statements, so an entry func's
    // epoch guard stays whole.
    for (AstCFunc* const cfuncp : visitor.m_reconFuncps) V3Sched::util::splitCheck(cfuncp);
}
