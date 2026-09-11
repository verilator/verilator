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
//   retargeted    - no storage, its VPI entry reads another signal's storage
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
//   collectAliases, resolveAliasCanonicals   pure alias nets, chains resolved
//   formGroups, analyseGroups                form, then prove or bail
//   resolveAliasChains                       reconstruct or retain aliases
//   restrictMultiInstanceToLocalCones        retain cones not class-internal
//   buildDependencyGraph, splitCyclesRetainCores, topoOrderSurvivors
//                                            retain cycle cores, order the rest
//   shareReconstructedAliases                fold aliases onto a canonical
//   pruneBodies                              backward liveness over the clones
//   emitReconstructions                      emit the funcs and shadows
//   retainWriteOnlySequential, retainCompletenessFloor   retain what is left
//
// ALIASES
//
// A pure alias net (`assign a = b;`, and the port-connection aliases V3Inline
// leaves behind) is the same net as its canonical. Where the canonical is
// itself reconstructed the alias shares its descriptor if the C type matches -
// V3EmitCSyms builds that entry from a VVpiLazyAliasRetarget snapshot, the
// alias AstVar being long gone by then - else it reconstructs read-only from
// the canonical, which a boundary canonical holds storage for anyway. Sharing
// is same-scope only, so an entry never names another instance's storage, and
// no entry points at a boundary's storage, where a deposit into the alias
// would mutate, and persist in, the canonical.
//
// RUNTIME
//
// A reconstructed row's datap is a VerilatedVarLazyDatap {refreshp, storagep,
// selfp}. A read calls refreshp, which compares the group's stamp in its
// module's epoch array against vlSymsp->__Vm_lazyEpoch, recomputes the cone if
// stale, and restamps; eval() bumps the epoch, so a cone is recomputed at most
// once per time step however many of its signals are read. A vpi_put_value
// into a reconstructed signal refreshes and then deposits, leaving the stamp
// fresh so reads return the deposit; into a retained signal it sets
// __Vm_vpiLazyWritten, and the next eval re-runs the settle region once to
// propagate it.
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
#include "V3String.h"

#include <algorithm>
#include <array>
#include <cstring>
#include <map>
#include <memory>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

VL_DEFINE_DEBUG_FUNCTIONS;

const char* const V3VpiLazy::RECONSTRUCT_FUNC_NAME = "__Vlazy_reconstruct";
const char* const V3VpiLazy::SHADOW_PREFIX = "__Vlazyrecon__";
const char* const V3VpiLazy::EPOCH_NAME = "__Vlazyepoch";

// Separate from the epoch guard, so --output-split-cfuncs can chop the statements up.
static const char* const RECONSTRUCT_BODY_FUNC_NAME = "__Vlazy_reconstruct_body";

std::string V3VpiLazy::reconFuncNameOf(const AstVar* shadowVarp) {
    const std::string& name = shadowVarp->name();
    UASSERT_OBJ(VString::startsWith(name, SHADOW_PREFIX), shadowVarp,
                "not a --vpi-lazy reconstruct shadow");
    // A target shadow is named "<prefix><group id>_<slot>"; one func per group.
    const std::string tail = name.substr(std::strlen(SHADOW_PREFIX));
    const size_t under = tail.find('_');
    UASSERT_OBJ(under != std::string::npos, shadowVarp, "malformed --vpi-lazy shadow name");
    return std::string{RECONSTRUCT_FUNC_NAME} + "__" + tail.substr(0, under);
}

//######################################################################

namespace {

// Retainable with ordinary storage? False where another mechanism already owns the signal.
bool retainableKind(const AstVar* varp) {
    if (varp->isIO()) return false;
    if (varp->isPrimaryIO()) return false;
    if (varp->isForceable()) return false;
    if (varp->isReadByDpi() || varp->isWrittenByDpi()) return false;
    if (varp->isSigModPublic()) return false;
    return true;
}

// Retainable and expressible as one same-dtype shadow: integral-or-packed, or an unpacked array
// of such. Dims past VPI_TABLE_MAX_DIMS are rejected: the shadow must fit a VlVarTableEntry row.
bool reconstructableKind(const AstVar* varp) {
    if (!retainableKind(varp)) return false;
    AstNodeDType* const dtypep = varp->dtypeSkipRefp();
    AstNodeDType* leafp = dtypep;
    while (AstUnpackArrayDType* const adtypep = VN_CAST(leafp, UnpackArrayDType)) {
        leafp = adtypep->subDTypep()->skipRefp();
    }
    if (!(VN_IS(leafp, BasicDType) || leafp->isIntegralOrPacked())) return false;
    const std::pair<uint32_t, uint32_t> dims = dtypep->dimensions(/*includeBasic*/ true);
    return dims.first + dims.second <= static_cast<uint32_t>(V3VpiLazy::VPI_TABLE_MAX_DIMS);
}

// One reconstruction unit, plus the variables it writes; see UNIT OF RECONSTRUCTION above.
struct Group final {
    AstScope* scopep = nullptr;  // Scope that authored the statements (see restrictMulti...)
    AstAlways* alwaysp = nullptr;  // Procedural block, or null for an assign group
    std::vector<AstAssignW*> partialps;  // Continuous assigns; empty unless an assign group
    std::vector<AstVarScope*> targets;  // VPI candidates this group defines, encounter order
    std::vector<AstVarScope*> temps;  // Other variables it writes, encounter order
    std::unordered_set<AstVarScope*> members;  // targets + temps, for O(1) membership
    std::unordered_map<AstVarScope*, size_t> slotOf;  // target -> index in 'targets'
    std::vector<AstVarScope*> zeroInitps;  // Partial assembly: zero these shadows first
    AstVar* keyp = nullptr;  // targets[0]->varp(): cross-instance group identity
    AstCFunc* funcp = nullptr;
    int epochSlot = -1;  // Index into the module's stamp array (assignEpochSlots)
    bool live = true;  // Cleared when the group is abandoned and its targets retained
    // Representatives only: the pruned statement clone and the group vars it still produces.
    AstNode* bodyp = nullptr;
    std::unordered_set<AstVarScope*> neededps;
};

// One partial write's footprint: the constant array indices selected (order need only be
// consistent between parts) plus the bit range within the selected element.
struct PartExtent final {
    std::vector<int32_t> idxs;
    int lsb = 0;
    int width = 0;
};

struct PartWrite final {
    AstAssignW* m_awp = nullptr;
    PartExtent m_ext;
};

// Base variable and footprint of a constant-selected partial write (`base[3][c +: w] = rhs;`),
// or nullptr if the LHS is not a constant element/range select of one variable.
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

// Walk an assignment LHS to its base VarRef, reporting whether a select makes the write partial
// (so the untouched bits are read). Null if the LHS is not a VarRef-rooted select chain.
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

// One pre-optimization walk gathering per-VarScope write/read counts and per-block write info.
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
    // Every VarScope in tree-encounter order; iterated only by the completeness floor.
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
            m_blockWrites.clear();
            m_blockWriteOrder.clear();
            m_comboAlwaysp = alwaysp;
            iterateChildren(alwaysp);
            m_comboAlwaysp = nullptr;
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

// Runs the classification/reconstruction phases over one gather pass; run()'s order is fixed.
class VpiLazyPreparer final {
    using CombBlock = LazyGatherVisitor::CombBlock;
    using Defined = std::unordered_set<AstVarScope*>;

    // STATE
    AstNetlist* const m_nodep;
    AstScope* const m_topScopep;
    LazyGatherVisitor m_gather;

    int m_combBailRetained = 0;  // Group-bail / non-sole-driver / cycle retains

    std::vector<std::unique_ptr<Group>> m_groups;  // Formation order (deterministic)
    std::unordered_map<AstVar*, std::vector<Group*>> m_groupsOfKey;
    std::unordered_map<AstVarScope*, Group*> m_groupOf;  // Solely-written var -> its group
    std::unordered_map<AstVarScope*, Group*> m_targetOf;  // Group target -> its group
    std::unordered_map<AstVarScope*, AstAssignW*> m_aliasAssignOf;  // alias -> its `assign`
    std::unordered_map<AstVarScope*, AstScope*> m_aliasScopeOf;  // alias -> authoring scope
    std::unordered_map<AstVarScope*, AstVarScope*> m_aliasImmTarget;  // alias -> immediate target
    std::vector<AstVarScope*> m_aliasOrder;  // m_aliasImmTarget keys, in encounter order
    // Alias -> chain-resolved canonical, and the aliases whose chain cycles.
    // Computed before group formation so a canonical can be a helper target.
    std::unordered_map<AstVarScope*, AstVarScope*> m_aliasCanonOf;
    std::unordered_set<AstVarScope*> m_aliasCyclic;
    // Vars rooting a visible alias chain but not themselves VPI-visible: reconstructing one lets
    // its aliases share its descriptor. Per AstVar, so every instance forms the same group shape.
    std::unordered_set<const AstVar*> m_helperCandVars;
    std::unordered_set<const AstVarScope*> m_helperTargets;  // Committed helper targets
    int m_helperCount = 0;  // Helper targets reconstructed, per instance

    int m_reconAliasShared = 0;  // Aliases sharing a reconstructed canonical's descriptor
    // Alias -> reconstructed canonical; committed by shareReconstructedAliases.
    std::unordered_map<AstVarScope*, AstVarScope*> m_reconAliasCanonOf;
    std::vector<AstVarScope*> m_sharedAliases;  // Committed subset, in m_aliasOrder order
    // Alias sharing a canonical's descriptor -> that canonical, for cone operand substitution.
    std::unordered_map<AstVarScope*, AstVarScope*> m_retargetCanonOf;

    std::unordered_map<Group*, std::vector<Group*>> m_dependents;  // u -> {v ...}

    std::vector<Group*> m_ordered;  // Topological order of reconstructed survivor groups
    std::unordered_set<AstVarScope*> m_reconTargets;  // Targets of m_ordered groups

    FileLine* m_funcFlp = nullptr;
    int m_reconstructed = 0;  // Reconstructed signals (per instance)
    int m_fallback = 0;  // Retained with storage (incl. group bails), snapshotted pre-emission
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
        ALIAS_CYCLE,  // Alias chain revisits a node
        ALIAS_KIND,  // Alias reconstruction cannot express: retained, never retargeted
        COMB_CYCLE,  // Genuine combinational cycle (SCC member or self-loop)
        TOPO_LEFTOVER,  // Unordered by Kahn's despite being a DAG; indicates a bug
        COMPLETENESS_FLOOR,  // No classification path claimed it; retained so VPI still sees it
        BOUNDARY_COMB_DTYPE,  // Comb boundary operand of a kind reconstruction cannot express
        BOUNDARY_COMB_ALIAS,  // Comb boundary operand that is an alias immediate target
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
                                            "alias cycle",
                                            "alias kind",
                                            "comb cycle",
                                            "topo leftover",
                                            "completeness floor",
                                            "boundary comb (dtype)",
                                            "boundary comb (alias)",
                                            "boundary comb (unexplained)",
                                            "boundary operand (seq)"};
        static_assert(sizeof(names) / sizeof(names[0]) == static_cast<size_t>(Bail::_COUNT),
                      "Bail name table out of sync with enum");
        return names[static_cast<size_t>(b)];
    }
    std::array<int, static_cast<size_t>(Bail::_COUNT)> m_bailCount{};
    std::unordered_set<const AstVarScope*> m_combTargets;  // Lazily built by hasCombDriver()
    // One shadow member per module and one VarScope per instance, mirroring AstVar/AstVarScope,
    // else N identically-named members collide in the same C++ class.
    std::unordered_map<AstVar*, AstVar*> m_shadowVarOfOrig;  // per-module member dedup
    std::unordered_map<AstVarScope*, AstVarScope*> m_shadowOf;  // per-instance VarScope
    // One stamp-array member per module, not one apiece for thousands of groups.
    std::unordered_map<const AstNodeModule*, AstVar*> m_epochVarOfMod;
    std::unordered_map<const AstScope*, AstVarScope*> m_epochOfScope;
    std::unordered_map<AstVar*, AstCFunc*> m_funcOfKey;
    // Short names for the emitted artefacts; ids are design-global (gidOf).
    std::unordered_map<const AstVar*, int> m_gidOfKey;
    std::unordered_map<const AstVar*, int> m_tempIdxOfVar;
    int m_nextGid = 0;
    int m_nextTempIdx = 0;

    int m_prunedStmts = 0;  // Cloned statements dropped as dead (pruneBodies)
    int m_writeOnlyRetained = 0;
    int m_floorRetained = 0;
    int m_crossScopeRetained = 0;  // Multi-instance cones reading outside their scope

public:
    VpiLazyPreparer(AstNetlist* nodep, AstScope* topScopep)
        : m_nodep{nodep}
        , m_topScopep{topScopep}
        , m_gather{nodep} {}

    void run() {
        collectAliases();
        resolveAliasCanonicals();
        formGroups();
        analyseGroups();
        resolveAliasChains();
        restrictMultiInstanceToLocalCones();
        buildDependencyGraph();
        splitCyclesRetainCores();
        topoOrderSurvivors();
        shareReconstructedAliases();
        pruneBodies();
        emitReconstructions();
        recordReconstructedAliasRetargets();
        retainWriteOnlySequential();
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

    Group* liveGroupOf(AstVarScope* u) const {
        const auto it = m_groupOf.find(u);
        if (it == m_groupOf.end()) return nullptr;
        return it->second->live ? it->second : nullptr;
    }

    // Root statements of a group, in execution order.
    template <typename T_Callable>
    void forEachStmt(const Group* g, T_Callable&& f) const {
        if (g->alwaysp) {
            for (AstNode* sp = g->alwaysp->stmtsp(); sp; sp = sp->nextp()) f(sp);
        } else {
            for (AstAssignW* const awp : g->partialps) f(static_cast<AstNode*>(awp));
        }
    }

    // Which classify/analysis skip path left this comb-driven operand out of any group.
    Bail combBoundaryReason(AstVarScope* u) {
        if (!reconstructableKind(u->varp())) return Bail::BOUNDARY_COMB_DTYPE;
        if (m_aliasImmTarget.count(u)) return Bail::BOUNDARY_COMB_ALIAS;
        // Stats catch-all: a comb-driven operand written elsewhere is retained as MULTIDRIVEN
        // before pinBoundary sees it, so no classification is left to make
        return Bail::BOUNDARY_COMB_UNKNOWN;  // LCOV_EXCL_LINE
    }

    // An alias sharing a descriptor has no storage: a cone operand that is one reads the
    // canonical, as pinning would restore it. tryAlias promises only equal width, hence the
    // dtype/scope tests.
    AstVarScope* aliasSubstituteFor(AstVarScope* u, const Group* g) const {
        const auto it = m_retargetCanonOf.find(u);
        if (it == m_retargetCanonOf.end()) return nullptr;
        AstVarScope* const canonp = it->second;
        if (!u->varp()->dtypep()->similarDType(canonp->varp()->dtypep())) return nullptr;
        if (instancesOf(g->keyp) > 1 && canonp->scopep() != g->scopep) return nullptr;
        return canonp;
    }

    bool hasCombDriver(AstVarScope* vscp) {
        if (m_combTargets.empty()) {
            for (const CombBlock& b : m_gather.m_combBlocks)
                for (AstVarScope* const t : b.m_targets) m_combTargets.insert(t);
        }
        return m_combTargets.count(vscp) != 0;
    }

    // Pin a still-lazy signal to RW storage (like --public-flat-rw), per instance.
    void retainTarget(AstVarScope* target, Bail why) {
        AstVar* const varp = target->varp();
        if (!varp->isSigVpiLazyRWPublic()) return;  // already reconstructed / retained
        varp->sigVpiLazyRWPublic(false);
        varp->sigVpiLazyRetained(true);
        m_combBailRetained += instancesOf(varp);
        m_bailCount[static_cast<size_t>(why)] += instancesOf(varp);
    }

    // Abandon every instance of a group and retain its targets. All-or-nothing per module: the
    // lazy flag and the func are shared, so a survivor would be built from the wrong instance.
    void killGroupsOfKey(AstVar* keyp, Bail why) {
        for (Group* const g : m_groupsOfKey.at(keyp)) {
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
        // V3EmitCSyms names the func from its target shadow's module, so the func must live in
        // the module every group variable belongs to; else this cannot be one group.
        for (AstVarScope* const w : written) {
            if (w->scopep() == scopep) continue;
            for (AstVarScope* const t : written) {
                if (t->varp()->isSigVpiLazyRWPublic() && retainableKind(t->varp()))
                    retainTarget(t, Bail::CROSS_SCOPE_WRITE);
            }
            return nullptr;
        }
        std::vector<AstVarScope*> targets;
        std::vector<AstVarScope*> temps;
        std::vector<AstVarScope*> soleTemps;
        for (AstVarScope* const w : written) {
            AstVar* const varp = w->varp();
            const bool sole = writeCountOf(w) == groupWrites.at(w);
            if (notSole.count(varp)) {
                // Multidriven in some instance: never a target, the choice being per module.
                if (varp->isSigVpiLazyRWPublic() && retainableKind(varp))
                    retainTarget(w, Bail::MULTIDRIVEN);
            } else if (!varp->isSigVpiLazyRWPublic()) {
                // Not VPI-visible: a plain temp, unless a visible alias chain roots here - then a
                // "helper target", giving the aliases a descriptor to share instead of storage.
                if (m_helperCandVars.count(varp) && reconstructableKind(varp)) {
                    targets.push_back(w);
                    m_helperTargets.insert(w);
                    continue;
                }
            } else if (!reconstructableKind(varp)) {
                if (retainableKind(varp)) retainTarget(w, Bail::DTYPE);
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

    // Record a bare `assign x = y;` as a pure alias: same net, so its entry can point at y.
    void tryAlias(AstVarScope* vscp, AstAssignW* awp, AstScope* scopep) {
        if (writeCountOf(vscp) != 1) return;
        if (!vscp->varp()->isSigVpiLazyRWPublic()) return;
        const AstVarRef* const rrefp = VN_CAST(awp->rhsp(), VarRef);
        if (!rrefp || !rrefp->access().isReadOnly()) return;
        if (vscp->varp()->isPrimaryIO()) return;
        AstVarScope* const tgtp = rrefp->varScopep();
        const AstNodeDType* const aliasDtp = vscp->varp()->dtypep()->skipRefp();
        const AstNodeDType* const tgtDtp = tgtp->varp()->dtypep()->skipRefp();
        // Bit-identical: same dtype node, or equal-width integral-or-packed dtypes (equal width
        // does not imply equal layout for real/string/UNPACKED).
        const bool sameStorage
            = aliasDtp == tgtDtp
              || (aliasDtp->width() == tgtDtp->width() && aliasDtp->isIntegralOrPacked()
                  && tgtDtp->isIntegralOrPacked());
        if (!sameStorage) return;
        if (m_aliasImmTarget.emplace(vscp, tgtp).second) {
            m_aliasOrder.push_back(vscp);
            m_aliasAssignOf.emplace(vscp, awp);
            m_aliasScopeOf.emplace(vscp, scopep);
        }
    }

    // Runs before group formation: formGroups() needs the chains to pick helper targets.
    void collectAliases() {
        for (const CombBlock& b : m_gather.m_combBlocks) {
            if (!b.m_assignwp) continue;
            AstVarRef* const vrp = VN_CAST(b.m_assignwp->lhsp(), VarRef);
            if (!vrp) continue;  // A select-rooted LHS is never a whole-net alias
            tryAlias(vrp->varScopep(), b.m_assignwp, b.m_scopep);
        }
    }

    // Can 'aliasp's VPI row share 'canonp's lazy descriptor? It is one selfp plus a byte offset,
    // so both must sit in the same instance scope and want the same C type.
    static bool canShareDescriptor(const AstVarScope* aliasp, const AstVarScope* canonp) {
        if (aliasp->scopep() != canonp->scopep()) return false;
        if (!reconstructableKind(aliasp->varp())) return false;
        return aliasp->varp()->vlEnumType() == canonp->varp()->vlEnumType();
    }

    // Resolve every alias chain transitively to its canonical, then flag as a helper candidate any
    // canonical that is not itself VPI-visible, so the chain's aliases can share its descriptor.
    void resolveAliasCanonicals() {
        for (AstVarScope* const aliasp : m_aliasOrder) {
            AstVarScope* canonp = aliasp;
            std::unordered_set<AstVarScope*> chain;  // This walk's nodes, for cycle + compression
            bool cycle = false;
            while (true) {
                const auto cit = m_aliasCanonOf.find(canonp);
                if (cit != m_aliasCanonOf.end()) {
                    canonp = cit->second;  // Cached tail of the chain
                    break;
                }
                const auto tit = m_aliasImmTarget.find(canonp);
                if (tit == m_aliasImmTarget.end()) break;  // canonp is the canonical (non-alias)
                if (!chain.insert(canonp).second) {
                    cycle = true;
                    break;
                }
                canonp = tit->second;
            }
            if (cycle) {
                m_aliasCyclic.insert(aliasp);  // Unresolvable: retained by resolveAliasChains
                continue;
            }
            for (AstVarScope* const np : chain) m_aliasCanonOf.emplace(np, canonp);
            m_aliasCanonOf.emplace(aliasp, canonp);
            if (!canonp->varp()->isSigVpiLazyRWPublic() && reconstructableKind(canonp->varp())
                && canShareDescriptor(aliasp, canonp))
                m_helperCandVars.insert(canonp->varp());
        }
    }

    // Split the combinational blocks into groups, merging one variable's partial-write set.
    void formGroups() {
        const std::vector<CombBlock>& blocks = m_gather.m_combBlocks;
        // Pass 1: the continuous partial-write sets, and which variables more than one group
        // writes. The latter is decided per AstVar so every instance forms the same group shape.
        std::unordered_map<AstVarScope*, std::vector<PartWrite>> partsOf;
        std::vector<AstVarScope*> partOrder;
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
            if (basep) {
                if (!partsOf.count(basep)) partOrder.push_back(basep);
                partsOf[basep].push_back(PartWrite{b.m_assignwp, std::move(ext)});
            }
            for (AstVarScope* const w : b.m_targets) {
                WInfo& wi = winfo[w];
                ++wi.m_blocks;
                wi.m_sum += b.m_writeCount.at(w);
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
                formPartialGroup(basep, partsOf.at(basep), b.m_scopep, notSole);
                continue;
            }
            if (AstAssignW* const awp = b.m_assignwp) {
                AstNodeExpr* const lhsp = awp->lhsp();
                if (AstVarRef* const vrp = VN_CAST(lhsp, VarRef)) {
                    if (m_aliasImmTarget.count(vrp->varScopep())) continue;  // collectAliases
                    makeGroup(b.m_scopep, nullptr, {awp}, b.m_targets, b.m_writeCount, notSole,
                              /*zeroInit*/ false);
                    continue;
                }
                // A continuous write shape the shadow cannot mirror (array element, variable
                // range, concatenation): retain its target rather than let the optimizer drop it.
                bool partial = false;
                if (const AstVarRef* const basep2 = lhsBaseRef(lhsp, partial)) {
                    AstVar* const varp = basep2->varScopep()->varp();
                    if (varp->isSigVpiLazyRWPublic() && retainableKind(varp))
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
            if (retainableKind(varp)) retainTarget(basep, Bail::DTYPE);
            return;
        }
        if (static_cast<int>(parts.size()) != writeCountOf(basep) || notSole.count(varp)) {
            // A full / procedural / impure / variable-range write exists too.
            retainTarget(basep, Bail::PARTIAL_MIXED_WRITE);
            return;
        }
        // Overlapping continuous writes are multidriven: assembly would depend on encounter
        // order. Bucketed by element index, then LSB-sorted so only adjacent pairs need
        // testing: O(n log n) even for a vector assembled from bit slices, which shares one
        // bucket (every part has an empty index list).
        const size_t depth = parts[0].m_ext.idxs.size();
        std::map<std::vector<int32_t>, std::vector<const PartExtent*>> byElem;
        for (const PartWrite& pw : parts) {
            // V3Slice expands every sub-array write to leaf elements, so parts share one depth;
            // degraded rather than asserted, as assuming disjointness would miscompile
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

    // Unsafe for a cold reconstruction to re-execute: a side effect, or a read of simulation
    // state no variable captures ($time, an unseeded $random). Pure calls are exempt:
    // isPredictOptimizable() is false for every AstNodeCCall only as V3Simulate cannot call.
    static bool unsafeToReexecute(AstNode* nodep) {
        if (!nodep->isPure()) return true;
        return !nodep->isPredictOptimizable() && !VN_IS(nodep, NodeCCall);
    }

    // Asked per root statement: exists() does not follow nextp() from its root.
    static bool impure(AstNode* stmtp) {
        return stmtp->exists([](AstNode* nodep) { return unsafeToReexecute(nodep); });
    }

    // Does 'nodep' read a group variable that the prefix walked so far has not unconditionally
    // full-width written? 'skipp' is an assignment's LHS base ref, whose read is checked apart.
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

    // One statement of the ordered walk. 'defined' carries the group variables the prefix has
    // unconditionally full-width written; a conditional merges back only what every path writes.
    bool walkStmt(AstNode* stmtp, const Group* g, Defined& defined, Bail& whyr) const {
        if (VN_IS(stmtp, Comment) || VN_IS(stmtp, JumpGo)) return true;
        if (AstNodeAssign* const asgnp = VN_CAST(stmtp, NodeAssign)) {
            // V3Active has rewritten any '<=' in a comb block and V3Force lowered AstAssignForce,
            // so only blocking and continuous assigns reach here; cloneBody makes both blocking.
            UASSERT_OBJ(VN_IS(stmtp, Assign) || VN_IS(stmtp, AssignW), stmtp,
                        "--vpi-lazy: unexpected assignment kind in a combinational block");
            // A timing-controlled AstAssignW lands in a block group, not an assign group. Only
            // --timing keeps the delay this far, and such a block never terminates: untested.
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

    // An unpacked array written only by unconditional constant-index element assigns and never
    // read is defined whatever the order: seed it defined, zeroing the shadow so a gap reads 0.
    void seedElementWrittenArrays(Group* g, Defined& defined) const {
        const auto trySeed = [&](AstVarScope* u) {
            if (!VN_IS(u->varp()->dtypeSkipRefp(), UnpackArrayDType)) return;
            bool anyRead = false;
            int writes = 0;
            g->alwaysp->foreach([&](AstVarRef* refp) {
                if (refp->varScopep() != u) return;
                if (!refp->access().isWriteOnly()) anyRead = true;
                if (!refp->access().isReadOnly()) ++writes;
            });
            if (anyRead || !writes) return;
            std::map<std::vector<int32_t>, std::vector<PartExtent>> byElem;
            int matched = 0;
            size_t depth = 0;
            for (AstNode* sp = g->alwaysp->stmtsp(); sp; sp = sp->nextp()) {
                AstNodeAssign* const asgnp = VN_CAST(sp, NodeAssign);
                if (!asgnp) continue;
                PartExtent ext;
                if (partialLhs(asgnp->lhsp(), ext) != u || ext.idxs.empty()) continue;
                if (!matched) depth = ext.idxs.size();
                if (ext.idxs.size() != depth) return;  // Mixed select depth
                byElem[ext.idxs].push_back(ext);
                ++matched;
            }
            // Per bucket, LSB-sorted so only adjacent pairs need an overlap test (O(n log n))
            for (auto& pr : byElem) {
                std::vector<PartExtent>& bucket = pr.second;
                std::sort(bucket.begin(), bucket.end(),
                          [](const PartExtent& a, const PartExtent& b) { return a.lsb < b.lsb; });
                for (size_t i = 1; i < bucket.size(); ++i)
                    if (bucket[i].lsb < bucket[i - 1].lsb + bucket[i - 1].width) return;
            }
            if (matched != writes) return;  // Some write was nested or variable-indexed
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
        // m_groups grows later (alias groups), so index rather than iterate.
        for (size_t i = 0; i < m_groups.size(); ++i) {
            Group* const g = m_groups[i].get();
            if (!g->live) continue;
            Bail why = Bail::UNSUPPORTED_STMT;
            const bool ok = g->alwaysp ? analyseBlockGroup(g, why) : analyseAssignGroup(g, why);
            if (!ok) killGroupsOfKey(g->keyp, why);
        }
    }

    // METHODS - Aliases

    // Alias's declared (left,right) bounds in EmitCSyms::getVarDims() order: unpacked outer-first,
    // then packed inner-first, then a ranged basic leaf. No alias carries an unpacked dim today
    // (V3Slice expands array assigns first); the branch mirrors getVarDims in case one ever does.
    static void snapshotAliasDims(const AstNodeDType* rootDtypep,
                                  std::vector<std::pair<int, int>>& unpackedLR,
                                  std::vector<std::pair<int, int>>& packedLR) {
        for (const AstNodeDType* dtypep = rootDtypep; dtypep;) {
            dtypep = dtypep->skipRefp();
            if (const AstNodeArrayDType* const adtypep = VN_CAST(dtypep, NodeArrayDType)) {
                if (VN_IS(dtypep, PackArrayDType)) {
                    packedLR.emplace_back(adtypep->left(), adtypep->right());
                } else {
                    unpackedLR.emplace_back(adtypep->left(), adtypep->right());  // LCOV_EXCL_LINE
                }
                dtypep = adtypep->subDTypep();
            } else {
                if (const AstBasicDType* const basicp = dtypep->basicp()) {
                    if (basicp->isRanged()) packedLR.emplace_back(basicp->left(), basicp->right());
                }
                break;
            }
        }
    }

    // Record the VPI entry that must stand in for 'aliasp' once the optimizer has dropped it: the
    // alias's own name and declared type/bounds over 'canonVscp's storage. Same-scope only, as
    // the entry is one selfp plus a byte offset: another instance's storage would read as this
    // one's, and V3EmitCSyms resolves the name against the ALIAS's module.
    void pushAliasRetarget(const AstVarScope* aliasp, const AstVarScope* canonVscp) {
        UASSERT_OBJ(aliasp->scopep() == canonVscp->scopep(), aliasp,
                    "--vpi-lazy alias retarget crosses scopes");
        const AstVar* const aliasVarp = aliasp->varp();
        const AstNodeDType* const aliasDtp = aliasVarp->dtypeSkipRefp();
        const AstBasicDType* const aliasBasicp = aliasDtp->basicp();
        VVpiLazyAliasRetarget rt{aliasp->scopep()->name(),
                                 aliasVarp->name(),
                                 canonVscp->varp()->name(),
                                 aliasDtp->isSigned(),
                                 aliasBasicp && aliasBasicp->keyword() == VBasicDTypeKwd::BIT,
                                 aliasVarp->isNet(),
                                 {},
                                 {}};
        snapshotAliasDims(aliasVarp->dtypep(), rt.m_aliasUnpackedLR, rt.m_aliasPackedLR);
        m_nodep->vpiLazyAliasRetargets().push_back(std::move(rt));
    }

    // Act on the chains resolveAliasCanonicals() resolved; see ALIASES above.
    void resolveAliasChains() {
        for (AstVarScope* const aliasp : m_aliasOrder) {
            if (m_aliasCyclic.count(aliasp)) {
                retainTarget(aliasp,
                             Bail::ALIAS_CYCLE);  // Unresolvable cycle: retain, do not drop
                continue;
            }
            // Reconstruct the alias read-only, its shadow reading the canonical: its own storage,
            // whether the canonical is reconstructed or a boundary holding storage already. An
            // entry over the canonical's storage would instead leak a deposit into the canonical,
            // and could not name it at all from another scope.
            AstVarScope* const canonp = m_aliasCanonOf.at(aliasp);
            if (reconstructableKind(aliasp->varp())) {
                const std::unordered_map<const AstVarScope*, int> writes{{aliasp, 1}};
                Group* const gp
                    = makeGroup(m_aliasScopeOf.at(aliasp), nullptr, {m_aliasAssignOf.at(aliasp)},
                                {aliasp}, writes, {}, /*zeroInit*/ false);
                if (gp) {
                    // Only a reconstructed canonical can share a descriptor;
                    // shareReconstructedAliases revisits once the topological order settles.
                    const auto cgit = m_targetOf.find(canonp);
                    if (cgit != m_targetOf.end() && cgit->second->live)
                        m_reconAliasCanonOf.emplace(aliasp, canonp);
                    continue;
                }
            }
            // Kinds reconstructableKind() excludes, and groups makeGroup refused: retain with
            // storage. Kinds retainableKind() excludes already own their storage and entry.
            // V3Slice expands the aggregate assigns that would reach this, so no test does.
            if (retainableKind(aliasp->varp()))  // LCOV_EXCL_LINE
                retainTarget(aliasp, Bail::ALIAS_KIND);  // LCOV_EXCL_LINE
        }
    }

    // METHODS - Scheduling

    // One loose vlSelf-relative func serves every instance, so a cone must be class-internal: a
    // cross-scope VarRef descopes to an absolute path. Retain the whole group otherwise.
    void restrictMultiInstanceToLocalCones() {
        std::unordered_set<const AstVar*> unshareable;
        for (const auto& ownp : m_groups) {
            const Group* const g = ownp.get();
            if (!g->live || instancesOf(g->keyp) <= 1) continue;
            bool bad = false;
            for (AstVarScope* const t : g->targets)
                if (t->scopep() != g->scopep) bad = true;
            forEachStmt(g, [&](AstNode* sp) {
                sp->foreach([&](const AstVarRef* refp) {
                    if (refp->varScopep()->scopep() != g->scopep) bad = true;
                });
            });
            if (bad) unshareable.insert(g->keyp);
        }
        if (unshareable.empty()) return;
        for (const auto& ownp : m_groups) {
            Group* const g = ownp.get();
            if (!g->live || !unshareable.count(g->keyp)) continue;
            g->live = false;
            for (AstVarScope* const t : g->targets) {
                AstVar* const varp = t->varp();
                if (!varp->isSigVpiLazyRWPublic()) continue;
                varp->sigVpiLazyRWPublic(false);
                varp->sigVpiLazyRetained(true);
                m_crossScopeRetained += instancesOf(varp);
            }
        }
    }

    // Dependency edges among groups: u defines a variable v reads, so the edge is u -> v.
    void buildDependencyGraph() {
        for (const auto& ownp : m_groups) {
            Group* const g = ownp.get();
            if (!g->live) continue;
            std::unordered_set<Group*> seen;
            const auto addDep = [&](AstVarScope* u) {
                Group* const ugp = liveGroupOf(u);
                if (!ugp || ugp == g) return;
                if (!seen.insert(ugp).second) return;
                m_dependents[ugp].push_back(g);
            };
            forEachStmt(g, [&](AstNode* sp) {
                sp->foreach([&](AstVarRef* refp) {
                    if (refp->access().isWriteOnly()) return;
                    AstVarScope* u = refp->varScopep();
                    if (g->members.count(u)) return;
                    if (AstVarScope* const canonp = aliasSubstituteFor(u, g)) u = canonp;
                    addDep(u);
                });
            });
            // An alias group's statement names only the next link in its chain, but sharing
            // retargets its readers to the chain-resolved canonical, so depend on that too: a
            // link retained in between is a boundary read, which would sever the ordering the
            // retargeted readers need (the transitive edge is redundant when no link is).
            for (AstVarScope* const t : g->targets) {
                const auto it = m_reconAliasCanonOf.find(t);
                if (it != m_reconAliasCanonOf.end()) addDep(it->second);
            }
        }
    }

    // Retain only genuine cycle members: a group merely downstream of a cycle still reconstructs
    // cold, reading the retained core as a boundary operand, so an SCC pass separates the two.
    void splitCyclesRetainCores() {
        std::vector<Group*> live;
        for (const auto& ownp : m_groups)
            if (ownp->live) live.push_back(ownp.get());
        V3Graph sccGraph;
        std::unordered_map<Group*, V3GraphVertex*> vtxOf;  // lookup only
        for (Group* const g : live) vtxOf.emplace(g, new V3GraphVertex{&sccGraph});
        for (Group* const u : live) {
            const auto dit = m_dependents.find(u);
            if (dit == m_dependents.end()) continue;
            V3GraphVertex* const uVtxp = vtxOf.at(u);
            for (Group* const v : dit->second) {
                if (!v->live) continue;
                new V3GraphEdge{&sccGraph, uVtxp, vtxOf.at(v), 1};
            }
        }
        sccGraph.stronglyConnected(&V3GraphEdge::followAlwaysTrue);
        for (Group* const g : live) {
            // Non-zero color = a real comb cycle (multi-node SCC or self-loop): retain it.
            if (g->live && vtxOf.at(g)->color() != 0) killGroupsOfKey(g->keyp, Bail::COMB_CYCLE);
        }
    }

    // Kahn topo-sort of the surviving groups (a DAG now the cycle members are gone). Prefers a
    // ready group in the previously ordered group's scope, so a scope's statements stay in runs.
    void topoOrderSurvivors() {
        std::vector<Group*> live;
        for (const auto& ownp : m_groups)
            if (ownp->live) live.push_back(ownp.get());
        std::unordered_map<Group*, int> inDegree;
        for (Group* const g : live) inDegree[g];  // ensure present
        for (Group* const u : live) {
            const auto dit = m_dependents.find(u);
            if (dit == m_dependents.end()) continue;
            for (Group* const v : dit->second)
                if (v->live) ++inDegree[v];
        }
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
            for (Group* const v : m_dependents[up]) {
                if (!v->live) continue;  // Skip edges to retained cycle cores
                if (--inDegree[v] == 0) pushReady(v);
            }
        }
        // Safety net: the survivors are a DAG, so nothing should be left over; retain any that is
        // (a bug) rather than let V3Dead drop it.
        const std::unordered_set<Group*> ordered{m_ordered.begin(), m_ordered.end()};
        for (Group* const g : live) {
            if (g->live && !ordered.count(g)) killGroupsOfKey(g->keyp, Bail::TOPO_LEFTOVER);
        }
        for (Group* const g : m_ordered) {
            if (!g->live) continue;
            for (AstVarScope* const t : g->targets) m_reconTargets.insert(t);
        }
    }

    // A bit-identical alias of a reconstructed canonical shares its descriptor - same func, same
    // shadow - instead of reconstructing. Per AstVar, as the lazy flag is shared by instances.
    void shareReconstructedAliases() {
        if (m_reconAliasCanonOf.empty()) return;
        std::vector<AstVarScope*> shareable;
        std::unordered_map<const AstVar*, int> shareableInstances;
        for (AstVarScope* const aliasp : m_aliasOrder) {
            const auto it = m_reconAliasCanonOf.find(aliasp);
            if (it == m_reconAliasCanonOf.end()) continue;
            AstVarScope* const canonp = it->second;
            if (!m_reconTargets.count(aliasp) || !m_reconTargets.count(canonp)) continue;
            if (!canShareDescriptor(aliasp, canonp)) continue;
            shareable.push_back(aliasp);
            ++shareableInstances[aliasp->varp()];
        }
        std::unordered_set<Group*> dropped;
        for (AstVarScope* const aliasp : shareable) {
            AstVar* const aliasVarp = aliasp->varp();
            if (shareableInstances.at(aliasVarp) != instancesOf(aliasVarp)) continue;
            Group* const g = m_targetOf.at(aliasp);
            g->live = false;
            dropped.insert(g);
            m_reconTargets.erase(aliasp);
            // Cones reading the alias now read the canonical (aliasSubstituteFor).
            m_retargetCanonOf.emplace(aliasp, m_reconAliasCanonOf.at(aliasp));
            m_sharedAliases.push_back(aliasp);
        }
        if (dropped.empty()) return;
        std::vector<Group*> kept;
        kept.reserve(m_ordered.size() - dropped.size());
        for (Group* const g : m_ordered)
            if (!dropped.count(g)) kept.push_back(g);
        m_ordered.swap(kept);
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

    // Must match V3EmitCSyms's routing, which rebuilds it via V3VpiLazy::reconFuncNameOf().
    std::string reconFuncName(const Group* g) {
        return std::string{V3VpiLazy::RECONSTRUCT_FUNC_NAME} + "__" + std::to_string(gidOf(g));
    }

    std::string reconBodyFuncName(const Group* g) {
        return std::string{RECONSTRUCT_BODY_FUNC_NAME} + "__" + std::to_string(gidOf(g));
    }

    AstCFunc* newReconFunc(AstScope* scopep, const std::string& name) const {
        AstCFunc* const funcp = new AstCFunc{m_funcFlp, name, scopep, ""};
        funcp->isStatic(false);
        funcp->isLoose(true);
        funcp->slow(true);
        // Called only via the syms recon-fn array, an out-of-tree address-take: entryPoint keeps
        // it past V3InlineCFuncs, blocks V3Combine, and stops the body func inlining back into it.
        funcp->entryPoint(true);
        // One func serves every instance: V3Gate/V3Dfg must not substitute an instance-specific
        // expression for a variable it reads.
        funcp->vpiLazyReconstruct(true);
        funcp->declPrivate(false);
        scopep->addBlocksp(funcp);
        return funcp;
    }

    // Give every group a module-local epoch slot shared by all its instances, then create each
    // module's stamp array once its group count is final.
    void assignEpochSlots() {
        std::unordered_map<const AstVar*, int> slotOfKey;
        std::unordered_map<AstNodeModule*, int> slotsOfMod;
        std::vector<AstNodeModule*> modOrder;  // Deterministic AstVar creation order
        for (Group* const g : m_ordered) {
            AstNodeModule* const modp = g->scopep->modp();
            UASSERT_OBJ(g->targets[0]->scopep()->modp() == modp, g->keyp,
                        "Lazy group key variable outside the group scope's module");
            if (slotsOfMod.emplace(modp, 0).second) modOrder.push_back(modp);
            int& slots = slotsOfMod.at(modp);
            const auto pair = slotOfKey.emplace(g->keyp, slots);
            if (pair.second) ++slots;
            g->epochSlot = pair.first->second;
        }
        for (AstNodeModule* const modp : modOrder) makeEpochVar(modp, slotsOfMod.at(modp));
    }

    // The module's freshness stamps: the last epoch at which each group reconstructed. Per
    // instance, as one func serves every instance and a shared slot would mark B fresh after A.
    void makeEpochVar(AstNodeModule* modp, int slots) {
        FileLine* const flp = modp->fileline();
        AstUnpackArrayDType* const dtypep = new AstUnpackArrayDType{
            flp, modp->findUInt64DType(), new AstRange{flp, slots - 1, 0}};
        v3Global.rootp()->typeTablep()->addTypesp(dtypep);
        AstVar* const epochVarp
            = new AstVar{flp, VVarType::MODULETEMP, V3VpiLazy::EPOCH_NAME, dtypep};
        // Stamps must start stale even under --x-initial unique, and it is MODULETEMP being
        // isTemp() that forces the zero (V3EmitCFunc::emitVarReset).
        UASSERT_OBJ(epochVarp->varType().isTemp(), epochVarp,
                    "Epoch stamp array must be zero-initialized");
        epochVarp->trace(false);
        modp->addStmtsp(epochVarp);
        m_epochVarOfMod.emplace(modp, epochVarp);
    }

    // Per-instance VarScope for the stamp array, so the guard can reference it as an AstVarRef.
    AstVarScope* epochFor(Group* g) {
        AstScope* const scopep = g->scopep;
        const auto it = m_epochOfScope.find(scopep);
        if (it != m_epochOfScope.end()) return it->second;
        AstVar* const epochVarp = m_epochVarOfMod.at(scopep->modp());
        AstVarScope* const epochVscp = new AstVarScope{epochVarp->fileline(), scopep, epochVarp};
        scopep->addVarsp(epochVscp);
        m_epochOfScope.emplace(scopep, epochVscp);
        return epochVscp;
    }

    AstNodeExpr* newEpochSel(AstVarScope* epochVscp, int slot, VAccess access) {
        return new AstArraySel{m_funcFlp, new AstVarRef{m_funcFlp, epochVscp, access}, slot};
    }
    AstNodeExpr* newModelEpoch() { return new AstCExpr{m_funcFlp, "vlSymsp->__Vm_lazyEpoch", 64}; }

    AstVarScope* attachShadow(AstVarScope* origp, AstVar* shadowVarp, bool isNew) {
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

    // The VPI-facing shadow of one group target, creating its per-module member on first use.
    AstVarScope* shadowForTarget(Group* g, size_t slot) {
        AstVarScope* const origp = g->targets[slot];
        const auto it = m_shadowOf.find(origp);
        if (it != m_shadowOf.end()) return it->second;
        AstVar* const origVarp = origp->varp();
        const auto vit = m_shadowVarOfOrig.find(origVarp);
        if (vit != m_shadowVarOfOrig.end()) return attachShadow(origp, vit->second, false);
        AstVar* const shadowVarp = new AstVar{origVarp->fileline(), VVarType::MODULETEMP,
                                              V3VpiLazy::SHADOW_PREFIX + std::to_string(gidOf(g))
                                                  + "_" + std::to_string(slot),
                                              origVarp->dtypep()};
        shadowVarp->origName(origVarp->name());  // VPI-facing name
        shadowVarp->lazyReconstructShadow(true);
        // A helper target emits no VPI row of its own, only the descriptor its aliases share.
        if (m_helperTargets.count(origp)) shadowVarp->lazyReconstructHelper(true);
        // Read-safe metadata only: the row's writability comes from emit, so the internal
        // RW/lazy/forceable flags, which change how other passes treat the shadow, are not copied.
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
            std::string{V3VpiLazy::SHADOW_PREFIX} + "t" + std::to_string(idx), origVarp->dtypep()};
        return attachShadow(origp, shadowVarp, true);
    }

    AstVarScope* shadowForMember(Group* g, AstVarScope* u) {
        const auto it = g->slotOf.find(u);
        return it != g->slotOf.end() ? shadowForTarget(g, it->second) : shadowForTemp(u);
    }

    // Detached clone of the group's statements, with every continuous assign rewritten as a
    // blocking one: an AstAssignW must never sit under a CFunc.
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

    // Pin a boundary operand to its own storage so the cold cone can read it. The cone is shared
    // by every instance, so it must read the variable, never a per-instance driver expression.
    void pinBoundary(AstVarScope* u) {
        AstVar* const uVarp = u->varp();
        // Already survives
        if (uVarp->isPrimaryIO() || uVarp->isSigUserRWPublic() || uVarp->isSigVpiLazyRetained())
            return;
        if (uVarp->isSigUserRdPublic()) {
            // Holds storage already, and retaining it would arm the write gate on a row that
            // refuses deposits. V3LinkParse clears the lazy flag when the attribute is explicit.
            UASSERT_OBJ(!uVarp->isSigVpiLazyRWPublic(), uVarp, "public_flat_rd is still lazy");
            return;
        }
        if (uVarp->isSigVpiLazyRWPublic()) {
            m_fallback += instancesOf(uVarp);
            // Sequential/undriven operands hold storage regardless, so pinning them is free.
            const Bail why = hasCombDriver(u) ? combBoundaryReason(u) : Bail::BOUNDARY_OPERAND_SEQ;
            m_bailCount[static_cast<size_t>(why)] += instancesOf(uVarp);
        }
        uVarp->sigVpiLazyRWPublic(false);
        uVarp->sigVpiLazyRetained(true);
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

    // Backward liveness prune of one detached list; returns the new head. 'neededr' - the group
    // variables later code reads - only grows, so one pass suffices; no dead-store elimination.
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

    // Keep 'stmtp'? Prunes inside it as a side effect. Everything here is pure, so dropping a
    // statement shows only through what it writes; a loop is kept whole (back edge not modelled).
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

    // Clone and prune each representative group's body before any operand rewiring, so the cone
    // refresh calls follow the pruned reads. REVERSE topo order makes temp liveness exact: every
    // consumer is pruned first. Matched per AstVar, as all instances share one read set.
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
            // Mirror emitReconstructions's operand rewiring: only a read landing on another
            // group's shadow keeps that group's temp alive; a boundary is read from its own.
            g->bodyp->foreachAndNext([&](AstVarRef* refp) {
                if (refp->access().isWriteOnly()) return;
                AstVarScope* u = refp->varScopep();
                if (g->members.count(u)) return;
                if (AstVarScope* const canonp = aliasSubstituteFor(u, g)) u = canonp;
                const Group* const ugp = liveGroupOf(u);
                if (!ugp || ugp == g) return;
                liveReads.insert(u->varp());
            });
        }
    }

    // Emit one demand-driven reconstruct function per group (steps labelled below). Added to the
    // tree at once so the remapped clones' dtypep() links survive V3Dead's dtype GC.
    void emitReconstructions() {
        m_fallback = m_combBailRetained;  // Retained with storage (incl. group bails so far)
        m_funcFlp = m_topScopep->fileline();
        assignEpochSlots();
        for (Group* const g : m_ordered) {
            // Every instance needs its own shadow VarScope for a per-instance descriptor; only
            // the FIRST instance of each group emits the loose reconstruct func.
            for (size_t slot = 0; slot < g->targets.size(); ++slot) shadowForTarget(g, slot);
            const auto fit = m_funcOfKey.find(g->keyp);
            if (fit != m_funcOfKey.end()) {
                g->funcp = fit->second;
                continue;  // non-representative instance: share the func
            }
            AstCFunc* const funcp = newReconFunc(g->scopep, reconFuncName(g));
            g->funcp = funcp;
            m_funcOfKey.emplace(g->keyp, funcp);

            // Redirect every group variable in the pruned clone to its shadow and collect the
            // operand groups. No re-typing: each shadow carries its original's dtype.
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
                if (AstVarScope* const canonp = aliasSubstituteFor(u, g)) {
                    u = canonp;
                    refp->varScopep(canonp);
                    refp->varp(canonp->varp());
                    refp->dtypeFrom(canonp->varp());
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

            // (1) epoch guard: compare the stamp, restamping as the first then-statement. Not an
            // early return: split-cfuncs may move the body into a func `return` would exit alone.
            AstVarScope* const epochVscp = epochFor(g);
            AstIf* const guardp = new AstIf{
                m_funcFlp,
                new AstNeq{m_funcFlp, newEpochSel(epochVscp, g->epochSlot, VAccess::READ),
                           newModelEpoch()}};
            funcp->addStmtsp(guardp);
            guardp->addThensp(new AstAssign{
                m_funcFlp, newEpochSel(epochVscp, g->epochSlot, VAccess::WRITE), newModelEpoch()});
            // Only a body big enough for --output-split-cfuncs to chop up earns its own function,
            // as the guard cannot go with it; the /4 slack allows for the optimizer growing it.
            AstCFunc* bodyFuncp = nullptr;
            if (const int splitAt = v3Global.opt.outputSplitCFuncs()) {
                int nodes = 0;
                for (AstNode* sp = bodyp; sp; sp = sp->nextp()) nodes += sp->nodeCount();
                if (nodes >= splitAt / 4) {
                    bodyFuncp = newReconFunc(g->scopep, reconBodyFuncName(g));
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

            // The original signals' VPI presence now comes from the shadows.
            for (AstVarScope* const t : g->targets) {
                if (m_helperTargets.count(t)) {
                    ++m_helperCount;  // Never lazy-flagged; visible only via its aliases
                    continue;
                }
                t->varp()->sigVpiLazyRWPublic(false);
                m_reconstructed += instancesOf(t->varp());
            }
        }
    }

    // Record the shared aliases' VPI entries. Runs after reconstruction so the canonicals' shadows
    // exist to name, and an alias pinned as a cone boundary keeps its own entry instead.
    void recordReconstructedAliasRetargets() {
        for (AstVarScope* const aliasp : m_sharedAliases) {
            AstVar* const aliasVarp = aliasp->varp();
            // Pinned as a cone boundary
            if (aliasVarp->isSigUserRWPublic() || aliasVarp->isSigVpiLazyRetained()) continue;
            AstVarScope* const canonp = m_reconAliasCanonOf.at(aliasp);
            pushAliasRetarget(aliasp, m_shadowOf.at(canonp));
            aliasVarp->sigVpiLazyRWPublic(false);  // Visibility now comes from the entry
            ++m_reconAliasShared;
        }
    }

    // Retain write-only signals (an always_ff register never read in RTL): not reconstructable,
    // but near-free to retain, as no readers means no extra hot-path scheduling edges.
    void retainWriteOnlySequential() {
        for (AstVarScope* const vscp : m_gather.m_writtenOrder) {
            AstVar* const varp = vscp->varp();
            if (!varp->isSigVpiLazyRWPublic()) continue;
            if (m_gather.m_writeCount[vscp] < 1 || m_gather.m_readCount[vscp] != 0) continue;
            // A combinationally driven signal is an alias or a group member, not a write-only
            // register: V3Inline moves its readers onto the canonical, zeroing its read count.
            if (hasCombDriver(vscp)) continue;
            if (!retainableKind(varp)) continue;  // Any dtype; only exclusions bail
            varp->sigVpiLazyRWPublic(false);
            varp->sigVpiLazyRetained(true);
            m_writeOnlyRetained += instancesOf(varp);
        }
    }

    // Completeness floor: everything handled above had its lazy flag cleared, so a VarScope still
    // flagged is a residual; retain it, keeping the VPI set a superset of --public-flat-rw's.
    void retainCompletenessFloor() {
        for (AstVarScope* const vscp : m_gather.m_vscOrder) {
            AstVar* const varp = vscp->varp();
            if (!varp->isSigVpiLazyRWPublic()) continue;  // reconstructed / retained already
            if (!retainableKind(varp)) continue;  // only exclusions bail
            retainTarget(vscp, Bail::COMPLETENESS_FLOOR);  // flips the shared AstVar flag once
            m_floorRetained += instancesOf(varp);  // counted once per AstVar (guard above)
        }
    }

    void reportStats() {
        const size_t reconstructedMembers = m_shadowVarOfOrig.size();
        UINFO(3, "vpi-lazy: reconstructed="
                     << m_reconstructed << " groups=" << m_ordered.size()
                     << " members=" << reconstructedMembers << " fallback=" << m_fallback
                     << " reconAliasShared=" << m_reconAliasShared
                     << " prunedStmts=" << m_prunedStmts << " helpers=" << m_helperCount
                     << " writeOnlyRetained=" << m_writeOnlyRetained << " crossScopeRetained="
                     << m_crossScopeRetained << " floorRetained=" << m_floorRetained);
        if (v3Global.opt.stats()) {
            V3Stats::addStat("VPI, lazy reconstructed", m_reconstructed);
            V3Stats::addStat("VPI, lazy groups", m_ordered.size());
            V3Stats::addStat("VPI, lazy reconstructed members", reconstructedMembers);
            V3Stats::addStat("VPI, lazy fallback retained", m_fallback);
            V3Stats::addStat("VPI, lazy alias to reconstructed", m_reconAliasShared);
            V3Stats::addStat("VPI, lazy helper targets", m_helperCount);
            V3Stats::addStat("VPI, lazy pruned statements", m_prunedStmts);
            V3Stats::addStat("VPI, lazy write-only retained", m_writeOnlyRetained);
            V3Stats::addStat("VPI, lazy cross-scope retained", m_crossScopeRetained);
            V3Stats::addStat("VPI, lazy floor retained", m_floorRetained);
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
    nodep->vpiLazyAliasRetargets().clear();
    AstScope* const topScopep = nodep->topScopep() ? nodep->topScopep()->scopep() : nullptr;
    if (!topScopep) return;
    VpiLazyPreparer{nodep, topScopep}.run();

    // A deposit into a retained signal is propagated by re-running 'settle' on the next eval.
    if (nodep->exists([](AstVar* varp) { return varp->isSigVpiLazyRetained(); })) {
        v3Global.setHasVpiLazyRetained();
    }

    V3Global::dumpCheckGlobalTree("vpi-lazy-prepare", 0, dumpTreeEitherLevel() >= 3);
}

//######################################################################

namespace {

// A temp shadow: cold storage for a group variable with no VPI descriptor slot of its own.
bool isTempShadow(const AstVar* varp) {
    return VString::startsWith(varp->name(), V3VpiLazy::SHADOW_PREFIX)
           && !varp->isLazyReconstructShadow();
}

// Where each temp shadow is used, captured in one forward pass: the enclosing func and the
// top-level statement of it that first mentions the shadow.
class TempShadowUseVisitor final : public VNVisitorConst {
public:
    struct Use final {
        AstCFunc* m_funcp = nullptr;  // Null once a second func, or no func at all, uses it
        AstNode* m_firstUsep = nullptr;  // First top-level statement of m_funcp using it
    };
    // STATE
    std::vector<AstVar*> m_order;  // Shadows in encounter order (determinism)
    std::unordered_map<AstVar*, Use> m_useOf;

private:
    AstCFunc* m_funcp = nullptr;  // Func currently being descended, null outside one
    AstNode* m_stmtp = nullptr;  // Top-level statement of m_funcp->stmtsp() being descended

    void visit(AstCFunc* nodep) override {
        VL_RESTORER(m_funcp);
        VL_RESTORER(m_stmtp);
        m_funcp = nodep;
        m_stmtp = nullptr;
        iterateAndNextConstNull(nodep->argsp());
        iterateAndNextConstNull(nodep->varsp());
        iterateConstNull(nodep->scopeNamep());
        // stmtsp by hand: the localized declaration is inserted before a top-level statement,
        // so only those, not their descendants, may be recorded as a first use.
        for (AstNode* stmtp = nodep->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
            m_stmtp = stmtp;
            iterateConst(stmtp);
        }
    }
    void visit(AstNodeVarRef* nodep) override {
        AstVar* const varp = nodep->varp();
        if (isTempShadow(varp)) {
            const auto pair = m_useOf.emplace(varp, Use{m_funcp, m_stmtp});
            if (pair.second) {
                m_order.push_back(varp);
            } else if (pair.first->second.m_funcp != m_funcp) {
                pair.first->second.m_funcp = nullptr;
            } else if (!pair.first->second.m_firstUsep) {
                // Reachable only if the func first mentioned it outside stmtsp, and shadow
                // references are statement-only
                pair.first->second.m_firstUsep = m_stmtp;  // LCOV_EXCL_LINE
            }
        }
        iterateChildrenConst(nodep);
    }
    void visit(AstNode* nodep) override { iterateChildrenConst(nodep); }

public:
    explicit TempShadowUseVisitor(AstNetlist* nodep) { iterateConst(nodep); }
};

// A temp shadow only one reconstruct func touches needs no per-instance member: make it an
// automatic local, declared before its first use so splitCheck can still break the func elsewhere.
int localizeTempShadows(AstNetlist* nodep) {
    const TempShadowUseVisitor uses{nodep};
    int localized = 0;
    for (AstVar* const varp : uses.m_order) {
        const TempShadowUseVisitor::Use& use = uses.m_useOf.at(varp);
        AstCFunc* const funcp = use.m_funcp;
        if (!funcp) continue;
        if (!VString::startsWith(funcp->name(), V3VpiLazy::RECONSTRUCT_FUNC_NAME)) continue;
        if (!use.m_firstUsep) continue;
        varp->unlinkFrBack();
        varp->funcLocal(true);
        varp->sigPublic(false);  // Was set only to hold it as a member
        use.m_firstUsep->addHereThisAsNext(varp);
        ++localized;
    }
    return localized;
}

}  // namespace

void V3VpiLazy::finalize(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ":");

    // prepare() clears the lazy flag whenever it retains, so the two are disjoint.
    nodep->foreach([](AstVar* varp) {
        UASSERT_OBJ(!varp->isSigVpiLazyRetained() || !varp->isSigVpiLazyRWPublic(), varp,
                    "--vpi-lazy signal is both retained and lazy");
    });

    const int localized = localizeTempShadows(nodep);
    if (v3Global.opt.stats()) V3Stats::addStat("VPI, lazy localized temps", localized);

    // prepare()'s pointers do not survive the intervening passes, so find the funcs by name
    // prefix. Only the BODY funcs are split; the entry func's epoch guard must stay whole.
    const std::string prefix = RECONSTRUCT_BODY_FUNC_NAME;
    std::vector<AstCFunc*> reconFuncps;  // Encounter order (determinism)
    nodep->foreach([&](AstCFunc* cfuncp) {
        if (VString::startsWith(cfuncp->name(), prefix)) reconFuncps.push_back(cfuncp);
    });
    if (reconFuncps.empty()) return;  // Nothing was reconstructed

    // Split oversized reconstruction funcs per --output-split-cfuncs, their size now settled.
    for (AstCFunc* const cfuncp : reconFuncps) V3Sched::util::splitCheck(cfuncp);
}
