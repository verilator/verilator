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
// merge into one group, assembled from a zero base. A group's targets are the
// VPI-visible variables it solely drives, its other written variables temp
// shadows. Its statements are cloned into a cold loose function with every
// written variable redirected to a "shadow", leaving the originals deletable.
// Operands belonging to another group are rewired to that group's shadows,
// keeping reconstruction O(N); other "boundary" operands keep their storage so
// the cone has something to read: retained if VPI-visible, else pinned with no
// row, as a compiler temporary has no RTL name.
//
// A group is claimed only if one ordered walk over its statements proves that
// every read of a group variable follows an unconditional full-width write of
// it, that every statement is pure and of a modelled kind, and that every
// target is written on all paths. Otherwise its targets are retained, and Bail
// records why for --stats.
//
// PHASES, in the fixed order run() lists
//
//   classifyCombDriven                       the bits a VPI put may not change
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
// crossScopeCopySources is copyStoredSources for the shape that never forms a
// group at all: a continuous `otherScope.dst = u;`, as an SV interface port
// driven from its parent is. Its descriptor's source is in another scope, and
// so addressed relative to the Syms object both scopes are members of.
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
// keeps its storage and a mask of the bits a put may not change. Instances of
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
#include <iterator>
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
    // Names survive the intervening optimisation passes.
    struct CrossScopeSrcNames final {
        std::string m_dstScopeName;  // Scope holding the copied shadow
        std::string m_dstVarName;  // Shadow variable
        std::string m_srcScopeName;  // Scope holding the copy source
        std::string m_srcVarName;  // Copy source variable
    };

    std::vector<CrossScopeSrcNames> m_crossScopeSrcs;
    std::map<std::pair<const AstScope*, const AstVar*>, V3VpiLazy::CrossScopeSrc>
        m_crossScopeResolved;
    bool m_crossScopeResolvedDone = false;
    std::map<const AstVar*, std::vector<V3VpiLazy::CombRun>> m_combRuns;
    // One instance of a PARTIAL variable whose instances differ.
    struct InstComb final {
        VVpiLazyComb m_comb;  // This instance's class
        std::vector<V3VpiLazy::CombRun> m_runs;  // Its masked bits, if PARTIAL
    };
    std::map<std::pair<std::string, const AstVar*>, InstComb> m_instComb;  // By scope name
    bool m_anyInstStub = false;  // instanceCallee() made a stub for retargetInstanceCalls()

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

using CrossScopeSrcNames = V3VpiLazyContext::CrossScopeSrcNames;
using InstComb = V3VpiLazyContext::InstComb;

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
    std::vector<AstVarScope*> zeroInitps;  // Partial assembly: zero these shadows first
    AstVarScope* copyFromp = nullptr;  // Converted: refresh by copying this variable instead
    AstVar* keyp = nullptr;  // targets[0]->varp(): cross-instance group identity
    AstCFunc* funcp = nullptr;
    bool live = true;  // Cleared when the group is abandoned and its targets retained
    GroupVertex* vtxp = nullptr;  // Its vertex in the dependency graph, null once dead
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
AstVarRef* partialLhsRef(AstNodeExpr* lhsp, PartExtent& extr) {
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

// Pre-optimization walk: write/read counts per VarScope, and per-block write info.
class LazyGatherVisitor final : public VNVisitor {
public:
    struct CombBlock final {
        AstAlways* m_alwaysp = nullptr;  // The combo block
        AstScope* m_scopep = nullptr;  // Scope that authored the block
        AstAssignW* m_assignwp = nullptr;  // Lone AstAssignW of a CONT_ASSIGN block
        std::vector<AstVarScope*> m_targets;  // Written vars, encounter order
        std::unordered_map<const AstVarScope*, int> m_writeCount;  // Writes within this block
    };
    // STATE
    std::unordered_map<const AstVarScope*, int> m_writeCount;  // Writes per var
    std::vector<AstVarScope*> m_writtenOrder;  // Vars with >=1 write, encounter order
    std::unordered_map<const AstVarScope*, int> m_readCount;  // Reads (RW counts as read)
    std::vector<CombBlock> m_combBlocks;  // Combo blocks, encounter order
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
    // Group target -> its group and index in its 'targets'
    std::unordered_map<AstVarScope*, std::pair<Group*, size_t>> m_targetOf;
    // Copy sources promoted from temp to target; per AstVar, so every instance forms one shape
    std::unordered_set<const AstVar*> m_helperCandVars;
    std::unordered_set<const AstVarScope*> m_helperTargets;  // Committed helper targets
    int m_helperCount = 0;  // Helper targets reconstructed, per instance
    std::vector<Group*> m_copyGroups;  // Copies of a variable that holds storage
    std::vector<Group*> m_foldedCopies;  // Copies of another cone's target, sharing its shadow
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
        PARTIAL_GAP,  // Partial writes leave bits undriven, which a VPI put may write
        READ_BEFORE_WRITE,  // A group var is read before an unconditional full-width write
        LATCH,  // A target is not written on every path through the block
        IMPURE,  // The block has a side effect reconstruction must not repeat
        UNSUPPORTED_STMT,  // A statement kind the ordered walk does not model
        UNSUPPORTED_LVALUE,  // A continuous write whose shape a shadow cannot mirror
        CROSS_SCOPE_WRITE,  // Writes a variable outside the scope that authored the statements
        CROSS_SCOPE_CONE,  // Multi-instance cone reading outside its scope; one func cannot serve
        COMB_CYCLE,  // Genuine combinational cycle (SCC member)
        COMPLETENESS_FLOOR,  // No classification path claimed it; retained so VPI still sees it
        BOUNDARY_COMB_DTYPE,  // Comb boundary operand of a kind reconstruction cannot express
        BOUNDARY_COMB_COPY,  // Comb boundary operand whose own row copies another variable
        BOUNDARY_OPERAND_SEQ,  // Read by another cone, no comb driver: sequential/undriven
        _COUNT
    };
    // METHODS
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
                                            "cross-scope write",
                                            "cross-scope cone",
                                            "comb cycle",
                                            "completeness floor",
                                            "boundary comb (dtype)",
                                            "boundary comb (copy)",
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
    std::unordered_map<const AstNodeModule*, AstVar*> m_epochVarOfMod;  // makeStampVar
    std::unordered_map<const AstScope*, AstVarScope*> m_epochOfScope;  // stampFor
    // Per group key, so shared by every instance of its module.
    struct KeyInfo final {
        int gid = -1;  // Design-global id naming the emitted artefacts (gidOf)
        AstCFunc* funcp = nullptr;  // Reconstruct func shared by every instance
        int epochSlot = -1;  // Index into the module's stamp array (assignEpochSlots)
    };
    std::unordered_map<const AstVar*, KeyInfo> m_keyInfo;
    std::unordered_map<const Group*, AstCFunc*> m_instStubOf;  // instanceCallee
    int m_nextGid = 0;
    int m_nextTempIdx = 0;

    int m_prunedStmts = 0;  // Cloned statements dropped as dead (pruneBodies)
    std::map<std::string, int> m_floorReason;  // Floor residual shape -> instances, for stats
    int m_crossScopeCopies = 0;  // Copy rows whose source is in another scope
    // Comb-driven bits of one instance of a VPI candidate: flat element -> {lsb, width}
    struct CombFootprint final {
        bool whole = false;
        std::map<int32_t, std::vector<std::pair<int, int>>> runsOf;
    };
    std::unordered_map<const AstVarScope*, CombFootprint> m_combFootOf;
    std::unordered_set<const AstVar*> m_combFootVars;  // Variables of m_combFootOf keys
    std::vector<AstVar*> m_combFootOrder;  // m_combFootVars, encounter order
    int m_combWhole = 0;  // Read-only variables, per instance
    int m_combPartial = 0;  // Masked variables, per instance

public:
    VpiLazyPreparer(AstNetlist* nodep, AstScope* topScopep, V3VpiLazyContext& ctx)
        : m_topScopep{topScopep}
        , m_ctx{ctx}
        , m_gather{nodep} {}

    // Pre-run VarScope order; run() adds shadow and stamp VarScopes, which carry no lazy role
    const std::vector<AstVarScope*>& vscOrder() const { return m_gather.m_vscOrder; }

    void run() {
        classifyCombDriven();
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

    template <typename T_Callable>
    void forEachStmt(const Group* g, T_Callable&& f) const {
        if (g->alwaysp) {
            for (AstNode* sp = g->alwaysp->stmtsp(); sp; sp = sp->nextp()) f(sp);
        } else {
            for (AstAssignW* const awp : g->partialps) f(static_cast<AstNode*>(awp));
        }
    }

    Bail combBoundaryReason(AstVarScope* u) {
        if (!reconstructableKind(u->varp())) return Bail::BOUNDARY_COMB_DTYPE;
        // A bailed group's targets are retained, so pinBoundary() returns before asking.
        UASSERT_OBJ(m_retargetSrcOf.count(u), u,
                    "--vpi-lazy comb boundary operand no skip path explains");
        return Bail::BOUNDARY_COMB_COPY;
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
        // Already reconstructed / retained, or holding storage regardless
        if (!varp->isSigVpiLazyCandidate() || storagePinnedElsewhere(varp)) return;
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

    // Its VPI presence moves to a shadow; a masked variable's undriven bits need the storage.
    static void dropStorage(AstVar* varp) {
        UASSERT_OBJ(!varp->isVpiLazyCombPartial(), varp,
                    "--vpi-lazy drops the storage of a variable with undriven bits");
        varp->vpiLazyRole(VVpiLazyRole::NONE);
    }

    // METHODS - Writability

    // Explicit public_flat_rw, forceable and top-level input signals keep flat-rw semantics.
    static bool combCandidate(const AstVar* varp) {
        return varp->isSigVpiLazyCandidate() && !varp->isForceable() && !varp->isPrimaryInish();
    }

    // A mask names bits of a table row's integral elements; any other kind is all or nothing.
    static bool combMaskable(const AstVar* varp, std::vector<int32_t>& dimsr, int& elemWidthr) {
        const AstNodeDType* dtypep = varp->dtypeSkipRefp();
        while (const AstUnpackArrayDType* const adtypep = VN_CAST(dtypep, UnpackArrayDType)) {
            dimsr.push_back(adtypep->elementsConst());
            dtypep = adtypep->subDTypep()->skipRefp();
        }
        if (!dtypep->isIntegralOrPacked()) return false;
        const std::pair<uint32_t, uint32_t> dims = varp->dtypeSkipRefp()->dimensions(true);
        if (dims.first + dims.second > static_cast<uint32_t>(V3VpiLazy::VPI_TABLE_MAX_DIMS))
            return false;
        elemWidthr = dtypep->width();
        return true;
    }

    // Row-major, as the storage is laid out; false unless the select names bits of one element.
    static bool combElement(const AstVar* varp, const PartExtent& ext, int32_t& elemr) {
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

    // Keeps an element's runs sorted, disjoint and non-adjacent, as intersectBits needs.
    static void addBits(CombFootprint& fp, int32_t elem, int lsb, int width) {
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

    static void unionBits(CombFootprint& dst, const CombFootprint& src) {
        if (dst.whole) return;
        if (src.whole) {
            dst.whole = true;
            dst.runsOf.clear();
            return;
        }
        for (const auto& pr : src.runsOf) {
            std::vector<std::pair<int, int>>& runs = dst.runsOf[pr.first];
            if (runs.empty()) {
                runs = pr.second;
            } else if (pr.second.size() <= 4) {
                for (const std::pair<int, int>& run : pr.second)
                    addBits(dst, pr.first, run.first, run.second);
            } else {
                std::vector<std::pair<int, int>> sorted;
                sorted.reserve(runs.size() + pr.second.size());
                std::merge(runs.begin(), runs.end(), pr.second.begin(), pr.second.end(),
                           std::back_inserter(sorted));
                runs.clear();
                for (const std::pair<int, int>& run : sorted) {
                    if (!runs.empty() && run.first <= runs.back().first + runs.back().second) {
                        runs.back().second = std::max(runs.back().second,
                                                      run.first + run.second - runs.back().first);
                    } else {
                        runs.push_back(run);
                    }
                }
            }
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

    // Adds to 'definedr' the bits every path through 'stmtsp' assigns. Arms only add, so
    // (D | then) & (D | else) == D | (then & else): each arm is walked from empty.
    // 'modelledr': full-width and constant-select assigns reached through ifs alone, the only
    // writes it decides. Both arms of a constant 'if' are walked, so a V3Const-folded branch
    // reads the same.
    static void latchWalk(AstNode* stmtsp, DefinedBits& definedr,
                          std::unordered_set<const AstVarRef*>& modelledr) {
        for (AstNode* sp = stmtsp; sp; sp = sp->nextp()) {
            if (AstNodeAssign* const asgnp = VN_CAST(sp, NodeAssign)) {
                PartExtent ext;
                int32_t elem = 0;
                if (AstVarRef* const refp = VN_CAST(asgnp->lhsp(), VarRef)) {
                    modelledr.insert(refp);
                    CombFootprint& fp = definedr[refp->varScopep()];
                    fp.whole = true;
                    fp.runsOf.clear();
                } else if (AstVarRef* const prefp = partialLhsRef(asgnp->lhsp(), ext)) {
                    if (combElement(prefp->varp(), ext, elem)) {
                        modelledr.insert(prefp);
                        addBits(definedr[prefp->varScopep()], elem, ext.lsb, ext.width);
                    }
                }
            } else if (AstNodeIf* const ifp = VN_CAST(sp, NodeIf)) {
                // An else-if chain is folded from its last 'else' up, iteratively
                std::vector<AstNodeIf*> chain{ifp};
                while (AstNodeIf* const nextp = VN_CAST(chain.back()->elsesp(), NodeIf)) {
                    if (nextp->nextp()) break;
                    chain.push_back(nextp);
                }
                DefinedBits delta;
                latchWalk(chain.back()->elsesp(), delta, modelledr);
                for (auto it = chain.rbegin(); it != chain.rend(); ++it) {
                    DefinedBits thenDelta;
                    latchWalk((*it)->thensp(), thenDelta, modelledr);
                    const int truth = constTruth((*it)->condp());
                    if (truth == 1) {
                        delta = std::move(thenDelta);
                    } else if (truth < 0) {
                        delta = intersectDefined(thenDelta, delta);
                    }
                }
                unionDefined(definedr, std::move(delta));
            }
        }
    }

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
        std::unordered_set<const AstVarRef*> modelled;
        if (kwd != VAlwaysKwd::CONT_ASSIGN)
            latchWalk(b.m_alwaysp->stmtsp(), proof.defined, modelled);
        b.m_alwaysp->foreach([&](const AstVarRef* refp) {
            if (!refp->access().isReadOnly() && !modelled.count(refp))
                proof.unprovable.insert(refp->varScopep());
        });
        return proof;
    }

    // See WRITABILITY above.
    void classifyCombDriven() {
        for (const CombBlock& b : m_gather.m_combBlocks) {
            if (std::none_of(b.m_targets.begin(), b.m_targets.end(),
                             [](const AstVarScope* t) { return combCandidate(t->varp()); }))
                continue;
            const LatchProof proof = proveLatches(b);
            std::unordered_map<const AstVarRef*, PartExtent> exact;
            b.m_alwaysp->foreach([&](AstNodeAssign* asgnp) {
                PartExtent ext;
                if (const AstVarRef* const refp = partialLhsRef(asgnp->lhsp(), ext))
                    exact.emplace(refp, std::move(ext));
            });
            Defined proven;
            b.m_alwaysp->foreach([&](AstVarRef* refp) {
                if (refp->access().isReadOnly()) return;
                AstVarScope* const vscp = refp->varScopep();
                if (!combCandidate(vscp->varp())) return;
                if (proof.unprovable.count(vscp)) {
                    const auto it = exact.find(refp);
                    addCombWrite(vscp, it == exact.end() ? nullptr : &it->second);
                    return;
                }
                // Every bit defined on every path has a write, so the union of writes is these
                const auto it = proof.defined.find(vscp);
                if (it != proof.defined.end() && proven.insert(vscp).second)
                    addCombBits(vscp, it->second);
            });
        }
        // V3Const made 'assign v = CONST' an initial plus a decl value, but it still drives v
        for (const AstVarScope* const vscp : m_gather.m_vscOrder) {
            AstVar* const varp = vscp->varp();
            if (combCandidate(varp) && varp->isContinuously() && varp->isConst() && varp->valuep()
                && !varp->isParam())
                addCombWrite(vscp, nullptr);
        }
        std::unordered_map<const AstVar*, std::vector<const AstVarScope*>> vscpsOf;
        for (const AstVarScope* const vscp : m_gather.m_vscOrder)
            if (m_combFootVars.count(vscp->varp())) vscpsOf[vscp->varp()].push_back(vscp);
        for (AstVar* const varp : m_combFootOrder) finishCombFootprint(varp, vscpsOf.at(varp));
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
    void finishCombFootprint(AstVar* varp, const std::vector<const AstVarScope*>& vscps) {
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

    Group* makeGroup(AstScope* scopep, AstAlways* alwaysp, std::vector<AstAssignW*>&& parts,
                     const std::vector<AstVarScope*>& written,
                     const std::unordered_map<const AstVarScope*, int>& groupWrites,
                     const std::unordered_set<const AstVar*>& notSole, bool zeroInit) {
        // V3EmitCSyms names the func from the target shadow's module: all group vars share it.
        for (AstVarScope* const w : written) {
            if (w->scopep() == scopep) continue;
            for (AstVarScope* const t : written) {
                if (m_xscopeSrcOf.count(t)) continue;  // crossScopeCopySources() may claim it
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
                retainTarget(w, Bail::MULTIDRIVEN);
            } else if (!varp->isSigVpiLazyCandidate()) {
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
        g->alwaysp = alwaysp;
        g->partialps = std::move(parts);
        g->targets = targets;
        g->temps = temps;
        g->members.insert(targets.begin(), targets.end());
        g->members.insert(temps.begin(), temps.end());
        if (zeroInit) g->zeroInitps = targets;
        g->keyp = targets[0]->varp();
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
            if (!dstp->varp()->isSigVpiLazyCandidate() || writeCountOf(dstp) != 1) return;
            if (srcp->varp()->isSigVpiLazyCandidate()) return;
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
            if (!dstp->varp()->isSigVpiLazyCandidate()) return;
            if (writeCountOf(dstp) != 1) return;
            if (!copyTargetKind(dstp->varp()) || srcp->varp()->isParam()) return;
            if (!sameLayout(dstp, srcp)) return;
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
                if (const AstVarRef* const basep2 = lhsBaseRef(lhsp, partial))
                    retainTarget(basep2->varScopep(), Bail::UNSUPPORTED_LVALUE);
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
        if (!varp->isSigVpiLazyCandidate()) return;
        if (!reconstructableKind(varp)) {
            retainTarget(basep, Bail::DTYPE);
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
        if (varp->isVpiLazyCombPartial()) {
            retainTarget(basep, Bail::PARTIAL_GAP);
            return;
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
        return nodep->exists([&](AstNode* childp) {
            AstVarRef* const refp = VN_CAST(childp, VarRef);
            if (!refp || refp == skipp || refp->access().isWriteOnly()) return false;
            return g->members.count(refp->varScopep()) && !defined.count(refp->varScopep());
        });
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
            const bool selfRead = awp->rhsp()->exists([&](AstNode* nodep) {
                const AstVarRef* const refp = VN_CAST(nodep, VarRef);
                return refp && g->members.count(refp->varScopep());
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
            // V3Slice leaves element assigns at one depth; kept as the safe fallback
            if (ext.idxs.size() != ei.depth) {  // LCOV_EXCL_START
                ei.mixedDepth = true;
                continue;
            }  // LCOV_EXCL_STOP
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

    // 'defined' as walkStmt has it for the whole block.
    bool walkBlockGroup(Group* g, Defined& defined, Bail& whyr) const {
        for (AstNode* sp = g->alwaysp->stmtsp(); sp; sp = sp->nextp()) {
            if (impure(sp)) {
                whyr = Bail::IMPURE;
                return false;
            }
        }
        seedElementWrittenArrays(g, defined);
        return walkStmts(g->alwaysp->stmtsp(), g, defined, whyr);
    }

    bool analyseBlockGroup(Group* g, Bail& whyr) const {
        Defined defined;
        if (!walkBlockGroup(g, defined, whyr)) return false;
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
        for (const auto& ownp : m_groups) {
            const Group* const g = ownp.get();
            if (!g->live || instancesOf(g->keyp) <= 1) continue;
            bool bad = false;
            forEachStmt(g, [&](AstNode* sp) {
                bad = bad || sp->exists([&](const AstVarRef* refp) {
                    return refp->varScopep()->scopep() != g->scopep;
                });
            });
            if (bad) killGroupsOfKey(g->keyp, Bail::CROSS_SCOPE_CONE);
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
            // Non-zero color = a real comb cycle (multi-node SCC): retain it.
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

    // Runs after copyStoredSources, so liveGroupOf() already says what kept its storage.
    void crossScopeCopySources() {
        std::unordered_map<const AstVar*, int> viable;
        std::vector<AstVarScope*> cand;
        for (AstVarScope* const dstp : m_xscopeOrder) {
            AstVarScope* const srcp = m_xscopeSrcOf.at(dstp);
            if (!dstp->varp()->isSigVpiLazyCandidate()) continue;  // retained meanwhile
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
        for (AstVarScope* const dstp : m_xscopeOrder) {
            // makeGroup() left it unretained for this pass, and a cone may yet read it
            if (!claimed.count(dstp->varp())) {
                retainTarget(dstp, Bail::CROSS_SCOPE_WRITE);
                continue;
            }
            // The retarget is what keeps a cone reading this target off pinBoundary().
            m_retargetSrcOf.emplace(dstp, m_xscopeSrcOf.at(dstp));
            m_crossScopeCopyTargets.push_back(dstp);
        }
    }

    // Cross-scope copies: a shadow and a Syms-relative descriptor source, no func, no epoch slot.
    void emitCrossScopeCopies() {
        for (AstVarScope* const dstp : m_crossScopeCopyTargets) {
            if (dstp->varp()->isSigVpiLazyRetained()) continue;
            AstVarScope* const srcp = m_xscopeSrcOf.at(dstp);
            pinBoundary(srcp);
            AstVarScope* const shadowp = crossScopeShadow(dstp);
            m_ctx.m_crossScopeSrcs.push_back(
                CrossScopeSrcNames{dstp->scopep()->name(), shadowp->varp()->name(),
                                   srcp->scopep()->name(), srcp->varp()->name()});
            dropStorage(dstp->varp());
            ++m_reconstructed;
            ++m_crossScopeCopies;
        }
    }

    // Reads pre-optimisation statements, so a width change appears as a Cast/Extend and is
    // refused: memcpy cannot convert.
    AstVarScope* soleCopySource(const Group* g) const {
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
        std::unordered_map<const AstVar*, int> foldable;  // Instances of a key that can fold
        for (Group* const g : m_ordered) {
            AstVarScope* u = soleCopySource(g);
            if (!u) continue;
            if (AstVarScope* const srcp = retargetSubstituteFor(u, g)) u = srcp;
            const Group* const ugp = liveGroupOf(u);
            // m_groupOf covers temps too, and only a target has a shadow with a func to call
            if (!ugp || ugp == g || !m_targetOf.count(u)) continue;
            if (ugp->copyFromp) u = ugp->copyFromp;  // Source folded too; chase it
            // srcOffset is from the target's own selfp, so the source must be the same instance.
            if (!sameLayout(g->targets[0], u) || u->scopep() != g->targets[0]->scopep()) continue;
            ++foldable[g->keyp];
            g->copyFromp = u;
        }
        // m_ordered order, not foldable's, so what is emitted does not depend on pointer hashing
        for (Group* const g : m_ordered) {
            if (!g->copyFromp) continue;
            // One instance could not fold: none may. Instances fold alike, so this is untested.
            if (!claimPerVar(foldable, g->keyp)) {  // LCOV_EXCL_START
                g->copyFromp = nullptr;
                continue;
            }  // LCOV_EXCL_STOP
            // Killing it makes the retarget safe: a consumer that cannot substitute pins instead.
            m_retargetSrcOf.emplace(g->targets[0], g->copyFromp);
            m_foldedCopies.push_back(g);
            g->live = false;
            if (g->bodyp) VL_DO_DANGLING(g->bodyp->deleteTree(), g->bodyp);
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
        if (tableFacing) {
            funcp->voidSelfArg(true);
            funcp->argTypes("void* voidSelf");
        }
        funcp->slow(true);
        // A table-facing func's only caller is the syms recon-fn array, which no pass can see.
        funcp->entryPoint(true);
        // One func serves every instance: V3Gate/V3Dfg must not substitute instance expressions.
        funcp->vpiLazyReconstruct(true);
        funcp->declPrivate(false);
        scopep->addBlocksp(funcp);
        return funcp;
    }

    // V3Descope takes a call's self pointer from its callee's scope, which for a shared func is
    // the representative's. A stub in the operand's own scope gets the call that instance's
    // self pointer; retargetInstanceCalls() then points the call at the shared func.
    AstCFunc* instanceCallee(const Group* ugp) {
        if (ugp->funcp->scopep() == ugp->scopep) return ugp->funcp;
        AstCFunc*& stubp = m_instStubOf[ugp];
        if (!stubp) {
            stubp = newReconFunc(
                ugp->scopep,
                std::string{RECONSTRUCT_INST_FUNC_NAME} + "__" + std::to_string(gidOf(ugp)), true);
            AstCCall* const callp = new AstCCall{m_funcFlp, ugp->funcp};
            callp->dtypeSetVoid();
            stubp->addStmtsp(callp->makeStmt());
            stubp->vpiLazyInstStub(true);
            m_ctx.m_anyInstStub = true;
        }
        return stubp;
    }

    // Slots per module over m_ordered; arrays are created in first-encounter module order.
    void assignEpochSlots() {
        std::unordered_map<const AstNodeModule*, size_t> idxOfMod;
        std::vector<std::pair<AstNodeModule*, int>> slotsOfMod;
        for (Group* const g : m_ordered) {
            AstNodeModule* const modp = g->scopep->modp();
            UASSERT_OBJ(g->targets[0]->scopep()->modp() == modp, g->keyp,
                        "Lazy group key variable outside the group scope's module");
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

    // Shadow of a cross-scope copy target, which belongs to no group and so has no group id.
    AstVarScope* crossScopeShadow(AstVarScope* origp) {
        const int idx
            = m_xscopeShadowIdx.emplace(origp->varp(), m_xscopeShadowIdx.size()).first->second;
        if (AstVarScope* const vscp = reuseShadow(origp)) return vscp;
        return newTargetShadow(origp, std::string{SHADOW_PREFIX} + "x" + std::to_string(idx));
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
        if (uVarp->isPrimaryIO() || uVarp->isSigUserRWPublic() || uVarp->isVpiLazyStorageKept())
            return;
        if (uVarp->isSigUserRdPublic()) {
            // Retaining would arm the write gate on a row that refuses writes.
            UASSERT_OBJ(!uVarp->isSigVpiLazyCandidate(), uVarp, "public_flat_rd is still lazy");
            return;
        }
        if (uVarp->isSigVpiLazyCandidate()) {
            m_fallback += instancesOf(uVarp);
            // Sequential/undriven operands hold storage regardless, so pinning them is free.
            const Bail why = hasCombDriver(u) ? combBoundaryReason(u) : Bail::BOUNDARY_OPERAND_SEQ;
            m_bailCount[static_cast<size_t>(why)] += instancesOf(uVarp);
            uVarp->vpiLazyRole(VVpiLazyRole::RETAINED);
        } else {
            // No RTL name, so no row: --public-flat-rw would not have one either.
            m_boundaryStorage += instancesOf(uVarp);
            uVarp->vpiLazyRole(VVpiLazyRole::PINNED);
        }
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
            const bool live = asgnp->lhsp()->exists([&](AstNode* nodep) {
                const AstVarRef* const refp = VN_CAST(nodep, VarRef);
                return refp && !refp->access().isReadOnly() && neededr.count(refp->varScopep());
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
            AstCFunc* const funcp = newReconFunc(g->scopep, reconFuncName(g), true);
            g->funcp = funcp;
            key.funcp = funcp;
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
                    AstVarScope* const shadowp = shadowForMember(u);
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
                    AstVarScope* const shadowp = shadowForMember(u);
                    refp->varScopep(shadowp);
                    refp->varp(shadowp->varp());
                    if (seenOps.insert(ugp).second) coneOps.push_back(ugp);
                    return;
                }
                pinBoundary(u);
            });

            // (1) epoch guard. Not an early return: split-cfuncs may move the body elsewhere.
            AstVarScope* const epochVscp = stampFor(g);
            AstIf* const guardp = new AstIf{m_funcFlp, newStaleCheck(epochVscp, key.epochSlot)};
            funcp->addStmtsp(guardp);
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
                AstCCall* const callp = new AstCCall{m_funcFlp, instanceCallee(ugp)};
                callp->dtypeSetVoid();
                addBodyStmt(callp->makeStmt());
            }
            // (3) zero the shadows a partial assembly builds up, then (4) run its statements.
            for (AstVarScope* const u : g->zeroInitps) {
                if (!g->neededps.count(u)) continue;  // Its element writes were pruned away
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
                addBodyStmt(new AstAssign{
                    m_funcFlp, new AstVarRef{m_funcFlp, shadowp, VAccess::WRITE}, zerop});
            }
            addBodyStmt(bodyp);

            // The shadows carry the original signals' VPI presence.
            for (AstVarScope* const t : g->targets) {
                if (m_helperTargets.count(t)) {
                    ++m_helperCount;  // Never lazy-flagged; read only by the copies of it
                    continue;
                }
                dropStorage(t->varp());
                m_reconstructed += instancesOf(t->varp());
            }
        }
        emitCopyRows(m_copyGroups, false);
        emitCopyRows(m_foldedCopies, true);
        emitCrossScopeCopies();
    }

    // Copy rows: a shadow and a descriptor source, no func, no epoch slot. A copy names the
    // stored source; a fold's shadow aliases the source cone's, whose func its row calls.
    void emitCopyRows(const std::vector<Group*>& groups, bool folded) {
        for (Group* const g : groups) {
            AstVar* const targetVarp = g->targets[0]->varp();
            // A shadow row on top of the retained row a consumer pinned would name it twice.
            if (targetVarp->isSigVpiLazyRetained()) continue;
            AstVar* srcVarp;
            if (folded) {
                const auto sit = m_shadowOf.find(g->copyFromp);
                UASSERT_OBJ(sit != m_shadowOf.end(), g->copyFromp->varp(),
                            "--vpi-lazy folded copy source has no shadow");
                srcVarp = sit->second->varp();
                UASSERT_OBJ(srcVarp->lazyReconFuncp(), srcVarp,
                            "--vpi-lazy folded copy source has no reconstruct func");
                ++m_foldedCount;
            } else {
                pinBoundary(g->copyFromp);  // The cone this row replaced would have pinned it too
                srcVarp = g->copyFromp->varp();
                ++m_copyCount;
            }
            AstVar* const shadowVarp = shadowForTarget(g, 0)->varp();
            UASSERT_OBJ(!shadowVarp->lazyCopySrc() || shadowVarp->lazyCopySrc() == srcVarp,
                        shadowVarp, "--vpi-lazy copy instances disagree on their source");
            shadowVarp->lazyCopySrc(srcVarp);
            if (shadowVarp->isLazyShadowAlias()) shadowVarp->noReset(true);  // No member to reset
            dropStorage(targetVarp);
            m_reconstructed += instancesOf(targetVarp);
        }
    }

    // A still-flagged VarScope is a residual: retain it, keeping the VPI set a superset of
    // --public-flat-rw's. Kind exclusions govern what may be reconstructed, not what may be
    // retained: else V3Gate substitutes the driver away and the row reads zero for ever.
    void retainCompletenessFloor() {
        for (AstVarScope* const vscp : m_gather.m_vscOrder) {
            AstVar* const varp = vscp->varp();
            if (!varp->isSigVpiLazyCandidate()) continue;  // reconstructed / retained already
            // Its row keeps --public-flat-rw semantics, so give it that flag: V3Force pins a
            // forceable net's force vars, not the net itself, and DFG may alias it away.
            if (storagePinnedElsewhere(varp)) {
                varp->sigUserRWPublic(true);
                varp->vpiLazyRole(VVpiLazyRole::NONE);
                const bool dpi = varp->isReadByDpi() || varp->isWrittenByDpi();
                m_floorReason[dpi ? "storage pinned (DPI)" : "storage pinned"]
                    += instancesOf(varp);
                continue;
            }
            m_floorReason[floorReason(vscp)] += instancesOf(varp);
            UINFO(9, "vpi-lazy floor: " << floorReason(vscp) << " " << vscp->name());
            retainTarget(vscp, Bail::COMPLETENESS_FLOOR);  // flips the shared AstVar flag once
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
        const int floorRetained = m_bailCount[static_cast<size_t>(Bail::COMPLETENESS_FLOOR)];
        UINFO(3, "vpi-lazy: reconstructed="
                     << m_reconstructed << " groups=" << m_ordered.size()
                     << " members=" << reconstructedMembers << " fallback=" << m_fallback
                     << " copyGroups=" << m_copyCount << " crossScopeCopies=" << m_crossScopeCopies
                     << " foldedCopies=" << m_foldedCount << " prunedStmts=" << m_prunedStmts
                     << " helpers=" << m_helperCount << " floorRetained=" << floorRetained);
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
    {
        VpiLazyPreparer preparer{nodep, topScopep, ctx};
        preparer.run();

        bool anyRetained = false;
        for (const AstVarScope* const vscp : preparer.vscOrder()) {
            const AstVar* const varp = vscp->varp();
            if (varp->isSigVpiLazyRetained() && !varp->isVpiLazyCombWhole()) anyRetained = true;
        }
        // A VPI write into a writable retained signal is propagated by re-running 'settle' on the
        // next eval.
        if (anyRetained) v3Global.setHasVpiLazyRetained();
    }

    V3Global::dumpCheckGlobalTree("vpi-lazy-prepare", 0, dumpTreeEitherLevel() >= 3);
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

//######################################################################

namespace {

// Everything resolveCrossScopeSrcs() needs from the tree, in one walk: the AstScope of each
// wanted scope name and the module-level AstVar of each wanted variable name.
class CrossScopeGatherVisitor final : public VNVisitorConst {
    // STATE
    const std::set<std::string>& m_wantScopes;
    const std::set<std::string>& m_wantVars;
    const AstNodeModule* m_modp = nullptr;
    bool m_modLevel = false;  // Directly under a module's stmtsp

public:
    std::map<std::string, const AstScope*> m_scopeps;
    std::map<std::pair<const AstNodeModule*, std::string>, const AstVar*> m_varps;

private:
    // VISITORS
    void visit(AstNodeModule* nodep) override {
        VL_RESTORER(m_modp);
        VL_RESTORER(m_modLevel);
        m_modp = nodep;
        m_modLevel = true;
        iterateChildrenConst(nodep);
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
        if (!m_wantVars.count(nodep->name())) return;
        const bool inserted = m_varps.emplace(std::make_pair(m_modp, nodep->name()), nodep).second;
        UASSERT_OBJ(inserted, nodep,
                    "Duplicate module-level variable name in " << m_modp->prettyNameQ());
    }
    // Module-level vars only: V3Descope moves CFuncs up but leaves their locals inside
    void visit(AstCFunc*) override {}
    void visit(AstNode* nodep) override {
        VL_RESTORER(m_modLevel);
        m_modLevel = false;
        iterateChildrenConst(nodep);
    }

public:
    // CONSTRUCTORS
    CrossScopeGatherVisitor(AstNetlist* nodep, const std::set<std::string>& wantScopes,
                            const std::set<std::string>& wantVars)
        : m_wantScopes{wantScopes}
        , m_wantVars{wantVars} {
        iterateConst(nodep);
    }
};

}  // namespace

void V3VpiLazy::resolveCrossScopeSrcs(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ":");
    V3VpiLazyContext* const ctxp = nodep->vpiLazyContextp();
    if (!ctxp) return;
    ctxp->m_crossScopeResolvedDone = true;
    if (ctxp->m_crossScopeSrcs.empty()) return;

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
    const CrossScopeGatherVisitor gather{nodep, wantScopes, wantVars};

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
        UASSERT_OBJ(srcVarp->isVpiLazyStorageKept() || srcVarp->isSigUserRWPublic()
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

void V3VpiLazy::retargetInstanceCalls(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ":");
    const V3VpiLazyContext* const ctxp = nodep->vpiLazyContextp();
    if (!ctxp || !ctxp->m_anyInstStub) return;
    std::unordered_map<const AstCFunc*, AstCFunc*> sharedOf;
    std::vector<AstCFunc*> stubps;
    nodep->foreach([&](AstCFunc* funcp) {
        if (!funcp->vpiLazyInstStub()) return;
        const AstStmtExpr* const stmtp = VN_CAST(funcp->stmtsp(), StmtExpr);
        const AstCCall* const callp = stmtp ? VN_CAST(stmtp->exprp(), CCall) : nullptr;
        UASSERT_OBJ(callp && !stmtp->nextp(), funcp, "--vpi-lazy instance stub is not one call");
        sharedOf.emplace(funcp, callp->funcp());
        stubps.push_back(funcp);
    });
    // The self pointer V3Descope gave the call stays, as when V3Combine retargets a call.
    nodep->foreach([&](AstCCall* callp) {
        const auto it = sharedOf.find(callp->funcp());
        if (it != sharedOf.end()) callp->funcp(it->second);
    });
    for (AstCFunc* const stubp : stubps)
        VL_DO_DANGLING(stubp->unlinkFrBack()->deleteTree(), stubp);
    V3Global::dumpCheckGlobalTree("vpi-lazy-retarget", 0, dumpTreeEitherLevel() >= 3);
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

// Everything finalize() needs from the tree, in one walk: which reconstruct func (if only one)
// uses each temp shadow, and the reconstruct funcs to split.
class FinalizeVisitor final : public VNVisitorConst {
public:
    struct Use final {
        AstCFunc* m_funcp = nullptr;  // Null once a second func, or no func at all, uses it
        AstNode* m_firstUsep = nullptr;  // First top-level statement of m_funcp using it
        std::vector<AstNodeVarRef*> m_refps;  // Every reference, unscoped on localization
    };
    // STATE
    std::vector<AstVar*> m_order;  // Temp shadows in encounter order (determinism)
    std::unordered_map<AstVar*, Use> m_useOf;
    std::unordered_map<AstVar*, std::vector<AstVarScope*>> m_vscpsOf;  // Of temp shadows
    std::vector<AstCFunc*> m_reconFuncps;  // Encounter order (determinism)
    std::unordered_map<AstCFunc*, std::vector<AstCFunc*>> m_calleesOf;

private:
    AstCFunc* m_funcp = nullptr;  // Func currently being descended, null outside one
    AstNode* m_stmtp = nullptr;  // Top-level statement of m_funcp->stmtsp() being descended

    void visit(AstCFunc* nodep) override {
        VL_RESTORER(m_funcp);
        VL_RESTORER(m_stmtp);
        m_funcp = nodep;
        m_stmtp = nullptr;
        if (nodep->vpiLazyReconstruct()) m_reconFuncps.push_back(nodep);
        iterateAndNextConstNull(nodep->argsp());
        iterateAndNextConstNull(nodep->varsp());
        iterateConstNull(nodep->scopeNamep());
        // By hand: the declaration goes before a top-level statement, so only those count.
        for (AstNode* stmtp = nodep->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
            m_stmtp = stmtp;
            iterateConst(stmtp);
        }
    }
    void visit(AstVarScope* nodep) override {
        if (nodep->varp()->isLazyReconstructTemp()) m_vscpsOf[nodep->varp()].push_back(nodep);
        iterateChildrenConst(nodep);
    }
    void visit(AstNodeCCall* nodep) override {
        if (m_funcp) m_calleesOf[m_funcp].push_back(nodep->funcp());
        iterateChildrenConst(nodep);
    }
    void visit(AstNodeVarRef* nodep) override {
        AstVar* const varp = nodep->varp();
        if (varp->isLazyReconstructTemp()) {
            const auto pair = m_useOf.emplace(varp, Use{m_funcp, m_stmtp, {}});
            if (pair.second) {
                m_order.push_back(varp);
            } else if (pair.first->second.m_funcp != m_funcp) {
                pair.first->second.m_funcp = nullptr;
            } else if (!pair.first->second.m_firstUsep) {
                // Only if first mentioned outside stmtsp, and shadow refs are statement-only
                pair.first->second.m_firstUsep = m_stmtp;  // LCOV_EXCL_LINE
            }
            pair.first->second.m_refps.push_back(nodep);
        }
        iterateChildrenConst(nodep);
    }
    void visit(AstNode* nodep) override { iterateChildrenConst(nodep); }

public:
    explicit FinalizeVisitor(AstNetlist* nodep) { iterateConst(nodep); }
};

// Reconstruct funcs and the V3DepthBlock and splitCheck sub-funcs they call, which lack the flag.
std::unordered_set<const AstCFunc*> reconFamily(const FinalizeVisitor& uses) {
    std::unordered_set<const AstCFunc*> family{uses.m_reconFuncps.begin(),
                                               uses.m_reconFuncps.end()};
    std::vector<AstCFunc*> work = uses.m_reconFuncps;
    while (!work.empty()) {
        AstCFunc* const funcp = work.back();
        work.pop_back();
        const auto it = uses.m_calleesOf.find(funcp);
        if (it == uses.m_calleesOf.end()) continue;
        for (AstCFunc* const calleep : it->second) {
            if (family.insert(calleep).second) work.push_back(calleep);
        }
    }
    return family;
}

// A temp shadow only one reconstruct func touches needs no per-instance member. Not V3Localize's
// job: it skips the isSigPublic() attachShadow sets. Not before V3DepthBlock, which would move a
// use into a sub-func that cannot see the local.
int localizeTempShadows(const FinalizeVisitor& uses) {
    const std::unordered_set<const AstCFunc*> family = reconFamily(uses);
    int localized = 0;
    for (AstVar* const varp : uses.m_order) {
        const auto uit = uses.m_useOf.find(varp);
        UASSERT_OBJ(uit != uses.m_useOf.end(), varp, "--vpi-lazy temp shadow has no recorded use");
        const FinalizeVisitor::Use& use = uit->second;
        AstCFunc* const funcp = use.m_funcp;
        if (!funcp) continue;
        if (!family.count(funcp)) continue;
        if (!use.m_firstUsep) continue;
        varp->unlinkFrBack();
        varp->funcLocal(true);
        varp->sigPublic(false);  // Was set only to hold it as a member
        varp->noReset(false);  // Reset at declaration, as any func local is
        use.m_firstUsep->addHereThisAsNext(varp);
        // As V3Localize leaves a func local: unscoped, its VarScopes gone
        for (AstNodeVarRef* const refp : use.m_refps) refp->varScopep(nullptr);
        const auto vit = uses.m_vscpsOf.find(varp);
        if (vit != uses.m_vscpsOf.end()) {
            for (AstVarScope* vscp : vit->second) {
                VL_DO_DANGLING(vscp->unlinkFrBack()->deleteTree(), vscp);
            }
        }
        ++localized;
    }
    return localized;
}

}  // namespace

//######################################################################

void V3VpiLazy::finalize(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ":");

    const FinalizeVisitor visitor{nodep};

    // Split oversized reconstruction funcs per --output-split-cfuncs, their size now settled.
    // prepare()'s pointers do not survive the intervening passes, so the walk above found the
    // funcs by their flag. splitCheck moves whole top-level statements, so an entry func's
    // epoch guard stays whole.
    for (AstCFunc* const cfuncp : visitor.m_reconFuncps) V3Sched::util::splitCheck(cfuncp);
    V3Global::dumpCheckGlobalTree("vpi-lazy-finalize", 0, dumpTreeEitherLevel() >= 3);
}

void V3VpiLazy::localizeTemps(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ":");
    if (!nodep->vpiLazyContextp()) return;
    const FinalizeVisitor visitor{nodep};
    const int localized = localizeTempShadows(visitor);
    if (v3Global.opt.stats()) V3Stats::addStat("VPI, lazy localized temps", localized);
    V3Global::dumpCheckGlobalTree("vpi-lazy-localize", 0, dumpTreeEitherLevel() >= 3);
}
