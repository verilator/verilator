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
// V3VpiLazy implements --vpi-lazy-public-rw.
//
// LinkParse marks every VPI-accessible variable isSigVpiLazyRWPublic(), but
// unlike --public-flat-rw those variables do NOT block optimization: the hot
// eval path is free to inline and delete them.
//
// This pass restores VPI *read* access to combinational signals the optimizer
// eliminates, without adding any cost to the hot eval path. For each lazy
// signal driven by a single, pure, full-width continuous assignment
// (`assign v = <expr>;`) we clone that defining expression into a cold
// "shadow" storage variable, leaving the original untouched so the optimizer
// is free to delete it. Operands that are themselves reconstructed are
// rewired to their own shadows (keeping reconstruction O(N)); other
// ("boundary") operands are forced to survive via sigUserRWPublic. Each
// captured assignment becomes one cold loose reconstruct func (one per module
// var, shared by all instances), reached on demand from the symbol table when
// a client reads the signal - never from eval(). A per-signal epoch stamp
// checked against a model-wide epoch counter (bumped at the end of eval() and
// on any vpi_put_value) makes each read recompute only its own operand cone,
// once per epoch.
//
// Signals that cannot be represented this way fall back to sigUserRWPublic
// (retained storage, direct VPI entry) - the "lazy fallback retained" stat.
//
// Pure alias nets (`assign a = b;`, and the port-connection aliases V3Inline
// leaves behind after collapsing a hierarchy) get read-WRITE coverage instead:
// a pure alias is the SAME NET as its canonical target, so its VPI entry is
// pointed directly at the canonical's storage - full read-write access, zero
// runtime cost. prepare() resolves alias chains transitively: if the
// canonical is itself reconstructed, the alias reconstructs read-only
// alongside it; otherwise the canonical is a boundary forced to survive, and
// V3EmitCSyms retargets the alias's VPI entry at the canonical's storage.
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

#include <unordered_map>
#include <unordered_set>
#include <vector>

VL_DEFINE_DEBUG_FUNCTIONS;

const char* const V3VpiLazy::RECONSTRUCT_FUNC_NAME = "__Vlazy_reconstruct";

//######################################################################

namespace {

// May we retain 'varp' with ordinary storage? False for signals handled by
// their own mechanisms: ports, forceable/DPI, and modpublic.
bool retainableKind(const AstVar* varp) {
    if (varp->isIO()) return false;
    if (varp->isPrimaryIO()) return false;
    if (varp->isForceable()) return false;
    if (varp->isReadByDpi() || varp->isWrittenByDpi()) return false;
    if (varp->isSigModPublic()) return false;
    return true;
}

// Reconstructable: retainable and representable as one same-dtype shadow var.
// Integral-or-packed qualifies (just packed bits); unpacked aggregates do not.
// Also rejects dims beyond VPI_TABLE_MAX_DIMS: the shadow must fit a
// VlVarTableEntry row, else V3EmitCSyms's table emitter aborts on it.
bool reconstructableKind(const AstVar* varp) {
    if (!retainableKind(varp)) return false;
    const AstNodeDType* const dtypep = varp->dtypeSkipRefp();
    if (!(VN_IS(dtypep, BasicDType) || dtypep->isIntegralOrPacked())) return false;
    const std::pair<uint32_t, uint32_t> dims = dtypep->dimensions(/*includeBasic*/ true);
    return dims.first + dims.second <= static_cast<uint32_t>(V3VpiLazy::VPI_TABLE_MAX_DIMS);
}

// Nearest enclosing AstScope of a still-attached node, walking true parents
// (aboveLoopp() skips list-sibling backlinks). Used to find where a driver
// STATEMENT was authored, as opposed to where its operands happen to live.
AstScope* enclosingScope(AstNode* nodep) {
    for (AstNode* p = nodep->aboveLoopp(); p; p = p->aboveLoopp()) {
        if (AstScope* const scopep = VN_CAST(p, Scope)) return scopep;
    }
    return nullptr;
}

// --------------------------------------------------------------------------
// always_comb fold: a block's last-write-wins value for a target is a pure
// function of its reads, so it folds to one expression. Other written vars fold
// as block-local temps if written before every read at top level (a branch
// write would need per-temp Cond merging, not modeled). foldCombBlock() returns
// a DETACHED prototype (nullptr = bail), cloned into the func and freed later.

// Per-attempt fold state (one FoldCtx per target).
struct FoldCtx final {
    const AstVarScope* target = nullptr;
    const std::unordered_set<const AstVarScope*>* temps = nullptr;  // block-local temp candidates
    std::unordered_map<const AstVarScope*, AstNodeExpr*> tempAcc;  // temp -> current acc (owned)
    int budget = 0;  // Shared node budget (see cloneAcc)
    int condDepth = 0;  // >0 while inside an if/case branch body
    bool bail = false;
    ~FoldCtx() {
        for (auto& pr : tempAcc)
            if (pr.second) pr.second->deleteTree();
    }
};

// Forward decls (mutual recursion).
AstNodeExpr* foldStmtList(AstNode* stmtsp, AstNodeExpr* acc, FoldCtx& ctx);
AstNodeExpr* cloneExpr(AstNodeExpr* srcp, FoldCtx& ctx);

// Each branch clones the accumulator, so N nested branches fold to O(2^N)
// nodes. Charge every clone against a shared budget; on exhaustion, bail to
// retention. 'srcCount' is the caller-cached srcp->nodeCount().
AstNodeExpr* cloneAcc(AstNodeExpr* srcp, int srcCount, int& budget, bool& bail) {
    if (bail || !srcp) return nullptr;
    budget -= srcCount;
    if (budget < 0) {
        bail = true;
        return nullptr;
    }
    return srcp->cloneTree(false);
}

// A budget-charged clone of temp 'tvscp's current accumulator, or nullptr (and
// bail) if the temp was read before it was written.
AstNodeExpr* tempClone(const AstVarScope* tvscp, FoldCtx& ctx) {
    const auto it = ctx.tempAcc.find(tvscp);
    if (it == ctx.tempAcc.end() || !it->second) {
        ctx.bail = true;
        return nullptr;
    }
    return cloneAcc(it->second, it->second->nodeCount(), ctx.budget, ctx.bail);
}

// Clone a source expression (assign RHS, if/case condition, ...) and substitute
// every read of a block-local temp with a charged clone of the temp's current
// accumulator. Returns the substituted clone (owned) or nullptr on bail.
AstNodeExpr* cloneExpr(AstNodeExpr* srcp, FoldCtx& ctx) {
    if (ctx.bail) return nullptr;
    AstNodeExpr* clonep = srcp->cloneTree(false);
    if (!ctx.temps || ctx.temps->empty()) return clonep;
    // The clone's root itself a temp read? (replaceWith needs a parent, so the
    // root is handled separately from the operand refs below.)
    if (AstVarRef* const rootp = VN_CAST(clonep, VarRef)) {
        if (ctx.temps->count(rootp->varScopep())) {
            AstNodeExpr* const sub = tempClone(rootp->varScopep(), ctx);
            VL_DO_DANGLING(clonep->deleteTree(), clonep);
            return sub;  // nullptr on bail
        }
    }
    std::vector<AstVarRef*> refs;
    clonep->foreach([&](AstVarRef* refp) {
        if (refp != clonep && ctx.temps->count(refp->varScopep())) refs.push_back(refp);
    });
    for (AstVarRef* const refp : refs) {
        AstNodeExpr* const sub = tempClone(refp->varScopep(), ctx);
        if (ctx.bail) break;
        refp->replaceWith(sub);
        VL_DO_DANGLING(refp->deleteTree(), refp);
    }
    if (ctx.bail) {
        VL_DO_DANGLING(clonep->deleteTree(), clonep);
        return nullptr;
    }
    return clonep;
}

// Fold a partial write `base[sel] = rhs` into the running accumulator 'acc' (the
// prior full-width value of 'base', owned). Returns
//   (acc & ~(mask << lsb)) | ((rhs & mask) << lsb)
// where mask = (1<<width)-1 at base's width. 'acc' is consumed. On bail returns
// nullptr (acc freed). lsb may be a constant or a pure expression (both cloned
// and charged); an impure lsb / absent prior value bails in the caller.
AstNodeExpr* foldPartialWrite(AstNodeExpr* acc, const AstVarScope* basep, const AstSel* selp,
                              AstNodeExpr* rhsp, FoldCtx& ctx) {
    AstNodeDType* const bdtypep = basep->varp()->dtypep();
    const int bwidth = bdtypep->width();
    const int selWidth = selp->widthConst();
    FileLine* const flp = selp->fileline();
    AstNodeExpr* const lsbp = selp->lsbp();
    const int accCount = acc->nodeCount();
    // Charged clones: acc once, lsb twice (mask-shift and rhs-shift).
    AstNodeExpr* const accClone = cloneAcc(acc, accCount, ctx.budget, ctx.bail);
    AstNodeExpr* const lsb1 = cloneExpr(lsbp, ctx);
    AstNodeExpr* const lsb1c
        = lsb1 ? cloneAcc(lsb1, lsb1->nodeCount(), ctx.budget, ctx.bail) : nullptr;
    AstNodeExpr* rhsClone = ctx.bail ? nullptr : cloneExpr(rhsp, ctx);
    if (ctx.bail || !accClone || !lsb1 || !lsb1c || !rhsClone) {
        ctx.bail = true;
        if (accClone) accClone->deleteTree();
        if (lsb1) lsb1->deleteTree();
        if (lsb1c) lsb1c->deleteTree();
        if (rhsClone) rhsClone->deleteTree();
        VL_DO_DANGLING(acc->deleteTree(), acc);
        return nullptr;
    }
    // mask = (1<<selWidth)-1 at base width.
    V3Number maskNum{flp, bwidth, 0};
    maskNum.setMask(selWidth);
    AstConst* const maskAp = new AstConst{flp, maskNum};
    AstConst* const maskBp = new AstConst{flp, maskNum};
    // acc & ~(mask << lsb)
    AstShiftL* const clrShiftp = new AstShiftL{flp, maskAp, lsb1, bwidth};
    AstNot* const notp = new AstNot{flp, clrShiftp};
    AstAnd* const clearedp = new AstAnd{flp, accClone, notp};
    // (rhs & mask) << lsb   (rhs zero-extended to base width first)
    if (rhsClone->width() < bwidth) rhsClone = new AstExtend{flp, rhsClone, bwidth};
    AstAnd* const maskedRhsp = new AstAnd{flp, rhsClone, maskBp};
    AstShiftL* const setShiftp = new AstShiftL{flp, maskedRhsp, lsb1c, bwidth};
    AstOr* const orp = new AstOr{flp, clearedp, setShiftp};
    orp->dtypep(bdtypep);
    VL_DO_DANGLING(acc->deleteTree(), acc);
    return orp;
}

// Fold one statement, updating 'acc' (the target's running value, owned; may be
// nullptr = no value yet) and, as a side effect, the temp environment in 'ctx'.
// Returns the new target accumulator (owned). On failure sets ctx.bail and
// returns 'acc' unchanged for the caller to clean up.
AstNodeExpr* foldStmt(AstNode* stmtp, AstNodeExpr* acc, FoldCtx& ctx) {
    if (ctx.bail) return acc;
    if (VN_IS(stmtp, Comment)) return acc;
    // Only plain blocking assigns fold; delayed/non-blocking writes don't
    // reach a combinational always body, so they fall through to the bail.
    if (AstAssign* const asgnp = VN_CAST(stmtp, Assign)) {
        // A CReset RHS is a reset directive, not a value expression (cloning it
        // emits a bare AstCReset the C emitter can't handle). Bail.
        if (VN_IS(asgnp->rhsp(), CReset)) {
            ctx.bail = true;
            return acc;
        }
        // LHS: a bare VarRef (full write) or Sel-of-VarRef (partial write) of
        // the target or a block-local temp. Anything else bails.
        AstVarScope* baseVscp = nullptr;
        const AstSel* selp = nullptr;
        if (const AstVarRef* const lhsp = VN_CAST(asgnp->lhsp(), VarRef)) {
            baseVscp = lhsp->varScopep();
        } else if (const AstSel* const lselp = VN_CAST(asgnp->lhsp(), Sel)) {
            if (const AstVarRef* const fromp = VN_CAST(lselp->fromp(), VarRef)) {
                baseVscp = fromp->varScopep();
                selp = lselp;
            }
        }
        const bool isTarget = baseVscp && baseVscp == ctx.target;
        const bool isTemp = baseVscp && !isTarget && ctx.temps && ctx.temps->count(baseVscp);
        if (!isTarget && !isTemp) {
            ctx.bail = true;
            return acc;
        }
        // A temp written inside a branch would need per-temp Cond merging: bail.
        if (isTemp && ctx.condDepth > 0) {
            ctx.bail = true;
            return acc;
        }
        if (!asgnp->rhsp()->isPure()) {
            ctx.bail = true;
            return acc;
        }
        // An impure Sel index would need its side effects preserved; bail.
        if (selp && !selp->lsbp()->isPure()) {
            ctx.bail = true;
            return acc;
        }
        if (isTarget) {
            if (!selp) {  // Full-width write: last-write-wins replace.
                if (acc) VL_DO_DANGLING(acc->deleteTree(), acc);
                return cloneExpr(asgnp->rhsp(), ctx);
            }
            // Partial write: requires a prior full-target value (else latch-like).
            if (!acc) {
                ctx.bail = true;
                return acc;
            }
            return foldPartialWrite(acc, ctx.target, selp, asgnp->rhsp(), ctx);
        }
        // Temp write: update the temp environment; target accumulator unchanged.
        AstNodeExpr*& tep = ctx.tempAcc[baseVscp];
        if (!selp) {
            if (tep) VL_DO_DANGLING(tep->deleteTree(), tep);
            tep = cloneExpr(asgnp->rhsp(), ctx);
        } else {
            if (!tep) {
                ctx.bail = true;
                return acc;
            }
            tep = foldPartialWrite(tep, baseVscp, selp, asgnp->rhsp(), ctx);
        }
        return acc;
    }
    if (AstIf* const ifp = VN_CAST(stmtp, If)) {
        // Fold each branch from a private copy of the incoming acc. A missing
        // branch keeps acc (folds to a clone of it): if(c) v=x; -> Cond(c,x,acc).
        const int accCount = acc ? acc->nodeCount() : 0;
        ++ctx.condDepth;
        AstNodeExpr* const thenAcc
            = foldStmtList(ifp->thensp(), cloneAcc(acc, accCount, ctx.budget, ctx.bail), ctx);
        AstNodeExpr* const elseAcc
            = foldStmtList(ifp->elsesp(), cloneAcc(acc, accCount, ctx.budget, ctx.bail), ctx);
        --ctx.condDepth;
        // Latch guard: a branch that leaves target undefined (no write, no prior
        // acc) must never fabricate a value.
        if (ctx.bail || !thenAcc || !elseAcc) {
            ctx.bail = true;
            if (thenAcc) VL_DO_DANGLING(thenAcc->deleteTree(), thenAcc);
            if (elseAcc) VL_DO_DANGLING(elseAcc->deleteTree(), elseAcc);
            return acc;
        }
        AstNodeExpr* const condp = cloneExpr(ifp->condp(), ctx);
        if (ctx.bail || !condp) {
            ctx.bail = true;
            if (condp) VL_DO_DANGLING(condp->deleteTree(), condp);
            VL_DO_DANGLING(thenAcc->deleteTree(), thenAcc);
            VL_DO_DANGLING(elseAcc->deleteTree(), elseAcc);
            return acc;
        }
        if (acc) VL_DO_DANGLING(acc->deleteTree(), acc);
        return new AstCond{ifp->fileline(), condp, thenAcc, elseAcc};
    }
    // V3Case lowers `case` to AstIf before this pass, so it never reaches here.
    // Anything else (calls, $display, event control) is impure/opaque: bail.
    ctx.bail = true;
    return acc;
}

AstNodeExpr* foldStmtList(AstNode* stmtsp, AstNodeExpr* acc, FoldCtx& ctx) {
    for (AstNode* sp = stmtsp; sp; sp = sp->nextp()) {
        acc = foldStmt(sp, acc, ctx);
        if (ctx.bail) return acc;
    }
    return acc;
}

// Fold a block for 'target' (see always_comb fold, above). nullptr to bail;
// 'budget' is shared across the block's per-target attempts.
AstNodeExpr* foldCombBlock(AstAlways* alwaysp, AstVarScope* target,
                           const std::unordered_set<const AstVarScope*>& temps, int& budget) {
    FoldCtx ctx;
    ctx.target = target;
    ctx.temps = &temps;
    ctx.budget = budget;
    AstNodeExpr* acc = foldStmtList(alwaysp->stmtsp(), nullptr, ctx);
    budget = ctx.budget;  // Charge this attempt against the shared block budget
    // Final latch guard: no path assigned a value.
    if (ctx.bail || !acc) {
        if (acc) VL_DO_DANGLING(acc->deleteTree(), acc);
        return nullptr;
    }
    // A folded value that still reads the target is a read-modify idiom or comb
    // loop: its shadow-reads-shadow reconstruction would read stale storage.
    // Bail (not guarded on temps: V3Split makes single-target blocks common).
    bool selfRef = false;
    acc->foreach([&](AstVarRef* refp) {
        if (refp->varScopep() == target) selfRef = true;
    });
    if (selfRef) {
        VL_DO_DANGLING(acc->deleteTree(), acc);
        return nullptr;
    }
    // Pin the prototype's type to the target's (assignment context) so the
    // func's `shadow = <expr>;` has matching widths.
    acc->dtypep(target->varp()->dtypep());
    return acc;
}

// --------------------------------------------------------------------------
// Tier B: continuous multi-range partial assembly. A signal driven only by
// separate partial-range `assign`s has no full-width driver, but is exactly
// reconstructable: assemble from a ZERO base (undriven bits are 0) via
// foldPartialWrite's masking. The caller only passes DISJOINT constant ranges
// (overlapping or variable-lsb writes retain instead), so order does not matter.
struct ContPartialWrite final {
    const AstSel* m_selp;  // The partial-write Sel (constant lsb/width)
    AstNodeExpr* m_rhsp;  // The assign RHS (pure)
};

// Assemble 'target' from 'parts' (see Tier B, above). Same detached-prototype
// contract as foldCombBlock; nullptr to bail.
AstNodeExpr* assembleContPartials(AstVarScope* target, const std::vector<ContPartialWrite>& parts,
                                  int& budget) {
    FoldCtx ctx;
    ctx.target = target;
    ctx.temps = nullptr;
    ctx.budget = budget;
    AstNodeDType* const dtypep = target->varp()->dtypep();
    FileLine* const flp = target->fileline();
    V3Number zeroNum{flp, dtypep->width(), 0};  // Zero base (undriven bits are 0)
    AstNodeExpr* acc = new AstConst{flp, zeroNum};
    acc->dtypep(dtypep);
    for (const ContPartialWrite& p : parts) {
        acc = foldPartialWrite(acc, target, p.m_selp, p.m_rhsp, ctx);
        if (ctx.bail || !acc) break;
    }
    budget = ctx.budget;
    if (ctx.bail || !acc) {
        if (acc) VL_DO_DANGLING(acc->deleteTree(), acc);
        return nullptr;
    }
    // Pin the prototype's type to the target's (assignment context).
    acc->dtypep(dtypep);
    return acc;
}

// One pre-optimization walk gathering everything prepare() needs: per-VarScope
// write/read counts, the sole pure full-width continuous driver, per-comb-always
// write info, and the per-target continuous partial writes (Tier B).
//
// Determinism: pointer-keyed maps are never iterated where order affects output;
// iteration always walks a companion vector in tree-encounter order. This rule
// holds throughout the file.
class LazyGatherVisitor final : public VNVisitor {
public:
    // A combinational always and the vars it writes (encounter order), with
    // per-var write counts within this block.
    struct CombBlock final {
        AstAlways* m_alwaysp;
        std::vector<AstVarScope*> m_targets;  // Written vars, encounter order
        std::unordered_map<const AstVarScope*, int> m_writeCount;  // Writes within this block
    };
    std::unordered_map<const AstVarScope*, int> m_writeCount;
    std::vector<AstVarScope*> m_writtenOrder;  // Vars with >=1 write, encounter order
    std::unordered_map<const AstVarScope*, int> m_readCount;  // Reads (RW counts as read)
    std::unordered_map<AstVarScope*, AstAssignW*> m_contDriver;
    std::vector<AstVarScope*> m_contOrder;  // m_contDriver keys, encounter order
    std::vector<CombBlock> m_combBlocks;
    // Tier B: per-target continuous partial writes (constant-range Sel of a bare
    // VarRef, pure rhs). Encounter order within each target; companion key list.
    std::unordered_map<AstVarScope*, std::vector<ContPartialWrite>> m_contPartials;
    std::vector<AstVarScope*> m_contPartialOrder;  // m_contPartials keys, encounter order
    // Per-AstVar VarScope count (== same-parameterization instances). Lets retain
    // stats report in the same per-instance unit as the reconstruct counts.
    std::unordered_map<const AstVar*, int> m_instanceCount;
    // Every VarScope in tree-encounter order; iterated only by the completeness floor.
    std::vector<AstVarScope*> m_vscOrder;

private:
    AstAlways* m_comboAlwaysp = nullptr;  // Non-null while inside a combo always body
    std::unordered_map<const AstVarScope*, int> m_blockWrites;  // Writes of the current block
    std::vector<AstVarScope*> m_blockWriteOrder;  // Vars written in this block, encounter order

    void bumpWrite(AstVarScope* vscp) {
        if (m_writeCount[vscp]++ == 0) m_writtenOrder.push_back(vscp);
        if (m_comboAlwaysp) {
            if (m_blockWrites[vscp]++ == 0) m_blockWriteOrder.push_back(vscp);
        }
    }

    void visit(AstNodeAssign* nodep) override {
        // Writes are counted generically in visit(AstVarRef) by lvalue access;
        // here we only record the sole pure full-width continuous driver.
        if (AstAssignW* const wp = VN_CAST(nodep, AssignW)) {
            if (AstVarRef* const lhsp = VN_CAST(wp->lhsp(), VarRef)) {
                if (!wp->timingControlp() && wp->rhsp()->isPure()) {
                    AstVarScope* const vscp = lhsp->varScopep();
                    if (!m_contDriver.count(vscp)) m_contOrder.push_back(vscp);
                    m_contDriver[vscp] = wp;
                }
            } else if (const AstSel* const selp = VN_CAST(wp->lhsp(), Sel)) {
                // Continuous partial write `assign base[const +: w] = rhs;`:
                // record for Tier B. Any other partial-write shape is simply not
                // recorded, so the target's write count falls short and it stays
                // retained.
                if (const AstVarRef* const fromp = VN_CAST(selp->fromp(), VarRef)) {
                    if (!wp->timingControlp() && wp->rhsp()->isPure()
                        && VN_IS(selp->lsbp(), Const)) {
                        AstVarScope* const vscp = fromp->varScopep();
                        if (!m_contPartials.count(vscp)) m_contPartialOrder.push_back(vscp);
                        m_contPartials[vscp].push_back(ContPartialWrite{selp, wp->rhsp()});
                    }
                }
            }
        }
        iterateChildren(nodep);
    }
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
        // Gather each child always's per-block write set in the same descent as
        // the global counts (keeps the sole-driver equality exact).
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
            if (!m_blockWriteOrder.empty()) {
                m_combBlocks.push_back(CombBlock{alwaysp, m_blockWriteOrder, m_blockWrites});
            }
        }
    }
    void visit(AstVarScope* nodep) override {
        ++m_instanceCount[nodep->varp()];
        m_vscOrder.push_back(nodep);
        iterateChildren(nodep);
    }
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    explicit LazyGatherVisitor(AstNetlist* nodep) { iterate(nodep); }
};

// Runs the classification/reconstruction phases over one gather pass. Each
// method below is a phase; run() lists them in a fixed, determinism-critical
// order that must not change.
class VpiLazyPreparer final {
    AstNetlist* const m_nodep;
    AstScope* const m_topScopep;
    LazyGatherVisitor m_gather;

    int m_combBailRetained = 0;  // fold-bail / non-sole-driver / cycle / dropped-driver retains

    std::unordered_set<AstVarScope*> m_candidates;  // Expression candidates (reconstruct)
    std::vector<AstVarScope*> m_candidateOrder;  // m_candidates, in deterministic insert order
    // Scope the driver STATEMENT was authored in, captured at classification
    // time (m_combFolded prototypes are later detached clones, so this can't
    // be recovered from the expression tree once folded).
    std::unordered_map<AstVarScope*, AstScope*> m_driverScope;
    std::unordered_map<AstVarScope*, AstVarScope*> m_aliasImmTarget;  // alias -> immediate target
    std::vector<AstVarScope*> m_aliasOrder;  // m_aliasImmTarget keys, in encounter order

    std::unordered_map<AstVarScope*, AstNodeExpr*> m_combFolded;  // target -> detached prototype
    std::vector<AstVarScope*> m_combOrder;  // m_combFolded keys, in encounter order
    // Per-block node budget guarding against exponential accumulator duplication
    // (see cloneAcc). 0 disables folding (every comb target is retained).
    const int m_foldBudget = v3Global.opt.vpiLazyFoldBudget();

    int m_retargeted = 0;
    std::vector<AstVarScope*> m_retargetCanons;  // Force to survive after reconstruction

    std::unordered_map<AstVarScope*, std::vector<AstVarScope*>> m_dependents;  // u -> {v ...}

    std::vector<AstVarScope*> m_ordered;  // Topological order of reconstructed survivors
    std::unordered_set<AstVarScope*> m_reconSet;  // m_ordered, for O(1) membership

    FileLine* m_funcFlp = nullptr;
    int m_reconstructed = 0;  // Continuous-assign / alias reconstructions
    int m_combReconstructed = 0;  // always_comb folds
    int m_fallback = 0;  // Retained with storage (incl. fold bails), snapshotted pre-emission
    // A module shared by N instances has one AstVar and N AstVarScopes; the
    // shadow mirrors that (one member per module, one VarScope per instance),
    // else N identically-named members collide in the same C++ class.
    std::unordered_map<AstVar*, AstVar*> m_origVarToShadowVar;  // per-module member dedup
    std::unordered_map<AstVarScope*, AstVarScope*> m_origToShadow;  // per-instance VarScope
    // Per-signal freshness epoch stamp, parallel to the shadow member.
    std::unordered_map<AstVar*, AstVar*> m_origVarToEpochVar;
    std::unordered_map<AstVarScope*, AstVarScope*> m_origToEpoch;
    // Per-signal reconstruct function, for wiring operand-cone calls and the
    // symbol-table refresh routing.
    std::unordered_map<AstVarScope*, AstCFunc*> m_reconFuncOf;

    int m_writeOnlyRetained = 0;
    int m_floorRetained = 0;
    int m_crossScopeRetained = 0;  // Multi-instance cones reading outside their scope

public:
    VpiLazyPreparer(AstNetlist* nodep, AstScope* topScopep)
        : m_nodep{nodep}
        , m_topScopep{topScopep}
        , m_gather{nodep} {}

    void run() {
        classifyContinuousDrivers();
        foldContinuousPartials();
        foldCombBlocks();
        resolveAliasChains();
        restrictMultiInstanceToLocalCones();
        buildDependencyGraph();
        splitCyclesRetainCores();
        topoOrderSurvivors();
        emitReconstructions();
        freeCombFoldPrototypes();
        forceRetargetCanonicalsSurvive();
        retainWriteOnlySequential();
        retainCompletenessFloor();
        reportStats();
    }

private:
    // VarScope (instance) count for 'varp'; see m_instanceCount.
    int instancesOf(const AstVar* varp) const {
        const auto it = m_gather.m_instanceCount.find(varp);
        return it != m_gather.m_instanceCount.end() ? it->second : 1;
    }

    // Pin a still-lazy signal to RW storage (like --public-flat-rw), per instance.
    void retainTarget(AstVarScope* target) {
        AstVar* const varp = target->varp();
        if (!varp->isSigVpiLazyRWPublic()) return;  // already reconstructed / retained
        varp->sigUserRWPublic(true);
        varp->sigVpiLazyRWPublic(false);
        m_combBailRetained += instancesOf(varp);
    }

    // 'driverStmtp' is any still-attached node inside the driver statement,
    // used to record which scope authored it (see m_driverScope).
    void addCandidate(AstVarScope* vscp, AstNode* driverStmtp) {
        if (m_candidates.insert(vscp).second) m_candidateOrder.push_back(vscp);
        m_driverScope[vscp] = enclosingScope(driverStmtp);
    }

    // A reconstruct function is one loose, vlSelf-relative function shared by
    // every instance of its module, so it is sound only when every instance
    // computes the same value from a class-internal cone. Two independent axes
    // break that for a multi-instance module and must retain the whole var:
    //   - a VarRef crossing into another scope descopes to an absolute
    //     (vlSymsp->TOP...) path, pinning the shared func to one instance; and
    //   - the driver STATEMENT itself authored outside the target's own scope
    //     (e.g. an interface member tied off from the parent, `assign if.b =
    //     ~if.a;`): every operand can be same-scope and the func still isn't a
    //     property of the shared class, because a sibling instance's parent may
    //     author a different expression for the same member.
    // Decide per-var: if ANY instance is unshareable, retain ALL instances -
    // else a surviving local-cone sibling keeps the var lazy and emits a func
    // built from the wrong (first-encountered) instance. Single-instance modules
    // are immune. Retention keeps the signal VPI-readable, just not lazy.
    void restrictMultiInstanceToLocalCones() {
        std::unordered_set<const AstVar*> unshareable;
        for (AstVarScope* const vscp : m_candidateOrder) {
            if (instancesOf(vscp->varp()) <= 1) continue;
            bool crossScope = false;
            driverExprOf(vscp)->foreach([&](const AstVarRef* refp) {
                if (refp->varScopep()->scopep() != vscp->scopep()) crossScope = true;
            });
            const bool ownScope = m_driverScope.at(vscp) == vscp->scopep();
            if (crossScope || !ownScope) unshareable.insert(vscp->varp());
        }
        std::vector<AstVarScope*> survivors;
        survivors.reserve(m_candidateOrder.size());
        for (AstVarScope* const vscp : m_candidateOrder) {
            AstVar* const varp = vscp->varp();
            if (!unshareable.count(varp)) {
                survivors.push_back(vscp);
                continue;
            }
            m_candidates.erase(vscp);
            if (varp->isSigVpiLazyRWPublic()) {  // count once; flag is shared across instances
                varp->sigUserRWPublic(true);
                varp->sigVpiLazyRWPublic(false);
                m_crossScopeRetained += instancesOf(varp);
            }
        }
        m_candidateOrder.swap(survivors);
    }

    AstNodeExpr* driverExprOf(AstVarScope* vscp) const {
        const auto it = m_combFolded.find(vscp);
        if (it != m_combFolded.end()) return it->second;
        return m_gather.m_contDriver.at(vscp)->rhsp();
    }

    // Classify each sole-continuous-driver lazy signal as an expression candidate
    // or a pure alias (`assign x = y;`; includes V3Inline's port aliases).
    void classifyContinuousDrivers() {
        for (AstVarScope* const vscp : m_gather.m_contOrder) {
            if (m_gather.m_writeCount[vscp] != 1) {
                // Multidriven: not a sole-driver candidate, but retain rather
                // than let the optimizer drop it (losing its VPI entry).
                if (vscp->varp()->isSigVpiLazyRWPublic() && retainableKind(vscp->varp()))
                    retainTarget(vscp);
                continue;
            }
            if (!vscp->varp()->isSigVpiLazyRWPublic()) continue;
            AstNodeExpr* const rhsp = m_gather.m_contDriver[vscp]->rhsp();
            if (const AstVarRef* const rrefp = VN_CAST(rhsp, VarRef)) {
                // A bare `assign x = y;` is a pure alias. Record x -> y if y is a
                // read-only operand with bit-identical storage and x is not a
                // real top-level IO port. Chains are resolved transitively below.
                AstVarScope* const tgtp = rrefp->varScopep();
                const AstNodeDType* const aliasDtp = vscp->varp()->dtypep()->skipRefp();
                const AstNodeDType* const tgtDtp = tgtp->varp()->dtypep()->skipRefp();
                // Bit-identical: same dtype node, or equal-width integral-or-packed
                // dtypes (excludes real/string/UNPACKED, where equal width does not
                // imply equal layout).
                const bool sameStorage
                    = aliasDtp == tgtDtp
                      || (aliasDtp->width() == tgtDtp->width() && aliasDtp->isIntegralOrPacked()
                          && tgtDtp->isIntegralOrPacked());
                if (rrefp->access().isReadOnly() && !vscp->varp()->isPrimaryIO() && sameStorage) {
                    if (m_aliasImmTarget.emplace(vscp, tgtp).second) m_aliasOrder.push_back(vscp);
                }
                continue;
            }
            if (!reconstructableKind(vscp->varp())) {
                // Non-reconstructable dtype (e.g. unpacked aggregate) with a sole
                // continuous driver: retain rather than let it be dropped.
                if (retainableKind(vscp->varp())) retainTarget(vscp);
                continue;
            }
            addCandidate(vscp, m_gather.m_contDriver[vscp]);
        }
    }

    // Tier B (see above), run before the comb fold so its writeCount-mismatch
    // bail sees these targets already folded. The equality check below proves
    // the shape safe.
    void foldContinuousPartials() {
        for (AstVarScope* const target : m_gather.m_contPartialOrder) {
            AstVar* const varp = target->varp();
            if (!varp->isSigVpiLazyRWPublic()) continue;
            if (m_combFolded.count(target)) continue;  // already assembled (defensive)
            UASSERT_OBJ(!m_gather.m_contDriver.count(target), target,
                        "Tier-B target with a coexisting full continuous driver should have "
                        "been retained by the sole-driver loop");
            if (!reconstructableKind(varp)) {
                // Non-reconstructable partial-write target (e.g. an IO port assembled
                // from bit-slice writes): retain if retainable, else leave to its own
                // mechanism. Mirrors the sole-driver loop.
                if (retainableKind(varp)) retainTarget(target);
                continue;
            }
            const std::vector<ContPartialWrite>& parts = m_gather.m_contPartials.at(target);
            if (static_cast<int>(parts.size()) != m_gather.m_writeCount[target]) {
                retainTarget(target);  // A full / comb / impure / var-lsb write exists
                continue;
            }
            // Overlapping continuous writes are multidriven: OR-assembling them
            // would depend on encounter order matching last-write-wins; retain.
            bool overlap = false;
            for (size_t i = 0; i < parts.size() && !overlap; ++i) {
                const int ilsb = parts[i].m_selp->lsbConst();
                const int imsb = ilsb + parts[i].m_selp->widthConst() - 1;
                for (size_t j = i + 1; j < parts.size(); ++j) {
                    const int jlsb = parts[j].m_selp->lsbConst();
                    const int jmsb = jlsb + parts[j].m_selp->widthConst() - 1;
                    if (ilsb <= jmsb && jlsb <= imsb) {
                        overlap = true;
                        break;
                    }
                }
            }
            if (overlap) {
                retainTarget(target);
                continue;
            }
            if (!m_foldBudget) {  // --vpi-lazy-fold-budget 0: no assembly
                retainTarget(target);
                continue;
            }
            int budget = m_foldBudget;
            AstNodeExpr* const protop = assembleContPartials(target, parts, budget);
            if (!protop) {
                retainTarget(target);  // Budget exhausted
                continue;
            }
            m_combFolded.emplace(target, protop);
            m_combOrder.push_back(target);
            addCandidate(target, const_cast<AstSel*>(parts[0].m_selp));
        }
    }

    // Fold each comb block into one pure expression for each reconstructable
    // lazy signal it solely drives, treating other written vars as temps. (No
    // Tier-B counterpart needed: V3Const already merges a fully-covered
    // constant-range always_comb into one concat assign before this pass.)
    void foldCombBlocks() {
        for (const LazyGatherVisitor::CombBlock& block : m_gather.m_combBlocks) {
            int budget = m_foldBudget;
            for (AstVarScope* const target : block.m_targets) {
                if (!target->varp()->isSigVpiLazyRWPublic()) continue;
                if (!reconstructableKind(target->varp())) {
                    // Non-reconstructable dtype (packed struct/union, ...):
                    // retain with storage so it stays VPI-visible.
                    if (retainableKind(target->varp())) retainTarget(target);
                    continue;
                }
                if (m_gather.m_contDriver.count(target) || m_combFolded.count(target)) continue;
                if (m_gather.m_writeCount[target] != block.m_writeCount.at(target)) {
                    retainTarget(target);  // Not this block's sole driver: retain
                    continue;
                }
                if (!m_foldBudget) {  // --vpi-lazy-fold-budget 0: no folding
                    retainTarget(target);
                    continue;
                }
                std::unordered_set<const AstVarScope*> temps;
                for (AstVarScope* const w : block.m_targets)
                    if (w != target) temps.insert(w);
                AstNodeExpr* const protop = foldCombBlock(block.m_alwaysp, target, temps, budget);
                if (!protop) {
                    retainTarget(target);
                    continue;
                }
                m_combFolded.emplace(target, protop);
                m_combOrder.push_back(target);
                addCandidate(target, block.m_alwaysp);
            }
        }
    }

    // Alias's declared (left,right) bounds in EmitCSyms::getVarDims() order:
    // unpacked outer-first, then packed inner-first, then a ranged basic leaf.
    static void snapshotAliasDims(const AstNodeDType* rootDtypep,
                                  std::vector<std::pair<int, int>>& unpackedLR,
                                  std::vector<std::pair<int, int>>& packedLR) {
        for (const AstNodeDType* dtypep = rootDtypep; dtypep;) {
            dtypep = dtypep->skipRefp();
            if (const AstNodeArrayDType* const adtypep = VN_CAST(dtypep, NodeArrayDType)) {
                if (VN_IS(dtypep, PackArrayDType)) {
                    packedLR.emplace_back(adtypep->left(), adtypep->right());
                } else {
                    unpackedLR.emplace_back(adtypep->left(), adtypep->right());
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

    // Resolve alias chains transitively to a canonical (non-alias) target, then:
    //   * canonical is a candidate -> reconstruct the alias read-only alongside it.
    //   * canonical is a boundary   -> retarget the alias at the canonical's
    //     storage (read-write) and force the canonical to survive; recorded on
    //     the netlist for V3EmitCSyms.
    // Aliases whose chain cycles: retain with storage.
    void resolveAliasChains() {
        // Memoized chain -> canonical resolution (path compression). Lookup only.
        // Cycle nodes are left uncached.
        std::unordered_map<AstVarScope*, AstVarScope*> resolvedCanon;
        for (AstVarScope* const aliasp : m_aliasOrder) {
            AstVarScope* canonp = aliasp;
            std::unordered_set<AstVarScope*> chain;  // This walk's nodes, for cycle + compression
            bool cycle = false;
            while (true) {
                const auto cit = resolvedCanon.find(canonp);
                if (cit != resolvedCanon.end()) {
                    canonp = cit->second;  // Cached tail of the chain
                    break;
                }
                const auto tit = m_aliasImmTarget.find(canonp);
                if (tit == m_aliasImmTarget.end()) break;  // canonp is the canonical (non-alias)
                if (!chain.insert(canonp).second) {
                    cycle = true;  // Revisited a chain node
                    break;
                }
                canonp = tit->second;
            }
            if (cycle) {
                retainTarget(aliasp);  // Unresolvable cycle: retain, do not drop
                continue;
            }
            for (AstVarScope* const np : chain) resolvedCanon.emplace(np, canonp);
            if (m_candidates.count(canonp)) {
                // Canonical is reconstructed: reconstruct this alias read-only too
                // (its shadow reads the canonical's shadow via operand rewiring).
                if (reconstructableKind(aliasp->varp()))
                    addCandidate(aliasp, m_gather.m_contDriver.at(aliasp));
                continue;
            }
            // Boundary canonical: retarget for read-write (forced to survive
            // later, after reconstruction has had its chance to retain it as a
            // boundary, so the fallback stat is exact). The emitted entry reads
            // the canonical's storage but reports the ALIAS's own metadata.
            const AstVar* const aliasVarp = aliasp->varp();
            const AstNodeDType* const aliasDtp = aliasVarp->dtypeSkipRefp();
            const AstBasicDType* const aliasBasicp = aliasDtp->basicp();
            VpiLazyAliasRetarget rt{aliasp->scopep()->name(),
                                    aliasVarp->name(),
                                    canonp->varp()->name(),
                                    aliasDtp->isSigned(),
                                    aliasBasicp && aliasBasicp->keyword() == VBasicDTypeKwd::BIT,
                                    aliasVarp->isNet()};
            snapshotAliasDims(aliasVarp->dtypep(), rt.m_aliasUnpackedLR, rt.m_aliasPackedLR);
            m_nodep->vpiLazyAliasRetargets().push_back(std::move(rt));
            m_retargetCanons.push_back(canonp);
            ++m_retargeted;
        }
    }

    // Dependency edges among candidates: operand u drives vscp, so the edge is
    // u -> vscp. A self-edge (u == vscp, a single-node comb self-loop) is
    // recorded like any other; the SCC pass then colors it as a cycle.
    void buildDependencyGraph() {
        for (AstVarScope* const vscp : m_candidateOrder) {
            std::unordered_set<AstVarScope*> seen;
            driverExprOf(vscp)->foreach([&](AstVarRef* refp) {
                AstVarScope* const u = refp->varScopep();
                if (!m_candidates.count(u)) return;
                if (!seen.insert(u).second) return;
                m_dependents[u].push_back(vscp);
            });
        }
    }

    // Retain only genuine cycle members: a candidate merely downstream of a cycle
    // can still reconstruct cold, reading the retained core as a boundary operand.
    // (A naive "retain whatever Kahn's left over" would pin the whole cone.) Use
    // an SCC pass to separate cores from cone.
    void splitCyclesRetainCores() {
        V3Graph sccGraph;
        std::unordered_map<AstVarScope*, V3GraphVertex*> vtxOf;  // lookup only
        for (AstVarScope* const vscp : m_candidateOrder)
            vtxOf.emplace(vscp, new V3GraphVertex{&sccGraph});
        for (AstVarScope* const u : m_candidateOrder) {
            const auto dit = m_dependents.find(u);
            if (dit == m_dependents.end()) continue;
            V3GraphVertex* const uVtxp = vtxOf.at(u);
            for (AstVarScope* const v : dit->second)
                new V3GraphEdge{&sccGraph, uVtxp, vtxOf.at(v), 1};
        }
        sccGraph.stronglyConnected(&V3GraphEdge::followAlwaysTrue);
        std::vector<AstVarScope*> survivors;
        survivors.reserve(m_candidateOrder.size());
        for (AstVarScope* const vscp : m_candidateOrder) {
            // Non-zero color = a genuine combinational cycle (a multi-node SCC
            // member or a single-node self-loop): retain it with storage.
            if (vtxOf.at(vscp)->color() != 0) {
                retainTarget(vscp);
                m_candidates.erase(vscp);
            } else {
                survivors.push_back(vscp);
            }
        }
        m_candidateOrder.swap(survivors);
    }

    // Kahn topo-sort of the survivors (a DAG now the cycle members are gone).
    // In-degree counts only survivor -> survivor edges.
    //
    // Scope affinity: prefer a ready node in the previously ordered node's scope,
    // so each scope's statements form contiguous runs (emitted as per-scope
    // sub-functions, dedupable across instances by V3Combine).
    void topoOrderSurvivors() {
        std::unordered_map<AstVarScope*, int> inDegree;
        for (AstVarScope* const vscp : m_candidateOrder) inDegree[vscp];  // ensure present
        for (AstVarScope* const u : m_candidateOrder) {
            const auto dit = m_dependents.find(u);
            if (dit == m_dependents.end()) continue;
            for (AstVarScope* const v : dit->second)
                if (m_candidates.count(v)) ++inDegree[v];
        }
        std::unordered_map<const AstScope*, std::vector<AstVarScope*>> readyOf;  // lookup only
        std::vector<AstScope*> scopeQueue;  // Scopes that (re)gained ready nodes, encounter order
        const auto pushReady = [&](AstVarScope* vscp) {
            std::vector<AstVarScope*>& stack = readyOf[vscp->scopep()];
            if (stack.empty()) scopeQueue.push_back(vscp->scopep());
            stack.push_back(vscp);
        };
        for (AstVarScope* const vscp : m_candidateOrder)
            if (inDegree[vscp] == 0) pushReady(vscp);
        const AstScope* curScopep = nullptr;
        size_t scopeQi = 0;  // Next scopeQueue entry to consider
        while (true) {
            AstVarScope* up = nullptr;
            if (curScopep) {  // Stay in the current scope while it has ready nodes
                std::vector<AstVarScope*>& stack = readyOf[curScopep];
                if (!stack.empty()) {
                    up = stack.back();
                    stack.pop_back();
                }
            }
            if (!up) {  // Advance to the next scope with ready nodes
                while (scopeQi < scopeQueue.size() && readyOf[scopeQueue[scopeQi]].empty())
                    ++scopeQi;
                if (scopeQi == scopeQueue.size()) break;
                curScopep = scopeQueue[scopeQi];
                std::vector<AstVarScope*>& stack = readyOf[curScopep];
                up = stack.back();
                stack.pop_back();
            }
            m_ordered.push_back(up);
            for (AstVarScope* const v : m_dependents[up]) {
                if (!m_candidates.count(v)) continue;  // Skip edges to retained cycle cores
                if (--inDegree[v] == 0) pushReady(v);
            }
        }
        m_reconSet.insert(m_ordered.begin(), m_ordered.end());

        // Safety net: the survivors are a DAG, so Kahn's orders all of them and
        // this finds nothing. Retain any leftover (a bug) rather than let V3Dead
        // drop it.
        for (AstVarScope* const vscp : m_candidateOrder) {
            if (!m_reconSet.count(vscp)) retainTarget(vscp);
        }
    }

    // Per-signal reconstruct function name; must match V3EmitCSyms's routing,
    // which rebuilds it from the shadow var's origName() (== the orig var name).
    static std::string reconFuncName(const AstVarScope* vscp) {
        return std::string{V3VpiLazy::RECONSTRUCT_FUNC_NAME} + "__" + vscp->varp()->name();
    }

    // The per-signal freshness stamp for 'origp' (last epoch its shadow was
    // reconstructed), parallel to shadowFor: one uint64 member per module, one
    // VarScope per instance.
    AstVarScope* epochFor(AstVarScope* origp) {
        const auto it = m_origToEpoch.find(origp);
        if (it != m_origToEpoch.end()) return it->second;
        AstVar* const origVarp = origp->varp();
        FileLine* const flp = origVarp->fileline();
        const auto vit = m_origVarToEpochVar.find(origVarp);
        AstVar* epochVarp;
        if (vit != m_origVarToEpochVar.end()) {
            epochVarp = vit->second;
        } else {
            epochVarp = new AstVar{flp, VVarType::MODULETEMP, "__Vlazyepoch__" + origVarp->name(),
                                   origVarp->findUInt64DType()};
            epochVarp->sigPublic(true);  // Keep as a struct member; don't optimize/localize
            epochVarp->trace(false);
            origp->scopep()->modp()->addStmtsp(epochVarp);
            m_origVarToEpochVar.emplace(origVarp, epochVarp);
        }
        AstVarScope* const epochVscp = new AstVarScope{flp, origp->scopep(), epochVarp};
        origp->scopep()->addVarsp(epochVscp);
        m_origToEpoch.emplace(origp, epochVscp);
        return epochVscp;
    }

    // The shadow VarScope for 'origp', creating its per-module shadow member on
    // first use (see m_origVarToShadowVar).
    AstVarScope* shadowFor(AstVarScope* origp) {
        const auto it = m_origToShadow.find(origp);
        if (it != m_origToShadow.end()) return it->second;
        AstVar* const origVarp = origp->varp();
        FileLine* const flp = origVarp->fileline();
        const auto vit = m_origVarToShadowVar.find(origVarp);
        AstVar* shadowVarp;
        if (vit != m_origVarToShadowVar.end()) {
            shadowVarp = vit->second;
        } else {
            shadowVarp = new AstVar{flp, VVarType::MODULETEMP, "__Vlazyrecon__" + origVarp->name(),
                                    origVarp->dtypep()};
            shadowVarp->origName(origVarp->name());  // VPI-facing name
            shadowVarp->sigPublic(true);  // Keep as a struct member; don't optimize/localize
            shadowVarp->lazyReconstructShadow(true);
            shadowVarp->trace(false);
            // Copy only read-safe metadata: the shadow stays read-only (emit
            // forces VLVF_PUB_RD), so RW/lazy/forceable flags are NOT copied.
            shadowVarp->direction(origVarp->direction());
            shadowVarp->declDirection(origVarp->declDirection());
            shadowVarp->isContinuously(origVarp->isContinuously());
            origp->scopep()->modp()->addStmtsp(shadowVarp);
            m_origVarToShadowVar.emplace(origVarp, shadowVarp);
        }
        // One shadow VarScope per instance scope, sharing the module's member.
        AstVarScope* const shadowVscp = new AstVarScope{flp, origp->scopep(), shadowVarp};
        origp->scopep()->addVarsp(shadowVscp);
        m_origToShadow.emplace(origp, shadowVscp);
        return shadowVscp;
    }

    // Emit one demand-driven reconstruct function per module var (steps labelled
    // below). Reading one VPI signal reconstructs only its operand cone, not the
    // whole model; the per-signal epoch stamp collapses shared sub-cones to one
    // recompute. Funcs are added to the tree immediately so the operand-remapped
    // clones' dtypep() links survive V3Dead's dtype GC and get re-typed by
    // V3Const/V3Width/DFG.
    void emitReconstructions() {
        m_fallback = m_combBailRetained;  // Retained with storage (incl. fold bails so far)
        m_funcFlp = m_topScopep->fileline();
        std::unordered_map<AstVar*, AstCFunc*> funcOfVar;  // One func per module AstVar
        for (AstVarScope* const vscp : m_ordered) {
            AstScope* const scopep = vscp->scopep();
            AstVar* const origVarp = vscp->varp();
            // Every instance needs its own shadow + epoch VarScope so EmitCSyms
            // emits a per-instance descriptor; only the FIRST instance of each
            // module AstVar emits the (loose, vlSelf-relative) reconstruct func.
            AstVarScope* const shadowVscp = shadowFor(vscp);
            AstVarScope* const epochVscp = epochFor(vscp);
            const auto fit = funcOfVar.find(origVarp);
            if (fit != funcOfVar.end()) {
                m_reconFuncOf.emplace(vscp, fit->second);
                continue;  // non-representative instance: share the func
            }
            AstCFunc* const funcp = new AstCFunc{m_funcFlp, reconFuncName(vscp), scopep, ""};
            funcp->isStatic(false);
            funcp->isLoose(true);
            funcp->slow(true);
            // Called only via the syms recon-fn array (out-of-tree address-take):
            // entryPoint keeps it past V3InlineCFuncs and blocks V3Combine merging.
            funcp->entryPoint(true);
            funcp->declPrivate(false);
            scopep->addBlocksp(funcp);
            m_reconFuncOf.emplace(vscp, funcp);
            funcOfVar.emplace(origVarp, funcp);

            // (1)+(2) epoch guard.
            const std::string em = epochVscp->varp()->nameProtect();
            funcp->addStmtsp(new AstCStmt{
                m_funcFlp, "if (vlSelf->" + em + " == vlSymsp->__Vm_lazyEpoch) return;\n"
                               + "vlSelf->" + em + " = vlSymsp->__Vm_lazyEpoch;\n"});

            // Clone the defining expression and rewire operands; collect the
            // reconstructed operands (deduped, encounter order) for cone calls.
            AstNodeExpr* const clonep = driverExprOf(vscp)->cloneTree(false);
            std::unordered_set<AstVarScope*> seenOp;
            std::vector<AstVarScope*> coneOps;
            clonep->foreach([&](AstVarRef* refp) {
                AstVarScope* const u = refp->varScopep();
                if (m_reconSet.count(u)) {
                    // Operand is reconstructed too: read its shadow, and ensure
                    // it is fresh by calling its reconstruct function first.
                    AstVarScope* const shadowp = shadowFor(u);
                    refp->varScopep(shadowp);
                    refp->varp(shadowp->varp());
                    if (seenOp.insert(u).second) coneOps.push_back(u);
                } else {
                    // Boundary operand: force it to survive with storage. Primary
                    // IO already survives; others need forcing.
                    AstVar* const uVarp = u->varp();
                    if (!uVarp->isPrimaryIO() && !uVarp->isSigUserRWPublic()) {
                        if (uVarp->isSigVpiLazyRWPublic()) m_fallback += instancesOf(uVarp);
                        uVarp->sigUserRWPublic(true);
                        uVarp->sigVpiLazyRWPublic(false);
                    }
                }
            });
            // (3) refresh the operand cone (each operand precedes vscp in topo
            // order, so its function already exists).
            for (AstVarScope* const u : coneOps) {
                AstCCall* const callp = new AstCCall{m_funcFlp, m_reconFuncOf.at(u)};
                callp->dtypeSetVoid();
                funcp->addStmtsp(callp->makeStmt());
            }
            // (4) assign this signal's shadow.
            AstVarRef* const lhsp = new AstVarRef{m_funcFlp, shadowVscp, VAccess::WRITE};
            funcp->addStmtsp(new AstAssign{m_funcFlp, lhsp, clonep});
            // The original signal's VPI presence now comes from the shadow.
            vscp->varp()->sigVpiLazyRWPublic(false);
            if (m_combFolded.count(vscp)) {
                m_combReconstructed += instancesOf(origVarp);
            } else {
                m_reconstructed += instancesOf(origVarp);
            }
        }
    }

    // Free the detached comb-fold prototypes: each signal's func now owns its
    // own clone of them.
    void freeCombFoldPrototypes() {
        for (AstVarScope* const vscp : m_combOrder) {
            AstNodeExpr* const protop = m_combFolded[vscp];
            VL_DO_DANGLING(protop->deleteTree(), protop);
        }
    }

    // Force each retarget's canonical to survive with RW storage. Runs after
    // reconstruction so the fallback stat is unaffected by aliasing.
    void forceRetargetCanonicalsSurvive() {
        for (AstVarScope* const canonp : m_retargetCanons) {
            AstVar* const canonVarp = canonp->varp();
            if (!canonVarp->isPrimaryIO() && !canonVarp->isSigUserRWPublic()) {
                canonVarp->sigUserRWPublic(true);
                canonVarp->sigVpiLazyRWPublic(false);
            }
        }
    }

    // Retain write-only signals (e.g. an always_ff register never read in RTL):
    // they can't be reconstructed, but retaining is near-free (no readers means
    // no extra hot-path scheduling edges).
    void retainWriteOnlySequential() {
        for (AstVarScope* const vscp : m_gather.m_writtenOrder) {
            AstVar* const varp = vscp->varp();
            if (!varp->isSigVpiLazyRWPublic()) continue;
            if (m_gather.m_writeCount[vscp] < 1 || m_gather.m_readCount[vscp] != 0) continue;
            if (m_gather.m_contDriver.count(vscp) || m_combFolded.count(vscp)) continue;
            if (!retainableKind(varp)) continue;  // Any dtype; only exclusions bail
            varp->sigUserRWPublic(true);
            varp->sigVpiLazyRWPublic(false);
            m_writeOnlyRetained += instancesOf(varp);
        }
    }

    // Completeness floor: anything handled above already had its lazy flag
    // cleared, so a VarScope still flagged here is a residual that would
    // otherwise be silently dropped from VPI. Retain it, guaranteeing the
    // VPI-visible set is a superset of --public-flat-rw's. (Retargeted aliases
    // keep their flag on purpose - visibility comes from the retarget entry.)
    void retainCompletenessFloor() {
        for (AstVarScope* const vscp : m_gather.m_vscOrder) {
            AstVar* const varp = vscp->varp();
            if (!varp->isSigVpiLazyRWPublic()) continue;  // reconstructed / retained already
            if (!retainableKind(varp)) continue;  // only exclusions bail
            if (m_aliasImmTarget.count(vscp)) continue;  // retargeted alias: stays a retarget
            retainTarget(vscp);  // flips the shared AstVar flag once
            m_floorRetained += instancesOf(varp);  // counted once per AstVar (guard above)
        }
    }

    void reportStats() {
        const size_t reconstructedMembers = m_origVarToShadowVar.size();
        UINFO(3, "vpi-lazy: reconstructed=" << m_reconstructed << " comb=" << m_combReconstructed
                                            << " members=" << reconstructedMembers << " fallback="
                                            << m_fallback << " retargeted=" << m_retargeted
                                            << " writeOnlyRetained=" << m_writeOnlyRetained
                                            << " crossScopeRetained=" << m_crossScopeRetained
                                            << " floorRetained=" << m_floorRetained);
        if (v3Global.opt.stats()) {
            V3Stats::addStat("VPI, lazy reconstructed", m_reconstructed);
            V3Stats::addStat("VPI, lazy comb reconstructed", m_combReconstructed);
            V3Stats::addStat("VPI, lazy reconstructed members", reconstructedMembers);
            V3Stats::addStat("VPI, lazy fallback retained", m_fallback);
            V3Stats::addStat("VPI, lazy alias retargeted", m_retargeted);
            V3Stats::addStat("VPI, lazy write-only retained", m_writeOnlyRetained);
            V3Stats::addStat("VPI, lazy cross-scope retained", m_crossScopeRetained);
            // The completeness floor's give-back: residual stateless signals
            // pinned with storage so every signal stays at least VPI-readable.
            V3Stats::addStat("VPI, lazy floor retained", m_floorRetained);
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
    V3Global::dumpCheckGlobalTree("vpi-lazy-prepare", 0, dumpTreeEitherLevel() >= 3);
}

//######################################################################

void V3VpiLazy::finalize(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ":");

    // The per-signal reconstruct funcs were built in prepare() and rode through
    // the optimizer in the tree. Find them by name prefix (prepare()'s pointers
    // don't survive the intervening passes); the prefix matches every
    // "__Vlazy_reconstruct__<name>".
    const std::string prefix = RECONSTRUCT_FUNC_NAME;
    std::vector<AstCFunc*> reconFuncps;  // Encounter order (determinism)
    nodep->foreach([&](AstCFunc* cfuncp) {
        if (VString::startsWith(cfuncp->name(), prefix)) reconFuncps.push_back(cfuncp);
    });
    if (reconFuncps.empty()) return;  // Nothing was reconstructed

    // Split oversized reconstruction funcs per --output-split-cfuncs (their size
    // is settled now), spreading a large design's code across many output files.
    for (AstCFunc* const cfuncp : reconFuncps) V3Sched::util::splitCheck(cfuncp);

    // Bump the freshness epoch at the end of eval(), so the next VPI read of any
    // reconstructed signal recomputes it from fresh model state.
    if (AstCFunc* const evalp = nodep->evalp()) {
        evalp->addStmtsp(new AstCStmt{evalp->fileline(), "++vlSymsp->__Vm_lazyEpoch;\n"});
    }
}
