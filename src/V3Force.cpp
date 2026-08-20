// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Convert forceable signals, process force/release
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
//  V3Force's Transformations:
//
//  Every force target on a variable is given a slot in that variable's VlForceVec.  A plain
//  bitwise variable is addressed by bit range, so a slot is a bit.  Anything else is addressed
//  by leaf: an aggregate is laid out depth first, and a leaf's slot is the member offsets its
//  path crosses plus each element index times that element's own slot count.  One numbering
//  covers 's.arr[2]', 's.scalar' and 'sa[0].arr[2]' alike, and a run-time element index
//  computes its slot with the same arithmetic.
//
//  For each forceable var/net "<name>":
//    - Create <name>__VforceVec (VlForceVec) to track active force ranges
//    - Create <name>__VforceRHS<ID> vars to hold RHS shadow values
//    - Add continuous assignments: <name>__VforceRHS<ID> = RHS
//
//  For each `force <name><path> = <RHS>` with ID:
//    - <name>__VforceVec.addForce(slot_lsb, slot_msb, &__VforceRHS, rhsLsb)
//
//  For each `release <name><path>`:
//    - If not continuously driven: <name><path> = VlForceVec::read(<name><path>, __VforceVec)
//    - <name>__VforceVec.release(slot_lsb, slot_msb)
//
//  For each read of <name><path>:
//    - Replace with: VlForceVec::read(<name><path>, __VforceVec, slot)
//
//  Slot-tracked variables register only ownership: VlForceVec records which force id owns
//  which slots, and every value lives in that force's own typed shadow (__VforceRHS<ID>).
//  A read of a leaf compiles to a chain over the forces that can reach it, outermost target
//  first, each consulting ownership at run time (blendOwned/ownsSlot); a read no force can
//  reach stays a plain read.  A whole-variable or intermediate-aggregate read goes through a
//  <name>__VforceSlotRd shadow, rebuilt as a raw copy plus one guarded write per force, with
//  raw put back where an inner force or release has punched a hole out of an enclosing one.
//  A force naming a whole aggregate is one entry covering its slot range, so generated code
//  scales with the number of force statements, never with data size.
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Force.h"

#include "V3AstUserAllocator.h"
#include "V3EmitCBase.h"
#include "V3Stats.h"
#include "V3UniqueNames.h"

VL_DEFINE_DEBUG_FUNCTIONS;

class ForceState final {
public:
    struct ForceRange VL_NOT_FINAL {
        int m_rangeLsb = 0;  // VlForceVec range: bit index or array element index
        int m_rangeMsb = 0;
        int m_padLsb = 0;  // Bit positions for RHS padding
        int m_padMsb = 0;
    };

    struct ForceInfo final : ForceRange {
        // MEMBERS
        int m_forceId = 0;  // Unique (per signal) variable of this force assignment
        AstVarScope* m_rhsVarVscp = nullptr;  // Scope of the var containing RHSID
        AstNodeExpr* m_rhsExprp = nullptr;  // Expression on RHS of this force assignment
        AstNodeExpr* m_lhsPathp = nullptr;  // Copy of the target path, owned here

        ForceInfo() = default;
        ForceInfo(int rangeLsb, int rangeMsb, int padLsb, int padMsb, int forceId,
                  AstVarScope* rhsVarVscp, AstNodeExpr* rhsExprp, AstNodeExpr* lhsPathp)
            : m_forceId{forceId}
            , m_rhsVarVscp{rhsVarVscp}
            , m_rhsExprp{rhsExprp}
            , m_lhsPathp{lhsPathp} {
            m_rangeLsb = rangeLsb;
            m_rangeMsb = rangeMsb;
            m_padLsb = padLsb;
            m_padMsb = padMsb;
        }
    };

    // Above this many forces reaching one read or release, per-site compiled chains
    // are routed through the variable's shared shadow function instead, so generated
    // code stays linear in force statements plus sites
    static constexpr int FORCE_CHAIN_MAX = 8;

    struct VarForceInfo final {
        AstVarScope* m_forceVecVscp = nullptr;
        AstVarScope* m_forceRdVscp = nullptr;  // __VforceRd: externally forceable merged value
        AstVarScope* m_slotRdVscp = nullptr;  // __VforceSlotRd: code-forced merged value
        AstVarScope* m_forceEnVscp = nullptr;
        AstVarScope* m_forceValVscp = nullptr;
        AstVarScope* m_varVscp = nullptr;
        AstVar* m_varp = nullptr;
        AstScope* m_scopep = nullptr;
        std::unordered_map<AstAssignForce*, ForceInfo> m_forces;
        // Statements identical to an earlier force (same path, range and right-hand
        // side) share its ForceInfo: each execution re-establishes the same ownership
        // and value, so one id, one shadow and one read arm serve them all
        std::unordered_map<AstAssignForce*, AstAssignForce*> m_forceAliases;
        // Shared per-variable shadow rebuild functions, created on first use, so each
        // procedural refresh site is one call however many forces the variable has
        mutable AstCFunc* m_slotRdRefreshFuncp = nullptr;
        mutable AstCFunc* m_forceRdRefreshFuncp = nullptr;
        mutable bool m_forceRdRefreshNeedsVec = false;

        // The variable's whole merged value, whichever shadow holds it: the externally
        // forceable __VforceRd (which also overlays the public enable/value) or the
        // code-force-only __VforceSlotRd.  Null when the variable keeps no whole-value shadow.
        AstVarScope* wholeReadShadowVscp() const {
            return m_slotRdVscp ? m_slotRdVscp : m_forceRdVscp;
        }
    };

    struct ForceHelperVars final {
        AstVar* m_rdVarp = nullptr;
        AstVar* m_enVarp = nullptr;
        AstVar* m_valVarp = nullptr;
    };

    // Slot ordinal of a leaf within its base variable, split into the part known at
    // verilation time and the part a run-time element index contributes.
    struct ForceOrdinal final {
        int m_constOffset = 0;
        AstNodeExpr* m_exprp = nullptr;  // Null when every element index is constant
    };

private:
    using ScopeVarCache = std::unordered_map<const AstVar*, AstVarScope*>;

    // NODE STATE
    //  AstVarRef::user1      -> bool.  Not to replace reference
    //  AstAssignForce::user2 -> bool.  Force is synthetic (externally forceable)
    //  AstVar::user3         -> ForceHelperVars via m_forceHelperVarsByVar
    const VNUser1InUse m_user1InUse;
    const VNUser2InUse m_user2InUse;

public:
    using ForceHelperVarsByVar = AstUser3Allocator<AstVar, ForceHelperVars>;

private:
    ForceHelperVarsByVar& m_forceHelperVarsByVar;
    std::vector<VarForceInfo> m_varInfos;  // Indexed by stable variable ID
    std::unordered_map<AstVarScope*, int> m_varToId;
    std::unordered_set<AstVar*> m_clockedWrites;
    std::unordered_map<AstVar*, std::vector<ForceInfo*>> m_rhsDepToForces;
    std::unordered_map<AstScope*, ScopeVarCache> m_scopeVarCaches;
    bool m_doingAssign = false;  // If true, we're processing procedural continuous assign
                                 // statements instead of force statements

public:
    ForceState(bool doingAssign, ForceHelperVarsByVar& forceHelperVarsByVar)
        : m_forceHelperVarsByVar{forceHelperVarsByVar}
        , m_doingAssign{doingAssign} {}
    ~ForceState() {
        // The target paths are copies kept for building shadow updates, and are never
        // linked into the tree, so this owns them
        for (VarForceInfo& info : m_varInfos) {
            for (auto& pair : info.m_forces) {
                if (AstNodeExpr* const pathp = pair.second.m_lhsPathp) {
                    VL_DO_DANGLING(pathp->deleteTree(), pathp);
                }
            }
        }
    }
    VL_UNCOPYABLE(ForceState);

    // STATIC METHODS
    static AstConst* makeZeroConst(AstNode* nodep, int width) {
        V3Number zero{nodep, width};
        zero.setAllBits0();
        return new AstConst{nodep->fileline(), zero};
    }

    static AstConst* makeConst32(FileLine* flp, int value) {
        return new AstConst{flp, AstConst::WidthedValue{}, 32, static_cast<uint32_t>(value)};
    }

    static AstConst* makeRangeMaskConst(AstNode* nodep, int width, int lsb, int msb) {
        V3Number mask{nodep, width};
        mask.setAllBits0();
        for (int bit = lsb; bit <= msb; ++bit) mask.setBit(bit, 1);
        return new AstConst{nodep->fileline(), mask};
    }

    // The bitwise force-read blend (en & val) | (~en & orig).  'enp' is consumed twice,
    // once directly and once cloned for the complement; 'valp' and 'origp' are consumed once.
    static AstNodeExpr* makeEnValBlend(FileLine* flp, AstNodeExpr* enp, AstNodeExpr* valp,
                                       AstNodeExpr* origp) {
        return new AstOr{flp, new AstAnd{flp, enp, valp},
                         new AstAnd{flp, new AstNot{flp, enp->cloneTreePure(false)}, origp}};
    }

    static AstNodeExpr* zeroPadToBaseWidth(AstNodeExpr* exprp, int baseWidth, int padLsb,
                                           int padMsb) {
        if (baseWidth <= 0) return exprp;
        const int lowPad = padLsb;
        const int highPad = baseWidth - (padMsb + 1);
        if (lowPad > 0) {
            exprp = new AstConcat{exprp->fileline(), exprp, makeZeroConst(exprp, lowPad)};
        }
        if (highPad > 0) {
            exprp = new AstConcat{exprp->fileline(), makeZeroConst(exprp, highPad), exprp};
        }
        return exprp;
    }

    static bool isUnpackedArrayDType(const AstNodeDType* dtypep) {
        return VN_IS(dtypep->skipRefp(), UnpackArrayDType);
    }

    // Force tracking gives every separately forceable leaf of a variable its own slot in that
    // variable's VlForceVec.  An aggregate is laid out depth first, so a leaf's slot is the sum
    // of a fixed offset per member crossed and the element index times the element's own slot
    // count.  That keeps 's.arr[2]', 's.scalar' and 'sa[0].arr[2]' in one numbering that cannot
    // collide, and lets a run-time element index be computed with the same arithmetic.
    static int forceSlots(const AstNodeDType* dtypep) {
        // Every caller operates on a variable already screened by forceSlotsOverflow, so the
        // count fits in int; share the recursion with the 64-bit overflow-checking version
        return static_cast<int>(forceSlots64(dtypep));
    }

    // The leaf count computed in 64 bits, so a variable whose leaves would overflow the
    // int slot arithmetic can be rejected rather than silently miscompiled.  Saturates at
    // one past INT_MAX; only a multi-gigabyte array can reach that.
    static int64_t forceSlots64(const AstNodeDType* dtypep) {
        constexpr int64_t k_cap = static_cast<int64_t>(std::numeric_limits<int>::max()) + 1;
        dtypep = dtypep->skipRefp();
        if (const AstUnpackArrayDType* const arrayp = VN_CAST(dtypep, UnpackArrayDType)) {
            const int64_t sub = forceSlots64(arrayp->subDTypep());
            const int64_t product = static_cast<int64_t>(arrayp->declRange().elements()) * sub;
            return product > k_cap ? k_cap : product;
        }
        if (const AstNodeUOrStructDType* const structp = VN_CAST(dtypep, NodeUOrStructDType)) {
            if (structp->packed()) return 1;
            int64_t slots = 0;
            for (AstMemberDType* memberp = structp->membersp(); memberp;
                 memberp = VN_AS(memberp->nextp(), MemberDType)) {
                slots += forceSlots64(memberp->dtypep());
                if (slots > k_cap) return k_cap;
            }
            return slots ? slots : 1;
        }
        return 1;
    }

    // True when the variable has more force slots than the int slot arithmetic can hold
    static bool forceSlotsOverflow(const AstNodeDType* dtypep) {
        return forceSlots64(dtypep) > std::numeric_limits<int>::max();
    }

    // Why a force statement cannot be registered, or nullptr if it can.  Discovery warns
    // on it and Convert drops the statement on it, so both consult this one predicate and
    // cannot fall out of step.
    static const char* forceUnsupportedReason(AstAssignForce* nodep) {
        AstNodeExpr* const lhsp = nodep->lhsp();
        if (forceSlotsOverflow(getOneVarRef(lhsp)->varp()->dtypep())) {
            return "Force of a variable with 2^31 or more elements";
        }
        // An aggregate target's value lives in a shadow typed as the target, whose leaf reads
        // index members/elements out of it, so a differently-typed right-hand side cannot fill
        // it.  A one-leaf unpacked struct or one-element unpacked array is such a target too,
        // though its slot count is one, so the test is the typed-shadow shape, not the count
        if (targetHasTypedShadow(lhsp)
            && !lhsp->dtypep()->skipRefp()->similarDType(nodep->rhsp()->dtypep()->skipRefp())) {
            return "Force of an unpacked aggregate from an expression of a different type";
        }
        return nullptr;
    }

    // A force target whose value is held in a shadow typed as the target itself, an unpacked
    // struct/union or an unpacked array of any leaf count, rather than as a flat bit vector.
    // Its leaf reads index members/elements out of that shadow.  Mirrors usesForceSlots, which
    // classifies whole variables, applied to a possibly-narrower force target.
    static bool targetHasTypedShadow(AstNodeExpr* lhsp) {
        return forceSlots(lhsp->dtypep()) > 1 || !isBitwiseDType(lhsp)
               || isUnpackedArrayDType(lhsp->dtypep());
    }

    // True when this variable's VlForceVec is indexed by leaf slot rather than by bit
    static bool usesForceSlots(AstVar* varp) {
        // An unpacked array is a VlUnpacked in C++ whatever its length, so a one-element
        // array must take the slot path too: its basicp() delegates through to the element
        // and would otherwise route it to the scalar bit path, emitting uncompilable code
        return forceSlots(varp->dtypep()) > 1 || !isBitwiseDType(varp)
               || isUnpackedArrayDType(varp->dtypep());
    }

    static int memberSlotOffset(const AstNodeDType* fromDtypep, const string& name) {
        const AstNodeUOrStructDType* const structp
            = VN_CAST(fromDtypep->skipRefp(), NodeUOrStructDType);
        UASSERT_OBJ(structp, fromDtypep, "Member select is not on a struct or union");
        int offset = 0;
        for (AstMemberDType* memberp = structp->membersp(); memberp;
             memberp = VN_AS(memberp->nextp(), MemberDType)) {
            if (memberp->name() == name) return offset;
            offset += forceSlots(memberp->dtypep());
        }
        structp->v3fatalSrc("Member '" << name << "' not found in struct or union");
        return 0;
    }

    static bool isBitwiseDType(AstNode* nodep) {
        const AstBasicDType* const basicp = nodep->dtypep()->skipRefp()->basicp();
        return basicp && !basicp->isDouble() && !basicp->isString() && !basicp->isOpaque();
    }

    static AstNodeExpr* castToNodeDType(AstNodeExpr* exprp, AstNode* dtypeFromp) {
        const AstNodeDType* const dtypep = dtypeFromp->dtypep()->skipRefp();
        const AstBasicDType* const basicp = dtypep->basicp();
        if (!basicp || basicp->isDouble() || basicp->isString() || basicp->isOpaque()
            || dtypep->isWide() || isUnpackedArrayDType(dtypep)) {
            return exprp;
        }
        return new AstCCast{exprp->fileline(), exprp, dtypeFromp};
    }

    static bool isNotReplaceable(const AstVarRef* const nodep) { return nodep->user1(); }
    static void markNonReplaceable(AstVarRef* const nodep) { nodep->user1SetOnce(); }

    // Mark every variable reference in a cloned path as reading (or writing) the raw storage:
    // set its access and keep the force read-replacer from rewriting it.
    static void markRawRead(AstNode* nodep) {
        nodep->foreach([](AstVarRef* const refp) {
            refp->access(VAccess::READ);
            markNonReplaceable(refp);
        });
    }

    static std::vector<ForceInfo*> forceInfosInIdOrder(VarForceInfo& info) {
        std::vector<ForceInfo*> forceps;
        forceps.reserve(info.m_forces.size());
        for (auto& it : info.m_forces) forceps.push_back(&it.second);
        std::sort(forceps.begin(), forceps.end(), [](const ForceInfo* ap, const ForceInfo* bp) {
            return ap->m_forceId < bp->m_forceId;
        });
        return forceps;
    }

    static std::vector<const ForceInfo*> forceInfosInIdOrder(const VarForceInfo& info) {
        std::vector<const ForceInfo*> forceps;
        forceps.reserve(info.m_forces.size());
        for (const auto& it : info.m_forces) forceps.push_back(&it.second);
        std::sort(forceps.begin(), forceps.end(), [](const ForceInfo* ap, const ForceInfo* bp) {
            return ap->m_forceId < bp->m_forceId;
        });
        return forceps;
    }

    // True when an enclosing selector reaches this node through its 'from' side, so that
    // selector names a longer path and covers this node.  A node used as an index instead is
    // a read of its own, as in 'mem[mem[0]]', and this is false for it.
    static bool isPathFromOfSelector(const AstNode* nodep) {
        const AstNode* const backp = nodep->backp();
        if (!backp) return false;
        if (const AstSel* const selp = VN_CAST(backp, Sel)) return selp->fromp() == nodep;
        if (const AstArraySel* const selp = VN_CAST(backp, ArraySel))
            return selp->fromp() == nodep;
        if (const AstStructSel* const selp = VN_CAST(backp, StructSel)) {
            return selp->fromp() == nodep;
        }
        return false;
    }

    static AstVarRef* getOneVarRef(AstNodeExpr* forceStmtp) {
        AstNode* const basep = AstArraySel::baseFromp(forceStmtp, true);
        if (AstSampled* sampledp = VN_CAST(basep, Sampled))
            if (AstNodeExpr* exprp = VN_CAST(sampledp->exprp(), NodeExpr))
                return getOneVarRef(exprp);
        AstVarRef* const varRefp = VN_CAST(basep, VarRef);
        UASSERT_OBJ(varRefp, forceStmtp, "Force/release expression has no VarRef at its base");
        return varRefp;
    }

    static AstNodeExpr* buildNestedArraySel(FileLine* flp, AstNodeExpr* fromp,
                                            const std::vector<int>& indicies) {
        AstNodeExpr* curp = fromp;
        for (const int idx : indicies) curp = new AstArraySel{flp, curp, idx};
        return curp;
    }

    template <typename Fn>
    static AstNodeStmt* foreachUnpackedLeaf(const std::vector<AstUnpackArrayDType*>& dims,
                                            Fn buildLeaf) {
        AstNodeStmt* headp = nullptr;
        AstNodeStmt* tailp = nullptr;
        if (dims.empty()) return nullptr;
        int total = 1;
        for (const AstUnpackArrayDType* const d : dims) total *= d->elementsConst();
        if (total <= 0) return nullptr;
        std::vector<int> idx(dims.size(), 0);
        for (int flat = 0; flat < total; ++flat) {
            AstNodeStmt* const stmtp = buildLeaf(idx, flat);
            if (!headp) {
                headp = stmtp;
            } else {
                tailp->addNext(stmtp);
            }
            tailp = stmtp;
            for (int d = static_cast<int>(dims.size()) - 1; d >= 0; --d) {
                if (++idx[d] < dims[d]->elementsConst()) break;
                idx[d] = 0;
            }
        }
        return headp;
    }

    ForceRange getForceRangeInfo(AstNodeExpr* lhsp, AstVar* varp, bool requireConstRangeSelect) {
        ForceRange info;
        info.m_padMsb = isBitwiseDType(varp) ? (varp->width() - 1) : 0;

        if (const AstSel* const outerSelp = VN_CAST(lhsp, Sel)) {
            int totalLsb = 0;
            for (AstNodeExpr* curp = lhsp; const AstSel* const selp = VN_CAST(curp, Sel);
                 curp = selp->fromp()) {
                if (requireConstRangeSelect) {
                    UASSERT_OBJ(VN_IS(selp->lsbp(), Const), lhsp,
                                "Unsupported: force on non-const range select");
                }
                totalLsb += selp->lsbConst();
            }
            info.m_padLsb = totalLsb;
            info.m_padMsb = totalLsb + outerSelp->widthConst() - 1;
        }

        info.m_rangeLsb = info.m_padLsb;
        info.m_rangeMsb = info.m_padMsb;
        if (usesForceSlots(varp)) {
            // An aggregate addresses VlForceVec by leaf slot rather than by bit, so the whole
            // member and element path decides the slot.  A whole-aggregate target covers every
            // slot it contains; those are lowered to per-leaf targets before this point, so what
            // arrives here selects one leaf.
            const ForceOrdinal ordinal = forceOrdinal(lhsp->fileline(), lhsp);
            UASSERT_OBJ(!ordinal.m_exprp, lhsp, "Unsupported: force on non-constant array select");
            info.m_rangeLsb = ordinal.m_constOffset;
            info.m_rangeMsb = info.m_rangeLsb + forceSlots(lhsp->dtypep()) - 1;
        }
        return info;
    }

    AstNodeExpr* addRhsValueReads(const VarForceInfo& varInfo, AstNodeExpr* exprp) const {
        if (!doingAssign()) return exprp;

        const std::vector<const ForceInfo*> forceps = forceInfosInIdOrder(varInfo);
        if (forceps.empty()) return exprp;

        // VlForceVec stores pointers to RHS shadows, so expose those reads to scheduling.
        AstCExpr* const cexprp = new AstCExpr{exprp->fileline(), AstCExpr::Pure{}};
        cexprp->dtypeFrom(exprp);
        cexprp->add("(");
        for (const ForceInfo* const finfop : forceps) {
            UASSERT_OBJ(finfop->m_rhsVarVscp, exprp, "No RHS var for forced variable");
            AstVarRef* const refp
                = new AstVarRef{exprp->fileline(), finfop->m_rhsVarVscp, VAccess::READ};
            markNonReplaceable(refp);
            cexprp->add("(void)(");
            cexprp->add(refp);
            cexprp->add("), ");
        }
        cexprp->add(exprp);
        cexprp->add(")");
        return cexprp;
    }

    AstNodeExpr* createForceReadCall(const VarForceInfo& varInfo, FileLine* flp, VCMethod method,
                                     AstNodeExpr* originalExprp, AstNode* dtypeFromp,
                                     AstNodeExpr* indexExprp) const {
        UASSERT(varInfo.m_forceVecVscp, "No forceVec for forced variable");

        // Protect only the read this call replaces, which would otherwise be replaced
        // again and recurse.  Everything else in the expression is an ordinary read and
        // must still see its own force, including an index read of the same array as in
        // 'mem[mem[0]]'.
        markNonReplaceable(getOneVarRef(originalExprp));
        AstNodeExpr* const origValp
            = addRhsValueReads(varInfo, castToNodeDType(originalExprp, dtypeFromp));

        AstCMethodHard* const callp = new AstCMethodHard{
            flp, new AstVarRef{flp, varInfo.m_forceVecVscp, VAccess::READ}, method, origValp};
        if (indexExprp) callp->addPinsp(indexExprp);
        callp->dtypeFrom(dtypeFromp);
        return callp;
    }

    AstNodeStmt* createForceRdUpdateStmt(const VarForceInfo& varInfo) const {
        UASSERT(varInfo.m_forceRdVscp, "No forceRd for forced variable");
        UASSERT(varInfo.m_varVscp, "No base var scope for forced variable");
        FileLine* const flp = varInfo.m_varVscp->fileline();
        AstVar* const varp = varInfo.m_varVscp->varp();
        if (VN_IS(varp->dtypeSkipRefp(), UnpackArrayDType)) {
            return createForceRdUpdateStmtUnpacked(varInfo);
        }
        if (usesForceSlots(varp)) {
            // An externally forceable aggregate enables its whole value at once, while code
            // may force single leaves.  Merge each leaf's slot first, then let the external
            // force override the whole value.
            AstNodeStmt* const stmtsp = createSlotRdUpdateStmt(varInfo, varInfo.m_forceRdVscp);
            AstNodeExpr* const rdReadp = new AstVarRef{flp, varInfo.m_forceRdVscp, VAccess::READ};
            stmtsp->addNext(new AstAssign{
                flp, new AstVarRef{flp, varInfo.m_forceRdVscp, VAccess::WRITE},
                new AstCond{flp, new AstVarRef{flp, varInfo.m_forceEnVscp, VAccess::READ},
                            new AstVarRef{flp, varInfo.m_forceValVscp, VAccess::READ}, rdReadp}});
            return stmtsp;
        }
        AstNodeExpr* readExprp = nullptr;
        AstVarRef* const baseRefp = new AstVarRef{flp, varInfo.m_varVscp, VAccess::READ};
        markNonReplaceable(baseRefp);
        AstNodeExpr* const enRefp = new AstVarRef{flp, varInfo.m_forceEnVscp, VAccess::READ};
        AstNodeExpr* const valRefp = new AstVarRef{flp, varInfo.m_forceValVscp, VAccess::READ};
        if (isBitwiseDType(varp)) {
            readExprp = makeEnValBlend(flp, enRefp, valRefp, baseRefp);
        } else {
            readExprp = new AstCond{flp, enRefp, valRefp, baseRefp};
        }

        return new AstAssign{flp, new AstVarRef{flp, varInfo.m_forceRdVscp, VAccess::WRITE},
                             readExprp};
    }

    AstNodeStmt* createForceRdUpdateStmtUnpacked(const VarForceInfo& varInfo) const {
        FileLine* const flp = varInfo.m_varVscp->fileline();
        AstVar* const varp = varInfo.m_varVscp->varp();
        AstUnpackArrayDType* const arrDtypep = VN_AS(varp->dtypep()->skipRefp(), UnpackArrayDType);
        const std::vector<AstUnpackArrayDType*> dims = arrDtypep->unpackDimensions();
        // Merge the code forces this variable's slots carry into the read shadow first, so a
        // procedural 'force' of an element is visible through the externally forceable read;
        // then overlay the per-element external enable and value on top of that merged value.
        AstNodeStmt* const stmtsp = createSlotRdUpdateStmt(varInfo, varInfo.m_forceRdVscp);
        stmtsp->addNext(foreachUnpackedLeaf(
            dims, [&](const std::vector<int>& idx, int /*flat*/) -> AstNodeStmt* {
                AstNodeExpr* const baseSelp = buildNestedArraySel(
                    flp, new AstVarRef{flp, varInfo.m_forceRdVscp, VAccess::READ}, idx);
                AstNodeExpr* const enSelp = buildNestedArraySel(
                    flp, new AstVarRef{flp, varInfo.m_forceEnVscp, VAccess::READ}, idx);
                AstNodeExpr* const valSelp = buildNestedArraySel(
                    flp, new AstVarRef{flp, varInfo.m_forceValVscp, VAccess::READ}, idx);
                AstNodeExpr* const readExprp = makeEnValBlend(flp, enSelp, valSelp, baseSelp);
                AstNodeExpr* const rdLhsSelp = buildNestedArraySel(
                    flp, new AstVarRef{flp, varInfo.m_forceRdVscp, VAccess::WRITE}, idx);
                return new AstAssign{flp, rdLhsSelp, readExprp};
            }));
        return stmtsp;
    }

    VarForceInfo& getOrCreateVarInfo(AstVarScope* vscp) {
        const auto it = m_varToId.find(vscp);
        if (it != m_varToId.end()) return m_varInfos[it->second];

        m_varToId.emplace(vscp, m_varInfos.size());
        m_varInfos.emplace_back();
        VarForceInfo& info = m_varInfos.back();
        info.m_varVscp = vscp;
        info.m_varp = vscp->varp();
        info.m_scopep = vscp->scopep();

        AstVar* const varp = info.m_varp;
        if (!varp->isForceable()) return info;

        FileLine* const flp = varp->fileline();
        ForceHelperVars& helperVars = m_forceHelperVarsByVar(varp);
        const bool helperVarsBuilt = helperVars.m_rdVarp != nullptr;
        UASSERT_OBJ(helperVarsBuilt == (helperVars.m_enVarp != nullptr)
                        && helperVarsBuilt == (helperVars.m_valVarp != nullptr),
                    varp, "Incomplete force helper set");
        if (!helperVarsBuilt) {
            const bool unpacked = isUnpackedArrayDType(varp->dtypep());
            const VVarType enValType = unpacked ? VVarType::WIRE : VVarType::VAR;
            AstNodeDType* const enDtypep
                = unpacked || isBitwiseDType(varp) ? varp->dtypep() : varp->findBitDType();
            helperVars.m_rdVarp
                = new AstVar{flp, VVarType::WIRE, varp->name() + "__VforceRd", varp->dtypep()};
            helperVars.m_rdVarp->sigPublic(true);
            helperVars.m_enVarp
                = new AstVar{flp, enValType, varp->name() + "__VforceEn", enDtypep};
            helperVars.m_enVarp->sigUserRWPublic(true);
            helperVars.m_valVarp
                = new AstVar{flp, enValType, varp->name() + "__VforceVal", varp->dtypep()};
            helperVars.m_valVarp->sigUserRWPublic(true);
            varp->addNextHere(helperVars.m_rdVarp);
            varp->addNextHere(helperVars.m_enVarp);
            varp->addNextHere(helperVars.m_valVarp);
        }

        info.m_forceRdVscp = findScopeVar(info.m_scopep, helperVars.m_rdVarp);
        info.m_forceEnVscp = findScopeVar(info.m_scopep, helperVars.m_enVarp);
        info.m_forceValVscp = findScopeVar(info.m_scopep, helperVars.m_valVarp);
        if (info.m_forceRdVscp || info.m_forceEnVscp || info.m_forceValVscp) {
            UASSERT_OBJ(info.m_forceRdVscp && info.m_forceEnVscp && info.m_forceValVscp, vscp,
                        "Incomplete pre-existing force helper set");
        } else {
            info.m_forceRdVscp = new AstVarScope{flp, info.m_scopep, helperVars.m_rdVarp};
            info.m_forceEnVscp = new AstVarScope{flp, info.m_scopep, helperVars.m_enVarp};
            info.m_forceValVscp = new AstVarScope{flp, info.m_scopep, helperVars.m_valVarp};
            info.m_scopep->addVarsp(info.m_forceRdVscp);
            info.m_scopep->addVarsp(info.m_forceEnVscp);
            info.m_scopep->addVarsp(info.m_forceValVscp);
        }
        return info;
    }

    void markClockedWrite(AstVar* varp) { m_clockedWrites.insert(varp); }
    bool hasClockedWrite(AstVar* varp) const { return m_clockedWrites.count(varp); }

    bool doingAssign() const { return m_doingAssign; }

    const VarForceInfo* getVarInfo(AstVarScope* vscp) const {
        const auto it = m_varToId.find(vscp);
        return it != m_varToId.end() ? &m_varInfos[it->second] : nullptr;
    }

    AstVarScope* findScopeVar(AstScope* scopep, const AstVar* varp) {
        ScopeVarCache& cache = m_scopeVarCaches[scopep];
        if (cache.empty()) {
            for (AstVarScope* vscp = scopep->varsp(); vscp;
                 vscp = VN_AS(vscp->nextp(), VarScope)) {
                cache.emplace(vscp->varp(), vscp);
            }
        }
        const auto it = cache.find(varp);
        return it != cache.end() ? it->second : nullptr;
    }
    void addForceAssignment(AstVar* varp, AstVarScope* vscp, AstNodeExpr* rhsExprp,
                            AstAssignForce* forceStmtp, int rangeLsb, int rangeMsb, int padLsb,
                            int padMsb, AstNodeExpr* lhsPathp) {
        v3Global.setUsesForce();
        varp->setForcedByCode();

        VarForceInfo& info = getOrCreateVarInfo(vscp);
        for (auto& it : info.m_forces) {
            const ForceInfo& other = it.second;
            if (other.m_rangeLsb != rangeLsb || other.m_rangeMsb != rangeMsb) continue;
            if (other.m_padLsb != padLsb || other.m_padMsb != padMsb) continue;
            if (!other.m_rhsExprp || !other.m_rhsExprp->sameTree(rhsExprp)) continue;
            if (!!other.m_lhsPathp != !!lhsPathp) continue;
            if (lhsPathp) {
                lhsPathp->foreach([](AstVarRef* const refp) { refp->access(VAccess::READ); });
                if (!other.m_lhsPathp->sameTree(lhsPathp)) continue;
            }
            info.m_forceAliases.emplace(forceStmtp, it.first);
            VL_DO_DANGLING(rhsExprp->deleteTree(), rhsExprp);
            if (lhsPathp) VL_DO_DANGLING(lhsPathp->deleteTree(), lhsPathp);
            UINFO(3, "Aliased identical force statement for " << varp->name() << "\n");
            return;
        }
        const int forceId = info.m_forces.size();
        FileLine* const flp = varp->fileline();
        AstScope* const scopep = vscp->scopep();
        // Allocate one force vector per variable, no matter how many individual force
        // statements later target slices/elements of that variable.
        if (!info.m_forceVecVscp) {
            AstCDType* const forceVecDtypep = new AstCDType{flp, "VlForceVec"};
            v3Global.rootp()->typeTablep()->addTypesp(forceVecDtypep);

            AstVar* const forceVecVarp
                = new AstVar{flp, VVarType::MEMBER,
                             varp->name() + (m_doingAssign ? "_VassignVec" : "__VforceVec") + "__"
                                 + scopep->nameDotless(),
                             forceVecDtypep};
            forceVecVarp->funcLocal(false);
            forceVecVarp->isInternal(true);
            varp->addNextHere(forceVecVarp);
            info.m_forceVecVscp = new AstVarScope{flp, scopep, forceVecVarp};
            scopep->addVarsp(info.m_forceVecVscp);
        }

        // The stored path is only ever used to build reads and rebased writes, and it came
        // from a force left-hand side, so drop the write access its references carry
        if (lhsPathp) {
            lhsPathp->foreach([](AstVarRef* const refp) { refp->access(VAccess::READ); });
        }
        auto pair
            = info.m_forces.emplace(forceStmtp, ForceInfo{rangeLsb, rangeMsb, padLsb, padMsb,
                                                          forceId, nullptr, rhsExprp, lhsPathp});
        ForceInfo& finfo = pair.first->second;
        if (doingAssign()) {
            std::vector<AstVar*> depVarps;
            finfo.m_rhsExprp->foreach([&](AstVarRef* const refp) {
                if (!refp->access().isReadOnly()) return;
                AstVar* const depVarp = refp->varp();
                if (depVarp
                    && std::find(depVarps.begin(), depVarps.end(), depVarp) == depVarps.end()) {
                    depVarps.push_back(depVarp);
                }
            });
            for (AstVar* const depVarp : depVarps) m_rhsDepToForces[depVarp].push_back(&finfo);
        }

        UINFO(3, "Added force ID " << forceId << " for " << varp->name() << " [" << rangeMsb << ":"
                                   << rangeLsb << "]\n");
    }

    static void collectArraySels(AstNodeExpr* exprp, std::vector<AstArraySel*>& out) {
        if (auto* const selp = VN_CAST(exprp, ArraySel)) {
            collectArraySels(selp->fromp(), out);
            out.push_back(selp);
        } else if (const auto* const memberp = VN_CAST(exprp, StructSel)) {
            collectArraySels(memberp->fromp(), out);
        }
    }

    static std::vector<AstArraySel*> arraySelsOf(AstNodeExpr* exprp) {
        std::vector<AstArraySel*> out;
        collectArraySels(exprp, out);
        return out;
    }

    struct SlotRange final {
        int m_lo = 0;
        int m_hi = 0;
    };

    // Strip any trailing bit or part selects to reach the leaf they address
    static AstNodeExpr* stripToLeaf(AstNodeExpr* nodep) {
        while (AstSel* const selp = VN_CAST(nodep, Sel)) nodep = selp->fromp();
        return nodep;
    }

    // Everything the member/element route of a force or read target means, computed in one
    // descent so the facets can never disagree.  A trailing bit or part select contributes
    // nothing here (it stays inside one leaf); each aggregate selector adds its slot offset,
    // and a run-time element index is interpreted three ways at once: it widens the static
    // slot range to the whole array (m_range), leaves the constant ordinal offset alone, and,
    // when a fileline is supplied, builds the run-time slot expression (m_ordinal.m_exprp).
    struct ForcePath final {
        AstNodeExpr* m_leafp = nullptr;  // Path with trailing bit/part selects stripped
        int m_depth = 0;  // Count of member and element selectors
        SlotRange m_range;  // Static slot range, run-time index widened, leaf included
        ForceOrdinal m_ordinal;  // Constant slot offset plus optional run-time index expr
    };

    static void analyzePathRecurse(AstNodeExpr* nodep, FileLine* flp, ForcePath& out) {
        if (const AstSel* const selp = VN_CAST(nodep, Sel)) {
            analyzePathRecurse(selp->fromp(), flp, out);  // bit/part select: no slot effect
            return;
        }
        if (AstArraySel* const selp = VN_CAST(nodep, ArraySel)) {
            analyzePathRecurse(selp->fromp(), flp, out);
            ++out.m_depth;
            // The element's own slot count is this dimension's stride, so nested dimensions
            // fall out of the recursion without needing the dimension sizes separately
            const int stride = forceSlots(selp->dtypep());
            if (const AstConst* const constp = VN_CAST(selp->bitp(), Const)) {
                const int off = static_cast<int>(constp->toSInt()) * stride;
                out.m_range.m_lo += off;
                out.m_range.m_hi += off;
                out.m_ordinal.m_constOffset += off;
                return;
            }
            // A read may select the element at run time.  Only a force target has to name a
            // constant element; 'array[i]' with a variable 'i' is an ordinary read, so its
            // static range widens to the whole array and its ordinal is a run-time expression.
            const AstUnpackArrayDType* const arrayp
                = VN_AS(selp->fromp()->dtypep()->skipRefp(), UnpackArrayDType);
            out.m_range.m_hi += (arrayp->declRange().elements() - 1) * stride;
            if (flp) {
                AstNodeExpr* termp = selp->bitp()->cloneTreePure(false);
                // V3Width sizes an array index to at most 32 bits, so widening is all that is
                // needed to keep the arithmetic below width matched.
                if (termp->width() < 32) termp = new AstExtend{flp, termp, 32};
                if (stride != 1) termp = new AstMul{flp, termp, makeConst32(flp, stride)};
                out.m_ordinal.m_exprp = out.m_ordinal.m_exprp
                                            ? new AstAdd{flp, out.m_ordinal.m_exprp, termp}
                                            : termp;
            }
            return;
        }
        if (const AstStructSel* const selp = VN_CAST(nodep, StructSel)) {
            analyzePathRecurse(selp->fromp(), flp, out);
            ++out.m_depth;
            const int off = memberSlotOffset(selp->fromp()->dtypep(), selp->name());
            out.m_range.m_lo += off;
            out.m_range.m_hi += off;
            out.m_ordinal.m_constOffset += off;
            return;
        }
        // An AstVarRef, or anything else, is the base the route is measured from
    }

    // Analyze a target's member/element route.  Pass a fileline only when the run-time slot
    // ordinal expression is needed; without one the static facets are still computed.
    static ForcePath analyzePath(AstNodeExpr* nodep, FileLine* flp = nullptr) {
        ForcePath out;
        out.m_leafp = stripToLeaf(nodep);
        analyzePathRecurse(nodep, flp, out);
        out.m_range.m_hi += forceSlots(out.m_leafp->dtypep()) - 1;
        return out;
    }

    // Slot range a path can address.  A constant path addresses exactly its subtree; a
    // run-time element index widens to every slot its array can reach.
    static SlotRange staticSlotRange(AstNodeExpr* nodep) { return analyzePath(nodep).m_range; }

    // Number of member and element selections above the base variable reference
    static int pathDepth(AstNodeExpr* nodep) { return analyzePath(nodep).m_depth; }

    // Build a copy of 'pathp' with its deepest 'stripDepth' selectors replaced by 'basep',
    // so a leaf path can be read out of a force's typed shadow, or written into the
    // whole-value shadow of its variable.  'pathp' is only read; 'basep' is consumed.
    static AstNodeExpr* rebaseSuffixOnto(AstNodeExpr* pathp, int stripDepth, AstNodeExpr* basep) {
        if (pathDepth(pathp) == stripDepth) return basep;
        FileLine* const flp = pathp->fileline();
        if (AstArraySel* const selp = VN_CAST(pathp, ArraySel)) {
            return new AstArraySel{flp, rebaseSuffixOnto(selp->fromp(), stripDepth, basep),
                                   selp->bitp()->cloneTreePure(false)};
        }
        if (const AstStructSel* const selp = VN_CAST(pathp, StructSel)) {
            AstStructSel* const newp = new AstStructSel{
                flp, rebaseSuffixOnto(selp->fromp(), stripDepth, basep), selp->name()};
            newp->dtypep(selp->dtypep());
            return newp;
        }
        pathp->v3fatalSrc("Unsupported selector in force path rebase");
        return nullptr;
    }

    // The force target path with any trailing bit or part selects stripped
    static AstNodeExpr* forceLeafPath(const ForceInfo* finfop) {
        return stripToLeaf(finfop->m_lhsPathp);
    }

    static bool isBitSelForce(const ForceInfo* finfop) { return VN_IS(finfop->m_lhsPathp, Sel); }

    // The leaf's structural identity within its variable: member selections by name,
    // element selections position-blind.  Two paths with different signatures can never
    // address the same slot, whatever their indices.  Callers pass a leaf reached through
    // stripToLeaf, so no trailing bit or part select survives to reach here.
    static string pathSignature(AstNodeExpr* nodep) {
        if (const AstArraySel* const selp = VN_CAST(nodep, ArraySel)) {
            return pathSignature(selp->fromp()) + "[]";
        }
        if (const AstStructSel* const selp = VN_CAST(nodep, StructSel)) {
            return pathSignature(selp->fromp()) + "." + selp->name();
        }
        return "";
    }

    // True when 'outerSig' is a proper prefix of 'innerSig' ending at a selector boundary, so
    // the outer path names an aggregate that structurally contains the inner leaf (e.g. "[]"
    // encloses "[].a", "" encloses "[].a").  Signatures are position-blind, so this holds for a
    // run-time element index too, where the static slot range cannot prove containment.
    static bool signatureEncloses(const string& outerSig, const string& innerSig) {
        if (outerSig.size() >= innerSig.size()) return false;
        if (innerSig.compare(0, outerSig.size(), outerSig) != 0) return false;
        const char next = innerSig[outerSig.size()];
        return next == '[' || next == '.';
    }

    // A force encloses 'leafp' when it is not a bit/part-select force and its target path is a
    // prefix of the leaf's.  Constant indices prove this from slot-range containment; a run-time
    // element index widens the leaf's static range past containment, so fall back to the
    // structural signature prefix.  Either way the run-time ownership guard, keyed on the leaf's
    // own slot ordinal, selects the element the force actually owns.
    static bool forceEnclosesLeaf(const ForceInfo* finfop, AstNodeExpr* leafp,
                                  const SlotRange& leafRange) {
        if (isBitSelForce(finfop)) return false;
        if (finfop->m_rangeLsb <= leafRange.m_lo && leafRange.m_hi <= finfop->m_rangeMsb) {
            return true;
        }
        return signatureEncloses(pathSignature(forceLeafPath(finfop)), pathSignature(leafp));
    }

    // Overlapping forces, widest slot range first.  Path-derived ranges on one variable are
    // always nested or disjoint, so this containment order is what makes an outer force's
    // whole-path write correct: any inner force that currently owns part of that range
    // writes after it.
    std::vector<const ForceInfo*> overlappingForces(const VarForceInfo& varInfo,
                                                    const SlotRange range) const {
        std::vector<const ForceInfo*> out;
        for (const ForceInfo* const finfop : forceInfosInIdOrder(varInfo)) {
            if (finfop->m_rangeMsb < range.m_lo || finfop->m_rangeLsb > range.m_hi) continue;
            out.push_back(finfop);
        }
        std::stable_sort(out.begin(), out.end(), [](const ForceInfo* ap, const ForceInfo* bp) {
            return (ap->m_rangeMsb - ap->m_rangeLsb) > (bp->m_rangeMsb - bp->m_rangeLsb);
        });
        return out;
    }

    static ForceOrdinal forceOrdinal(FileLine* flp, AstNodeExpr* nodep) {
        return analyzePath(nodep, flp).m_ordinal;
    }

    static AstNodeExpr* buildForceOrdinalExpr(FileLine* flp, AstNodeExpr* nodep) {
        const ForceOrdinal ordinal = forceOrdinal(flp, nodep);
        if (!ordinal.m_exprp) return makeConst32(flp, ordinal.m_constOffset);
        if (!ordinal.m_constOffset) return ordinal.m_exprp;
        return new AstAdd{flp, ordinal.m_exprp, makeConst32(flp, ordinal.m_constOffset)};
    }

    static AstNodeExpr* buildRhsDataExpr(FileLine* flp, const ForceInfo& finfo) {
        UASSERT(finfo.m_rhsVarVscp, "RHS var scope not assigned");
        return new AstVarRef{flp, finfo.m_rhsVarVscp, VAccess::READ};
    }

    void finalizeRhsVars() {
        for (VarForceInfo& info : m_varInfos) {
            if (info.m_forces.empty()) continue;
            UASSERT_OBJ(info.m_scopep, info.m_varp, "Missing scope for force RHS vars");
            const std::vector<ForceInfo*> forceps = forceInfosInIdOrder(info);
            for (ForceInfo* const finfop : forceps) makeRhsCaptureBlock(info, *finfop);
            if (usesForceSlots(info.m_varp) && !info.m_forceRdVscp) makeSlotRdShadow(info);
            if (info.m_forceRdVscp) makeForceRdBlocks(info, forceps);
        }
    }

    // One force's captured value: a public shadow variable holding it, kept current by a
    // combinational block that re-evaluates the right-hand side.
    void makeRhsCaptureBlock(VarForceInfo& info, ForceInfo& finfo) {
        AstVar* const varp = info.m_varp;
        AstScope* const scopep = info.m_scopep;
        FileLine* const flp = varp->fileline();
        UASSERT_OBJ(finfo.m_rhsExprp, varp, "Missing RHS expression for ForceInfo");

        AstVar* const rhsVarp
            = new AstVar{flp, VVarType::VAR,
                         varp->name() + (doingAssign() ? "_VassignRHS" : "__VforceRHS")
                             + std::to_string(finfo.m_forceId) + "__" + scopep->nameDotless(),
                         finfo.m_rhsExprp->dtypep()};
        rhsVarp->noSubst(true);
        rhsVarp->sigPublic(true);
        rhsVarp->setForcedByCode();
        varp->addNextHere(rhsVarp);
        finfo.m_rhsVarVscp = new AstVarScope{flp, scopep, rhsVarp};
        scopep->addVarsp(finfo.m_rhsVarVscp);

        // The re-capture tracks later changes of the right-hand side.  A read that reaches
        // back into the force's own slots stays raw: substituting it would make this block
        // read its own force's shadow back, a combinational cycle.  A read of a disjoint
        // sibling leaf of the same variable is not such a cycle, so on a slot-tracked
        // variable it keeps normal read semantics and sees that sibling's own force.  A
        // bitwise variable has no per-leaf slots to compare, so every self-reference stays
        // raw.  The capture at the force statement itself always reads fully substituted.
        finfo.m_rhsExprp->foreach([&](AstVarRef* const refp) {
            if (refp->varp() != varp) return;
            if (usesForceSlots(varp)) {
                AstNodeExpr* pathp = refp;
                while (isPathFromOfSelector(pathp)) pathp = VN_AS(pathp->backp(), NodeExpr);
                const SlotRange r = staticSlotRange(pathp);
                if (r.m_hi < finfo.m_rangeLsb || r.m_lo > finfo.m_rangeMsb) return;
            }
            markNonReplaceable(refp);
        });
        AstAssign* const rhsAssignp = new AstAssign{
            flp, new AstVarRef{flp, finfo.m_rhsVarVscp, VAccess::WRITE}, finfo.m_rhsExprp};

        if (!info.m_forceRdVscp) {
            // touch() is a runtime no-op that creates an ordering edge from this capture to
            // the force vector, so later scheduling keeps the update path connected.  A
            // forceable signal already has that edge through its __VforceRd update.
            AstCMethodHard* const touchCallp
                = new AstCMethodHard{flp, new AstVarRef{flp, info.m_forceVecVscp, VAccess::WRITE},
                                     VCMethod::FORCE_TOUCH};
            touchCallp->dtypeSetVoid();
            rhsAssignp->addNextHere(touchCallp->makeStmt());
        }
        scopep->addBlocksp(newComboActive(
            flp, "force-rhs-update", new AstAlways{flp, VAlwaysKwd::ALWAYS, nullptr, rhsAssignp}));
    }

    // The whole-value shadow of a slot-tracked variable, merging every leaf's force, kept
    // current by a combinational block so a whole-variable read can consult it.
    void makeSlotRdShadow(VarForceInfo& info) {
        AstVar* const varp = info.m_varp;
        AstScope* const scopep = info.m_scopep;
        FileLine* const flp = varp->fileline();
        // The scope is part of the name, as for the force vector and RHS shadows: the
        // variable is shared across instances of its module or interface, so an unqualified
        // name collides between instances (a duplicate class member that trace keeps live).
        AstVar* const slotRdVarp
            = new AstVar{flp, VVarType::WIRE,
                         varp->name() + (doingAssign() ? "_VassignSlotRd" : "__VforceSlotRd")
                             + "__" + scopep->nameDotless(),
                         varp->dtypep()};
        slotRdVarp->noSubst(true);
        varp->addNextHere(slotRdVarp);
        info.m_slotRdVscp = new AstVarScope{flp, scopep, slotRdVarp};
        scopep->addVarsp(info.m_slotRdVscp);
        scopep->addBlocksp(
            newComboActive(flp, "force-slot-rd-update",
                           new AstAlways{flp, VAlwaysKwd::ALWAYS, nullptr,
                                         createSlotRdUpdateStmt(info, info.m_slotRdVscp)}));
    }

    // The externally forceable read shadow: a static block that zeroes the enable and seeds
    // the shadow, and an update block sensitive to the enable, value, raw variable and every
    // RHS shadow.
    void makeForceRdBlocks(VarForceInfo& info, const std::vector<ForceInfo*>& forceps) {
        AstVar* const varp = info.m_varp;
        AstScope* const scopep = info.m_scopep;
        FileLine* const flp = varp->fileline();

        AstActive* const activeInitp = new AstActive{
            flp, "force-init", new AstSenTree{flp, new AstSenItem{flp, AstSenItem::Static{}}}};
        activeInitp->senTreeStorep(activeInitp->sentreep());
        AstNodeStmt* initStmtp = nullptr;
        if (AstUnpackArrayDType* const arrDtypep
            = VN_CAST(varp->dtypeSkipRefp(), UnpackArrayDType)) {
            const std::vector<AstUnpackArrayDType*> dims = arrDtypep->unpackDimensions();
            const int innerWidth = dims.back()->subDTypep()->skipRefp()->width();
            initStmtp = foreachUnpackedLeaf(
                dims, [&](const std::vector<int>& idx, int /*flat*/) -> AstNodeStmt* {
                    AstNodeExpr* const lhsp = buildNestedArraySel(
                        flp, new AstVarRef{flp, info.m_forceEnVscp, VAccess::WRITE}, idx);
                    return new AstAssign{flp, lhsp, makeZeroConst(varp, innerWidth)};
                });
        } else {
            initStmtp = new AstAssign{flp, new AstVarRef{flp, info.m_forceEnVscp, VAccess::WRITE},
                                      makeZeroConst(varp, info.m_forceEnVscp->width())};
        }
        initStmtp->addNext(makeForceRdRefreshStmt(info));
        activeInitp->addStmtsp(new AstInitial{flp, initStmtp});
        scopep->addBlocksp(activeInitp);

        AstSenItem* itemsp = nullptr;
        auto addSenItem = [&](AstVarScope* vscp) {
            if (!vscp) return;
            AstSenItem* const nextp = new AstSenItem{flp, VEdgeType::ET_CHANGED,
                                                     new AstVarRef{flp, vscp, VAccess::READ}};
            if (itemsp) {
                itemsp->addNext(nextp);
            } else {
                itemsp = nextp;
            }
        };
        addSenItem(info.m_forceEnVscp);
        addSenItem(info.m_forceValVscp);
        AstVarRef* const origSenRefp = new AstVarRef{flp, info.m_varVscp, VAccess::READ};
        markNonReplaceable(origSenRefp);
        if (!itemsp) varp->v3fatalSrc("force-rd-update missing force-enable sen item");
        itemsp->addNext(new AstSenItem{flp, VEdgeType::ET_CHANGED, origSenRefp});
        for (ForceInfo* const finfop : forceps) addSenItem(finfop->m_rhsVarVscp);

        AstActive* const activep
            = new AstActive{flp, "force-rd-update", new AstSenTree{flp, itemsp}};
        activep->senTreeStorep(activep->sentreep());
        activep->addStmtsp(
            new AstAlways{flp, VAlwaysKwd::ALWAYS, nullptr, createForceRdUpdateStmt(info)});
        scopep->addBlocksp(activep);
    }

    // A combinational AstActive wrapping 'bodyp', with its sensitivity tree stored
    static AstActive* newComboActive(FileLine* flp, const char* name, AstNode* bodyp) {
        AstActive* const activep = new AstActive{
            flp, name, new AstSenTree{flp, new AstSenItem{flp, AstSenItem::Combo{}}}};
        activep->senTreeStorep(activep->sentreep());
        activep->addStmtsp(bodyp);
        return activep;
    }

    // Build 'rd<path> = forceVec.read(var<path>, slot)' for every leaf of a slot-indexed
    // variable, so that a read of the whole variable sees each leaf's own force.
    // Guard: force 'id' currently owns something in [lsb, msb]
    AstNodeExpr* buildOwnsExpr(const VarForceInfo& varInfo, FileLine* flp, int id, int lsb,
                               int msb) const {
        AstCMethodHard* const callp
            = new AstCMethodHard{flp, new AstVarRef{flp, varInfo.m_forceVecVscp, VAccess::READ},
                                 lsb == msb ? VCMethod::FORCE_OWNS_SLOT : VCMethod::FORCE_OWNS_ANY,
                                 makeConst32(flp, id)};
        callp->addPinsp(makeConst32(flp, lsb));
        if (lsb != msb) callp->addPinsp(makeConst32(flp, msb));
        callp->dtypeSetBit();
        return callp;
    }

    // The value force 'finfop' contributes at 'leafp', typed as the leaf.  For a force of
    // an enclosing aggregate this reads the leaf's own suffix out of the force's typed
    // shadow; for a bit or part select force the narrow shadow is positioned into the leaf.
    AstNodeExpr* buildArmRhsExpr(const ForceInfo* finfop, AstNodeExpr* leafp) const {
        FileLine* const flp = leafp->fileline();
        UASSERT_OBJ(finfop->m_rhsVarVscp, leafp, "No RHS var for forced variable");
        const SlotRange leafRange = staticSlotRange(leafp);
        if (forceEnclosesLeaf(finfop, leafp, leafRange)) {
            // Enclosing (or exact) force: the leaf's suffix within the force's target
            const int stripDepth = pathDepth(forceLeafPath(finfop));
            return rebaseSuffixOnto(leafp, stripDepth,
                                    new AstVarRef{flp, finfop->m_rhsVarVscp, VAccess::READ});
        }
        AstNodeExpr* rhsp = new AstVarRef{flp, finfop->m_rhsVarVscp, VAccess::READ};
        if (isBitSelForce(finfop)) {
            AstNodeExpr* const leafDtypeFromp = forceLeafPath(finfop);
            rhsp = zeroPadToBaseWidth(rhsp, leafDtypeFromp->width(), finfop->m_padLsb,
                                      finfop->m_padMsb);
            rhsp->dtypeFrom(leafDtypeFromp);
        }
        return rhsp;
    }

    // Compile the forced value of a single leaf as a chain over the forces that can reach
    // it.  Slot ownership, which depends on run-time activation order, comes from the
    // force vector; everything typed is compiled here.  With no overlapping force the raw
    // read is returned untouched.
    // The forces that can reach 'leafp': those overlapping its slot range, except
    // non-enclosing ones naming a different leaf within the element, which can never
    // alias it whatever their indices
    std::vector<const ForceInfo*> forcesReachingLeaf(const VarForceInfo& varInfo,
                                                     AstNodeExpr* leafp) const {
        const SlotRange leafRange = staticSlotRange(leafp);
        const string leafSignature = pathSignature(leafp);
        std::vector<const ForceInfo*> arms;
        for (const ForceInfo* const finfop : overlappingForces(varInfo, leafRange)) {
            const bool enclosing = forceEnclosesLeaf(finfop, leafp, leafRange);
            if (!enclosing && pathSignature(forceLeafPath(finfop)) != leafSignature) continue;
            arms.push_back(finfop);
        }
        return arms;
    }

    // A leaf's current forced value routes through the variable's whole-value shadow rather
    // than an inline blend chain when the leaf is itself an aggregate (no single chain can
    // express it), or when more forces reach it than a chain should carry.  Reads and release
    // retention pass the same reaching-force count here, so they cannot pick the chain-vs-
    // shadow boundary differently.
    static bool routesThroughShadow(AstNodeExpr* leafp, size_t reachingForceCount) {
        return forceSlots(leafp->dtypep()) > 1
               || reachingForceCount > static_cast<size_t>(FORCE_CHAIN_MAX);
    }

    AstNodeExpr* buildForcedLeafExpr(const VarForceInfo& varInfo, AstNodeExpr* leafp,
                                     AstNodeExpr* rawExprp) const {
        const std::vector<const ForceInfo*> arms = forcesReachingLeaf(varInfo, leafp);
        if (arms.empty()) return rawExprp;
        FileLine* const flp = leafp->fileline();
        const bool bitwiseLeaf = isBitwiseDType(leafp);
        AstNodeExpr* chainp = rawExprp;
        for (const ForceInfo* const finfop : arms) {
            AstNodeExpr* const slotp = buildForceOrdinalExpr(flp, leafp);
            AstNodeExpr* const armRhsp = buildArmRhsExpr(finfop, leafp);
            if (bitwiseLeaf) {
                AstCMethodHard* const callp = new AstCMethodHard{
                    flp, new AstVarRef{flp, varInfo.m_forceVecVscp, VAccess::READ},
                    VCMethod::FORCE_BLEND_OWNED, chainp};
                callp->addPinsp(armRhsp);
                callp->addPinsp(makeConst32(flp, finfop->m_forceId));
                callp->addPinsp(slotp);
                callp->dtypeFrom(leafp);
                chainp = callp;
            } else {
                AstCMethodHard* const ownsp = new AstCMethodHard{
                    flp, new AstVarRef{flp, varInfo.m_forceVecVscp, VAccess::READ},
                    VCMethod::FORCE_OWNS_SLOT, makeConst32(flp, finfop->m_forceId)};
                ownsp->addPinsp(slotp);
                ownsp->dtypeSetBit();
                AstCond* const condp = new AstCond{flp, ownsp, armRhsp, chainp};
                condp->dtypeFrom(leafp);
                chainp = condp;
            }
        }
        return chainp;
    }

    // Statements producing the merged value of 'regionPathp' (a constant path within the
    // variable) into the same path rebased onto 'dstBasep': copy the raw region, then let
    // each force that can own part of it write its piece, outermost force first, each
    // guarded on current ownership.  Cost is one copy plus one statement per force.
    AstNodeStmt* buildMergedRegionStmts(const VarForceInfo& varInfo, AstNodeExpr* regionPathp,
                                        AstNodeExpr* dstBasep) const {
        FileLine* const flp = regionPathp->fileline();
        const SlotRange region = staticSlotRange(regionPathp);
        const int regionDepth = pathDepth(regionPathp);

        AstNodeExpr* const rawp = regionPathp->cloneTreePure(false);
        markRawRead(rawp);
        AstNodeExpr* const dstWholep
            = rebaseSuffixOnto(regionPathp, regionDepth, dstBasep->cloneTreePure(false));
        AstNodeStmt* const headp = new AstAssign{flp, dstWholep, rawp};
        AstNodeStmt* tailp = headp;

        for (const ForceInfo* const finfop : overlappingForces(varInfo, region)) {
            AstNodeStmt* armp = nullptr;
            // The force encloses the region only when its target path is also a prefix of the
            // region's: on a single-slot variable a leaf force and a whole-variable region
            // share one slot range yet the force path is the deeper of the two, so the leaf
            // must be written inside the region rather than read whole out of its shadow
            if (finfop->m_rangeLsb <= region.m_lo && region.m_hi <= finfop->m_rangeMsb
                && !isBitSelForce(finfop) && pathDepth(forceLeafPath(finfop)) <= regionDepth) {
                // Force encloses the region: its shadow holds the whole region's suffix
                const int stripDepth = pathDepth(forceLeafPath(finfop));
                AstNodeExpr* const srcp
                    = rebaseSuffixOnto(regionPathp, stripDepth,
                                       new AstVarRef{flp, finfop->m_rhsVarVscp, VAccess::READ});
                AstNodeExpr* const dstp
                    = rebaseSuffixOnto(regionPathp, regionDepth, dstBasep->cloneTreePure(false));
                armp = new AstAssign{flp, dstp, srcp};
            } else {
                // Force inside the region: write its leaf within the destination
                AstNodeExpr* const fLeafp = forceLeafPath(finfop);
                AstNodeExpr* const dstp
                    = rebaseSuffixOnto(fLeafp, regionDepth, dstBasep->cloneTreePure(false));
                AstNodeExpr* const armRhsp = buildArmRhsExpr(finfop, fLeafp);
                if (isBitwiseDType(fLeafp) && isBitSelForce(finfop)) {
                    // Blend into the destination's current value: an enclosing force's arm
                    // may already have written this leaf, and those bits must survive
                    AstNodeExpr* const curp
                        = rebaseSuffixOnto(fLeafp, regionDepth, dstBasep->cloneTreePure(false));
                    markRawRead(curp);
                    AstCMethodHard* const blendp = new AstCMethodHard{
                        flp, new AstVarRef{flp, varInfo.m_forceVecVscp, VAccess::READ},
                        VCMethod::FORCE_BLEND_OWNED, curp};
                    blendp->addPinsp(armRhsp);
                    blendp->addPinsp(makeConst32(flp, finfop->m_forceId));
                    blendp->addPinsp(makeConst32(flp, finfop->m_rangeLsb));
                    blendp->dtypeFrom(fLeafp);
                    armp = new AstAssign{flp, dstp, blendp};
                } else {
                    armp = new AstAssign{flp, dstp, armRhsp};
                }
            }
            const int guardLo = std::max(finfop->m_rangeLsb, region.m_lo);
            const int guardHi = std::min(finfop->m_rangeMsb, region.m_hi);
            AstIf* const ifp = new AstIf{
                flp, buildOwnsExpr(varInfo, flp, finfop->m_forceId, guardLo, guardHi), armp};
            tailp->addNextHere(ifp);
            tailp = ifp;
        }
        // Reads and writes of the source variable in here are the raw storage by design
        for (AstNode* stmtp = headp; stmtp; stmtp = stmtp->nextp()) {
            stmtp->foreach([&varInfo](AstVarRef* const refp) {
                if (refp->varScopep() == varInfo.m_varVscp) markNonReplaceable(refp);
            });
        }
        return headp;
    }

    // Keep the whole-value shadow of a slot-tracked variable up to date
    AstNodeStmt* createSlotRdUpdateStmt(const VarForceInfo& info, AstVarScope* targetVscp) const {
        FileLine* const flp = info.m_varVscp->fileline();
        AstVarRef* const regionp = new AstVarRef{flp, info.m_varVscp, VAccess::READ};
        AstVarRef* const dstp = new AstVarRef{flp, targetVscp, VAccess::WRITE};
        AstNodeStmt* const stmtsp = buildMergedRegionStmts(info, regionp, dstp);
        VL_DO_DANGLING(regionp->deleteTree(), regionp);
        VL_DO_DANGLING(dstp->deleteTree(), dstp);
        return stmtsp;
    }

    // Wrap 'bodyp' as one function per variable, so a procedural refresh of the shadow
    // is a single call however many forces the variable has and wherever it is read.
    // The arguments carry the accesses scheduling must know about at each call site:
    // the shadow written, the raw variable read, and the force vector read.  Everything
    // else the body reads feeds the always block that maintains the same shadow, whose
    // visible logic already orders any other process against this call.
    AstCFunc* createRefreshFunc(const VarForceInfo& info, const string& name, AstVarScope* dstVscp,
                                bool needsVec, AstNodeStmt* bodyp) const {
        FileLine* const flp = info.m_varVscp->fileline();
        AstScope* const scopep = info.m_scopep;
        AstCFunc* const funcp = new AstCFunc{flp, name, scopep, ""};
        funcp->isStatic(false);
        funcp->dontCombine(true);
        // An entry point the way V3Task's non-inlined functions are: lifetime analysis
        // treats each call as opaque and analyzes the shared body on its own, rather
        // than editing it under whichever caller it happens to trace it from
        funcp->entryPoint(true);
        funcp->argTypes(EmitCUtil::symClassVar());
        const auto makeArg
            = [&](const string& argName, AstVarScope* forVscp, VDirection::en direction) {
                  AstVar* const argVarp
                      = new AstVar{flp, VVarType::BLOCKTEMP, argName, forVscp->varp()->dtypep()};
                  argVarp->funcLocal(true);
                  argVarp->direction(VDirection{direction});
                  funcp->addArgsp(argVarp);
                  AstVarScope* const argVscp = new AstVarScope{flp, scopep, argVarp};
                  scopep->addVarsp(argVscp);
                  return argVscp;
              };
        AstVarScope* const dstArgVscp = makeArg("dstr", dstVscp, VDirection::REF);
        AstVarScope* const srcArgVscp = makeArg("srcr", info.m_varVscp, VDirection::CONSTREF);
        AstVarScope* const vecArgVscp
            = needsVec ? makeArg("vecr", info.m_forceVecVscp, VDirection::REF) : nullptr;
        for (AstNode* stmtp = bodyp; stmtp; stmtp = stmtp->nextp()) {
            stmtp->foreach([&](AstVarRef* const refp) {
                AstVarScope* argVscp = nullptr;
                if (refp->varScopep() == dstVscp) {
                    argVscp = dstArgVscp;
                } else if (refp->varScopep() == info.m_varVscp) {
                    argVscp = srcArgVscp;
                } else if (vecArgVscp && refp->varScopep() == info.m_forceVecVscp) {
                    argVscp = vecArgVscp;
                }
                if (!argVscp) return;
                refp->varp(argVscp->varp());
                refp->varScopep(argVscp);
            });
        }
        funcp->addStmtsp(bodyp);
        scopep->addBlocksp(funcp);
        return funcp;
    }

    AstNodeStmt* makeRefreshCallStmt(const VarForceInfo& info, AstCFunc* funcp,
                                     AstVarScope* dstVscp, bool needsVec) const {
        UASSERT_OBJ(funcp, info.m_varVscp, "Refresh function not created for variable");
        FileLine* const flp = info.m_varVscp->fileline();
        AstVarRef* const dstp = new AstVarRef{flp, dstVscp, VAccess::WRITE};
        AstVarRef* const srcp = new AstVarRef{flp, info.m_varVscp, VAccess::READ};
        markNonReplaceable(srcp);
        dstp->addNext(srcp);
        if (needsVec) srcp->addNext(new AstVarRef{flp, info.m_forceVecVscp, VAccess::READ});
        AstCCall* const callp = new AstCCall{flp, funcp, dstp};
        callp->argTypes("vlSymsp");
        callp->dtypeSetVoid();
        return callp->makeStmt();
    }

    AstNodeStmt* makeSlotRdRefreshStmt(const VarForceInfo& info) const {
        if (!info.m_slotRdRefreshFuncp) {
            info.m_slotRdRefreshFuncp = createRefreshFunc(
                info, info.m_slotRdVscp->varp()->name() + "Upd_" + info.m_scopep->nameDotless(),
                info.m_slotRdVscp,
                /*needsVec=*/true, createSlotRdUpdateStmt(info, info.m_slotRdVscp));
        }
        return makeRefreshCallStmt(info, info.m_slotRdRefreshFuncp, info.m_slotRdVscp, true);
    }

    AstNodeStmt* makeForceRdRefreshStmt(const VarForceInfo& info) const {
        if (!info.m_forceRdRefreshFuncp) {
            info.m_forceRdRefreshNeedsVec
                = usesForceSlots(info.m_varp)
                  && !VN_IS(info.m_varp->dtypeSkipRefp(), UnpackArrayDType);
            info.m_forceRdRefreshFuncp = createRefreshFunc(
                info,
                (doingAssign() ? "_Vassign" : "__Vforce") + std::string{"RdUpd__"}
                    + info.m_varp->name() + "_" + info.m_scopep->nameDotless(),
                info.m_forceRdVscp, info.m_forceRdRefreshNeedsVec, createForceRdUpdateStmt(info));
        }
        return makeRefreshCallStmt(info, info.m_forceRdRefreshFuncp, info.m_forceRdVscp,
                                   info.m_forceRdRefreshNeedsVec);
    }

    // Refresh whichever whole-value shadow the variable keeps, so a same-timestep read of
    // it is current
    AstNodeStmt* makeWholeRdRefreshStmt(const VarForceInfo& info) const {
        return info.m_slotRdVscp ? makeSlotRdRefreshStmt(info) : makeForceRdRefreshStmt(info);
    }

    AstNode* createRhsUpdatesForWrite(FileLine* flp, AstVar* writtenVarp) const {
        if (!doingAssign()) return nullptr;

        const auto it = m_rhsDepToForces.find(writtenVarp);
        if (it == m_rhsDepToForces.end()) return nullptr;

        AstNode* headp = nullptr;
        AstNode* tailp = nullptr;
        for (const ForceInfo* const finfop : it->second) {
            UASSERT_OBJ(finfop->m_rhsVarVscp, writtenVarp, "No RHS var for forced variable");
            UASSERT_OBJ(finfop->m_rhsExprp, writtenVarp, "Missing RHS expression");
            AstAssign* const updatep
                = new AstAssign{flp, new AstVarRef{flp, finfop->m_rhsVarVscp, VAccess::WRITE},
                                finfop->m_rhsExprp->cloneTreePure(false)};
            if (tailp) {
                tailp->addNextHere(updatep);
            } else {
                headp = updatep;
            }
            tailp = updatep;
        }
        return headp;
    }

    const ForceInfo& getForceInfo(AstAssignForce* forceStmtp) const {
        AstVarScope* const vscp = getOneVarRef(forceStmtp->lhsp())->varScopep();
        const VarForceInfo* const varInfo = getVarInfo(vscp);
        UASSERT(varInfo, "Force info not found for variable");
        const auto aliasIt = varInfo->m_forceAliases.find(forceStmtp);
        if (aliasIt != varInfo->m_forceAliases.end()) forceStmtp = aliasIt->second;
        auto it2 = varInfo->m_forces.find(forceStmtp);
        UASSERT(it2 != varInfo->m_forces.end(), "Force statement not found");
        return it2->second;
    }

    static bool selOverlapsAnyForce(const VarForceInfo& varInfo, int selLsb, int selMsb) {
        for (const auto& pair : varInfo.m_forces) {
            if (pair.second.m_rangeLsb <= selMsb && pair.second.m_rangeMsb >= selLsb) return true;
        }
        return false;
    }

    AstNodeExpr* createForceReadExpression(const VarForceInfo& varInfo,
                                           AstVarRef* originalRefp) const {
        FileLine* const flp = originalRefp->fileline();
        return createForceReadCall(varInfo, flp, VCMethod::FORCE_READ,
                                   originalRefp->cloneTreePure(false), originalRefp->varp(),
                                   nullptr);
    }

    static AstNodeExpr* rebuildSelPath(AstNodeExpr* pathp, AstNodeExpr* baseExprp) {
        if (const AstSel* const selp = VN_CAST(pathp, Sel)) {
            AstNodeExpr* const fromp = rebuildSelPath(selp->fromp(), baseExprp);
            AstSel* const outp
                = new AstSel{selp->fileline(), fromp, selp->lsbConst(), selp->widthConst()};
            outp->dtypeFrom(selp);
            return outp;
        }
        return baseExprp;
    }
};

// Split deassign concat LHS before converting to release internals.
static void splitDeassign(AstDeassign* nodep) {
    AstConcat* const concatp = VN_CAST(nodep->lhsp(), Concat);
    if (!concatp) return;

    FileLine* const flp = nodep->fileline();
    AstDeassign* const newLp = new AstDeassign{flp, concatp->lhsp()->unlinkFrBack()};
    AstDeassign* const newRp = new AstDeassign{flp, concatp->rhsp()->unlinkFrBack()};
    AstNodeExpr* const conp = concatp->unlinkFrBack();
    nodep->replaceWith(newLp);
    newLp->addNextHere(newRp);
    VL_DO_DANGLING(nodep->deleteTree(), nodep);
    VL_DO_DANGLING(conp->deleteTree(), conp);

    splitDeassign(newLp);
    splitDeassign(newRp);
}

//######################################################################
// ForceDiscoveryVisitor - Discover force statements

class ForceDiscoveryVisitor final : public VNVisitorConst {
    ForceState& m_state;
    bool m_inClockedActive = false;

    void buildForceableUnpackedArray(AstVarScope* const nodep,
                                     AstUnpackArrayDType* const arrDtypep) {
        AstVar* const varp = nodep->varp();
        const std::vector<AstUnpackArrayDType*> dims = arrDtypep->unpackDimensions();
        UASSERT_OBJ(!dims.empty(), varp,
                    "buildForceableUnpackedArray called with non-unpacked dtype");
        const AstNodeDType* const leafDtypep = dims.back()->subDTypep()->skipRefp();
        const AstBasicDType* const innerBasicp = leafDtypep->basicp();
        const bool innerBitwise = innerBasicp && !innerBasicp->isDouble()
                                  && !innerBasicp->isString() && !innerBasicp->isOpaque();
        if (!innerBitwise) {
            varp->v3warn(E_UNSUPPORTED,
                         "Unsupported: Forcing unpacked arrays of non-bitwise inner type: "
                             << varp->name());  // (#4735)
            return;
        }

        FileLine* const flp = varp->fileline();
        const int innerWidth = leafDtypep->width();

        ForceState::VarForceInfo& info = m_state.getOrCreateVarInfo(nodep);
        AstVarScope* const enVscp = info.m_forceEnVscp;
        AstVarScope* const valVscp = info.m_forceValVscp;

        AstSenItem* const itemsp = new AstSenItem{flp, VEdgeType::ET_CHANGED,
                                                  new AstVarRef{flp, enVscp, VAccess::READ}};
        AstActive* const activep = new AstActive{flp, "force-update", new AstSenTree{flp, itemsp}};
        activep->senTreeStorep(activep->sentreep());

        AstNodeStmt* const alwaysBodyHeadp = ForceState::foreachUnpackedLeaf(
            dims, [&](const std::vector<int>& idx, int flat) -> AstNodeStmt* {
                AstVarRef* const origRefp = new AstVarRef{flp, nodep, VAccess::READ};
                ForceState::markNonReplaceable(origRefp);
                AstNodeExpr* const origSelp = ForceState::buildNestedArraySel(flp, origRefp, idx);
                AstNodeExpr* const enSelp = ForceState::buildNestedArraySel(
                    flp, new AstVarRef{flp, enVscp, VAccess::READ}, idx);
                AstNodeExpr* const valSelp = ForceState::buildNestedArraySel(
                    flp, new AstVarRef{flp, valVscp, VAccess::READ}, idx);
                AstNodeExpr* const forceExprp
                    = ForceState::makeEnValBlend(flp, enSelp, valSelp, origSelp);
                AstNodeExpr* const lhsSelp = ForceState::buildNestedArraySel(
                    flp, new AstVarRef{flp, nodep, VAccess::WRITE}, idx);

                AstAssignForce* const forceAssignp = new AstAssignForce{flp, lhsSelp, forceExprp};
                forceAssignp->user2(true);

                AstNodeExpr* const rhsClonep = forceExprp->cloneTreePure(false);
                rhsClonep->foreach([varp](AstVarRef* const r) {
                    if (r->varp() == varp) ForceState::markNonReplaceable(r);
                });
                m_state.addForceAssignment(varp, nodep, rhsClonep, forceAssignp,
                                           /*rangeLsb=*/flat, /*rangeMsb=*/flat,
                                           /*padLsb=*/0, /*padMsb=*/innerWidth - 1,
                                           lhsSelp->cloneTreePure(false));
                return forceAssignp;
            });
        activep->addStmtsp(new AstAlways{flp, VAlwaysKwd::ALWAYS, nullptr, alwaysBodyHeadp});
        nodep->scopep()->addBlocksp(activep);
    }

    void visit(AstAssignForce* nodep) override {
        if (nodep->user2()) return;  // External force statements are pre-registered.
        UINFO(2, "Discovering force statement: " << nodep << "\n");

        AstVarRef* const lhsVarRefp = m_state.getOneVarRef(nodep->lhsp());
        AstVar* const forcedVarp = lhsVarRefp->varp();
        UASSERT(forcedVarp, "VarRef missing Varp");

        // A force the slot machinery cannot represent (more leaves than the int slot
        // arithmetic holds, or an aggregate target from a differently-typed right-hand side)
        // is reported here and left for the convert visitor to drop
        if (const char* const reason = ForceState::forceUnsupportedReason(nodep)) {
            nodep->v3warn(E_UNSUPPORTED, "Unsupported: " << reason);
            return;
        }
        // Resolve force bookkeeping range/padding for the LHS shape.
        ForceState::ForceRange rangeInfo
            = m_state.getForceRangeInfo(nodep->lhsp(), forcedVarp, true);

        // Keep narrow rhs, VlForceVec blends unpacked-array bit-select forces at read time
        AstNodeExpr* const rhsExprp = nodep->rhsp()->cloneTreePure(false);

        m_state.addForceAssignment(forcedVarp, lhsVarRefp->varScopep(), rhsExprp, nodep,
                                   rangeInfo.m_rangeLsb, rangeInfo.m_rangeMsb, rangeInfo.m_padLsb,
                                   rangeInfo.m_padMsb, nodep->lhsp()->cloneTreePure(false));
    }

    void visit(AstRelease* nodep) override {
        AstVarRef* const lhsVarRefp = m_state.getOneVarRef(nodep->lhsp());
        if (!ForceState::usesForceSlots(lhsVarRefp->varp())) return;
        if (ForceState::forceSlotsOverflow(lhsVarRefp->varp()->dtypep())) {
            nodep->v3warn(E_UNSUPPORTED,
                          "Unsupported: Release of a variable with 2^31 or more elements");
            return;
        }
    }

    void visit(AstAssign* nodep) override {
        if (m_state.doingAssign() && m_inClockedActive) {
            if (AstVarRef* const lhsp = VN_CAST(nodep->lhsp(), VarRef)) {
                m_state.markClockedWrite(lhsp->varp());
            }
        }
        iterateChildrenConst(nodep);
    }

    void visit(AstActive* nodep) override {
        VL_RESTORER(m_inClockedActive);
        m_inClockedActive = nodep->hasClocked();
        iterateChildrenConst(nodep);
    }

    void visit(AstVarScope* nodep) override {
        if (nodep->varp()->isForceable()) {
            // assignAll() runs after forceAll() and traverses the same netlist with a fresh
            // ForceState. Reuse already-created public helper vars instead of regenerating
            // duplicate __Vforce* members for every forceable signal.
            if (m_state.doingAssign()) {
                m_state.getOrCreateVarInfo(nodep);
                iterateChildrenConst(nodep);
                return;
            }

            if (AstUnpackArrayDType* const arrDtypep
                = VN_CAST(nodep->varp()->dtypeSkipRefp(), UnpackArrayDType)) {
                buildForceableUnpackedArray(nodep, arrDtypep);
                iterateChildrenConst(nodep);
                return;
            }

            const AstBasicDType* const bdtypep = nodep->varp()->basicp();
            if (bdtypep && bdtypep->keyword() == VBasicDTypeKwd::STRING) {
                nodep->varp()->v3error(
                    "Forcing strings is not permitted: " << nodep->varp()->name());
            }

            // Build the per-signal force update logic.
            AstVar* const varp = nodep->varp();
            FileLine* const flp = varp->fileline();
            ForceState::VarForceInfo& info = m_state.getOrCreateVarInfo(nodep);
            AstVarScope* const enVscp = info.m_forceEnVscp;
            AstVarScope* const valVscp = info.m_forceValVscp;

            // Build an update block triggered by force-enable changes.
            AstSenItem* const itemsp = new AstSenItem{flp, VEdgeType::ET_CHANGED,
                                                      new AstVarRef{flp, enVscp, VAccess::READ}};
            AstActive* const activep
                = new AstActive{flp, "force-update", new AstSenTree{flp, itemsp}};
            activep->senTreeStorep(activep->sentreep());

            // Build expression selecting forced value when enabled, otherwise original value.
            // forceExpr = (isBitwise) ? ((en & val) | (~en & orig)) : (en ? val : orig);
            AstVarRef* const refp = new AstVarRef{flp, nodep, VAccess::READ};
            ForceState::markNonReplaceable(refp);
            AstVarRef* const enRefp = new AstVarRef{flp, enVscp, VAccess::READ};
            AstVarRef* const valRefp = new AstVarRef{flp, valVscp, VAccess::READ};
            const AstBasicDType* const basicp = varp->dtypep()->skipRefp()->basicp();
            AstNodeExpr* const forceExprp
                = basicp && basicp->isRanged()
                      ? ForceState::makeEnValBlend(flp, enRefp, valRefp, refp)
                      : static_cast<AstNodeExpr*>(new AstCond{flp, enRefp, valRefp, refp});
            AstAssignForce* const forceAssignp
                = new AstAssignForce{flp, new AstVarRef{flp, nodep, VAccess::WRITE}, forceExprp};
            forceAssignp->user2(true);
            activep->addStmtsp(new AstAlways{flp, VAlwaysKwd::ALWAYS, nullptr, forceAssignp});
            nodep->scopep()->addBlocksp(activep);

            // Clone the RHS for tracking and preserve original var refs as non-replaceable.
            AstNodeExpr* const rhsClonep = forceExprp->cloneTreePure(false);
            rhsClonep->foreach([varp](AstVarRef* const refp) {
                if (refp->varp() == varp) ForceState::markNonReplaceable(refp);
            });

            // Compute full assignment range (including unpacked arrays) for force bookkeeping.
            const bool bitwiseVar = ForceState::isBitwiseDType(varp);
            const int padMsb = bitwiseVar ? (varp->width() - 1) : 0;
            const int rangeLsb = 0;
            // A slot-tracked variable's whole-value force covers every slot, so a later
            // ownership query for this synthetic force answers over the right range
            const int rangeMsb = ForceState::usesForceSlots(varp)
                                     ? ForceState::forceSlots(varp->dtypep()) - 1
                                     : padMsb;
            if (ForceState::isUnpackedArrayDType(varp->dtypep())) {
                nodep->v3fatalSrc("Forceable unpacked arrays should have been rejected earlier");
            }
            m_state.addForceAssignment(varp, nodep, rhsClonep, forceAssignp, rangeLsb, rangeMsb, 0,
                                       padMsb, new AstVarRef{flp, nodep, VAccess::READ});
        }
        iterateChildrenConst(nodep);
    }

    void visit(AstNode* nodep) override { iterateChildrenConst(nodep); }

public:
    explicit ForceDiscoveryVisitor(AstNetlist* nodep, ForceState& state)
        : m_state{state} {
        iterateAndNextConstNull(nodep->modulesp());
    }
};

//######################################################################
// ForceConvertVisitor - Convert force/release statements

class ForceConvertVisitor final : public VNVisitor {
    ForceState& m_state;

    void visit(AstAssignForce* nodep) override {
        UINFO(2, "Converting force statement: " << nodep << "\n");

        AstNodeExpr* const lhsp = nodep->lhsp();
        AstVarRef* const lhsVarRefp = m_state.getOneVarRef(lhsp);
        AstVar* const forcedVarp = lhsVarRefp->varp();

        // Discovery reported forces it could not register and left them alone; drop them here
        if (ForceState::forceUnsupportedReason(nodep)) {
            VL_DO_DANGLING(pushDeletep(nodep->unlinkFrBack()), nodep);
            return;
        }

        const ForceState::ForceInfo& info = m_state.getForceInfo(nodep);
        const ForceState::VarForceInfo* const varInfo
            = m_state.getVarInfo(lhsVarRefp->varScopep());
        UASSERT_OBJ(varInfo && varInfo->m_forceVecVscp, nodep, "Force info not set up");

        FileLine* const flp = nodep->fileline();

        // Assign RHS shadow value immediately so force takes effect in the same timestep.
        UASSERT_OBJ(info.m_rhsVarVscp, nodep, "No RHS var for forced variable");
        AstAssign* const rhsAssignp
            = new AstAssign{flp, new AstVarRef{flp, info.m_rhsVarVscp, VAccess::WRITE},
                            nodep->rhsp()->cloneTreePure(false)};

        AstAssign* valAssignp = nullptr;
        AstAssign* enAssignp = nullptr;
        const bool bitwiseForcedVar = ForceState::isBitwiseDType(forcedVarp);
        // When an externally forceable signal is also forced in (System)Verilog code
        // keep the public __VforceEn/__VforceVal signals in sync with the procedural force too.
        // Those signals hold one whole value, so a force naming a single leaf of a slot-indexed
        // variable cannot be expressed in them and lives only in VlForceVec.
        const bool wholeSlotVar = !ForceState::usesForceSlots(forcedVarp) || VN_IS(lhsp, VarRef);
        // An unpacked array's external enable and value are per element, so the whole-value
        // mask arithmetic below does not apply to it.  A procedural force of such a variable
        // lives in its slots and is merged into the read shadow, so the public enable and
        // value are left to the external interface alone.
        const bool unpackedArrayVar = ForceState::isUnpackedArrayDType(forcedVarp->dtypep());
        if (!nodep->user2() && varInfo->m_forceEnVscp && varInfo->m_forceValVscp && wholeSlotVar
            && !unpackedArrayVar) {
            AstNodeExpr* baseExprp = nodep->rhsp()->cloneTreePure(false);
            baseExprp->foreach(
                [](AstVarRef* const refp) { ForceState::markNonReplaceable(refp); });
            if (bitwiseForcedVar) {
                baseExprp = ForceState::zeroPadToBaseWidth(baseExprp, forcedVarp->width(),
                                                           info.m_padLsb, info.m_padMsb);
            }
            if (bitwiseForcedVar) {
                // forceVal = (forceVal & ~mask(range)) | (rhs_padded & mask(range));
                // forceEn  = forceEn | mask(range);
                AstConst* const maskConstp = ForceState::makeRangeMaskConst(
                    nodep, forcedVarp->width(), info.m_rangeLsb, info.m_rangeMsb);
                AstNodeExpr* const valReadp
                    = new AstVarRef{flp, varInfo->m_forceValVscp, VAccess::READ};
                AstNodeExpr* const valWritep
                    = new AstVarRef{flp, varInfo->m_forceValVscp, VAccess::WRITE};
                AstNodeExpr* const notMaskp = new AstNot{flp, maskConstp};
                AstNodeExpr* const maskedOldp = new AstAnd{flp, valReadp, notMaskp};
                AstNodeExpr* const newValp = new AstOr{flp, maskedOldp, baseExprp};
                valAssignp = new AstAssign{flp, valWritep, newValp};

                AstNodeExpr* const enReadp
                    = new AstVarRef{flp, varInfo->m_forceEnVscp, VAccess::READ};
                AstNodeExpr* const enWritep
                    = new AstVarRef{flp, varInfo->m_forceEnVscp, VAccess::WRITE};
                AstNodeExpr* const newEnp
                    = new AstOr{flp, enReadp, maskConstp->cloneTreePure(false)};
                enAssignp = new AstAssign{flp, enWritep, newEnp};
            } else {
                AstConst* const oneConstp = ForceState::makeRangeMaskConst(nodep, 1, 0, 0);
                AstNodeExpr* const rhsValp = ForceState::castToNodeDType(baseExprp, forcedVarp);
                valAssignp = new AstAssign{
                    flp, new AstVarRef{flp, varInfo->m_forceValVscp, VAccess::WRITE}, rhsValp};
                enAssignp = new AstAssign{
                    flp, new AstVarRef{flp, varInfo->m_forceEnVscp, VAccess::WRITE}, oneConstp};
            }
        }

        // Slot-tracked variables register only which force owns which slots; the value
        // stays in the force's own typed shadow, which compiled reads consult directly.
        // Bitwise variables keep the value-carrying entry.
        AstNodeStmt* stmtp = nullptr;
        if (ForceState::usesForceSlots(forcedVarp)) {
            UASSERT_OBJ(info.m_forceId >= 0, nodep, "Force registered with a negative id");
            const AstSel* const selLhsp = VN_CAST(lhsp, Sel);
            const bool bitSel = selLhsp && ForceState::isBitwiseDType(selLhsp->fromp())
                                && (info.m_padMsb - info.m_padLsb + 1) < selLhsp->fromp()->width();
            AstCMethodHard* const addForceCallp = new AstCMethodHard{
                flp, new AstVarRef{flp, varInfo->m_forceVecVscp, VAccess::WRITE},
                VCMethod::FORCE_ADD_AT, ForceState::makeConst32(flp, info.m_forceId)};
            addForceCallp->addPinsp(ForceState::makeConst32(flp, info.m_rangeLsb));
            if (bitSel) {
                const int elemWidth = selLhsp->fromp()->width();
                UASSERT_OBJ(0 <= info.m_padLsb && info.m_padLsb <= info.m_padMsb
                                && info.m_padMsb < elemWidth,
                            nodep, "Force bit range outside the forced slot");
                addForceCallp->addPinsp(ForceState::makeConst32(flp, info.m_padLsb));
                addForceCallp->addPinsp(ForceState::makeConst32(flp, info.m_padMsb));
                addForceCallp->addPinsp(ForceState::makeConst32(flp, elemWidth));
            } else {
                UASSERT_OBJ(info.m_rangeLsb <= info.m_rangeMsb, nodep,
                            "Force slot range lsb past msb");
                addForceCallp->addPinsp(ForceState::makeConst32(flp, info.m_rangeMsb));
            }
            addForceCallp->dtypeSetVoid();
            stmtp = addForceCallp->makeStmt();
        } else {
            UASSERT_OBJ(info.m_rangeLsb <= info.m_rangeMsb, nodep, "Force range lsb past msb");
            AstNodeExpr* const rhsDatap = ForceState::buildRhsDataExpr(flp, info);
            AstCExpr* const rhsAddrp = new AstCExpr{flp};
            rhsAddrp->add("&(");
            rhsAddrp->add(rhsDatap);
            rhsAddrp->add(")");
            AstCMethodHard* const addForceCallp = new AstCMethodHard{
                flp, new AstVarRef{flp, varInfo->m_forceVecVscp, VAccess::WRITE},
                VCMethod::FORCE_ADD, ForceState::makeConst32(flp, info.m_rangeLsb)};
            addForceCallp->addPinsp(ForceState::makeConst32(flp, info.m_rangeMsb));
            addForceCallp->addPinsp(rhsAddrp);
            addForceCallp->addPinsp(ForceState::makeConst32(flp, info.m_rangeLsb));
            addForceCallp->dtypeSetVoid();
            stmtp = addForceCallp->makeStmt();
        }

        AstNode* tailp = rhsAssignp;
        if (valAssignp) {
            tailp->addNextHere(valAssignp);
            tailp = valAssignp;
        }
        if (enAssignp) {
            tailp->addNextHere(enAssignp);
            tailp = enAssignp;
        }
        tailp->addNextHere(stmtp);
        if (varInfo->m_forceRdVscp) {
            stmtp->addNextHere(m_state.makeForceRdRefreshStmt(*varInfo));
        }
        nodep->replaceWith(rhsAssignp);
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }

    void visit(AstRelease* nodep) override {
        UINFO(2, "Converting release statement: " << nodep << "\n");

        AstNodeExpr* const lhsp = nodep->lhsp();
        AstVarRef* const lhsVarRefp = m_state.getOneVarRef(lhsp);
        AstVar* const releasedVarp = lhsVarRefp->varp();

        const ForceState::VarForceInfo* const varInfo
            = m_state.getVarInfo(lhsVarRefp->varScopep());
        if (!varInfo || varInfo->m_forces.empty()) {
            // Releasing something never forced keeps its value, so there is nothing to do
            VL_DO_DANGLING(pushDeletep(nodep->unlinkFrBack()), nodep);
            return;
        }

        FileLine* const flp = nodep->fileline();

        const ForceState::ForceRange rangeInfo
            = m_state.getForceRangeInfo(lhsp, releasedVarp, false);

        const AstSel* const selLhsp = VN_CAST(lhsp, Sel);
        const bool arrayBitSel
            = ForceState::usesForceSlots(releasedVarp) && selLhsp
              && ForceState::isBitwiseDType(selLhsp->fromp())
              && (rangeInfo.m_padMsb - rangeInfo.m_padLsb + 1) < selLhsp->fromp()->width();
        AstCMethodHard* const releaseCallp = new AstCMethodHard{
            flp, new AstVarRef{flp, varInfo->m_forceVecVscp, VAccess::WRITE},
            VCMethod::FORCE_RELEASE, ForceState::makeConst32(flp, rangeInfo.m_rangeLsb)};
        releaseCallp->addPinsp(ForceState::makeConst32(flp, rangeInfo.m_rangeMsb));
        if (arrayBitSel) {
            UASSERT_OBJ(rangeInfo.m_rangeLsb == rangeInfo.m_rangeMsb
                            && rangeInfo.m_padLsb <= rangeInfo.m_padMsb,
                        nodep, "Bit-select release must name one slot and an ordered bit range");
            releaseCallp->addPinsp(ForceState::makeConst32(flp, rangeInfo.m_padLsb));
            releaseCallp->addPinsp(ForceState::makeConst32(flp, rangeInfo.m_padMsb));
            releaseCallp->addPinsp(ForceState::makeConst32(flp, selLhsp->fromp()->width()));
        } else {
            UASSERT_OBJ(rangeInfo.m_rangeLsb <= rangeInfo.m_rangeMsb, nodep,
                        "Release range lsb past msb");
        }
        releaseCallp->dtypeSetVoid();
        // forceVec.release(range_lsb, range_msb [, bit_lsb, bit_msb]);
        AstNodeStmt* const releasep = releaseCallp->makeStmt();

        AstAssign* clearEnp = nullptr;
        // Releases must also clear the external/public force-enable, but only for
        // directly forceable variables and only for non-array-select cases that use that external
        // force.  An unpacked array's enable is per element and mask arithmetic does not apply
        // to it; its procedural release lives in the force vector, so the external enable is
        // left to the external interface alone.
        if (releasedVarp->isForceable() && varInfo->m_forceEnVscp
            && !ForceState::isUnpackedArrayDType(releasedVarp->dtypep())
            && (!ForceState::usesForceSlots(releasedVarp) || VN_IS(lhsp, VarRef))) {
            AstNodeExpr* const enWritep
                = new AstVarRef{flp, varInfo->m_forceEnVscp, VAccess::WRITE};
            if (ForceState::isBitwiseDType(releasedVarp)) {
                const int varWidth = releasedVarp->width();
                if (rangeInfo.m_rangeLsb == 0 && rangeInfo.m_rangeMsb == varWidth - 1) {
                    clearEnp
                        = new AstAssign{flp, enWritep, ForceState::makeZeroConst(nodep, varWidth)};
                } else {
                    // forceEn = forceEn & ~mask(range);
                    AstNodeExpr* const enReadp
                        = new AstVarRef{flp, varInfo->m_forceEnVscp, VAccess::READ};
                    AstConst* const maskConst = ForceState::makeRangeMaskConst(
                        nodep, varWidth, rangeInfo.m_rangeLsb, rangeInfo.m_rangeMsb);
                    AstNodeExpr* const newEnp
                        = new AstAnd{flp, enReadp, new AstNot{flp, maskConst}};
                    clearEnp = new AstAssign{flp, enWritep, newEnp};
                }
            } else {
                clearEnp = new AstAssign{flp, enWritep, ForceState::makeZeroConst(nodep, 1)};
            }
        }

        const AstSel* const selp = VN_CAST(lhsp, Sel);

        AstNode* stmtListp = releasep;
        if (clearEnp) {
            clearEnp->addNextHere(stmtListp);
            stmtListp = clearEnp;
        }

        // IEEE 1800-2023 10.6.2: When released, if the variable is not continuously driven,
        // it maintains its current value until the next procedural assignment.
        const bool fullBitwiseRelease = ForceState::isBitwiseDType(releasedVarp)
                                        && !ForceState::usesForceSlots(releasedVarp) && !selp
                                        && rangeInfo.m_rangeLsb == 0
                                        && rangeInfo.m_rangeMsb == releasedVarp->width() - 1;
        if (!releasedVarp->isContinuously()
            && !(m_state.doingAssign() && m_state.hasClockedWrite(releasedVarp)
                 && fullBitwiseRelease)) {
            // Retention is compiled the same way reads are: leaves take the blend chain,
            // aggregates take a raw copy plus one guarded write per force.
            // if (!continuously_driven) lhs = current_forced_value(lhs_path);
            // forceVec.release(range);
            if (ForceState::usesForceSlots(releasedVarp)) {
                // Strip every trailing bit or part select to reach the leaf, as reads do:
                // a released target may carry more than one, as in 'a[0][7:4][3:0]'
                AstNodeExpr* const leafp = ForceState::stripToLeaf(lhsp);
                AstNodeStmt* retainp = nullptr;
                const bool aggregate = ForceState::forceSlots(leafp->dtypep()) > 1;
                const size_t reachingCount
                    = aggregate ? 0 : m_state.forcesReachingLeaf(*varInfo, leafp).size();
                AstVarScope* const shadowVscp = varInfo->wholeReadShadowVscp();
                // A slot-tracked variable reached here has been forced (the release of an
                // unforced target returned above), so finalizeRhsVars has given it a whole-value
                // shadow.  An aggregate leaf therefore always routes through that shadow.
                UASSERT_OBJ(shadowVscp, lhsp,
                            "Forced slot-tracked variable has no whole-value shadow");
                // Rebuild the shadow and copy the released region out of it when the leaf routes
                // through the shadow (the same test reads use).  The shadow merges into its own
                // storage, so a hole an earlier release punched survives; building an aggregate
                // straight into the variable would let an enclosing force's arm clobber it
                // before its own hole repair reads the retained raw value back.
                if (ForceState::routesThroughShadow(leafp, reachingCount)) {
                    retainp = m_state.makeWholeRdRefreshStmt(*varInfo);
                    AstNodeExpr* const srcp = lhsp->cloneTreePure(false);
                    AstVarRef* const srcBasep = m_state.getOneVarRef(srcp);
                    srcBasep->varp(shadowVscp->varp());
                    srcBasep->varScopep(shadowVscp);
                    ForceState::markRawRead(srcp);
                    AstNodeExpr* const dstp = lhsp->cloneTreePure(false);
                    dstp->foreach(
                        [](AstVarRef* const refp) { ForceState::markNonReplaceable(refp); });
                    retainp->addNext(new AstAssign{flp, dstp, srcp});
                } else {
                    AstNodeExpr* const rawp = leafp->cloneTreePure(false);
                    ForceState::markRawRead(rawp);
                    AstNodeExpr* forceReadp = m_state.buildForcedLeafExpr(*varInfo, leafp, rawp);
                    if (selp) forceReadp = ForceState::rebuildSelPath(lhsp, forceReadp);
                    retainp = new AstAssign{flp, lhsp->cloneTreePure(false), forceReadp};
                }
                retainp->addNext(static_cast<AstNodeStmt*>(stmtListp));
                stmtListp = retainp;
            } else {
                AstNodeExpr* const forceReadp
                    = selp ? ForceState::rebuildSelPath(
                                 lhsp, m_state.createForceReadExpression(*varInfo, lhsVarRefp))
                           : m_state.createForceReadExpression(*varInfo, lhsVarRefp);
                AstAssign* const assignp
                    = new AstAssign{flp, lhsp->cloneTreePure(false), forceReadp};
                assignp->addNextHere(stmtListp);
                stmtListp = assignp;
            }
        }

        if (varInfo->m_forceRdVscp) stmtListp->addNext(m_state.makeForceRdRefreshStmt(*varInfo));

        nodep->replaceWith(stmtListp);
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }

    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    ForceConvertVisitor(AstNetlist* nodep, ForceState& state)
        : m_state{state} {
        iterateAndNextNull(nodep->modulesp());
    }
};

//######################################################################
// ForceReplaceVisitor - Replace variable reads with force-aware reads

class ForceReplaceVisitor final : public VNVisitor {
    const ForceState& m_state;
    VDouble0 m_nonOverlappingForceSels;  // Statistic tracking
    AstNodeStmt* m_stmtp = nullptr;
    bool m_inLogic = false;
    // Statements already given a shadow refresh, so several reads in one statement share it
    std::set<std::pair<AstNodeStmt*, const ForceState::VarForceInfo*>> m_slotRdRefreshed;

    void iterateLogic(AstNode* nodep) {
        VL_RESTORER(m_inLogic);
        m_inLogic = true;
        iterateChildren(nodep);
    }

    void visit(AstNodeStmt* nodep) override {
        VL_RESTORER(m_stmtp);
        m_stmtp = nodep;
        iterateChildren(nodep);
    }
    void visit(AstAssign* nodep) override {
        VL_RESTORER(m_stmtp);
        m_stmtp = nodep;
        iterate(nodep->lhsp());
        iterate(nodep->rhsp());
        if (AstVarRef* const lhsp = VN_CAST(AstArraySel::baseFromp(nodep->lhsp(), true), VarRef)) {
            if (AstNode* const updatep
                = m_state.createRhsUpdatesForWrite(nodep->fileline(), lhsp->varp())) {
                nodep->addNextHere(updatep);
            }
        }
    }
    void visit(AstAssignCont* nodep) override {
        VL_RESTORER(m_stmtp);
        m_stmtp = nodep;
        iterateAndNextNull(nodep->timingControlp());
        iterate(nodep->rhsp());
    }
    void visit(AstDeassign*) override {}
    void visit(AstCFunc* nodep) override { iterateLogic(nodep); }
    void visit(AstCoverToggle* nodep) override { iterateLogic(nodep); }
    void visit(AstNodeProcedure* nodep) override { iterateLogic(nodep); }
    void visit(AstAlways* nodep) override {
        if (nodep->keyword() == VAlwaysKwd::CONT_ASSIGN) {
            iterateChildren(nodep);
            return;
        }
        iterateLogic(nodep);
    }
    void visit(AstSenItem* nodep) override { iterateLogic(nodep); }
    void visit(AstSel* nodep) override {
        // A select of a leaf inside an aggregate goes through the slot-indexed path instead
        if (replacePathRead(nodep)) return;
        // Replace Sel on a wide with readSelI/Q/W to avoid materializing the full value
        AstVarRef* const refp = VN_CAST(nodep->fromp(), VarRef);
        if (!refp || ForceState::isNotReplaceable(refp) || !refp->access().isReadOnly()) {
            visit(static_cast<AstNode*>(nodep));
            return;
        }

        AstVar* const varp = refp->varp();
        const ForceState::VarForceInfo* const varInfo = m_state.getVarInfo(refp->varScopep());
        if (!varInfo || varInfo->m_forceRdVscp || varInfo->m_forces.empty()
            || !ForceState::isBitwiseDType(varp) || !varp->dtypep()->isWide()) {
            visit(static_cast<AstNode*>(nodep));
            return;
        }

        if (const AstConst* const lsbConstp = VN_CAST(nodep->lsbp(), Const)) {
            const int selLsb = lsbConstp->toSInt();
            const int selMsb = selLsb + nodep->width() - 1;
            if (!varp->isSigPublic()
                && !ForceState::selOverlapsAnyForce(*varInfo, selLsb, selMsb)) {
                m_nonOverlappingForceSels++;
                ForceState::markNonReplaceable(refp);
                visit(static_cast<AstNode*>(nodep));
                return;
            }
        }

        FileLine* const flp = nodep->fileline();
        ForceState::markNonReplaceable(refp);
        AstVarRef* const refClonep = refp->cloneTreePure(false);
        ForceState::markNonReplaceable(refClonep);
        AstCMethodHard* const callp = new AstCMethodHard{
            flp, new AstVarRef{flp, varInfo->m_forceVecVscp, VAccess::READ},
            VCMethod::FORCE_READ_SEL, ForceState::makeConst32(flp, varp->width())};
        callp->addPinsp(refClonep);
        callp->addPinsp(nodep->lsbp()->cloneTreePure(false));
        callp->addPinsp(ForceState::makeConst32(flp, nodep->width()));
        callp->dtypeFrom(nodep);
        nodep->replaceWith(callp);
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }
    // Replace a read of one leaf of a slot-indexed variable, reached through any mix of member
    // and element selections, with a force-aware read of that leaf's slot.  Returns false when
    // this node is not such a read, so the caller keeps iterating.
    bool replacePathRead(AstNodeExpr* nodep) {
        if (ForceState::isPathFromOfSelector(nodep)) return false;  // An outer node covers it

        // Trailing bit or part selects address bits inside the leaf, so find the leaf first
        // and put those selects back on top of the force-aware read afterwards.
        AstNodeExpr* const leafp = ForceState::stripToLeaf(nodep);
        if (VN_IS(leafp, VarRef)) return false;  // Whole variable, visit(AstVarRef) handles it

        AstVarRef* const baseRefp = VN_CAST(AstArraySel::baseFromp(leafp, true), VarRef);
        if (!baseRefp || ForceState::isNotReplaceable(baseRefp)) return false;
        const ForceState::VarForceInfo* const varInfo = m_state.getVarInfo(baseRefp->varScopep());
        if (!varInfo) return false;
        // An externally forceable aggregate other than an unpacked array keeps its merged value
        // in __VforceRd, and reads of it go through that instead
        if (varInfo->m_forceRdVscp
            && !ForceState::isUnpackedArrayDType(baseRefp->varp()->dtypep())) {
            return false;
        }
        // In assignAll() an externally forceable array's committed value lives in
        // __VforceRd, so element reads use that rather than the ownership entries (#8085)
        if (m_state.doingAssign() && varInfo->m_forceRdVscp) {
            baseRefp->varp(varInfo->m_forceRdVscp->varp());
            baseRefp->varScopep(varInfo->m_forceRdVscp);
            return false;
        }
        if (!ForceState::usesForceSlots(baseRefp->varp())) return false;
        if (!baseRefp->access().isReadOnly()) return false;
        // A non-aggregate leaf no force can reach stays a plain read
        const bool aggregate = ForceState::forceSlots(leafp->dtypep()) > 1;
        const size_t reachingCount
            = aggregate ? 0 : m_state.forcesReachingLeaf(*varInfo, leafp).size();
        if (!aggregate && reachingCount == 0) return false;

        // An intermediate selection still naming an aggregate is not one leaf, and a leaf
        // more forces can reach than a chain should carry is treated the same: rebase it
        // onto the whole-value shadow, which merges every leaf's force, and keep iterating
        // so any index expressions inside it are still substituted.
        if (ForceState::routesThroughShadow(leafp, reachingCount)) {
            if (varInfo->m_slotRdVscp) {
                if (m_inLogic && m_stmtp && m_slotRdRefreshed.emplace(m_stmtp, varInfo).second) {
                    m_stmtp->addHereThisAsNext(m_state.makeSlotRdRefreshStmt(*varInfo));
                }
                baseRefp->varp(varInfo->m_slotRdVscp->varp());
                baseRefp->varScopep(varInfo->m_slotRdVscp);
                ForceState::markNonReplaceable(baseRefp);
                return false;
            }
            // With no whole-value shadow an aggregate read has no chain to fall back on; a
            // leaf reached by too many forces still builds one below.
            if (aggregate) return false;
        }

        // Substitute forced reads inside the index expressions before anything is cloned, so
        // the fallback value and the slot ordinal use the same, force-aware index.  An index
        // is an ordinary read, including when it reads the same array as in 'mem[mem[0]]'.
        for (AstArraySel* const selp : ForceState::arraySelsOf(leafp)) {
            iterateAndNextNull(selp->bitp());
        }
        AstNodeExpr* const rawp = leafp->cloneTreePure(false);
        rawp->foreach([](AstVarRef* const refp) { ForceState::markNonReplaceable(refp); });
        AstNodeExpr* const readExprp = m_state.buildForcedLeafExpr(*varInfo, leafp, rawp);
        if (leafp == nodep) {
            nodep->replaceWith(readExprp);
        } else {
            nodep->replaceWith(ForceState::rebuildSelPath(nodep, readExprp));
        }
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
        return true;
    }

    void visit(AstArraySel* nodep) override {
        // A selection used as an index is a read in its own right, as in 'mem[mem[0]]', so
        // isPathFromOfSelector() inside replacePathRead() only skips selections along 'fromp'.
        if (!replacePathRead(nodep)) iterateChildren(nodep);
    }
    void visit(AstStructSel* nodep) override {
        if (!replacePathRead(nodep)) iterateChildren(nodep);
    }

    void visit(AstVarRef* nodep) override {
        if (ForceState::isNotReplaceable(nodep)) return;
        // The array an ArraySel selects from is left to visit(AstArraySel), which builds
        // the force-aware read for the whole select. The index is an ordinary read and
        // must still be substituted here, so check which child this is.
        if (const AstArraySel* const backSelp = VN_CAST(nodep->backp(), ArraySel)) {
            if (backSelp->fromp() == nodep) return;
        }

        const ForceState::VarForceInfo* const varInfo = m_state.getVarInfo(nodep->varScopep());
        if (!varInfo) return;

        if (varInfo->m_forceRdVscp) {
            if (nodep->access().isRW()) {
                if (m_inLogic) {
                    nodep->v3warn(E_UNSUPPORTED,
                                  "Unsupported: Signals used via read-write reference cannot be "
                                  "forced");
                }
                return;
            }
            if (nodep->access().isReadOnly()) {
                nodep->varp(varInfo->m_forceRdVscp->varp());
                nodep->varScopep(varInfo->m_forceRdVscp);
                return;
            }
            if (m_inLogic && m_stmtp) {
                m_stmtp->addNextHere(m_state.makeForceRdRefreshStmt(*varInfo));
            }
            return;
        }

        // On a slot-indexed variable a member or element path is rewritten at its outermost
        // selector, which needs the base reference left as it is.  A bit-range variable
        // instead has its whole value read here, and the selects above pick from that.
        if (ForceState::usesForceSlots(nodep->varp()) && ForceState::isPathFromOfSelector(nodep)) {
            return;
        }

        // A variable may reach here with a release recorded but no force left: a
        // self-assigning 'force s = s' is removed as redundant before this pass, leaving
        // its 'release s' behind.  Nothing is forced, so the read stays as it is.
        if (varInfo->m_forces.empty()) return;

        if (varInfo->m_slotRdVscp) {
            if (nodep->access().isRW()) {
                if (m_inLogic) {
                    nodep->v3warn(E_UNSUPPORTED,
                                  "Unsupported: Signals used via read-write reference cannot be "
                                  "forced");
                }
                return;
            }
            // Reading the whole of a slot-indexed variable means reading its shadow, which
            // already merges the force on each leaf
            if (nodep->access().isReadOnly()) {
                // In procedural code the read may happen in the same time step as the force,
                // before the block that maintains the shadow has had a chance to run, so
                // refresh it just ahead of this statement as well.
                if (m_inLogic && m_stmtp && m_slotRdRefreshed.emplace(m_stmtp, varInfo).second) {
                    m_stmtp->addHereThisAsNext(m_state.makeSlotRdRefreshStmt(*varInfo));
                }
                nodep->varp(varInfo->m_slotRdVscp->varp());
                nodep->varScopep(varInfo->m_slotRdVscp);
            }
            return;
        }

        if (nodep->access().isRW()) {
            nodep->v3warn(E_UNSUPPORTED,
                          "Unsupported: Signals used via read-write reference cannot be forced");
        } else if (nodep->access().isReadOnly()) {
            ForceState::markNonReplaceable(nodep);
            AstNodeExpr* const readExprp = m_state.createForceReadExpression(*varInfo, nodep);
            nodep->replaceWith(readExprp);
            VL_DO_DANGLING(pushDeletep(nodep), nodep);
        }
    }
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    explicit ForceReplaceVisitor(AstNetlist* nodep, const ForceState& state)
        : m_state{state} {
        iterateAndNextNull(nodep->modulesp());
    }
    ~ForceReplaceVisitor() override {
        V3Stats::addStat("Non-overlapping force sels", m_nonOverlappingForceSels);
    }
};
//######################################################################
//

//######################################################################
// V3Force - Main entry point

static void forceAllImpl(AstNetlist* nodep, ForceState::ForceHelperVarsByVar& helperVars) {
    UINFO(2, __FUNCTION__ << ":\n");
    if (!v3Global.hasForceableSignals()) return;
    {
        // Scoped so the state, which owns copies of the target paths, is gone before the
        // tree check below looks for anything left unlinked
        ForceState state{false, helperVars};
        { ForceDiscoveryVisitor{nodep, state}; }
        state.finalizeRhsVars();
        { ForceConvertVisitor{nodep, state}; }
        { ForceReplaceVisitor{nodep, state}; }
    }
    V3Global::dumpCheckGlobalTree("force", 0, dumpTreeEitherLevel() >= 3);
}

static void assignAllImpl(AstNetlist* nodep, ForceState::ForceHelperVarsByVar& helperVars) {
    UINFO(2, __FUNCTION__ << ":\n");
    if (!v3Global.hasAssignDeassign()) return;

    std::vector<AstDeassign*> deassignps;
    nodep->foreach([&](AstDeassign* deassignp) { deassignps.push_back(deassignp); });
    for (AstDeassign* const deassignp : deassignps) splitDeassign(deassignp);

    std::vector<AstAssignCont*> assignContps;
    deassignps.clear();
    nodep->foreach([&](AstNodeStmt* nodep) {
        if (AstAssignCont* const assignContp = VN_CAST(nodep, AssignCont)) {
            assignContps.push_back(assignContp);
        } else if (AstDeassign* const deassignp = VN_CAST(nodep, Deassign)) {
            deassignps.push_back(deassignp);
        }
    });

    for (AstAssignCont* const assignp : assignContps) {
        assignp->replaceWith(new AstAssignForce{assignp->fileline(),
                                                assignp->lhsp()->unlinkFrBack(),
                                                assignp->rhsp()->unlinkFrBack()});
        assignp->deleteTree();
    }
    for (AstDeassign* const deassignp : deassignps) {
        deassignp->replaceWith(
            new AstRelease{deassignp->fileline(), deassignp->lhsp()->cloneTreePure(true)});
        deassignp->deleteTree();
    }
    {
        ForceState state{true, helperVars};
        { ForceDiscoveryVisitor{nodep, state}; }
        state.finalizeRhsVars();
        { ForceConvertVisitor{nodep, state}; }
        { ForceReplaceVisitor{nodep, state}; }
    }
    V3Global::dumpCheckGlobalTree("assign-deassign", 0, dumpTreeEitherLevel() >= 3);
}

void V3Force::forceAndAssignAll(AstNetlist* nodep) {
    const VNUser3InUse user3InUse;
    ForceState::ForceHelperVarsByVar helperVars;
    forceAllImpl(nodep, helperVars);
    assignAllImpl(nodep, helperVars);
}
