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
//  A whole-variable read cannot be one such call when the variable is, or holds, an unpacked
//  struct or union, as its leaves are not one uniform stride.  Those variables get a
//  <name>__VforceSlotRd shadow, kept up to date by copying the variable and then overriding
//  only the paths that are forced, and whole-variable reads are pointed at it.  A force or
//  release naming such an aggregate is lowered to one target per leaf before any of the above.
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Force.h"

#include "V3AstUserAllocator.h"
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

    struct VarForceInfo final {
        AstVarScope* m_forceVecVscp = nullptr;
        AstVarScope* m_forceRdVscp = nullptr;
        AstVarScope* m_slotRdVscp = nullptr;  // Whole-value read of a slot-indexed variable
        AstVarScope* m_forceEnVscp = nullptr;
        AstVarScope* m_forceValVscp = nullptr;
        AstVarScope* m_varVscp = nullptr;
        AstVar* m_varp = nullptr;
        AstScope* m_scopep = nullptr;
        std::unordered_map<AstAssignForce*, ForceInfo> m_forces;
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
    //  AstVarRef::user1      -> Flag indicating not to replace reference
    //  AstAssignForce::user2 -> true if force is synthetic (externally forceable)
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
        dtypep = dtypep->skipRefp();
        if (const AstUnpackArrayDType* const arrayp = VN_CAST(dtypep, UnpackArrayDType)) {
            return arrayp->declRange().elements() * forceSlots(arrayp->subDTypep());
        }
        if (const AstNodeUOrStructDType* const structp = VN_CAST(dtypep, NodeUOrStructDType)) {
            // A packed struct or union is one bitwise value, so bit ranges address it instead
            if (structp->packed()) return 1;
            int slots = 0;
            for (AstMemberDType* memberp = structp->membersp(); memberp;
                 memberp = VN_AS(memberp->nextp(), MemberDType)) {
                slots += forceSlots(memberp->dtypep());
            }
            // Union members overlay in storage but are tracked apart, as they always have been
            return slots ? slots : 1;
        }
        return 1;
    }

    // True when a type is, or holds, an unpacked struct or union.  VlForceVec reaches a slot
    // by striding over the target, which such a type does not lay out as one uniform stride,
    // so it is these types, and only these, that need the per-leaf handling below.
    static bool holdsUnpackedStructOrUnion(const AstNodeDType* dtypep) {
        dtypep = dtypep->skipRefp();
        if (const AstUnpackArrayDType* const arrayp = VN_CAST(dtypep, UnpackArrayDType)) {
            return holdsUnpackedStructOrUnion(arrayp->subDTypep());
        }
        if (const AstNodeUOrStructDType* const structp = VN_CAST(dtypep, NodeUOrStructDType)) {
            return !structp->packed();
        }
        return false;
    }

    // True when this variable's VlForceVec is indexed by leaf slot rather than by bit
    static bool usesForceSlots(AstVar* varp) {
        return forceSlots(varp->dtypep()) > 1 || !isBitwiseDType(varp);
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

    // A target path is addressed by walking its member and element selections.  Any other
    // way of selecting has no slot to be given, so report it rather than force nothing.
    static AstNode* unsupportedPathSelector(AstNodeExpr* nodep) {
        if (VN_IS(nodep, AssocSel) || VN_IS(nodep, WildcardSel) || VN_IS(nodep, CMethodHard)) {
            return nodep;
        }
        if (const AstSel* const selp = VN_CAST(nodep, Sel)) {
            return unsupportedPathSelector(selp->fromp());
        }
        if (const AstArraySel* const selp = VN_CAST(nodep, ArraySel)) {
            return unsupportedPathSelector(selp->fromp());
        }
        if (const AstStructSel* const selp = VN_CAST(nodep, StructSel)) {
            return unsupportedPathSelector(selp->fromp());
        }
        return nullptr;
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
            readExprp = new AstOr{
                flp, new AstAnd{flp, enRefp, valRefp},
                new AstAnd{flp, new AstNot{flp, enRefp->cloneTreePure(false)}, baseRefp}};
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
        return foreachUnpackedLeaf(
            dims, [&](const std::vector<int>& idx, int /*flat*/) -> AstNodeStmt* {
                AstVarRef* const baseRefp = new AstVarRef{flp, varInfo.m_varVscp, VAccess::READ};
                markNonReplaceable(baseRefp);
                AstNodeExpr* const baseSelp = buildNestedArraySel(flp, baseRefp, idx);
                AstNodeExpr* const enSelp = buildNestedArraySel(
                    flp, new AstVarRef{flp, varInfo.m_forceEnVscp, VAccess::READ}, idx);
                AstNodeExpr* const valSelp = buildNestedArraySel(
                    flp, new AstVarRef{flp, varInfo.m_forceValVscp, VAccess::READ}, idx);
                AstNodeExpr* const readExprp = new AstOr{
                    flp, new AstAnd{flp, enSelp, valSelp},
                    new AstAnd{flp, new AstNot{flp, enSelp->cloneTreePure(false)}, baseSelp}};
                AstNodeExpr* const rdLhsSelp = buildNestedArraySel(
                    flp, new AstVarRef{flp, varInfo.m_forceRdVscp, VAccess::WRITE}, idx);
                return new AstAssign{flp, rdLhsSelp, readExprp};
            });
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

    static void forceOrdinalRecurse(FileLine* flp, AstNodeExpr* nodep, ForceOrdinal& out) {
        if (const AstSel* const selp = VN_CAST(nodep, Sel)) {
            // A bit or part select stays inside one leaf, and is tracked as a bit range
            forceOrdinalRecurse(flp, selp->fromp(), out);
            return;
        }
        if (AstArraySel* const selp = VN_CAST(nodep, ArraySel)) {
            forceOrdinalRecurse(flp, selp->fromp(), out);
            // The element's own slot count is this dimension's stride, so nested dimensions
            // fall out of the recursion without needing the dimension sizes separately
            const int stride = forceSlots(selp->dtypep());
            if (const AstConst* const constp = VN_CAST(selp->bitp(), Const)) {
                out.m_constOffset += constp->toSInt() * stride;
                return;
            }
            // A read may select the element at run time.  Only a force target has to name a
            // constant element; 'array[i]' with a variable 'i' is an ordinary read.
            AstNodeExpr* termp = selp->bitp()->cloneTreePure(false);
            // V3Width sizes an array index to at most 32 bits, so widening is all that is
            // needed to keep the arithmetic below width matched.
            if (termp->width() < 32) termp = new AstExtend{flp, termp, 32};
            if (stride != 1) termp = new AstMul{flp, termp, makeConst32(flp, stride)};
            out.m_exprp = out.m_exprp ? new AstAdd{flp, out.m_exprp, termp} : termp;
            return;
        }
        if (const AstStructSel* const selp = VN_CAST(nodep, StructSel)) {
            forceOrdinalRecurse(flp, selp->fromp(), out);
            out.m_constOffset += memberSlotOffset(selp->fromp()->dtypep(), selp->name());
            return;
        }
        // An AstVarRef, or anything else, is the base the path is measured from
    }

    static ForceOrdinal forceOrdinal(FileLine* flp, AstNodeExpr* nodep) {
        ForceOrdinal out;
        forceOrdinalRecurse(flp, nodep, out);
        return out;
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
            AstVar* const varp = info.m_varp;
            if (info.m_forces.empty()) continue;

            AstScope* const scopep = info.m_scopep;
            UASSERT_OBJ(scopep, varp, "Missing scope for force RHS vars");

            FileLine* const flp = varp->fileline();
            const std::vector<ForceInfo*> forceps = forceInfosInIdOrder(info);

            for (ForceInfo* const finfop : forceps) {
                ForceInfo& finfo = *finfop;
                UASSERT_OBJ(finfo.m_rhsExprp, varp, "Missing RHS expression for ForceInfo");

                // Create per-force temporary storage for the captured RHS value.
                AstVar* const rhsVarp = new AstVar{
                    flp, VVarType::VAR,
                    varp->name() + (doingAssign() ? "_VassignRHS" : "__VforceRHS")
                        + std::to_string(finfo.m_forceId) + "__" + scopep->nameDotless(),
                    finfo.m_rhsExprp->dtypep()};
                rhsVarp->noSubst(true);
                rhsVarp->sigPublic(true);
                rhsVarp->setForcedByCode();
                varp->addNextHere(rhsVarp);
                finfo.m_rhsVarVscp = new AstVarScope{flp, scopep, rhsVarp};
                scopep->addVarsp(finfo.m_rhsVarVscp);

                // Build assignments for RHS capture. Public/forceable signals with __VforceRd
                // already have an explicit force-read update path, so they do not need the
                // forceVec.touch() ordering edge here.
                // always_comb begin
                //   forceRHS[id] = rhsExpr;
                //   forceVec.touch();  // Only without __VforceRd
                // end
                AstAssign* const rhsAssignp = new AstAssign{
                    flp, new AstVarRef{flp, finfo.m_rhsVarVscp, VAccess::WRITE}, finfo.m_rhsExprp};

                if (!info.m_forceRdVscp) {
                    // touch() is intentionally a semantic no-op at runtime: it creates an
                    // explicit use/ordering edge from the RHS-capture logic to the force vector
                    // so later optimization/scheduling passes keep this update path connected.
                    AstCMethodHard* const touchCallp = new AstCMethodHard{
                        flp, new AstVarRef{flp, info.m_forceVecVscp, VAccess::WRITE},
                        VCMethod::FORCE_TOUCH};
                    touchCallp->dtypeSetVoid();
                    AstNodeStmt* const touchStmtp = touchCallp->makeStmt();
                    rhsAssignp->addNextHere(touchStmtp);
                }

                // Run both updates in a combinational always block.
                AstAlways* const alwaysp
                    = new AstAlways{flp, VAlwaysKwd::ALWAYS, nullptr, rhsAssignp};
                AstSenTree* const senTreep
                    = new AstSenTree{flp, new AstSenItem{flp, AstSenItem::Combo{}}};
                AstActive* const activep = new AstActive{flp, "force-rhs-update", senTreep};
                activep->senTreeStorep(activep->sentreep());
                activep->addStmtsp(alwaysp);
                scopep->addBlocksp(activep);
            }

            if (holdsUnpackedStructOrUnion(varp->dtypep()) && !info.m_forceRdVscp) {
                // Reads of a leaf go straight to that leaf's slot, but a read of the whole
                // variable has to merge every leaf, which no single VlForceVec read can do.
                // Keep a shadow of the whole value up to date and read that instead.
                // Named per pass, as forceAll() and assignAll() each track their own
                // overrides and so each need their own shadow of the same variable
                AstVar* const slotRdVarp = new AstVar{
                    flp, VVarType::WIRE,
                    varp->name() + (doingAssign() ? "_VassignSlotRd" : "__VforceSlotRd"),
                    varp->dtypep()};
                slotRdVarp->noSubst(true);
                varp->addNextHere(slotRdVarp);
                info.m_slotRdVscp = new AstVarScope{flp, scopep, slotRdVarp};
                scopep->addVarsp(info.m_slotRdVscp);

                // Combinational, so scheduling orders this ahead of whatever reads the shadow
                // rather than leaving the update to a later region
                AstActive* const activep
                    = new AstActive{flp, "force-slot-rd-update",
                                    new AstSenTree{flp, new AstSenItem{flp, AstSenItem::Combo{}}}};
                activep->senTreeStorep(activep->sentreep());
                activep->addStmtsp(new AstAlways{flp, VAlwaysKwd::ALWAYS, nullptr,
                                                 createSlotRdUpdateStmt(info, info.m_slotRdVscp)});
                scopep->addBlocksp(activep);
            }

            if (info.m_forceRdVscp) {
                AstActive* const activeInitp = new AstActive{
                    flp, "force-init",
                    new AstSenTree{flp, new AstSenItem{flp, AstSenItem::Static{}}}};
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
                    initStmtp = new AstAssign{
                        flp, new AstVarRef{flp, info.m_forceEnVscp, VAccess::WRITE},
                        makeZeroConst(varp, info.m_forceEnVscp->width())};
                }
                initStmtp->addNext(createForceRdUpdateStmt(info));
                activeInitp->addStmtsp(new AstInitial{flp, initStmtp});
                scopep->addBlocksp(activeInitp);

                AstSenItem* itemsp = nullptr;
                auto addSenItem = [&](AstVarScope* vscp) {
                    if (!vscp) return;
                    AstSenItem* const nextp = new AstSenItem{
                        flp, VEdgeType::ET_CHANGED, new AstVarRef{flp, vscp, VAccess::READ}};
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
                AstSenItem* const origItemp
                    = new AstSenItem{flp, VEdgeType::ET_CHANGED, origSenRefp};
                if (!itemsp) varp->v3fatalSrc("force-rd-update missing force-enable sen item");
                itemsp->addNext(origItemp);
                for (ForceInfo* const finfop : forceps) addSenItem(finfop->m_rhsVarVscp);

                AstActive* const activep
                    = new AstActive{flp, "force-rd-update", new AstSenTree{flp, itemsp}};
                activep->senTreeStorep(activep->sentreep());
                activep->addStmtsp(new AstAlways{flp, VAlwaysKwd::ALWAYS, nullptr,
                                                 createForceRdUpdateStmt(info)});
                scopep->addBlocksp(activep);
            }
        }
    }

    // Build 'rd<path> = forceVec.read(var<path>, slot)' for every leaf of a slot-indexed
    // variable, so that a read of the whole variable sees each leaf's own force.
    // Rebuild a target path over a different base variable, so the same member and element
    // path can be applied to the shadow as to the variable it shadows
    static AstNodeExpr* rebasePath(AstNodeExpr* pathp, AstVarScope* baseVscp, VAccess access) {
        AstNodeExpr* const clonep = pathp->cloneTreePure(false);
        AstVarRef* const baseRefp = VN_CAST(AstArraySel::baseFromp(clonep, true), VarRef);
        UASSERT_OBJ(baseRefp, pathp, "Force target path has no VarRef at its base");
        baseRefp->varp(baseVscp->varp());
        baseRefp->varScopep(baseVscp);
        baseRefp->access(access);
        markNonReplaceable(baseRefp);
        return clonep;
    }

    // Keep a whole-value shadow of a slot-indexed variable up to date.  Copying the variable
    // and then overriding only the paths that are actually forced keeps this proportional to
    // the number of force statements rather than to the number of leaves, which matters when
    // the variable holds a large array.  The copy also gives overlaid union members the same
    // value, as the override writes through the storage they share.
    AstNodeStmt* createSlotRdUpdateStmt(const VarForceInfo& info, AstVarScope* targetVscp) const {
        FileLine* const flp = info.m_varVscp->fileline();
        AstVarRef* const wholeRhsp = new AstVarRef{flp, info.m_varVscp, VAccess::READ};
        markNonReplaceable(wholeRhsp);
        AstNodeStmt* headp
            = new AstAssign{flp, new AstVarRef{flp, targetVscp, VAccess::WRITE}, wholeRhsp};
        AstNodeStmt* tailp = headp;

        for (const ForceInfo* const finfop : forceInfosInIdOrder(info)) {
            UASSERT_OBJ(finfop->m_lhsPathp, info.m_varp, "Force with no recorded target path");
            // A bit or part select addresses inside one leaf, and the read below already
            // applies the forced bit range, so override at the leaf
            AstNodeExpr* leafp = finfop->m_lhsPathp;
            while (const AstSel* const selp = VN_CAST(leafp, Sel)) leafp = selp->fromp();

            AstNodeExpr* const readFromp = rebasePath(leafp, info.m_varVscp, VAccess::READ);
            AstNodeExpr* const readp
                = forceSlots(leafp->dtypep()) > 1
                      ? createForceReadRangeExpression(info, readFromp, finfop->m_rangeLsb)
                      : createForceReadIndexExpression(info, readFromp,
                                                       makeConst32(flp, finfop->m_rangeLsb));
            VL_DO_DANGLING(readFromp->deleteTree(), readFromp);
            AstAssign* const assignp
                = new AstAssign{flp, rebasePath(leafp, targetVscp, VAccess::WRITE), readp};
            // Only override while this force is active, so a force that never executes, or
            // was released, does not write the raw value over an overlaid union sibling
            AstIf* const ifp = new AstIf{
                flp, createIsForcedExpression(info, flp, finfop->m_rangeLsb, finfop->m_rangeMsb),
                assignp};
            tailp->addNextHere(ifp);
            tailp = ifp;
        }
        return headp;
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

    AstNodeExpr* createForceReadIndexExpression(const VarForceInfo& varInfo,
                                                AstNodeExpr* originalExprp,
                                                AstNodeExpr* indexExprp) const {
        FileLine* const flp = originalExprp->fileline();
        return createForceReadCall(varInfo, flp, VCMethod::FORCE_READ_INDEX,
                                   originalExprp->cloneTreePure(false), originalExprp, indexExprp);
    }

    // Read a whole uniform-stride subtree, an unpacked-array member for example, whose leaves
    // occupy the slot range starting at slotLsb
    AstNodeExpr* createForceReadRangeExpression(const VarForceInfo& varInfo,
                                                AstNodeExpr* originalExprp, int slotLsb) const {
        FileLine* const flp = originalExprp->fileline();
        return createForceReadCall(varInfo, flp, VCMethod::FORCE_READ_RANGE,
                                   originalExprp->cloneTreePure(false), originalExprp,
                                   makeConst32(flp, slotLsb));
    }

    // True when any active force overlaps the slot range, for guarding shadow updates
    AstNodeExpr* createIsForcedExpression(const VarForceInfo& varInfo, FileLine* flp, int lsb,
                                          int msb) const {
        AstCMethodHard* const callp
            = new AstCMethodHard{flp, new AstVarRef{flp, varInfo.m_forceVecVscp, VAccess::READ},
                                 VCMethod::FORCE_IS_FORCED, makeConst32(flp, lsb)};
        callp->addPinsp(makeConst32(flp, msb));
        callp->dtypeSetBit();
        return callp;
    }

    // True for a path built only from selections over a variable, which can be cloned per leaf
    // without changing how often anything is evaluated
    static bool isSimpleRef(const AstNodeExpr* nodep) {
        if (VN_IS(nodep, VarRef)) return true;
        if (const AstSel* const selp = VN_CAST(nodep, Sel)) {
            return VN_IS(selp->lsbp(), Const) && isSimpleRef(selp->fromp());
        }
        if (const AstArraySel* const selp = VN_CAST(nodep, ArraySel)) {
            return VN_IS(selp->bitp(), Const) && isSimpleRef(selp->fromp());
        }
        if (const AstStructSel* const selp = VN_CAST(nodep, StructSel)) {
            return isSimpleRef(selp->fromp());
        }
        return false;
    }

    // Collect one left/right pair per leaf of an aggregate, so a target naming the whole
    // aggregate can be rewritten as a target per leaf.  'rhsp' is null for a release.
    static void collectAggregateLeaves(AstNodeExpr* lhsp, AstNodeExpr* rhsp,
                                       std::vector<std::pair<AstNodeExpr*, AstNodeExpr*>>& out) {
        FileLine* const flp = lhsp->fileline();
        AstNodeDType* const dtypep = lhsp->dtypep()->skipRefp();
        // A uniform-stride subtree, a plain unpacked array of a bitwise type for example, is
        // one slot range that VlForceVec addresses on its own, so it is one target and the
        // generated code stays independent of its size
        if (!holdsUnpackedStructOrUnion(dtypep)) {
            out.emplace_back(lhsp->cloneTreePure(false),
                             rhsp ? rhsp->cloneTreePure(false) : nullptr);
            return;
        }
        if (const AstUnpackArrayDType* const arrayp = VN_CAST(dtypep, UnpackArrayDType)) {
            for (int i = 0; i < arrayp->declRange().elements(); ++i) {
                AstNodeExpr* const subLhsp = new AstArraySel{flp, lhsp->cloneTreePure(false), i};
                AstNodeExpr* const subRhsp
                    = rhsp ? new AstArraySel{flp, rhsp->cloneTreePure(false), i} : nullptr;
                collectAggregateLeaves(subLhsp, subRhsp, out);
                VL_DO_DANGLING(subLhsp->deleteTree(), subLhsp);
                if (subRhsp) VL_DO_DANGLING(subRhsp->deleteTree(), subRhsp);
            }
            return;
        }
        const AstNodeUOrStructDType* const structp = VN_CAST(dtypep, NodeUOrStructDType);
        if (structp && !structp->packed()) {
            for (AstMemberDType* memberp = structp->membersp(); memberp;
                 memberp = VN_AS(memberp->nextp(), MemberDType)) {
                AstStructSel* const subLhsp
                    = new AstStructSel{flp, lhsp->cloneTreePure(false), memberp->name()};
                subLhsp->dtypep(memberp->dtypep());
                AstStructSel* subRhsp = nullptr;
                if (rhsp) {
                    subRhsp = new AstStructSel{flp, rhsp->cloneTreePure(false), memberp->name()};
                    subRhsp->dtypep(memberp->dtypep());
                }
                collectAggregateLeaves(subLhsp, subRhsp, out);
                VL_DO_DANGLING(subLhsp->deleteTree(), subLhsp);
                if (subRhsp) VL_DO_DANGLING(subRhsp->deleteTree(), subRhsp);
            }
            return;
        }
        out.emplace_back(lhsp->cloneTreePure(false), rhsp ? rhsp->cloneTreePure(false) : nullptr);
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

// Rewrite a force or release that names a whole aggregate into one per leaf, so that every leaf
// gets its own slot, its own shadow value and a shadow of its own type.  Reads reach a leaf
// through a member or element path, and only a per-leaf target lets such a read see the force.
static void expandAggregateTargets(AstNetlist* nodep) {
    std::vector<AstNodeStmt*> stmtps;
    nodep->foreach([&](AstNodeStmt* stmtp) {
        if (VN_IS(stmtp, AssignForce) || VN_IS(stmtp, Release)) stmtps.push_back(stmtp);
    });
    for (AstNodeStmt* const stmtp : stmtps) {
        AstAssignForce* const forcep = VN_CAST(stmtp, AssignForce);
        AstNodeExpr* const lhsp = forcep ? forcep->lhsp() : VN_AS(stmtp, Release)->lhsp();
        if (AstNode* const badp = ForceState::unsupportedPathSelector(lhsp)) {
            badp->v3warn(E_UNSUPPORTED,
                         "Unsupported: Force or release of "
                             << badp->prettyTypeName()
                             << ", as only member and element selections have a force target");
            VL_DO_DANGLING(stmtp->unlinkFrBack()->deleteTree(), stmtp);
            continue;
        }
        AstNodeExpr* const rhsp = forcep ? forcep->rhsp() : nullptr;
        if (ForceState::forceSlots(lhsp->dtypep()) <= 1) continue;
        // A uniform unpacked array is one stride that VlForceVec addresses on its own, so it
        // needs no per-leaf targets and keeps the generated code independent of its size
        if (!ForceState::holdsUnpackedStructOrUnion(lhsp->dtypep())) continue;
        // The right-hand side is cloned once per leaf, which is only safe when evaluating it
        // more than once cannot be observed.  V3Task lifts an impure right-hand side into a
        // temporary before this point, so one should never arrive here.
        if (rhsp && !rhsp->isPure()) rhsp->v3fatalSrc("Force of an aggregate from an impure RHS");

        std::vector<std::pair<AstNodeExpr*, AstNodeExpr*>> leaves;
        ForceState::collectAggregateLeaves(lhsp, rhsp, leaves);
        if (leaves.empty()) continue;

        FileLine* const flp = stmtp->fileline();
        AstNodeStmt* headp = nullptr;
        AstNodeStmt* tailp = nullptr;
        for (const auto& leaf : leaves) {
            AstNodeStmt* const leafStmtp
                = forcep
                      ? static_cast<AstNodeStmt*>(new AstAssignForce{flp, leaf.first, leaf.second})
                      : static_cast<AstNodeStmt*>(new AstRelease{flp, leaf.first});
            if (tailp) {
                tailp->addNextHere(leafStmtp);
            } else {
                headp = leafStmtp;
            }
            tailp = leafStmtp;
        }
        stmtp->replaceWith(headp);
        VL_DO_DANGLING(stmtp->deleteTree(), stmtp);
    }
}

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
                AstNodeExpr* const forceExprp = new AstOr{
                    flp, new AstAnd{flp, enSelp, valSelp},
                    new AstAnd{flp, new AstNot{flp, enSelp->cloneTreePure(false)}, origSelp}};
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

        // Resolve force bookkeeping range/padding for the LHS shape.
        ForceState::ForceRange rangeInfo
            = m_state.getForceRangeInfo(nodep->lhsp(), forcedVarp, true);

        // Keep narrow rhs, VlForceVec blends unpacked-array bit-select forces at read time
        AstNodeExpr* const rhsExprp = nodep->rhsp()->cloneTreePure(false);

        m_state.addForceAssignment(forcedVarp, lhsVarRefp->varScopep(), rhsExprp, nodep,
                                   rangeInfo.m_rangeLsb, rangeInfo.m_rangeMsb, rangeInfo.m_padLsb,
                                   rangeInfo.m_padMsb, nodep->lhsp()->cloneTreePure(false));
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
                      ? static_cast<AstNodeExpr*>(new AstOr{
                            flp, new AstAnd{flp, enRefp, valRefp},
                            new AstAnd{flp, new AstNot{flp, enRefp->cloneTreePure(false)}, refp}})
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
            int rangeLsb = 0;
            int rangeMsb = padMsb;
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
        if (!nodep->user2() && varInfo->m_forceEnVscp && varInfo->m_forceValVscp && wholeSlotVar) {
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

        // Verilog pseudocode:
        //   forceVec.addForce(range_lsb, range_msb, &forceRHS[id], rhs_lsb);
        const AstSel* const selLhsp = VN_CAST(lhsp, Sel);
        // A slot holds one whole leaf, so a bit or part select of that leaf has to carry its
        // bit range alongside the slot ordinal
        const bool arrayBitSel
            = ForceState::usesForceSlots(forcedVarp) && selLhsp
              && ForceState::isBitwiseDType(selLhsp->fromp())
              && (info.m_padMsb - info.m_padLsb + 1) < selLhsp->fromp()->width();
        AstNodeExpr* const rhsDatap = ForceState::buildRhsDataExpr(flp, info);
        AstCExpr* const rhsAddrp = new AstCExpr{flp};
        rhsAddrp->add("&(");
        rhsAddrp->add(rhsDatap);
        rhsAddrp->add(")");
        AstCMethodHard* const addForceCallp = new AstCMethodHard{
            flp, new AstVarRef{flp, varInfo->m_forceVecVscp, VAccess::WRITE}, VCMethod::FORCE_ADD,
            ForceState::makeConst32(flp, info.m_rangeLsb)};
        addForceCallp->addPinsp(ForceState::makeConst32(flp, info.m_rangeMsb));
        addForceCallp->addPinsp(rhsAddrp);
        addForceCallp->addPinsp(
            ForceState::makeConst32(flp, arrayBitSel ? info.m_padLsb : info.m_rangeLsb));
        if (arrayBitSel) {
            addForceCallp->addPinsp(ForceState::makeConst32(flp, info.m_padLsb));
            addForceCallp->addPinsp(ForceState::makeConst32(flp, info.m_padMsb));
            addForceCallp->addPinsp(ForceState::makeConst32(flp, selLhsp->fromp()->width()));
        }
        addForceCallp->dtypeSetVoid();
        AstNodeStmt* const stmtp = addForceCallp->makeStmt();

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
            stmtp->addNextHere(m_state.createForceRdUpdateStmt(*varInfo));
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
        if (!varInfo) {
            VL_DO_DANGLING(pushDeletep(nodep->unlinkFrBack()), nodep);
            return;
        }
        UASSERT_OBJ(!varInfo->m_forces.empty(), nodep, "Var info for variable with no forces");

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
            releaseCallp->addPinsp(ForceState::makeConst32(flp, rangeInfo.m_padLsb));
            releaseCallp->addPinsp(ForceState::makeConst32(flp, rangeInfo.m_padMsb));
        }
        releaseCallp->dtypeSetVoid();
        // forceVec.release(range_lsb, range_msb [, bit_lsb, bit_msb]);
        AstNodeStmt* const releasep = releaseCallp->makeStmt();

        AstAssign* clearEnp = nullptr;
        // Releases must also clear the external/public force-enable, but only for
        // directly forceable variables and only for non-array-select cases that use that external
        // force.
        if (releasedVarp->isForceable() && varInfo->m_forceEnVscp
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
            // A slot-indexed variable recovers its current forced value through the same slot
            // ordinal the force used, so member and element paths agree with each other.
            // if (!continuously_driven) lhs = force_read_current(lhs_path);
            // forceVec.release(range);
            AstNodeExpr* forceReadp = nullptr;
            if (ForceState::usesForceSlots(releasedVarp)) {
                AstNodeExpr* const leafp = selp ? selp->fromp() : lhsp;
                forceReadp = ForceState::forceSlots(leafp->dtypep()) > 1
                                 ? m_state.createForceReadRangeExpression(*varInfo, leafp,
                                                                          rangeInfo.m_rangeLsb)
                                 : m_state.createForceReadIndexExpression(
                                       *varInfo, leafp,
                                       ForceState::makeConst32(flp, rangeInfo.m_rangeLsb));
                if (selp) forceReadp = ForceState::rebuildSelPath(lhsp, forceReadp);
            } else {
                forceReadp
                    = selp ? ForceState::rebuildSelPath(
                                 lhsp, m_state.createForceReadExpression(*varInfo, lhsVarRefp))
                           : m_state.createForceReadExpression(*varInfo, lhsVarRefp);
            }
            AstAssign* const assignp = new AstAssign{flp, lhsp->cloneTreePure(false), forceReadp};
            assignp->addNextHere(stmtListp);
            stmtListp = assignp;
        }

        if (varInfo->m_forceRdVscp) stmtListp->addNext(m_state.createForceRdUpdateStmt(*varInfo));

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
        AstNodeExpr* leafp = nodep;
        while (const AstSel* const selp = VN_CAST(leafp, Sel)) leafp = selp->fromp();
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
        if (!ForceState::usesForceSlots(baseRefp->varp())) return false;
        if (!baseRefp->access().isReadOnly()) return false;
        // An intermediate selection still naming an aggregate is not one leaf.  Rebase it onto
        // the whole-value shadow, which merges every leaf's force, and keep iterating so any
        // index expressions inside it are still substituted.
        if (ForceState::forceSlots(leafp->dtypep()) > 1) {
            if (varInfo->m_slotRdVscp) {
                if (m_inLogic && m_stmtp && m_slotRdRefreshed.emplace(m_stmtp, varInfo).second) {
                    m_stmtp->addHereThisAsNext(
                        m_state.createSlotRdUpdateStmt(*varInfo, varInfo->m_slotRdVscp));
                }
                baseRefp->varp(varInfo->m_slotRdVscp->varp());
                baseRefp->varScopep(varInfo->m_slotRdVscp);
                ForceState::markNonReplaceable(baseRefp);
            }
            return false;
        }

        // Substitute forced reads inside the index expressions before anything is cloned, so
        // the fallback value and the slot ordinal use the same, force-aware index.  An index
        // is an ordinary read, including when it reads the same array as in 'mem[mem[0]]'.
        for (AstArraySel* const selp : ForceState::arraySelsOf(leafp)) {
            iterateAndNextNull(selp->bitp());
        }
        FileLine* const flp = nodep->fileline();
        AstNodeExpr* const readExprp = m_state.createForceReadIndexExpression(
            *varInfo, leafp, ForceState::buildForceOrdinalExpr(flp, leafp));
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
                m_stmtp->addNextHere(m_state.createForceRdUpdateStmt(*varInfo));
            }
            return;
        }

        // On a slot-indexed variable a member or element path is rewritten at its outermost
        // selector, which needs the base reference left as it is.  A bit-range variable
        // instead has its whole value read here, and the selects above pick from that.
        if (ForceState::usesForceSlots(nodep->varp()) && ForceState::isPathFromOfSelector(nodep)) {
            return;
        }

        UASSERT_OBJ(!varInfo->m_forces.empty(), nodep, "Var info for variable with no forces");

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
                    m_stmtp->addHereThisAsNext(
                        m_state.createSlotRdUpdateStmt(*varInfo, varInfo->m_slotRdVscp));
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
    expandAggregateTargets(nodep);
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
    expandAggregateTargets(nodep);
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
