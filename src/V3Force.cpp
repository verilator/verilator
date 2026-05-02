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
//  For each forceable var/net "<name>":
//    - Create <name>__VforceVec (VlForceVec) to track active force ranges
//    - Create <name>__VforceRHS<ID> vars to hold RHS shadow values
//    - Add continuous assignments: <name>__VforceRHS<ID> = RHS
//
//  For each `force <name>[range] = <RHS>` with ID:
//    - <name>__VforceVec.addForce(lsb, msb, &__VforceRHS, rhsLsb)
//
//  For each `release <name>[range]`:
//    - If not continuously driven: <name> = VlForceVec::read(<name>, __VforceVec)
//    - <name>__VforceVec.release(lsb, msb)
//
//  For each read of <name>:
//    - Replace with: VlForceVec::read(<name>, __VforceVec)
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Force.h"

#include "V3AstUserAllocator.h"
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
        bool m_hasArraySel = false;  // If this has an array select on LHS
        AstVarScope* m_rhsVarVscp = nullptr;  // Scope of the var containing RHSID
        AstNodeExpr* m_rhsExprp = nullptr;  // Expression on RHS of this force assignment

        ForceInfo() = default;
        ForceInfo(int rangeLsb, int rangeMsb, int padLsb, int padMsb, int forceId,
                  bool hasArraySel, AstVarScope* rhsVarVscp, AstNodeExpr* rhsExprp)
            : m_forceId{forceId}
            , m_hasArraySel{hasArraySel}
            , m_rhsVarVscp{rhsVarVscp}
            , m_rhsExprp{rhsExprp} {
            m_rangeLsb = rangeLsb;
            m_rangeMsb = rangeMsb;
            m_padLsb = padLsb;
            m_padMsb = padMsb;
        }
    };

    struct VarForceInfo final {
        AstVarScope* m_forceVecVscp = nullptr;
        AstVarScope* m_forceRdVscp = nullptr;
        AstVarScope* m_forceEnVscp = nullptr;
        AstVarScope* m_forceValVscp = nullptr;
        AstVarScope* m_varVscp = nullptr;
        AstScope* m_scopep = nullptr;
        std::unordered_map<AstAssignForce*, ForceInfo> m_forces;
        std::unordered_map<string, int> m_forcePathToIndex;
        int m_nextForcePathIndex = 1;  // Start at 1 so 0 can be the base path (whole signal)

    private:
        static void buildForcePathKeyRecurse(AstNodeExpr* nodep, string& out) {
            if (VN_IS(nodep, VarRef)) return;
            if (const AstSel* const selp = VN_CAST(nodep, Sel)) {
                buildForcePathKeyRecurse(selp->fromp(), out);
                out += "|S" + cvtToStr(selp->lsbConst()) + ":" + cvtToStr(selp->widthConst());
                return;
            }
            if (AstStructSel* const selp = VN_CAST(nodep, StructSel)) {
                AstNodeExpr* const fromp = selp->fromp();
                buildForcePathKeyRecurse(fromp, out);
                out += "|T" + selp->name();
                return;
            }
            nodep->v3fatalSrc("Unsupported: opaque force path selector "
                              << nodep->prettyTypeName());
        }

        static string forcePathKey(AstNodeExpr* nodep) {
            string out;
            buildForcePathKeyRecurse(nodep, out);
            return out;
        }

    public:
        int getOrCreateForcePathIndex(AstNodeExpr* nodep) {
            const auto pair
                = m_forcePathToIndex.emplace(forcePathKey(nodep), m_nextForcePathIndex);
            if (pair.second) ++m_nextForcePathIndex;
            return pair.first->second;
        }

        int findForcePathIndex(AstNodeExpr* nodep) const {
            const auto it = m_forcePathToIndex.find(forcePathKey(nodep));
            return it != m_forcePathToIndex.end() ? it->second : -1;
        }
    };

    struct ArraySelInfo final {
        std::vector<AstArraySel*> m_sels;
        bool m_hasBitSel = false;
    };

    struct ForceRangeInfo final : ForceRange {
        bool m_hasArraySel = false;
        ArraySelInfo m_arrayInfo;
    };

private:
    // NODE STATE
    //  AstVarRef::user1      -> Flag indicating not to replace reference
    //  AstAssignForce::user2 -> true if force is synthetic (externally forceable)
    const VNUser1InUse m_user1InUse;
    const VNUser2InUse m_user2InUse;

    std::unordered_map<AstVar*, VarForceInfo> m_varInfo;
    bool m_doingAssign = false;  // If true, we're processing procedural continuous assign
                                 // statements instead of force statements

public:
    ForceState(bool doingAssign)
        : m_doingAssign{doingAssign} {}
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

    static bool isOpaquePathSelector(const AstNode* nodep) {
        return VN_IS(nodep, Sel) || VN_IS(nodep, NodeSel) || VN_IS(nodep, StructSel);
    }

    static bool isOutermostOpaquePathSelector(const AstNode* nodep) {
        if (!isOpaquePathSelector(nodep)) return false;
        const AstNode* const backp = nodep->backp();
        return !backp || !isOpaquePathSelector(backp);
    }

    static AstVarRef* getOneVarRef(AstNodeExpr* forceStmtp) {
        AstNode* const basep = AstArraySel::baseFromp(forceStmtp, true);
        if (AstSampled* sampledp = VN_CAST(basep, Sampled))
            if (AstNodeExpr* exprp = VN_CAST(sampledp->exprp(), NodeExpr))
                return getOneVarRef(exprp);
        if (AstCCast* const ccastp = VN_CAST(basep, CCast)) return getOneVarRef(ccastp->lhsp());
        if (AstCMethodHard* const callp = VN_CAST(basep, CMethodHard)) {
            if (callp->pinsp()) return getOneVarRef(callp->pinsp());
        }
        AstVarRef* const varRefp = VN_CAST(basep, VarRef);
        UASSERT_OBJ(varRefp, forceStmtp, "`force` assignment has no VarRef on LHS");
        return varRefp;
    }

    ForceRangeInfo getForceRangeInfo(AstNodeExpr* lhsp, AstVar* varp,
                                     bool requireConstRangeSelect) {
        ForceRangeInfo info;
        info.m_arrayInfo = getArraySelInfo(lhsp);
        info.m_hasArraySel = !info.m_arrayInfo.m_sels.empty();

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
        if (info.m_hasArraySel) {
            // Unpacked array selections are tracked as a single flattened element index
            // inside VlForceVec, regardless of how many unpacked dimensions the source uses.
            std::vector<int> indices;
            indices.reserve(info.m_arrayInfo.m_sels.size());
            for (AstArraySel* const selp : info.m_arrayInfo.m_sels) {
                UASSERT_OBJ(VN_IS(selp->bitp(), Const), selp,
                            "Unsupported: force on non-constant array select");
                indices.push_back(VN_AS(selp->bitp(), Const)->toSInt());
            }
            info.m_rangeLsb = flattenIndex(indices, arraySelDimSizes(info.m_arrayInfo));

            info.m_rangeMsb = info.m_rangeLsb;
        } else if (isUnpackedArrayDType(varp->dtypep())) {
            lhsp->v3fatalSrc("Whole unpacked-array force/release should have been lowered via "
                             "element selections");
        }
        if (!isBitwiseDType(varp) && !info.m_hasArraySel && !VN_IS(lhsp, VarRef)) {
            // Non-bitwise member/struct paths cannot use a real bit range, so map each distinct
            // source path onto a synthetic index in VlForceVec and use that index consistently
            // for force, release, and readback.
            VarForceInfo& varInfo = getOrCreateVarInfo(varp);
            const int index = varInfo.getOrCreateForcePathIndex(lhsp);
            info.m_rangeLsb = index;
            info.m_rangeMsb = index;
        }
        return info;
    }

    AstNodeExpr* createForceReadCall(const VarForceInfo& varInfo, FileLine* flp, VCMethod method,
                                     AstNodeExpr* originalExprp, AstNode* dtypeFromp,
                                     AstNodeExpr* indexExprp) const {
        UASSERT(varInfo.m_forceVecVscp, "No forceVec for forced variable");

        originalExprp->foreach(
            [](AstVarRef* const refp) { ForceState::markNonReplaceable(refp); });
        AstNodeExpr* const origValp = castToNodeDType(originalExprp, dtypeFromp);

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
        AstNodeExpr* readExprp = nullptr;
        AstVarRef* const baseRefp = new AstVarRef{flp, varInfo.m_varVscp, VAccess::READ};
        markNonReplaceable(baseRefp);
        AstNodeExpr* const enRefp = new AstVarRef{flp, varInfo.m_forceEnVscp, VAccess::READ};
        AstNodeExpr* const valRefp = new AstVarRef{flp, varInfo.m_forceValVscp, VAccess::READ};
        if (isBitwiseDType(varInfo.m_varVscp->varp())) {
            readExprp = new AstOr{
                flp, new AstAnd{flp, enRefp, valRefp},
                new AstAnd{flp, new AstNot{flp, enRefp->cloneTreePure(false)}, baseRefp}};
        } else {
            readExprp = new AstCond{flp, enRefp, valRefp, baseRefp};
        }

        return new AstAssign{flp, new AstVarRef{flp, varInfo.m_forceRdVscp, VAccess::WRITE},
                             readExprp};
    }

    VarForceInfo& getOrCreateVarInfo(AstVar* varp) { return m_varInfo[varp]; }

    bool doingAssign() const { return m_doingAssign; }

    const VarForceInfo* getVarInfo(AstVar* varp) const {
        const auto it = m_varInfo.find(varp);
        return it != m_varInfo.end() ? &it->second : nullptr;
    }

    void addForceAssignment(AstVar* varp, AstVarScope* vscp, AstNodeExpr* rhsExprp,
                            AstAssignForce* forceStmtp, int rangeLsb, int rangeMsb, int padLsb,
                            int padMsb, bool hasArraySel) {
        v3Global.setUsesForce();
        varp->setForcedByCode();

        VarForceInfo& info = getOrCreateVarInfo(varp);
        if (!info.m_scopep) info.m_scopep = vscp->scopep();
        const int forceId = info.m_forces.size();
        FileLine* const flp = varp->fileline();
        AstScope* const scopep = vscp->scopep();
        // Allocate one force vector per variable, no matter how many individual force
        // statements later target slices/elements of that variable.
        if (!info.m_forceVecVscp) {
            AstCDType* const forceVecDtypep = new AstCDType{flp, "VlForceVec"};
            v3Global.rootp()->typeTablep()->addTypesp(forceVecDtypep);

            AstVar* const forceVecVarp = new AstVar{
                flp, VVarType::MEMBER,
                varp->name() + (m_doingAssign ? "_VassignVec" : "__VforceVec"), forceVecDtypep};
            forceVecVarp->funcLocal(false);
            forceVecVarp->isInternal(true);
            varp->addNextHere(forceVecVarp);
            info.m_forceVecVscp = new AstVarScope{flp, scopep, forceVecVarp};
            scopep->addVarsp(info.m_forceVecVscp);
        }

        info.m_forces.emplace(forceStmtp, ForceInfo{rangeLsb, rangeMsb, padLsb, padMsb, forceId,
                                                    hasArraySel, nullptr, rhsExprp});

        UINFO(3, "Added force ID " << forceId << " for " << varp->name() << " [" << rangeMsb << ":"
                                   << rangeLsb << "]\n");
    }

    static void collectArraySelInfo(AstNodeExpr* exprp, ArraySelInfo& info) {
        if (const auto* const selp = VN_CAST(exprp, Sel)) {
            info.m_hasBitSel = true;
            collectArraySelInfo(selp->fromp(), info);
        } else if (auto* const selp = VN_CAST(exprp, ArraySel)) {
            collectArraySelInfo(selp->fromp(), info);
            info.m_sels.push_back(selp);
        } else if (const auto* const memberp = VN_CAST(exprp, StructSel)) {
            collectArraySelInfo(memberp->fromp(), info);
        }
    }

    static ArraySelInfo getArraySelInfo(AstNodeExpr* exprp) {
        ArraySelInfo info;
        collectArraySelInfo(exprp, info);
        return info;
    }

    static std::vector<int> arraySelDimSizes(const ArraySelInfo& info) {
        std::vector<int> dims;
        dims.reserve(info.m_sels.size());
        for (AstArraySel* const selp : info.m_sels) {
            AstNodeDType* const dtypep = selp->fromp()->dtypep()->skipRefp();
            const AstUnpackArrayDType* const arrayp = VN_CAST(dtypep, UnpackArrayDType);
            UASSERT_OBJ(arrayp, selp, "Array select is not on unpacked array");
            dims.push_back(arrayp->declRange().elements());
        }
        return dims;
    }

    static int flattenIndex(const std::vector<int>& indices, const std::vector<int>& dimSizes) {
        UASSERT(indices.size() == dimSizes.size(), "Array index and dimension size mismatch");
        int index = 0;
        int stride = 1;
        for (int i = static_cast<int>(indices.size()) - 1; i >= 0; --i) {
            index += indices[i] * stride;
            stride *= dimSizes[i];
        }
        return index;
    }

    static AstNodeExpr* buildFlattenIndexExpr(FileLine* flp, const ArraySelInfo& info) {
        const std::vector<int> dimSizes = arraySelDimSizes(info);
        std::vector<int> constIndices;
        constIndices.reserve(info.m_sels.size());
        for (AstArraySel* const selp : info.m_sels) {
            constIndices.push_back(VN_AS(selp->bitp(), Const)->toSInt());
        }
        return makeConst32(flp, flattenIndex(constIndices, dimSizes));
    }

    static AstNodeExpr* buildRhsDataExpr(FileLine* flp, const ForceInfo& finfo) {
        UASSERT(finfo.m_rhsVarVscp, "RHS var scope not assigned");
        return new AstVarRef{flp, finfo.m_rhsVarVscp, VAccess::READ};
    }

    AstNodeStmt* createRhsUpdateStmts(const VarForceInfo& info) const {
        AstNodeStmt* stmtsp = nullptr;
        std::vector<const ForceInfo*> forceps;
        forceps.reserve(info.m_forces.size());
        for (const auto& fit : info.m_forces) forceps.push_back(&fit.second);
        std::sort(forceps.begin(), forceps.end(), [](const ForceInfo* ap, const ForceInfo* bp) {
            return ap->m_forceId < bp->m_forceId;
        });
        for (const ForceInfo* const finfop : forceps) {
            UASSERT(finfop->m_rhsVarVscp, "RHS var scope not assigned");
            UASSERT(finfop->m_rhsExprp, "Missing RHS expression for ForceInfo");
            AstAssign* const assignp
                = new AstAssign{finfop->m_rhsExprp->fileline(),
                                new AstVarRef{finfop->m_rhsExprp->fileline(), finfop->m_rhsVarVscp,
                                              VAccess::WRITE},
                                finfop->m_rhsExprp->cloneTreePure(false)};
            stmtsp = AstNode::addNextNull(stmtsp, assignp);
        }
        return stmtsp;
    }

    void finalizeRhsVars() {
        for (auto& it : m_varInfo) {
            AstVar* const varp = it.first;
            VarForceInfo& info = it.second;
            if (info.m_forces.empty()) continue;

            AstScope* const scopep = info.m_scopep;
            UASSERT_OBJ(scopep, varp, "Missing scope for force RHS vars");

            FileLine* const flp = varp->fileline();
            // Process force entries in stable force-id order.
            std::vector<ForceInfo*> forceps;
            forceps.reserve(info.m_forces.size());
            for (auto& fit : info.m_forces) forceps.push_back(&fit.second);
            std::sort(forceps.begin(), forceps.end(),
                      [](const ForceInfo* ap, const ForceInfo* bp) {
                          return ap->m_forceId < bp->m_forceId;
                      });

            for (ForceInfo* const finfop : forceps) {
                ForceInfo& finfo = *finfop;
                UASSERT_OBJ(finfo.m_rhsExprp, varp, "Missing RHS expression for ForceInfo");

                // Create per-force temporary storage for the captured RHS value.
                AstVar* const rhsVarp
                    = new AstVar{flp, VVarType::VAR,
                                 varp->name() + (doingAssign() ? "_VassignRHS" : "__VforceRHS")
                                     + std::to_string(finfo.m_forceId),
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

            if (info.m_forceRdVscp) {
                AstActive* const activeInitp = new AstActive{
                    flp, "force-init",
                    new AstSenTree{flp, new AstSenItem{flp, AstSenItem::Static{}}}};
                activeInitp->senTreeStorep(activeInitp->sentreep());
                AstAssign* const initEnp
                    = new AstAssign{flp, new AstVarRef{flp, info.m_forceEnVscp, VAccess::WRITE},
                                    makeZeroConst(varp, info.m_forceEnVscp->width())};
                initEnp->addNextHere(createForceRdUpdateStmt(info));
                activeInitp->addStmtsp(new AstInitial{flp, initEnp});
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

    const ForceInfo& getForceInfo(AstAssignForce* forceStmtp) const {
        AstVar* varp = getOneVarRef(forceStmtp->lhsp())->varp();
        auto it = m_varInfo.find(varp);
        UASSERT(it != m_varInfo.end(), "Force info not found for variable");
        auto it2 = it->second.m_forces.find(forceStmtp);
        UASSERT(it2 != it->second.m_forces.end(), "Force statement not found");
        return it2->second;
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

    static AstNodeExpr* cloneLValue(AstNodeExpr* lhsp) {
        AstNodeExpr* const clonep = lhsp->cloneTreePure(false);
        clonep->foreach([](AstNodeVarRef* const refp) { refp->access(VAccess::WRITE); });
        return clonep;
    }
};

//######################################################################
// ForceDiscoveryVisitor - Discover force statements

class ForceDiscoveryVisitor final : public VNVisitorConst {
    ForceState& m_state;

    void visit(AstAssignForce* nodep) override {
        if (nodep->user2()) return;  // External force statements are pre-registered.
        UINFO(2, "Discovering force statement: " << nodep << "\n");

        AstVarRef* const lhsVarRefp = m_state.getOneVarRef(nodep->lhsp());
        AstVar* const forcedVarp = lhsVarRefp->varp();
        UASSERT(forcedVarp, "VarRef missing Varp");

        // Resolve force bookkeeping range/padding for the LHS shape.
        ForceState::ForceRangeInfo rangeInfo
            = m_state.getForceRangeInfo(nodep->lhsp(), forcedVarp, true);

        // Start from a cloned RHS expression; adjust below for partial bit selects.
        const AstSel* const selLhsp = VN_CAST(nodep->lhsp(), Sel);
        AstNodeExpr* rhsExprp = nodep->rhsp()->cloneTreePure(false);

        // For bitwise selects inside arrays, merge updated bits with preserved base bits.
        if (rangeInfo.m_hasArraySel && rangeInfo.m_arrayInfo.m_hasBitSel && selLhsp
            && ForceState::isBitwiseDType(selLhsp->fromp())) {
            AstNodeExpr* const baseExprp = selLhsp->fromp()->cloneTreePure(false);
            baseExprp->foreach(
                [](AstVarRef* const refp) { ForceState::markNonReplaceable(refp); });

            // Pad the selected value back to full base width before masking/or-ing.
            rhsExprp = ForceState::zeroPadToBaseWidth(rhsExprp, selLhsp->fromp()->width(),
                                                      rangeInfo.m_padLsb, rangeInfo.m_padMsb);

            // Keep untouched base bits and insert the newly forced bit range.
            // rhsExpr = (baseExpr & ~mask(range)) | (zeroPad(force_rhs) & mask(range));
            AstConst* const maskConstp = ForceState::makeRangeMaskConst(
                nodep->lhsp(), selLhsp->fromp()->width(), rangeInfo.m_padLsb, rangeInfo.m_padMsb);
            AstNodeExpr* const maskedOldp
                = new AstAnd{nodep->lhsp()->fileline(), baseExprp,
                             new AstNot{nodep->lhsp()->fileline(), maskConstp}};
            rhsExprp = new AstOr{nodep->lhsp()->fileline(), maskedOldp, rhsExprp};
        }

        m_state.addForceAssignment(forcedVarp, lhsVarRefp->varScopep(), rhsExprp, nodep,
                                   rangeInfo.m_rangeLsb, rangeInfo.m_rangeMsb, rangeInfo.m_padLsb,
                                   rangeInfo.m_padMsb, rangeInfo.m_hasArraySel);
    }

    void visit(AstVarScope* nodep) override {
        if (nodep->varp()->isForceable()) {
            if (VN_IS(nodep->varp()->dtypeSkipRefp(), UnpackArrayDType)) {
                nodep->varp()->v3warn(
                    E_UNSUPPORTED,
                    "Unsupported: Forcing unpacked arrays: " << nodep->varp()->name());  // (#4735)
                return;
            }

            const AstBasicDType* const bdtypep = nodep->varp()->basicp();
            if (bdtypep && bdtypep->keyword() == VBasicDTypeKwd::STRING) {
                nodep->varp()->v3error(
                    "Forcing strings is not permitted: " << nodep->varp()->name());
            }

            // Create per-signal storage for force enable/value state.
            AstVar* const varp = nodep->varp();
            FileLine* const flp = varp->fileline();
            AstVar* const rdVarp
                = new AstVar{flp, VVarType::WIRE, varp->name() + "__VforceRd", varp->dtypep()};
            rdVarp->noSubst(true);
            rdVarp->sigPublic(true);
            AstNodeDType* const enDtypep
                = ForceState::isBitwiseDType(varp) ? varp->dtypep() : varp->findBitDType();
            AstVar* const enVarp
                = new AstVar{flp, VVarType::VAR, varp->name() + "__VforceEn", enDtypep};
            enVarp->sigUserRWPublic(true);
            AstVar* const valVarp
                = new AstVar{flp, VVarType::VAR, varp->name() + "__VforceVal", varp->dtypep()};
            valVarp->sigUserRWPublic(true);
            varp->addNextHere(rdVarp);
            varp->addNextHere(enVarp);
            varp->addNextHere(valVarp);
            AstVarScope* const rdVscp = new AstVarScope{flp, nodep->scopep(), rdVarp};
            AstVarScope* const enVscp = new AstVarScope{flp, nodep->scopep(), enVarp};
            AstVarScope* const valVscp = new AstVarScope{flp, nodep->scopep(), valVarp};
            nodep->scopep()->addVarsp(rdVscp);
            nodep->scopep()->addVarsp(enVscp);
            nodep->scopep()->addVarsp(valVscp);

            // Register force metadata so later transforms can find these helper vars.
            ForceState::VarForceInfo& info = m_state.getOrCreateVarInfo(varp);
            info.m_forceRdVscp = rdVscp;
            info.m_forceEnVscp = enVscp;
            info.m_forceValVscp = valVscp;
            info.m_varVscp = nodep;

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
                                       padMsb, false);
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
        const ForceState::VarForceInfo* const varInfo = m_state.getVarInfo(forcedVarp);
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
        // Don't do this for array selections; those are represented only in VlForceVec.
        if (!nodep->user2() && varInfo->m_forceEnVscp && varInfo->m_forceValVscp
            && !info.m_hasArraySel) {
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
        addForceCallp->addPinsp(ForceState::makeConst32(flp, info.m_rangeLsb));
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

        const ForceState::VarForceInfo* const varInfo = m_state.getVarInfo(releasedVarp);
        if (!varInfo) {
            VL_DO_DANGLING(pushDeletep(nodep->unlinkFrBack()), nodep);
            return;
        }
        UASSERT_OBJ(!varInfo->m_forces.empty(), nodep, "Var info for variable with no forces");

        FileLine* const flp = nodep->fileline();

        const ForceState::ForceRangeInfo rangeInfo
            = m_state.getForceRangeInfo(lhsp, releasedVarp, false);

        AstCMethodHard* const releaseCallp = new AstCMethodHard{
            flp, new AstVarRef{flp, varInfo->m_forceVecVscp, VAccess::WRITE},
            VCMethod::FORCE_RELEASE, ForceState::makeConst32(flp, rangeInfo.m_rangeLsb)};
        releaseCallp->addPinsp(ForceState::makeConst32(flp, rangeInfo.m_rangeMsb));
        releaseCallp->dtypeSetVoid();
        // forceVec.release(range_lsb, range_msb);
        AstNodeStmt* const releasep = releaseCallp->makeStmt();

        AstAssign* clearEnp = nullptr;
        // Releases must also clear the external/public force-enable, but only for
        // directly forceable variables and only for non-array-select cases that use that external
        // force.
        if (releasedVarp->isForceable() && varInfo->m_forceEnVscp && !rangeInfo.m_hasArraySel) {
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
        AstNodeExpr* const basep = selp ? selp->fromp() : lhsp;

        AstNode* stmtListp = releasep;
        if (clearEnp) {
            clearEnp->addNextHere(stmtListp);
            stmtListp = clearEnp;
        }

        // IEEE 1800-2023 10.6.2: When released, if the variable is not continuously driven,
        // it maintains its current value until the next procedural assignment.
        if (!releasedVarp->isContinuously()) {
            // Member/struct paths on non-bitwise types do not lower to a plain VarRef/bit range,
            // so their current forced value is recovered via the same synthetic path index.
            // if (!continuously_driven) lhs = force_read_current(lhs_path);
            // forceVec.release(range);
            const bool hasOpaquePath = !ForceState::isBitwiseDType(releasedVarp)
                                       && !rangeInfo.m_hasArraySel && !VN_IS(lhsp, VarRef);
            AstNodeExpr* forceReadp = nullptr;
            if (hasOpaquePath) {
                forceReadp = m_state.createForceReadIndexExpression(
                    *varInfo, lhsp, ForceState::makeConst32(flp, rangeInfo.m_rangeLsb));
            } else if (rangeInfo.m_hasArraySel) {
                forceReadp = m_state.createForceReadIndexExpression(
                    *varInfo, basep,
                    ForceState::buildFlattenIndexExpr(flp, rangeInfo.m_arrayInfo));
                if (selp) { forceReadp = ForceState::rebuildSelPath(lhsp, forceReadp); }
            } else {
                forceReadp
                    = selp ? ForceState::rebuildSelPath(
                                 lhsp, m_state.createForceReadExpression(*varInfo, lhsVarRefp))
                           : m_state.createForceReadExpression(*varInfo, lhsVarRefp);
            }
            AstAssign* const assignp
                = new AstAssign{flp, ForceState::cloneLValue(lhsp), forceReadp};
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
    AstNodeStmt* m_stmtp = nullptr;
    bool m_inLogic = false;
    std::unordered_set<AstNodeStmt*> m_refreshedStmtps;

    void refreshBeforeStmt(const ForceState::VarForceInfo& varInfo) {
        if (!m_stmtp || m_refreshedStmtps.count(m_stmtp)) return;
        AstNodeStmt* const updatep = m_state.createRhsUpdateStmts(varInfo);
        if (!updatep) return;
        m_stmtp->addHereThisAsNext(updatep);
        m_refreshedStmtps.insert(m_stmtp);
    }

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
    }
    void visit(AstAssignCont* nodep) override {
        VL_RESTORER(m_stmtp);
        m_stmtp = nodep;
        iterateAndNextNull(nodep->timingControlp());
        iterate(nodep->rhsp());
    }
    void visit(AstDeassign*) override {}
    void visit(AstCMethodHard* nodep) override {
        if (m_state.doingAssign() && nodep->method() == VCMethod::FORCE_READ && nodep->pinsp()) {
            AstVarRef* const baseRefp = m_state.getOneVarRef(nodep->pinsp());
            AstVar* const varp = baseRefp->varp();
            const ForceState::VarForceInfo* const varInfo = m_state.getVarInfo(varp);
            const AstVarRef* const fromRefp = VN_CAST(nodep->fromp(), VarRef);
            if (varInfo && (!fromRefp || fromRefp->varScopep() != varInfo->m_forceVecVscp)) {
                refreshBeforeStmt(*varInfo);
                AstNodeExpr* const assignReadp
                    = m_state.createForceReadExpression(*varInfo, baseRefp);
                AstNodeExpr* const oldPinp = nodep->pinsp();
                oldPinp->replaceWith(assignReadp);
                VL_DO_DANGLING(pushDeletep(oldPinp), oldPinp);
                iterate(nodep->fromp());
                return;
            }
        }
        iterateChildren(nodep);
    }
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
    void visit(AstArraySel* nodep) override {
        if (nodep->backp() && VN_IS(nodep->backp(), ArraySel)) {
            // Only the outermost unpacked array selection should become a force-aware read;
            // inner nested selections are folded into the final flattened index.
            iterateChildren(nodep);
            return;
        }

        AstVarRef* const baseRefp = m_state.getOneVarRef(nodep);
        AstVar* const varp = baseRefp->varp();
        const ForceState::VarForceInfo* const varInfo = m_state.getVarInfo(varp);
        // Skip non-forceable reads, reads we intentionally protected earlier, and intermediate
        // selections that still evaluate to an unpacked array rather than a scalar element.
        if (ForceState::isNotReplaceable(baseRefp) || !varInfo
            || !ForceState::isUnpackedArrayDType(varp->dtypep())
            || VN_IS(nodep->dtypep()->skipRefp(), UnpackArrayDType)) {
            iterateChildren(nodep);
            return;
        }

        if (!baseRefp->access().isReadOnly()) {
            iterateChildren(nodep);
            return;
        }
        const ForceState::ArraySelInfo arrayInfo = ForceState::getArraySelInfo(nodep);
        AstNodeExpr* const indexExprp
            = ForceState::buildFlattenIndexExpr(nodep->fileline(), arrayInfo);
        refreshBeforeStmt(*varInfo);
        AstNodeExpr* const readExprp
            = m_state.createForceReadIndexExpression(*varInfo, nodep, indexExprp);
        nodep->replaceWith(readExprp);
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }

    void visit(AstVarRef* nodep) override {
        if (ForceState::isNotReplaceable(nodep)) return;
        if (nodep->backp() && VN_IS(nodep->backp(), ArraySel)) return;

        AstVar* const varp = nodep->varp();
        const ForceState::VarForceInfo* const varInfo = m_state.getVarInfo(varp);
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

        // For opaque member/struct paths we rewrite the outer path node instead of the base
        // VarRef, so leave the base reference alone and let visit(AstNode*) handle it.
        if (nodep->backp() && (VN_IS(nodep->backp(), Sel) || VN_IS(nodep->backp(), StructSel))
            && !ForceState::isBitwiseDType(nodep->varp())
            && !ForceState::isUnpackedArrayDType(nodep->varp()->dtypep())) {
            return;
        }

        UASSERT_OBJ(!varInfo->m_forces.empty(), nodep, "Var info for variable with no forces");

        if (nodep->access().isRW()) {
            nodep->v3warn(E_UNSUPPORTED,
                          "Unsupported: Signals used via read-write reference cannot be forced");
        } else if (nodep->access().isReadOnly()) {
            refreshBeforeStmt(*varInfo);
            ForceState::markNonReplaceable(nodep);
            AstNodeExpr* const readExprp = m_state.createForceReadExpression(*varInfo, nodep);
            nodep->replaceWith(readExprp);
            VL_DO_DANGLING(pushDeletep(nodep), nodep);
        }
    }
    void visit(AstNode* nodep) override {
        if (ForceState::isOutermostOpaquePathSelector(nodep)) {
            // Handle the whole opaque path at its outermost node so we can assign one stable
            // synthetic force-path index to the full selection/member chain.
            AstNodeExpr* const exprp = VN_AS(nodep, NodeExpr);
            AstNode* const basep = AstArraySel::baseFromp(exprp, true);
            AstVarRef* const baseRefp = VN_CAST(basep, VarRef);
            if (baseRefp) {
                AstVar* const varp = baseRefp->varp();
                if (!ForceState::isBitwiseDType(varp)
                    && !ForceState::isUnpackedArrayDType(varp->dtypep())) {
                    const ForceState::VarForceInfo* const varInfo = m_state.getVarInfo(varp);
                    if (!ForceState::isNotReplaceable(baseRefp) && varInfo) {
                        const int forcePathIndex = varInfo->findForcePathIndex(exprp);
                        if (forcePathIndex >= 0) {
                            if (!baseRefp->access().isReadOnly()) return;
                            refreshBeforeStmt(*varInfo);
                            AstNodeExpr* const readExprp = m_state.createForceReadIndexExpression(
                                *varInfo, exprp,
                                ForceState::makeConst32(nodep->fileline(), forcePathIndex));
                            nodep->replaceWith(readExprp);
                            VL_DO_DANGLING(pushDeletep(nodep), nodep);
                            return;
                        }
                    }
                }
            }
        }
        iterateChildren(nodep);
    }

public:
    explicit ForceReplaceVisitor(AstNetlist* nodep, const ForceState& state)
        : m_state{state} {
        iterateAndNextNull(nodep->modulesp());
    }
};
//######################################################################
//

//######################################################################
// V3Force - Main entry point

void V3Force::forceAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ":\n");
    if (!v3Global.hasForceableSignals()) return;
    ForceState state{false};
    { ForceDiscoveryVisitor{nodep, state}; }
    state.finalizeRhsVars();
    { ForceConvertVisitor{nodep, state}; }
    { ForceReplaceVisitor{nodep, state}; }
    V3Global::dumpCheckGlobalTree("force", 0, dumpTreeEitherLevel() >= 3);
}

void V3Force::assignAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ":\n");
    if (!v3Global.hasAssignDeassign()) return;
    std::vector<AstAssignCont*> assignContps;
    nodep->foreach([&](AstAssignCont* assignp) { assignContps.push_back(assignp); });
    for (AstAssignCont* const assignp : assignContps) {
        assignp->replaceWith(new AstAssignForce{assignp->fileline(),
                                                assignp->lhsp()->unlinkFrBack(),
                                                assignp->rhsp()->unlinkFrBack()});
        assignp->deleteTree();
    }

    std::vector<AstDeassign*> deassignps;
    nodep->foreach([&](AstDeassign* deassignp) { deassignps.push_back(deassignp); });
    for (AstDeassign* const deassignp : deassignps) {
        deassignp->replaceWith(
            new AstRelease{deassignp->fileline(), deassignp->lhsp()->unlinkFrBack()});
        deassignp->deleteTree();
    }
    ForceState state{true};
    { ForceDiscoveryVisitor{nodep, state}; }
    state.finalizeRhsVars();
    { ForceConvertVisitor{nodep, state}; }
    { ForceReplaceVisitor{nodep, state}; }
    V3Global::dumpCheckGlobalTree("assign-deassign", 0, dumpTreeEitherLevel() >= 3);
}
