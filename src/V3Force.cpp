// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Covert forceable signals, process force/release
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2025 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
//  V3Force's Transformations:
//
//  For each forceable net with name "<name>":
//      add 3 extra signals:
//          - <name>__VforceRd: a net with same type as signal
//          - <name>__VforceEn: a var with same type as signal, which is the bitwise force enable
//          - <name>__VforceVal: a var with same type as signal, which is the forced value
//      add an initial statement:
//          initial <name>__VforceEn = 0;
//      add a continuous assignment:
//          assign <name>__VforceRd = <name>__VforceEn ? <name>__VforceVal : <name>;
//      replace all READ references to <name> with a read reference to <name>_VforceRd
//
//  Replace each AstAssignForce with 3 assignments:
//      - <lhs>__VforceEn = 1
//      - <lhs>__VforceVal = <rhs>
//      - <lhs>__VforceRd = <rhs>
//
//  Replace each AstRelease with 1 or 2 assignments:
//      - <lhs>__VforceEn = 0
//      - <lhs>__VforceRd = <lhs> // iff lhs is a net
//
//  After each WRITE of forced LHS
//      reevaluate <lhs>__VforceRd to support immediate force/release
//
//  After each WRITE of forced RHS
//      reevaluate <lhs>__VforceVal to support VarRef rollback after release
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Force.h"

#include "V3AstUserAllocator.h"

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// Convert force/release statements and signals marked 'forceable'

class ForceState final {
    constexpr static int ELEMENTS_MAX = 1000;
    // TYPES
    struct ForceComponentsVar final {
        AstVar* const m_rdVarp;  // New variable to replace read references with
        AstVar* const m_valVarp;  // Forced value
        AstVar* const m_enVarp;  // Force enabled signal
        explicit ForceComponentsVar(AstVar* varp)
            : m_rdVarp{new AstVar{varp->fileline(), VVarType::WIRE, varp->name() + "__VforceRd",
                                  varp->dtypep()}}
            , m_valVarp{new AstVar{varp->fileline(), VVarType::VAR, varp->name() + "__VforceVal",
                                   varp->dtypep()}}
            , m_enVarp{new AstVar{varp->fileline(), VVarType::VAR, varp->name() + "__VforceEn",
                                  getEnVarpDTypep(varp)}} {
            m_rdVarp->addNext(m_enVarp);
            m_rdVarp->addNext(m_valVarp);
            varp->addNextHere(m_rdVarp);
        }
    };

public:
    struct ForceComponentsVarScope final {
        AstVarScope* const m_rdVscp;  // New variable to replace read references with
        AstVarScope* const m_valVscp;  // Forced value
        AstVarScope* const m_enVscp;  // Force enabled signal
        explicit ForceComponentsVarScope(AstVarScope* vscp, ForceComponentsVar& fcv)
            : m_rdVscp{new AstVarScope{vscp->fileline(), vscp->scopep(), fcv.m_rdVarp}}
            , m_valVscp{new AstVarScope{vscp->fileline(), vscp->scopep(), fcv.m_valVarp}}
            , m_enVscp{new AstVarScope{vscp->fileline(), vscp->scopep(), fcv.m_enVarp}} {
            m_rdVscp->addNext(m_enVscp);
            m_rdVscp->addNext(m_valVscp);
            vscp->addNextHere(m_rdVscp);

            FileLine* const flp = vscp->fileline();

            // Add initialization of the enable signal
            AstActive* const activeInitp = new AstActive{
                flp, "force-init", new AstSenTree{flp, new AstSenItem{flp, AstSenItem::Static{}}}};
            activeInitp->senTreeStorep(activeInitp->sentreep());
            vscp->scopep()->addBlocksp(activeInitp);

            AstVarRef* const enRefp = new AstVarRef{flp, m_enVscp, VAccess::WRITE};

            AstNodeStmt* toInsertp = nullptr;
            AstNodeStmt* outerStmtp = nullptr;
            std::vector<AstNodeExpr*> loopVarRefs;
            if (VN_IS(enRefp->dtypep()->skipRefp(), UnpackArrayDType)) {
                // Create a loop to set all elements of __VforceEn array to 0.
                // That loop node is then copied and used for updating elements of __VforceRd array
                if (AstUnpackArrayDType* const unpackedp
                    = VN_CAST(m_rdVscp->varp()->dtypep(), UnpackArrayDType)) {
                    std::vector<AstUnpackArrayDType*> dims = unpackedp->unpackDimensions();
                    loopVarRefs.reserve(dims.size());
                    for (size_t i = 0; i < dims.size(); i++) {
                        AstVar* const loopVarp = new AstVar{
                            flp, VVarType::MODULETEMP,
                            m_rdVscp->varp()->name() + "__VwhileIter" + std::to_string(i),
                            VFlagBitPacked{}, 32};
                        m_rdVscp->varp()->addNext(loopVarp);
                        AstVarScope* const loopVarScopep
                            = new AstVarScope{flp, m_rdVscp->scopep(), loopVarp};
                        m_rdVscp->addNext(loopVarScopep);
                        AstVarRef* const readRefp
                            = new AstVarRef{flp, loopVarScopep, VAccess::READ};
                        loopVarRefs.push_back(readRefp);
                        AstNodeStmt* const currInitp
                            = new AstAssign{flp, new AstVarRef{flp, loopVarScopep, VAccess::WRITE},
                                            new AstConst{flp, 0}};
                        if (toInsertp) {
                            toInsertp->addNextHere(currInitp);
                        } else {
                            outerStmtp = currInitp;
                        }
                        AstLoop* const currWhilep = new AstLoop{flp};
                        currInitp->addNextHere(currWhilep);
                        AstLoopTest* const loopTestp = new AstLoopTest{
                            flp, currWhilep,
                            new AstNeq{flp, readRefp,
                                       new AstConst{
                                           flp, static_cast<uint32_t>(dims[i]->elementsConst())}}};
                        currWhilep->addStmtsp(loopTestp);
                        toInsertp = loopTestp;
                        AstAssign* const currIncrp = new AstAssign{
                            flp, new AstVarRef{flp, loopVarScopep, VAccess::WRITE},
                            new AstAdd{flp, readRefp->cloneTree(false), new AstConst{flp, 1}}};
                        currWhilep->addStmtsp(currIncrp);
                    }
                }
            }
            V3Number zero{m_enVscp, m_enVscp->width()};
            AstNodeExpr* const enRhsp = new AstConst{flp, zero};
            AstNodeExpr* enLhsp = applySelects(enRefp, loopVarRefs);
            AstNodeStmt* stmtp = new AstAssign{flp, enLhsp, enRhsp};
            if (toInsertp) {
                toInsertp->addNextHere(stmtp);
                stmtp = outerStmtp;
            }
            activeInitp->addStmtsp(new AstInitial{flp, stmtp->cloneTree(true)});
            {  // Add the combinational override
                // Explicitly list dependencies for update.
                // Note: rdVscp is also needed to retrigger assignment for the first time.
                AstSenItem* const itemsp = new AstSenItem{
                    flp, VEdgeType::ET_CHANGED, new AstVarRef{flp, m_rdVscp, VAccess::READ}};
                itemsp->addNext(new AstSenItem{flp, VEdgeType::ET_CHANGED,
                                               new AstVarRef{flp, m_valVscp, VAccess::READ}});
                itemsp->addNext(new AstSenItem{flp, VEdgeType::ET_CHANGED,
                                               new AstVarRef{flp, m_enVscp, VAccess::READ}});
                AstVarRef* const origp = new AstVarRef{flp, vscp, VAccess::READ};
                ForceState::markNonReplaceable(origp);
                itemsp->addNext(new AstSenItem{flp, VEdgeType::ET_CHANGED, origp});
                AstActive* const activep
                    = new AstActive{flp, "force-update", new AstSenTree{flp, itemsp}};
                activep->senTreeStorep(activep->sentreep());

                // Reuse the statements created for __VforceEn initialization
                // and replace var ref on the LHS and the RHS
                AstVarRef* const rdRefp = new AstVarRef{flp, m_rdVscp, VAccess::WRITE};
                AstNodeExpr* const rdRhsp = forcedUpdate(vscp, loopVarRefs);
                enRefp->replaceWith(rdRefp);
                VL_DO_DANGLING(enRefp->deleteTree(), enRefp);
                enRhsp->replaceWith(rdRhsp);
                VL_DO_DANGLING(enRhsp->deleteTree(), enRhsp);

                activep->addStmtsp(new AstAlways{flp, VAlwaysKwd::ALWAYS, nullptr, stmtp});
                vscp->scopep()->addBlocksp(activep);
            }
        }
        static AstNodeExpr* applySelects(AstNodeExpr* exprp,
                                         const std::vector<AstNodeExpr*>& selectExprs) {
            for (AstNodeExpr* const sp : selectExprs) {
                exprp = new AstArraySel{exprp->fileline(), exprp, sp->cloneTreePure(false)};
            }
            return exprp;
        }
        AstNodeExpr* forcedUpdate(AstVarScope* const vscp,
                                  const std::vector<AstNodeExpr*>& selectExprs) const {
            FileLine* const flp = vscp->fileline();
            AstVarRef* origRefp = new AstVarRef{flp, vscp, VAccess::READ};
            ForceState::markNonReplaceable(origRefp);
            AstNodeExpr* const origp = applySelects(origRefp, selectExprs);
            if (ForceState::isRangedDType(vscp)) {
                return new AstOr{
                    flp,
                    new AstAnd{
                        flp,
                        applySelects(new AstVarRef{flp, m_enVscp, VAccess::READ}, selectExprs),
                        applySelects(new AstVarRef{flp, m_valVscp, VAccess::READ}, selectExprs)},
                    new AstAnd{
                        flp,
                        new AstNot{flp, applySelects(new AstVarRef{flp, m_enVscp, VAccess::READ},
                                                     selectExprs)},
                        origp}};
            }
            return new AstCond{
                flp, applySelects(new AstVarRef{flp, m_enVscp, VAccess::READ}, selectExprs),
                applySelects(new AstVarRef{flp, m_valVscp, VAccess::READ}, selectExprs), origp};
        }
    };

private:
    // NODE STATE
    //  AstVar::user1p        -> ForceComponentsVar* instance (via m_forceComponentsVar)
    //  AstVarScope::user1p   -> ForceComponentsVarScope* instance (via m_forceComponentsVarScope)
    //  AstVarRef::user2      -> Flag indicating not to replace reference
    //  AstAssign::user2      -> Flag indicating that assignment was created for AstRelease
    //  AstVarScope::user3p   -> AstAssign*, the assignment <lhs>__VforceVal = <rhs>
    const VNUser1InUse m_user1InUse;
    const VNUser2InUse m_user2InUse;
    const VNUser3InUse m_user3InUse;
    AstUser1Allocator<AstVar, ForceComponentsVar> m_forceComponentsVar;
    AstUser1Allocator<AstVarScope, ForceComponentsVarScope> m_forceComponentsVarScope;
    std::unordered_map<const AstVarScope*,
                       std::pair<std::unordered_set<AstVarScope*>, std::vector<AstVarScope*>>>
        m_valVscps;
    // `valVscp` force components of a forced RHS

    static AstNodeDType* getEnVarpDTypep(AstVar* const varp) {
        AstNodeDType* const origDTypep = varp->dtypep()->skipRefp();
        if (VN_IS(origDTypep, UnpackArrayDType)) {
            size_t elemNum = 1;
            AstNodeDType* dtp = origDTypep;
            while (AstUnpackArrayDType* const uDtp = VN_CAST(dtp, UnpackArrayDType)) {
                dtp = uDtp->subDTypep()->skipRefp();
                elemNum *= uDtp->elementsConst();
            }
            if (elemNum > ELEMENTS_MAX) {
                varp->v3warn(E_UNSUPPORTED, "Unsupported: Force of unpacked array variable with "
                                            ">= "
                                                << ELEMENTS_MAX << " elements");
            }
            bool complexElem = true;
            if (AstBasicDType* const basicp = VN_CAST(dtp, BasicDType)) {
                complexElem = basicp->isOpaque();
            }
            if (complexElem) {
                varp->v3warn(E_UNSUPPORTED, "Unsupported: Force of unpacked array variable with "
                                            "elements of complex data type");
            }
            return origDTypep;
        } else if (VN_IS(origDTypep, BasicDType)) {
            return isRangedDType(varp) ? origDTypep : varp->findBitDType();
        } else if (VN_IS(origDTypep, PackArrayDType)) {
            return origDTypep;
        } else if (const AstNodeUOrStructDType* const sdtp
                   = VN_CAST(origDTypep, NodeUOrStructDType)) {
            if (!sdtp->packed()) {
                varp->v3warn(E_UNSUPPORTED,
                             "Unsupported: Force of unpacked struct / union variable");
            }
            return origDTypep;
        } else {
            varp->v3fatalSrc("Unsupported: Force of variable of unhandled data type");
            return origDTypep;
        }
    }

public:
    // CONSTRUCTORS
    ForceState() = default;
    VL_UNCOPYABLE(ForceState);

    // STATIC METHODS
    static bool isRangedDType(AstNode* nodep) {
        // If ranged we need a multibit enable to support bit-by-bit part-select forces,
        // otherwise forcing a real or other opaque dtype and need a single bit enable.
        const AstBasicDType* const basicp = nodep->dtypep()->skipRefp()->basicp();
        return basicp && basicp->isRanged();
    }
    static bool isNotReplaceable(const AstVarRef* const nodep) { return nodep->user2(); }
    static void markNonReplaceable(AstVarRef* const nodep) { nodep->user2SetOnce(); }

    // Get all ValVscps for a VarScope
    const std::vector<AstVarScope*>* getValVscps(AstVarRef* const refp) const {
        auto it = m_valVscps.find(refp->varScopep());
        if (it != m_valVscps.end()) return &(it->second.second);
        return nullptr;
    }

    // Add a ValVscp for a VarScope
    void addValVscp(AstVarRef* const refp, AstVarScope* const valVscp) {
        if (m_valVscps[refp->varScopep()].first.find(valVscp)
            != m_valVscps[refp->varScopep()].first.end())
            return;
        m_valVscps[refp->varScopep()].first.emplace(valVscp);
        m_valVscps[refp->varScopep()].second.push_back(valVscp);
    }

    // METHODS
    const ForceComponentsVarScope& getForceComponents(AstVarScope* vscp) {
        AstVar* const varp = vscp->varp();
        return m_forceComponentsVarScope(vscp, vscp, m_forceComponentsVar(varp, varp));
    }
    ForceComponentsVarScope* tryGetForceComponents(AstVarRef* nodep) const {
        return m_forceComponentsVarScope.tryGet(nodep->varScopep());
    }
    void setValVscpAssign(AstVarScope* valVscp, AstAssign* rhsExpr) { valVscp->user3p(rhsExpr); }
    AstAssign* getValVscpAssign(AstVarScope* valVscp) const {
        return VN_CAST(valVscp->user3p(), Assign);
    }
};

class ForceConvertVisitor final : public VNVisitor {
    // STATE
    ForceState& m_state;

    // STATIC METHODS
    // Replace each AstNodeVarRef in the given 'nodep' that writes a variable by transforming the
    // referenced AstVarScope with the given function.
    static void transformWritenVarScopes(AstNode* nodep,
                                         std::function<AstVarScope*(AstVarScope*)> f) {
        UASSERT_OBJ(nodep->backp(), nodep, "Must have backp, otherwise will be lost if replaced");
        nodep->foreach([&f](AstNodeVarRef* refp) {
            if (refp->access() != VAccess::WRITE) return;
            // TODO: this is not strictly speaking safe for some complicated lvalues, eg.:
            //       'force foo[a(cnt)] = 1;', where 'cnt' is an out parameter, but it will
            //       do for now...
            refp->replaceWith(
                new AstVarRef{refp->fileline(), f(refp->varScopep()), VAccess::WRITE});
            VL_DO_DANGLING(refp->deleteTree(), refp);
        });
    }

    // VISITORS
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

    void visit(AstAssignForce* nodep) override {
        // The AstAssignForce node will be removed for sure
        FileLine* const flp = nodep->fileline();
        AstNodeExpr* const lhsp = nodep->lhsp();  // The LValue we are forcing
        AstNodeExpr* const rhsp = nodep->rhsp();  // The value we are forcing it to
        VNRelinker relinker;
        nodep->unlinkFrBack(&relinker);
        VL_DO_DANGLING(pushDeletep(nodep), nodep);

        // Set corresponding enable signals to ones
        V3Number ones{lhsp, ForceState::isRangedDType(lhsp) ? lhsp->width() : 1};
        ones.setAllBits1();
        AstAssign* const setEnp
            = new AstAssign{flp, lhsp->cloneTreePure(false), new AstConst{rhsp->fileline(), ones}};
        transformWritenVarScopes(setEnp->lhsp(), [this](AstVarScope* vscp) {
            return m_state.getForceComponents(vscp).m_enVscp;
        });
        // Set corresponding value signals to the forced value
        AstAssign* const setValp
            = new AstAssign{flp, lhsp->cloneTreePure(false), rhsp->cloneTreePure(false)};
        transformWritenVarScopes(setValp->lhsp(), [this, rhsp, setValp](AstVarScope* vscp) {
            AstVarScope* const valVscp = m_state.getForceComponents(vscp).m_valVscp;
            m_state.setValVscpAssign(valVscp, setValp);
            rhsp->foreach([valVscp, this](AstVarRef* refp) { m_state.addValVscp(refp, valVscp); });
            return valVscp;
        });

        // Set corresponding read signal directly as well, in case something in the same
        // process reads it later
        AstAssign* const setRdp = new AstAssign{flp, lhsp->unlinkFrBack(), rhsp->unlinkFrBack()};
        transformWritenVarScopes(setRdp->lhsp(), [this](AstVarScope* vscp) {
            return m_state.getForceComponents(vscp).m_rdVscp;
        });

        setEnp->addNext(setValp);
        setEnp->addNext(setRdp);
        relinker.relink(setEnp);
    }

    void visit(AstRelease* nodep) override {
        FileLine* const flp = nodep->fileline();
        AstNodeExpr* const lhsp = nodep->lhsp();  // The LValue we are releasing
        // The AstRelease node will be removed for sure
        VNRelinker relinker;
        nodep->unlinkFrBack(&relinker);
        VL_DO_DANGLING(pushDeletep(nodep), nodep);

        // Set corresponding enable signals to zero
        V3Number zero{lhsp, ForceState::isRangedDType(lhsp) ? lhsp->width() : 1};
        zero.setAllBits0();
        AstAssign* const resetEnp
            = new AstAssign{flp, lhsp->cloneTreePure(false), new AstConst{lhsp->fileline(), zero}};
        transformWritenVarScopes(resetEnp->lhsp(), [this](AstVarScope* vscp) {
            return m_state.getForceComponents(vscp).m_enVscp;
        });

        // IEEE 1800-2023 10.6.2: When released, then if the variable is not driven by a continuous
        // assignment and does not currently have an active procedural continuous assignment, the
        // variable shall not immediately change value and shall maintain its current value until
        // the next procedural assignment to the variable is executed. Releasing a variable that is
        // driven by a continuous assignment or currently has an active assign procedural
        // continuous assignment shall reestablish that assignment and schedule a reevaluation in
        // the continuous assignment's scheduling region.
        AstAssign* const resetRdp
            = new AstAssign{flp, lhsp->cloneTreePure(false), lhsp->unlinkFrBack()};
        resetRdp->user2(true);
        // Replace write refs on the LHS
        resetRdp->lhsp()->foreach([this](AstVarRef* refp) {
            if (refp->access() != VAccess::WRITE) return;
            AstVarScope* const vscp = refp->varScopep();
            if (vscp->varp()->isContinuously()) {
                AstVarRef* const newpRefp = new AstVarRef{
                    refp->fileline(), m_state.getForceComponents(vscp).m_rdVscp, VAccess::WRITE};
                refp->replaceWith(newpRefp);
                VL_DO_DANGLING(refp->deleteTree(), refp);
            }
        });
        // Replace write refs on RHS
        if (VN_IS(resetRdp->rhsp(), ArraySel)) {
            std::vector<AstNodeExpr*> selIndices;
            AstNodeExpr* exprp = resetRdp->rhsp();
            while (AstArraySel* const selp = VN_CAST(exprp, ArraySel)) {
                selIndices.push_back(selp->bitp());
                exprp = selp->fromp();
            }
            if (AstVarRef* const refp = VN_CAST(exprp, VarRef)) {
                AstVarScope* const vscp = refp->varScopep();
                std::vector<AstNodeExpr*> reversedIndices(selIndices.size());
                std::reverse_copy(selIndices.begin(), selIndices.end(), reversedIndices.begin());
                AstNodeExpr* const origRhsp = resetRdp->rhsp();
                origRhsp->replaceWith(
                    m_state.getForceComponents(vscp).forcedUpdate(vscp, reversedIndices));
                VL_DO_DANGLING(origRhsp->deleteTree(), origRhsp);
            } else {
                exprp->v3warn(
                    E_UNSUPPORTED,
                    "Unsupported: Release statement argument is too complex array select");
            }
        } else {
            resetRdp->rhsp()->foreach([this](AstVarRef* refp) {
                if (refp->access() != VAccess::WRITE) return;
                AstVarScope* const vscp = refp->varScopep();
                if (vscp->varp()->isContinuously()) {
                    refp->access(VAccess::READ);
                    ForceState::markNonReplaceable(refp);
                } else {
                    refp->replaceWith(m_state.getForceComponents(vscp).forcedUpdate(vscp, {}));
                    VL_DO_DANGLING(refp->deleteTree(), refp);
                }
            });
        }

        resetRdp->addNext(resetEnp);
        relinker.relink(resetRdp);
    }

    void visit(AstVarScope* nodep) override {
        // If this signal is marked externally forceable, create the public force signals
        if (nodep->varp()->isForceable()) {
            if (VN_IS(nodep->varp()->dtypeSkipRefp(), UnpackArrayDType)) {
                nodep->varp()->v3warn(
                    E_UNSUPPORTED,
                    "Unsupported: Forcing unpacked arrays: " << nodep->varp()->name());  // (#4735)
                return;
            }

            const AstBasicDType* const bdtypep = nodep->varp()->basicp();
            const bool strtype = bdtypep && bdtypep->keyword() == VBasicDTypeKwd::STRING;
            if (strtype) {
                nodep->varp()->v3error(
                    "Forcing strings is not permitted: " << nodep->varp()->name());
            }

            const ForceState::ForceComponentsVarScope& fc = m_state.getForceComponents(nodep);
            fc.m_enVscp->varp()->sigUserRWPublic(true);
            fc.m_valVscp->varp()->sigUserRWPublic(true);
        }
    }

public:
    // CONSTRUCTOR
    // cppcheck-suppress constParameterCallback
    ForceConvertVisitor(AstNetlist* nodep, ForceState& state)
        : m_state{state} {
        // Transform all force and release statements
        iterateAndNextNull(nodep->modulesp());
    }
};

class ForceReplaceVisitor final : public VNVisitor {
    // STATE
    const ForceState& m_state;
    AstNodeStmt* m_stmtp = nullptr;
    bool m_inLogic = false;
    bool m_releaseRhs = false;  // Inside RHS of assignment created for release statement
    std::vector<AstNodeExpr*> m_selIndices;  // Indices of array select expressions above

    // METHODS
    void iterateLogic(AstNode* logicp) {
        VL_RESTORER(m_inLogic);
        m_inLogic = true;
        iterateChildren(logicp);
    }

    // VISITORS
    void visit(AstNodeStmt* nodep) override {
        VL_RESTORER(m_stmtp);
        m_stmtp = nodep;
        iterateChildren(nodep);
    }
    void visit(AstAssign* nodep) override {
        VL_RESTORER(m_stmtp);
        VL_RESTORER(m_releaseRhs);
        m_stmtp = nodep;
        iterate(nodep->lhsp());
        m_releaseRhs = nodep->user2();
        iterate(nodep->rhsp());
    }
    void visit(AstCFunc* nodep) override { iterateLogic(nodep); }
    void visit(AstCoverToggle* nodep) override { iterateLogic(nodep); }
    void visit(AstNodeProcedure* nodep) override { iterateLogic(nodep); }
    void visit(AstAlways* nodep) override {
        // TODO: this is the old behavioud prior to moving AssignW under Always.
        // Review if this is appropriate or if we are missing something...
        if (nodep->keyword() == VAlwaysKwd::CONT_ASSIGN) {
            iterateChildren(nodep);
            return;
        }
        iterateLogic(nodep);
    }
    void visit(AstSenItem* nodep) override { iterateLogic(nodep); }
    void visit(AstArraySel* nodep) override {
        m_selIndices.push_back(nodep->bitp());
        iterateChildren(nodep);
        UASSERT_OBJ(m_selIndices.size(), nodep, "Underflow");
        m_selIndices.pop_back();
    }
    void visit(AstVarRef* nodep) override {
        if (ForceState::isNotReplaceable(nodep)) return;

        switch (nodep->access()) {
        case VAccess::READ: {
            // Replace VarRef from forced LHS with rdVscp.
            if (ForceState::ForceComponentsVarScope* const fcp
                = m_state.tryGetForceComponents(nodep)) {
                nodep->varp(fcp->m_rdVscp->varp());
                nodep->varScopep(fcp->m_rdVscp);
            }
            break;
        }
        case VAccess::WRITE: {
            if (!m_inLogic) return;
            // Emit rdVscp update after each write to any VarRef on forced LHS.
            if (ForceState::ForceComponentsVarScope* const fcp
                = m_state.tryGetForceComponents(nodep)) {
                FileLine* const flp = nodep->fileline();
                std::vector<AstNodeExpr*> reversedIndices(m_selIndices.size());
                std::reverse_copy(m_selIndices.begin(), m_selIndices.end(),
                                  reversedIndices.begin());
                AstNodeExpr* const lhsp = ForceState::ForceComponentsVarScope::applySelects(
                    new AstVarRef{flp, fcp->m_rdVscp, VAccess::WRITE}, reversedIndices);
                AstNodeExpr* const rhsp = fcp->forcedUpdate(nodep->varScopep(), reversedIndices);
                m_stmtp->addNextHere(new AstAssign{flp, lhsp, rhsp});
            }
            // Emit valVscp update after each write to any VarRef on forced RHS.
            if (!m_state.getValVscps(nodep)) break;
            for (AstVarScope* const valVscp : *m_state.getValVscps(nodep)) {
                FileLine* const flp = nodep->fileline();
                AstAssign* assignp = m_state.getValVscpAssign(valVscp);
                UASSERT_OBJ(assignp, flp, "Missing stored assignment for forced valVscp");

                assignp = assignp->cloneTreePure(false);

                assignp->rhsp()->foreach(
                    [](AstVarRef* refp) { ForceState::markNonReplaceable(refp); });

                m_stmtp->addNextHere(assignp);
            }
            break;
        }
        default:
            if (!m_inLogic) return;
            if (m_state.tryGetForceComponents(nodep) || m_state.getValVscps(nodep)) {
                nodep->v3warn(
                    E_UNSUPPORTED,
                    "Unsupported: Signals used via read-write reference cannot be forced");
            }
            break;
        }
    }
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTOR
    explicit ForceReplaceVisitor(AstNetlist* nodep, const ForceState& state)
        : m_state{state} {
        iterateChildren(nodep);
    }
};
//######################################################################
//

void V3Force::forceAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ":");
    if (!v3Global.hasForceableSignals()) return;
    {
        ForceState state;
        { ForceConvertVisitor{nodep, state}; }
        { ForceReplaceVisitor{nodep, state}; }
        V3Global::dumpCheckGlobalTree("force", 0, dumpTreeEitherLevel() >= 3);
    }
}
