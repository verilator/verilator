// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: FSM coverage emit pass
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "V3PchAstNoMT.h"

#include "V3FsmEmit.h"

#include "V3Ast.h"
#include "V3FsmShared.h"

VL_DEFINE_DEBUG_FUNCTIONS;

namespace {

AstConst* makeTypedConst(FileLine* flp, AstNodeDType* dtypep, int value) {
    AstConst* const constp = new AstConst{flp, AstConst::DTyped{}, dtypep};
    constp->num().setLong(value);
    return constp;
}

AstNodeExpr* makeEqValue(FileLine* flp, AstVarScope* vscp, int value) {
    return new AstEq{flp, new AstVarRef{flp, vscp, VAccess::READ},
                     makeTypedConst(flp, vscp->dtypep(), value)};
}

AstNodeExpr* makeNeqValue(FileLine* flp, AstVarScope* vscp, int value) {
    return new AstNeq{flp, new AstVarRef{flp, vscp, VAccess::READ},
                      makeTypedConst(flp, vscp->dtypep(), value)};
}

AstNodeExpr* andExpr(FileLine* flp, AstNodeExpr* lhsp, AstNodeExpr* rhsp) {
    if (!lhsp) return rhsp;
    return new AstLogAnd{flp, lhsp, rhsp};
}

string arcTag(const V3FsmDesc& desc, const V3FsmArcDesc& arc) {
    if (!arc.isReset) return "";
    return desc.resetInclude ? "[reset_include]" : "[reset]";
}

AstSenTree* buildSenTree(FileLine* flp, const std::vector<V3FsmSenDesc>& senses) {
    AstSenTree* const sentreep = new AstSenTree{flp, nullptr};
    for (const V3FsmSenDesc& sense : senses) {
        if (!sense.vscp) continue;
        auto* const senItemp = new AstSenItem{
            flp, VEdgeType{static_cast<int>(sense.edgeType)},
            new AstVarRef{flp, sense.vscp, VAccess::READ}};
        sentreep->addSensesp(senItemp);
    }
    return sentreep;
}

AstNodeExpr* buildResetCond(FileLine* flp, const V3FsmResetCondDesc& resetCond) {
    if (!resetCond.vscp) return nullptr;
    AstNodeExpr* condp = new AstVarRef{flp, resetCond.vscp, VAccess::READ};
    if (resetCond.negated) condp = new AstNot{flp, condp};
    return condp;
}

class FsmEmitVisitor final : public VNVisitor {
    void emitOne(const V3FsmDesc& desc) {
        FileLine* const flp = desc.flp ? desc.flp : desc.stateVscp->fileline();
        AstNodeModule* const modp = desc.scopep->modp();
        AstVarScope* const prevVscp
            = desc.scopep->createTemp("__Vfsmcov_prev__" + desc.stateVarp->shortName(),
                                      desc.stateVscp->dtypep());

        AstActive* const initActivep
            = new AstActive{flp, "fsm-coverage-init",
                            new AstSenTree{flp, new AstSenItem{flp, AstSenItem::Initial{}}}};
        initActivep->senTreeStorep(initActivep->sentreep());
        initActivep->addStmtsp(new AstInitialStatic{
            flp, new AstAssign{flp, new AstVarRef{flp, prevVscp, VAccess::WRITE},
                               new AstVarRef{flp, desc.stateVscp, VAccess::READ}}});
        desc.scopep->addBlocksp(initActivep);

        if (desc.senses.empty()) return;
        AstSenTree* const senTreep = buildSenTree(flp, desc.senses);
        AstActive* const activep = new AstActive{flp, "fsm-coverage", senTreep};
        activep->senTreeStorep(senTreep);
        desc.scopep->addBlocksp(activep);
        AstAlwaysPre* const preSavep = new AstAlwaysPre{flp};
        AstAlwaysPost* const covPostp = new AstAlwaysPost{flp};
        activep->addStmtsp(preSavep);
        activep->addStmtsp(covPostp);
        preSavep->addStmtsp(new AstAssign{flp, new AstVarRef{flp, prevVscp, VAccess::WRITE},
                                          new AstVarRef{flp, desc.stateVscp, VAccess::READ}});

        for (const auto& state : desc.states) {
            AstCoverOtherDecl* const declp = new AstCoverOtherDecl{
                flp, "v_fsm_state/" + modp->prettyName(), desc.stateVarName + "::" + state.first,
                "", 0};
            declp->hier(desc.scopep->prettyName());
            modp->addStmtsp(declp);
            AstNodeExpr* guardp
                = andExpr(flp, makeNeqValue(flp, prevVscp, state.second),
                          makeEqValue(flp, desc.stateVscp, state.second));
            covPostp->addStmtsp(new AstIf{flp, guardp, new AstCoverInc{flp, declp}});
        }

        for (const auto& arc : desc.arcs) {
            AstCoverOtherDecl* const declp = new AstCoverOtherDecl{
                flp, "v_fsm_arc/" + modp->prettyName(),
                desc.stateVarName + "::" + arc.fromLabel + "->" + arc.toLabel + arcTag(desc, arc),
                "", 0};
            declp->hier(desc.scopep->prettyName());
            modp->addStmtsp(declp);
            AstNodeExpr* guardp = nullptr;
            if (arc.isReset) {
                guardp = buildResetCond(flp, desc.resetCond);
                guardp = andExpr(flp, guardp, makeEqValue(flp, desc.stateVscp, arc.toValue));
            } else if (arc.isDefault) {
                for (const auto& state : desc.states) {
                    guardp = andExpr(flp, guardp, makeNeqValue(flp, prevVscp, state.second));
                }
                guardp = andExpr(flp, guardp, makeEqValue(flp, desc.stateVscp, arc.toValue));
            } else {
                guardp = andExpr(flp, makeEqValue(flp, prevVscp, arc.fromValue),
                                 makeEqValue(flp, desc.stateVscp, arc.toValue));
            }
            covPostp->addStmtsp(new AstIf{flp, guardp, new AstCoverInc{flp, declp}});
        }
    }

    void visit(AstNetlist* nodep) override {
        for (const auto& it : V3FsmRegistry::instance().all()) emitOne(it.second);
        iterateChildren(nodep);
    }
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    explicit FsmEmitVisitor(AstNetlist* rootp) { iterate(rootp); }
};

}  // namespace

void V3FsmEmit::emit(AstNetlist* rootp) {
    UINFO(2, __FUNCTION__ << ":");
    { FsmEmitVisitor{rootp}; }
    V3FsmRegistry::instance().clear();
    V3Global::dumpCheckGlobalTree("fsm-emit", 0, dumpTreeEitherLevel() >= 3);
}
