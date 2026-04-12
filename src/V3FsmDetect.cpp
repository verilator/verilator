// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: FSM coverage detect pass
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

#include "V3FsmDetect.h"

#include "V3Ast.h"
#include "V3FsmShared.h"

#include <unordered_map>

VL_DEFINE_DEBUG_FUNCTIONS;

namespace {

static V3FsmResetCondDesc describeResetCond(AstNodeExpr* condp) {
    V3FsmResetCondDesc desc;
    if (AstVarRef* const vrefp = VN_CAST(condp, VarRef)) {
        desc.vscp = vrefp->varScopep();
        return desc;
    }
    if (AstNot* const notp = VN_CAST(condp, Not)) {
        if (AstVarRef* const vrefp = VN_CAST(notp->lhsp(), VarRef)) {
            desc.vscp = vrefp->varScopep();
            desc.negated = true;
        }
    }
    return desc;
}

static std::vector<V3FsmSenDesc> describeSenTree(AstSenTree* sentreep) {
    std::vector<V3FsmSenDesc> senses;
    if (!sentreep) return senses;
    for (AstSenItem* itemp = sentreep->sensesp(); itemp; itemp = VN_AS(itemp->nextp(), SenItem)) {
        AstNodeVarRef* const vrefp = itemp->varrefp();
        if (!vrefp) continue;
        V3FsmSenDesc desc;
        desc.edgeType = static_cast<uint8_t>(itemp->edgeType());
        desc.vscp = vrefp->varScopep();
        senses.push_back(desc);
    }
    return senses;
}

class FsmDetectVisitor final : public VNVisitor {
    AstScope* m_scopep = nullptr;

    static AstNodeDType* unwrapEnumCandidate(AstNodeDType* dtypep) {
        AstNodeDType* resultp = dtypep;
        while (resultp) {
            if (VN_IS(resultp, EnumDType)) return resultp;
            if (AstDefImplicitDType* const imp = VN_CAST(resultp, DefImplicitDType)) {
                resultp = imp->subDTypep();
                continue;
            }
            if (AstRefDType* const refp = VN_CAST(resultp, RefDType)) {
                resultp = refp->subDTypep();
                continue;
            }
            if (AstConstDType* const constp = VN_CAST(resultp, ConstDType)) {
                resultp = constp->subDTypep();
                continue;
            }
            break;
        }
        return resultp;
    }

    static bool isSimpleResetCond(AstNodeExpr* condp) {
        if (VN_IS(condp, VarRef)) return true;
        if (const AstNot* const notp = VN_CAST(condp, Not)) return VN_IS(notp->lhsp(), VarRef);
        return false;
    }

    static AstCase* caseFromStmt(AstNode* stmtp) {
        if (!stmtp) return nullptr;
        if (AstCase* const casep = VN_CAST(stmtp, Case)) return casep;
        if (AstBegin* const beginp = VN_CAST(stmtp, Begin)) {
            if (beginp->stmtsp() && !beginp->stmtsp()->nextp()) return VN_CAST(beginp->stmtsp(), Case);
        }
        return nullptr;
    }

    static AstNode* unwrapSingleBlock(AstNode* stmtp) {
        if (AstBegin* const beginp = VN_CAST(stmtp, Begin)) return beginp->stmtsp();
        return stmtp;
    }

    static bool isIgnorableStmt(AstNode* nodep) { return VN_IS(nodep, CoverInc); }

    static AstNode* singleMeaningfulStmt(AstNode* stmtp) {
        AstNode* resultp = nullptr;
        for (AstNode* nodep = unwrapSingleBlock(stmtp); nodep; nodep = nodep->nextp()) {
            if (isIgnorableStmt(nodep)) continue;
            if (resultp) return nullptr;
            resultp = nodep;
        }
        return resultp;
    }

    static AstNodeAssign* directStateAssign(AstNode* stmtp, AstVarScope* stateVscp) {
        AstNode* const nodep = singleMeaningfulStmt(stmtp);
        if (!nodep) return nullptr;
        AstNodeAssign* const assp = VN_CAST(nodep, NodeAssign);
        if (!assp) return nullptr;
        AstVarRef* const vrefp = VN_CAST(assp->lhsp(), VarRef);
        if (!vrefp || vrefp->varScopep() != stateVscp) return nullptr;
        return assp;
    }

    static bool branchHasNestedIf(AstNode* stmtp) {
        for (AstNode* nodep = unwrapSingleBlock(stmtp); nodep; nodep = nodep->nextp()) {
            if (isIgnorableStmt(nodep)) continue;
            if (VN_IS(nodep, If)) return true;
        }
        return false;
    }

    static string labelForValue(const std::unordered_map<int, string>& labels, int value) {
        const auto it = labels.find(value);
        return it == labels.end() ? ("S" + cvtToStr(value)) : it->second;
    }

    static bool exprConstValue(AstNodeExpr* exprp, int& value) {
        if (!exprp) return false;
        if (AstConst* const constp = VN_CAST(exprp, Const)) {
            value = constp->toSInt();
            return true;
        }
        if (AstEnumItemRef* const itemRefp = VN_CAST(exprp, EnumItemRef)) {
            AstConst* const constp = itemRefp->itemp() ? VN_CAST(itemRefp->itemp()->valuep(), Const)
                                                       : nullptr;
            if (!constp) return false;
            value = constp->toSInt();
            return true;
        }
        return false;
    }

    static void addArc(V3FsmDesc& desc, const string& fromLabel, int fromValue,
                       const string& toLabel, int toValue, bool isReset, bool isCond,
                       bool isDefault, FileLine* flp) {
        V3FsmArcDesc arc;
        arc.fromLabel = fromLabel;
        arc.fromValue = fromValue;
        arc.toLabel = toLabel;
        arc.toValue = toValue;
        arc.isReset = isReset;
        arc.isCond = isCond;
        arc.isDefault = isDefault;
        arc.flp = flp;
        desc.arcs.push_back(arc);
    }

    static bool emitCaseItemArcs(V3FsmDesc& desc, AstCaseItem* itemp, AstVarScope* stateVscp,
                                 const std::unordered_map<int, string>& labels, bool inclCond) {
        std::vector<std::pair<string, int>> froms;
        if (itemp->isDefault()) {
            if (!inclCond) return false;
            froms.emplace_back("default", 0);
        } else {
            for (AstNodeExpr* condp = itemp->condsp(); condp;
                 condp = VN_CAST(condp->nextp(), NodeExpr)) {
                int value = 0;
                if (!exprConstValue(condp, value)) continue;
                froms.emplace_back(labelForValue(labels, value), value);
            }
            if (froms.empty()) return false;
        }

        if (AstNodeAssign* const assp = directStateAssign(itemp->stmtsp(), stateVscp)) {
            int toValue = 0;
            if (exprConstValue(assp->rhsp(), toValue)) {
                const string toLabel = labelForValue(labels, toValue);
                for (const auto& from : froms) {
                    addArc(desc, from.first, from.second, toLabel, toValue, false, false,
                           itemp->isDefault(), assp->fileline());
                }
                return true;
            }
        }

        if (AstIf* const ifp = VN_CAST(singleMeaningfulStmt(itemp->stmtsp()), If)) {
            const bool tier2 = !branchHasNestedIf(ifp->thensp()) && !branchHasNestedIf(ifp->elsesp())
                               && directStateAssign(ifp->thensp(), stateVscp)
                               && directStateAssign(ifp->elsesp(), stateVscp);
            if (tier2 || inclCond) {
                for (AstNode* branchp : {ifp->thensp(), ifp->elsesp()}) {
                    if (AstNodeAssign* const assp = directStateAssign(branchp, stateVscp)) {
                        int toValue = 0;
                        if (exprConstValue(assp->rhsp(), toValue)) {
                            const string toLabel = labelForValue(labels, toValue);
                            for (const auto& from : froms) {
                                addArc(desc, from.first, from.second, toLabel, toValue, false,
                                       true, itemp->isDefault(), assp->fileline());
                            }
                        }
                    }
                }
                return true;
            }
        }
        return false;
    }

    static void addResetArcs(V3FsmDesc& desc, AstNode* stmtsp, AstVarScope* stateVscp,
                             const std::unordered_map<int, string>& labels) {
        for (AstNode* nodep = unwrapSingleBlock(stmtsp); nodep; nodep = nodep->nextp()) {
            if (AstNodeAssign* const assp = VN_CAST(nodep, NodeAssign)) {
                AstVarRef* const vrefp = VN_CAST(assp->lhsp(), VarRef);
                int toValue = 0;
                if (vrefp && vrefp->varScopep() == stateVscp && exprConstValue(assp->rhsp(), toValue)) {
                    addArc(desc, "ANY", 0, labelForValue(labels, toValue), toValue, true, false,
                           false, assp->fileline());
                }
            }
        }
    }

    void processCase(AstCase* casep, AstNodeExpr* resetCondp, AstAlways* alwaysp) {
        AstVarRef* const selp = VN_CAST(casep->exprp(), VarRef);
        if (!selp) return;
        AstVarScope* const stateVscp = selp->varScopep();
        if (!stateVscp) return;
        AstVar* const stateVarp = selp->varp();
        AstNodeDType* resolvedp = unwrapEnumCandidate(stateVscp->dtypep());
        if (!resolvedp) resolvedp = unwrapEnumCandidate(stateVarp->dtypep());
        AstEnumDType* const enump = VN_CAST(resolvedp, EnumDType);
        const bool forced = stateVarp->attrFsmState();
        if (!enump && !forced) return;

        std::vector<std::pair<string, int>> states;
        std::unordered_map<int, string> labels;
        if (enump) {
            for (AstEnumItem* itemp = enump->itemsp(); itemp; itemp = VN_AS(itemp->nextp(), EnumItem)) {
                int value = 0;
                if (!exprConstValue(itemp->valuep(), value)) continue;
                states.emplace_back(itemp->name(), value);
                labels.emplace(value, itemp->name());
            }
            if (states.size() < 2) return;
        } else {
            const int width = stateVarp->width();
            if (width < 1 || width >= 31) return;
            const unsigned stateCount = 1U << width;
            for (unsigned value = 0; value < stateCount; ++value) {
                const string label = "S" + cvtToStr(value);
                states.emplace_back(label, static_cast<int>(value));
                labels.emplace(static_cast<int>(value), label);
            }
        }

        V3FsmDesc& desc = V3FsmRegistry::instance().upsert(stateVscp);
        if (!desc.stateVscp) {
            desc.stateVarp = stateVarp;
            desc.stateVscp = stateVscp;
            desc.scopep = m_scopep;
            desc.senses = describeSenTree(alwaysp->sentreep());
            desc.resetCond = describeResetCond(resetCondp);
            desc.hasResetCond = desc.resetCond.vscp;
            desc.stateVarName = stateVscp->prettyName();
            desc.states = states;
            desc.resetInclude = stateVarp->attrFsmResetArc();
            desc.inclCond = stateVarp->attrFsmArcInclCond();
            desc.flp = casep->fileline();
        }
        for (AstCaseItem* itemp = casep->itemsp(); itemp; itemp = VN_AS(itemp->nextp(), CaseItem)) {
            emitCaseItemArcs(desc, itemp, stateVscp, labels, desc.inclCond);
        }
    }

    void processAlways(AstAlways* alwaysp) {
        if (!alwaysp->sentreep() || !alwaysp->sentreep()->hasClocked() || !m_scopep) return;
        std::vector<std::pair<AstCase*, AstNodeExpr*>> candidates;
        AstNode* stmtsp = unwrapSingleBlock(alwaysp->stmtsp());
        AstIf* const firstIfp = VN_CAST(stmtsp, If);
        if (firstIfp && firstIfp == stmtsp) {
            if (AstCase* const casep = caseFromStmt(firstIfp->elsesp())) {
                candidates.emplace_back(casep, isSimpleResetCond(firstIfp->condp()) ? firstIfp->condp()
                                                                                     : nullptr);
            }
        }
        for (AstNode* nodep = stmtsp; nodep; nodep = nodep->nextp()) {
            if (AstCase* const casep = VN_CAST(nodep, Case)) candidates.emplace_back(casep, nullptr);
        }
        if (candidates.empty()) return;

        AstVarScope* firstVscp = nullptr;
        for (const auto& cand : candidates) {
            AstVarRef* const selp = VN_CAST(cand.first->exprp(), VarRef);
            AstVarScope* const vscp = selp ? selp->varScopep() : nullptr;
            if (!vscp) continue;
            if (!firstVscp) {
                firstVscp = vscp;
                processCase(cand.first, cand.second, alwaysp);
            } else if (vscp != firstVscp) {
                cand.first->v3warn(FSMMULTI,
                                   "FSM coverage: multiple enum-typed case statements found in "
                                   "the same always block. Only the first candidate will be "
                                   "instrumented.");
            } else {
                processCase(cand.first, cand.second, alwaysp);
            }
        }

        if (firstIfp && firstVscp) {
            if (V3FsmDesc* const descp = V3FsmRegistry::instance().find(firstVscp)) {
                if (descp->hasResetCond) {
                    std::unordered_map<int, string> labels;
                    for (const auto& state : descp->states) labels.emplace(state.second, state.first);
                    addResetArcs(*descp, firstIfp->thensp(), firstVscp, labels);
                }
            }
        }
    }

    void visit(AstScope* nodep) override {
        VL_RESTORER(m_scopep);
        m_scopep = nodep;
        iterateChildren(nodep);
    }

    void visit(AstAlways* nodep) override { processAlways(nodep); }

    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    explicit FsmDetectVisitor(AstNetlist* rootp) { iterate(rootp); }
};

}  // namespace

void V3FsmDetect::detect(AstNetlist* rootp) {
    UINFO(2, __FUNCTION__ << ":");
    V3FsmRegistry::instance().clear();
    { FsmDetectVisitor{rootp}; }
    V3Global::dumpCheckGlobalTree("fsm-detect", 0, dumpTreeEitherLevel() >= 3);
}
