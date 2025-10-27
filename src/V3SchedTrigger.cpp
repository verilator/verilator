// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Create triggers for code scheduling
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
//
//
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Const.h"
#include "V3EmitCBase.h"
#include "V3EmitV.h"
#include "V3Order.h"
#include "V3Sched.h"
#include "V3SenExprBuilder.h"
#include "V3Stats.h"

VL_DEFINE_DEBUG_FUNCTIONS;

namespace V3Sched {

void TriggerKit::addFirstIterationTriggerAssignment(AstVarScope* flagp, uint32_t index) const {
    FileLine* const flp = flagp->fileline();
    AstVarRef* const vrefp = new AstVarRef{flp, m_vscp, VAccess::WRITE};
    AstCMethodHard* const callp = new AstCMethodHard{flp, vrefp, VCMethod::TRIGGER_SET_BIT};
    callp->addPinsp(new AstConst{flp, index});
    callp->addPinsp(new AstVarRef{flp, flagp, VAccess::READ});
    callp->dtypeSetVoid();
    m_funcp->stmtsp()->addHereThisAsNext(callp->makeStmt());
}

// Utility to set then clear an extra trigger
void TriggerKit::addExtraTriggerAssignment(AstVarScope* extraTriggerVscp, uint32_t index) const {
    FileLine* const flp = extraTriggerVscp->fileline();
    AstVarRef* const vrefp = new AstVarRef{flp, m_vscp, VAccess::WRITE};
    AstCMethodHard* const callp = new AstCMethodHard{flp, vrefp, VCMethod::TRIGGER_SET_BIT};
    callp->addPinsp(new AstConst{flp, index});
    callp->addPinsp(new AstVarRef{flp, extraTriggerVscp, VAccess::READ});
    callp->dtypeSetVoid();
    AstNode* const stmtp = callp->makeStmt();
    stmtp->addNext(new AstAssign{flp, new AstVarRef{flp, extraTriggerVscp, VAccess::WRITE},
                                 new AstConst{flp, AstConst::BitFalse{}}});
    m_funcp->stmtsp()->addHereThisAsNext(stmtp);
}

// Create a TRIGGERVEC and the related TriggerKit for the given AstSenTree vector
const TriggerKit TriggerKit::create(AstNetlist* netlistp,  //
                                    AstCFunc* const initFuncp,  //
                                    SenExprBuilder& senExprBuilder,  //
                                    const std::vector<const AstSenTree*>& senTreeps,  //
                                    const string& name,  //
                                    const ExtraTriggers& extraTriggers,  //
                                    bool slow) {
    AstTopScope* const topScopep = netlistp->topScopep();
    AstScope* const scopeTopp = topScopep->scopep();
    FileLine* const flp = scopeTopp->fileline();

    // Gather all the unique SenItems under the SenTrees
    // List of unique SenItems used by all 'senTreeps'
    std::vector<const AstSenItem*> senItemps;
    // Map from SenItem to the equivalent index in 'senItemps'
    std::unordered_map<const AstSenItem*, size_t> senItemp2Index;
    {
        // Set of unique SenItems
        std::unordered_set<VNRef<const AstSenItem>> uniqueSenItemps;
        for (const AstSenTree* const senTreep : senTreeps) {
            for (const AstSenItem *itemp = senTreep->sensesp(), *nextp; itemp; itemp = nextp) {
                nextp = VN_AS(itemp->nextp(), SenItem);
                const auto pair = uniqueSenItemps.emplace(*itemp);
                if (pair.second) {
                    senItemp2Index.emplace(itemp, senItemps.size());
                    senItemps.push_back(itemp);
                }
                senItemp2Index.emplace(itemp, senItemp2Index.at(&(pair.first->get())));
            }
        }
    }

    std::unordered_map<const AstSenTree*, AstSenTree*> map;

    const uint32_t nTriggers = senItemps.size() + extraTriggers.size();

    // Create the TRIGGERVEC variable
    AstBasicDType* const tDtypep
        = new AstBasicDType{flp, VBasicDTypeKwd::TRIGGERVEC, VSigning::UNSIGNED,
                            static_cast<int>(nTriggers), static_cast<int>(nTriggers)};
    netlistp->typeTablep()->addTypesp(tDtypep);
    AstVarScope* const vscp = scopeTopp->createTemp("__V" + name + "Triggered", tDtypep);

    // Create the trigger computation function
    AstCFunc* const funcp = util::makeSubFunction(netlistp, "_eval_triggers__" + name, slow);
    if (v3Global.opt.profExec()) funcp->addStmtsp(util::profExecSectionPush(flp, "trig " + name));

    // Create the trigger dump function (for debugging, always 'slow')
    AstCFunc* const dumpp = util::makeSubFunction(netlistp, "_dump_triggers__" + name, true);
    dumpp->ifdef("VL_DEBUG");

    // Add a print to the dumping function if there are no triggers pending
    {
        AstCMethodHard* const callp = new AstCMethodHard{
            flp, new AstVarRef{flp, vscp, VAccess::READ}, VCMethod::TRIGGER_ANY};
        callp->dtypeSetBit();
        AstIf* const ifp = new AstIf{flp, callp};
        dumpp->addStmtsp(ifp);
        ifp->addElsesp(new AstCStmt{flp, "VL_DBG_MSGF(\"         No triggers active\\n\");"});
    }

    // Set the given trigger to the given value
    const auto setTrigBit = [&](uint32_t index, AstNodeExpr* valp) {
        AstVarRef* const vrefp = new AstVarRef{flp, vscp, VAccess::WRITE};
        AstCMethodHard* const callp = new AstCMethodHard{flp, vrefp, VCMethod::TRIGGER_SET_BIT};
        callp->addPinsp(new AstConst{flp, index});
        callp->addPinsp(valp);
        callp->dtypeSetVoid();
        return callp->makeStmt();
    };

    // Create a reference to a trigger flag
    const auto getTrig = [&](uint32_t index) {
        AstVarRef* const vrefp = new AstVarRef{flp, vscp, VAccess::READ};
        const uint32_t wordIndex = index / 64;
        const uint32_t bitIndex = index % 64;
        AstCMethodHard* const callp
            = new AstCMethodHard{flp, vrefp, VCMethod::TRIGGER_WORD, new AstConst{flp, wordIndex}};
        callp->dtypeSetUInt64();
        AstNodeExpr* const termp
            = new AstAnd{flp, new AstConst{flp, AstConst::Unsized64{}, 1ULL << bitIndex}, callp};
        return termp;
    };

    // Add a debug dumping statement for this trigger
    const auto addDebug = [&](uint32_t index, const string& text = "") {
        std::stringstream ss;
        ss << "VL_DBG_MSGF(\"         ";
        ss << "'" << name << "' region trigger index " << std::to_string(index) << " is active";
        if (!text.empty()) ss << ": " << text;
        ss << "\\n\");";

        AstIf* const ifp = new AstIf{flp, getTrig(index)};
        dumpp->addStmtsp(ifp);
        ifp->addThensp(new AstCStmt{flp, ss.str()});
    };

    // Add a print for each of the extra triggers
    for (unsigned i = 0; i < extraTriggers.size(); ++i) {
        addDebug(i, "Internal '" + name + "' trigger - " + extraTriggers.description(i));
    }

    // Add trigger computation
    uint32_t triggerNumber = extraTriggers.size();
    uint32_t triggerBitIdx = triggerNumber;
    AstNodeStmt* initialTrigsp = nullptr;
    std::vector<uint32_t> senItemIndex2TriggerIndex;
    senItemIndex2TriggerIndex.reserve(senItemps.size());
    constexpr uint32_t TRIG_VEC_WORD_SIZE_LOG2 = 6;  // 64-bits
    constexpr uint32_t TRIG_VEC_WORD_SIZE = 1 << TRIG_VEC_WORD_SIZE_LOG2;
    std::vector<AstNodeExpr*> trigExprps;
    trigExprps.reserve(TRIG_VEC_WORD_SIZE);
    for (const AstSenItem* const senItemp : senItemps) {
        UASSERT_OBJ(senItemp->isClocked() || senItemp->isHybrid(), senItemp,
                    "Cannot create trigger expression for non-clocked sensitivity");

        // Store the trigger number
        senItemIndex2TriggerIndex.push_back(triggerNumber);

        // Add the trigger computation
        const auto& pair = senExprBuilder.build(senItemp);
        trigExprps.emplace_back(pair.first);

        // Add initialization time trigger
        if (pair.second || v3Global.opt.xInitialEdge()) {
            initialTrigsp
                = AstNode::addNext(initialTrigsp, setTrigBit(triggerNumber, new AstConst{flp, 1}));
        }

        // Add a debug statement for this trigger
        std::stringstream ss;
        ss << "@(";
        V3EmitV::verilogForTree(senItemp, ss);
        ss << ")";
        std::string desc = VString::quoteBackslash(ss.str());
        desc = VString::replaceSubstr(desc, "\n", "\\n");
        addDebug(triggerNumber, desc);

        //
        ++triggerNumber;

        // Add statements on every word boundary
        if (triggerNumber % TRIG_VEC_WORD_SIZE == 0) {
            if (triggerBitIdx % TRIG_VEC_WORD_SIZE != 0) {
                // Set leading triggers bit-wise
                for (AstNodeExpr* const exprp : trigExprps) {
                    funcp->addStmtsp(setTrigBit(triggerBitIdx++, exprp));
                }
            } else {
                // Set whole word as a unit
                UASSERT_OBJ(triggerNumber == triggerBitIdx + TRIG_VEC_WORD_SIZE, senItemp,
                            "Mismatched index");
                UASSERT_OBJ(trigExprps.size() == TRIG_VEC_WORD_SIZE, senItemp,
                            "There should be TRIG_VEC_WORD_SIZE expressions");
                // Concatenate all bits in a tree
                for (uint32_t level = 0; level < TRIG_VEC_WORD_SIZE_LOG2; ++level) {
                    const uint32_t stride = 1 << level;
                    for (uint32_t i = 0; i < TRIG_VEC_WORD_SIZE; i += 2 * stride) {
                        trigExprps[i] = new AstConcat{trigExprps[i]->fileline(),
                                                      trigExprps[i + stride], trigExprps[i]};
                        trigExprps[i + stride] = nullptr;
                    }
                }
                // Set the whole word in the trigger vector
                AstVarRef* const vrefp = new AstVarRef{flp, vscp, VAccess::WRITE};
                AstCMethodHard* const callp
                    = new AstCMethodHard{flp, vrefp, VCMethod::TRIGGER_SET_WORD};
                callp->addPinsp(new AstConst{flp, triggerBitIdx / TRIG_VEC_WORD_SIZE});
                callp->addPinsp(trigExprps[0]);
                callp->dtypeSetVoid();
                funcp->addStmtsp(callp->makeStmt());
                triggerBitIdx += TRIG_VEC_WORD_SIZE;
            }
            UASSERT_OBJ(triggerNumber == triggerBitIdx, senItemp, "Mismatched index");
            trigExprps.clear();
        }
    }
    // Set trailing triggers bit-wise
    for (AstNodeExpr* const exprp : trigExprps) {
        funcp->addStmtsp(setTrigBit(triggerBitIdx++, exprp));
    }
    trigExprps.clear();

    // Construct the map from old SenTrees to new SenTrees
    for (const AstSenTree* const senTreep : senTreeps) {
        AstSenTree* const trigpSenp = new AstSenTree{flp, nullptr};
        for (const AstSenItem *itemp = senTreep->sensesp(), *nextp; itemp; itemp = nextp) {
            nextp = VN_AS(itemp->nextp(), SenItem);
            const uint32_t tiggerIndex = senItemIndex2TriggerIndex.at(senItemp2Index.at(itemp));
            trigpSenp->addSensesp(new AstSenItem{flp, VEdgeType::ET_TRUE, getTrig(tiggerIndex)});
        }
        topScopep->addSenTreesp(trigpSenp);
        map[senTreep] = trigpSenp;
    }

    // Get the SenExprBuilder results
    const SenExprBuilder::Results senResults = senExprBuilder.getAndClearResults();

    // Add the init and update statements
    for (AstNodeStmt* const nodep : senResults.m_inits) initFuncp->addStmtsp(nodep);
    for (AstNodeStmt* const nodep : senResults.m_postUpdates) funcp->addStmtsp(nodep);
    if (!senResults.m_preUpdates.empty()) {
        for (AstNodeStmt* const nodep : vlstd::reverse_view(senResults.m_preUpdates)) {
            UASSERT_OBJ(funcp->stmtsp(), funcp,
                        "No statements in trigger eval function, but there are pre updates");
            funcp->stmtsp()->addHereThisAsNext(nodep);
        }
    }

    // Add the initialization statements
    if (initialTrigsp) {
        AstVarScope* const tempVscp = scopeTopp->createTemp("__V" + name + "DidInit", 1);
        AstVarRef* const condp = new AstVarRef{flp, tempVscp, VAccess::READ};
        AstIf* const ifp = new AstIf{flp, new AstNot{flp, condp}};
        funcp->addStmtsp(ifp);
        ifp->branchPred(VBranchPred::BP_UNLIKELY);
        ifp->addThensp(util::setVar(tempVscp, 1));
        ifp->addThensp(initialTrigsp);
    }

    // Add a call to the dumping function if debug is enabled
    {
        AstCStmt* const stmtp = new AstCStmt{flp};
        funcp->addStmtsp(stmtp);
        stmtp->add("#ifdef VL_DEBUG\n");
        stmtp->add("if (VL_UNLIKELY(vlSymsp->_vm_contextp__->debug())) {\n");
        stmtp->add(util::callVoidFunc(dumpp));
        stmtp->add("}\n");
        stmtp->add("#endif");
    }

    if (v3Global.opt.profExec()) funcp->addStmtsp(util::profExecSectionPop(flp));

    // The debug code might leak signal names, so simply delete it when using --protect-ids
    if (v3Global.opt.protectIds()) dumpp->stmtsp()->unlinkFrBackWithNext()->deleteTree();

    // These might get large when we have a lot of triggers, so split if necessary
    util::splitCheck(funcp);
    util::splitCheck(dumpp);

    return TriggerKit{vscp, funcp, dumpp, map};
}

}  // namespace V3Sched
