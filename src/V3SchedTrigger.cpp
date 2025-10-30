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

namespace {

AstVarScope* newArgument(AstCFunc* funcp, AstNodeDType* dtypep, const std::string& name,
                         VDirection direction) {
    FileLine* const flp = funcp->fileline();
    AstScope* const scopep = funcp->scopep();
    AstVar* const varp = new AstVar{flp, VVarType::BLOCKTEMP, name, dtypep};
    varp->funcLocal(true);
    varp->direction(direction);
    funcp->addArgsp(varp);
    AstVarScope* const vscp = new AstVarScope{flp, scopep, varp};
    scopep->addVarsp(vscp);
    return vscp;
}

AstVarScope* newLocal(AstCFunc* funcp, AstNodeDType* dtypep, const std::string& name) {
    FileLine* const flp = funcp->fileline();
    AstScope* const scopep = funcp->scopep();
    AstVar* const varp = new AstVar{flp, VVarType::BLOCKTEMP, name, dtypep};
    varp->funcLocal(true);
    funcp->addVarsp(varp);
    AstVarScope* const vscp = new AstVarScope{flp, scopep, varp};
    scopep->addVarsp(vscp);
    return vscp;
}

}  // namespace

AstCFunc* TriggerKit::createAndNotFunc() const {
    AstNetlist* const netlistp = v3Global.rootp();
    FileLine* const flp = netlistp->topScopep()->fileline();

    // Create the function
    AstCFunc* const funcp = util::makeSubFunction(netlistp, "_trigger_andNot__" + m_name, false);
    funcp->slow(m_slow);
    funcp->isStatic(true);
    funcp->rtnType("bool");

    // Add arguments
    AstVarScope* const oVscp = newArgument(funcp, m_trigDTypep, "out", VDirection::OUTPUT);
    AstVarScope* const aVscp = newArgument(funcp, m_trigDTypep, "inA", VDirection::CONSTREF);
    AstVarScope* const bVscp = newArgument(funcp, m_trigDTypep, "inB", VDirection::CONSTREF);

    // Add loop counter variable
    AstVarScope* const nVscp
        = newLocal(funcp, netlistp->findBitDType(32, 32, VSigning::UNSIGNED), "n");
    nVscp->varp()->noReset(true);

    // Creates read/write reference
    const auto rd = [flp](AstVarScope* vp) { return new AstVarRef{flp, vp, VAccess::READ}; };
    const auto wr = [flp](AstVarScope* vp) { return new AstVarRef{flp, vp, VAccess::WRITE}; };

    // Function body
    AstLoop* const loopp = new AstLoop{flp};
    funcp->addStmtsp(util::setVar(nVscp, 0));
    funcp->addStmtsp(loopp);
    funcp->addStmtsp(new AstCReturn{flp, new AstConst{flp, AstConst::BitFalse{}}});

    // Loop body
    AstNodeExpr* const lhsp = new AstArraySel{flp, wr(oVscp), rd(nVscp)};
    AstNodeExpr* const aWordp = new AstArraySel{flp, rd(aVscp), rd(nVscp)};
    AstNodeExpr* const bWordp = new AstArraySel{flp, rd(bVscp), rd(nVscp)};
    AstNodeExpr* const rhsp = new AstAnd{flp, aWordp, new AstNot{flp, bWordp}};
    AstNodeExpr* const limp = new AstConst{flp, AstConst::WidthedValue{}, 32, m_nTotalWords};
    loopp->addStmtsp(new AstAssign{flp, lhsp, rhsp});
    loopp->addStmtsp(util::incrementVar(nVscp));
    loopp->addStmtsp(new AstLoopTest{flp, loopp, new AstLt{flp, rd(nVscp), limp}});

    // Done
    return funcp;
}
AstCFunc* TriggerKit::createAnySetFunc() const {
    AstNetlist* const netlistp = v3Global.rootp();
    FileLine* const flp = netlistp->topScopep()->fileline();

    // Create function
    AstCFunc* const funcp = util::makeSubFunction(netlistp, "_trigger_anySet__" + m_name, false);
    funcp->slow(m_slow);
    funcp->isStatic(true);
    funcp->rtnType("bool");

    // Add argument
    AstVarScope* const iVscp = newArgument(funcp, m_trigDTypep, "in", VDirection::CONSTREF);

    // Add loop counter variable
    AstVarScope* const nVscp
        = newLocal(funcp, netlistp->findBitDType(32, 32, VSigning::UNSIGNED), "n");
    nVscp->varp()->noReset(true);

    // Creates read reference
    const auto rd = [flp](AstVarScope* vp) { return new AstVarRef{flp, vp, VAccess::READ}; };

    // Function body
    AstLoop* const loopp = new AstLoop{flp};
    funcp->addStmtsp(util::setVar(nVscp, 0));
    funcp->addStmtsp(loopp);
    funcp->addStmtsp(new AstCReturn{flp, new AstConst{flp, AstConst::BitFalse{}}});

    // Loop body
    AstNodeExpr* const condp = new AstArraySel{flp, rd(iVscp), rd(nVscp)};
    AstNodeStmt* const thenp = new AstCReturn{flp, new AstConst{flp, AstConst::BitTrue{}}};
    AstNodeExpr* const limp = new AstConst{flp, AstConst::WidthedValue{}, 32, m_nTotalWords};
    loopp->addStmtsp(new AstIf{flp, condp, thenp});
    loopp->addStmtsp(util::incrementVar(nVscp));
    loopp->addStmtsp(new AstLoopTest{flp, loopp, new AstLt{flp, rd(nVscp), limp}});

    // Done
    return funcp;
}
AstCFunc* TriggerKit::createClearFunc() const {
    AstNetlist* const netlistp = v3Global.rootp();
    FileLine* const flp = netlistp->topScopep()->fileline();

    // Create function
    AstCFunc* const funcp = util::makeSubFunction(netlistp, "_trigger_clear__" + m_name, false);
    funcp->slow(m_slow);
    funcp->isStatic(true);
    funcp->rtnType("bool");

    // Add arguments
    AstVarScope* const oVscp = newArgument(funcp, m_trigDTypep, "out", VDirection::OUTPUT);

    // Add loop counter variable
    AstVarScope* const nVscp
        = newLocal(funcp, netlistp->findBitDType(32, 32, VSigning::UNSIGNED), "n");
    nVscp->varp()->noReset(true);

    // Creates read/write reference
    const auto rd = [flp](AstVarScope* vp) { return new AstVarRef{flp, vp, VAccess::READ}; };
    const auto wr = [flp](AstVarScope* vp) { return new AstVarRef{flp, vp, VAccess::WRITE}; };

    // Function body
    AstLoop* const loopp = new AstLoop{flp};
    funcp->addStmtsp(util::setVar(nVscp, 0));
    funcp->addStmtsp(loopp);
    funcp->addStmtsp(new AstCReturn{flp, new AstConst{flp, AstConst::BitFalse{}}});

    // Loop body
    AstNodeExpr* const lhsp = new AstArraySel{flp, wr(oVscp), rd(nVscp)};
    AstNodeExpr* const rhsp = new AstConst{flp, AstConst::DTyped{}, m_wordDTypep};
    AstNodeExpr* const limp = new AstConst{flp, AstConst::WidthedValue{}, 32, m_nTotalWords};
    loopp->addStmtsp(new AstAssign{flp, lhsp, rhsp});
    loopp->addStmtsp(util::incrementVar(nVscp));
    loopp->addStmtsp(new AstLoopTest{flp, loopp, new AstLt{flp, rd(nVscp), limp}});

    // Done
    return funcp;
}
AstCFunc* TriggerKit::createOrIntoFunc() const {
    AstNetlist* const netlistp = v3Global.rootp();
    FileLine* const flp = netlistp->topScopep()->fileline();

    // Create function
    AstCFunc* const funcp = util::makeSubFunction(netlistp, "_trigger_orInto__" + m_name, false);
    funcp->slow(m_slow);
    funcp->isStatic(true);
    funcp->rtnType("bool");

    // Add arguments
    AstVarScope* const oVscp = newArgument(funcp, m_trigDTypep, "out", VDirection::INOUT);
    AstVarScope* const iVscp = newArgument(funcp, m_trigDTypep, "in", VDirection::CONSTREF);

    // Add loop counter variable
    AstVarScope* const nVscp
        = newLocal(funcp, netlistp->findBitDType(32, 32, VSigning::UNSIGNED), "n");
    nVscp->varp()->noReset(true);

    // Creates read/write reference
    const auto rd = [flp](AstVarScope* vp) { return new AstVarRef{flp, vp, VAccess::READ}; };
    const auto wr = [flp](AstVarScope* vp) { return new AstVarRef{flp, vp, VAccess::WRITE}; };

    // Function body
    AstLoop* const loopp = new AstLoop{flp};
    funcp->addStmtsp(util::setVar(nVscp, 0));
    funcp->addStmtsp(loopp);
    funcp->addStmtsp(new AstCReturn{flp, new AstConst{flp, AstConst::BitFalse{}}});

    // Loop body
    AstNodeExpr* const lhsp = new AstArraySel{flp, wr(oVscp), rd(nVscp)};
    AstNodeExpr* const oWordp = new AstArraySel{flp, rd(oVscp), rd(nVscp)};
    AstNodeExpr* const iWordp = new AstArraySel{flp, rd(iVscp), rd(nVscp)};
    AstNodeExpr* const rhsp = new AstOr{flp, oWordp, iWordp};
    AstNodeExpr* const limp = new AstConst{flp, AstConst::WidthedValue{}, 32, m_nTotalWords};
    loopp->addStmtsp(new AstAssign{flp, lhsp, rhsp});
    loopp->addStmtsp(util::incrementVar(nVscp));
    loopp->addStmtsp(new AstLoopTest{flp, loopp, new AstLt{flp, rd(nVscp), limp}});

    // Done
    return funcp;
}

AstNodeStmt* TriggerKit::newAndNotCall(AstVarScope* const oVscp,  //
                                       AstVarScope* const aVscp,  //
                                       AstVarScope* const bVscp) const {
    if (!m_andNotp) m_andNotp = createAndNotFunc();
    FileLine* const flp = v3Global.rootp()->topScopep()->fileline();
    AstCCall* const callp = new AstCCall{flp, m_andNotp};
    callp->addArgsp(new AstVarRef{flp, oVscp, VAccess::WRITE});
    callp->addArgsp(new AstVarRef{flp, aVscp, VAccess::READ});
    callp->addArgsp(new AstVarRef{flp, bVscp, VAccess::READ});
    callp->dtypeSetVoid();
    return callp->makeStmt();
}
AstNodeExpr* TriggerKit::newAnySetCall(AstVarScope* const vscp) const {
    if (!m_anySetp) m_anySetp = createAnySetFunc();
    FileLine* const flp = v3Global.rootp()->topScopep()->fileline();
    AstCCall* const callp = new AstCCall{flp, m_anySetp};
    callp->addArgsp(new AstVarRef{flp, vscp, VAccess::WRITE});
    callp->dtypeSetBit();
    return callp;
}
AstNodeStmt* TriggerKit::newClearCall(AstVarScope* const vscp) const {
    if (!m_clearp) m_clearp = createClearFunc();
    FileLine* const flp = v3Global.rootp()->topScopep()->fileline();
    AstCCall* const callp = new AstCCall{flp, m_clearp};
    callp->addArgsp(new AstVarRef{flp, vscp, VAccess::WRITE});
    callp->dtypeSetVoid();
    return callp->makeStmt();
}
AstNodeStmt* TriggerKit::newOrIntoCall(AstVarScope* const oVscp, AstVarScope* const iVscp) const {
    if (!m_orIntop) m_orIntop = createOrIntoFunc();
    FileLine* const flp = v3Global.rootp()->topScopep()->fileline();
    AstCCall* const callp = new AstCCall{flp, m_orIntop};
    callp->addArgsp(new AstVarRef{flp, oVscp, VAccess::WRITE});
    callp->addArgsp(new AstVarRef{flp, iVscp, VAccess::READ});
    callp->dtypeSetVoid();
    return callp->makeStmt();
}

AstNodeStmt* TriggerKit::newCompCall() const { return util::callVoidFunc(m_compp); }

AstNodeStmt* TriggerKit::newDumpCall(AstVarScope* const vscp, const std::string& tag,
                                     bool debugOnly) const {
    FileLine* const flp = v3Global.rootp()->topScopep()->fileline();
    AstCCall* const callp = new AstCCall{flp, m_dumpp};
    callp->addArgsp(new AstVarRef{flp, vscp, VAccess::READ});
    callp->addArgsp(new AstConst{flp, AstConst::String{}, tag});
    callp->dtypeSetVoid();
    AstCStmt* const cstmtp = new AstCStmt{flp};
    cstmtp->add("#ifdef VL_DEBUG\n");
    if (debugOnly) {
        cstmtp->add("if (VL_UNLIKELY(vlSymsp->_vm_contextp__->debug())) {\n");
        cstmtp->add(callp->makeStmt());
        cstmtp->add("}\n");
    } else {
        cstmtp->add(callp->makeStmt());
    }
    cstmtp->add("#endif");
    return cstmtp;
}

AstSenTree* TriggerKit::newTriggerSenTree(AstVarScope* const vscp,
                                          const std::vector<uint32_t>& indices) const {
    AstNetlist* const netlistp = v3Global.rootp();
    AstTopScope* const topScopep = netlistp->topScopep();
    FileLine* const flp = topScopep->fileline();

    AstSenTree* const senTreep = new AstSenTree{flp, nullptr};
    topScopep->addSenTreesp(senTreep);
    for (const uint32_t index : indices) {
        UASSERT(index <= m_nTotalWords * WORD_SIZE, "Invalid trigger index");
        const uint32_t wordIndex = index / WORD_SIZE;
        const uint32_t bitIndex = index % WORD_SIZE;
        AstVarRef* const refp = new AstVarRef{flp, vscp, VAccess::READ};
        AstNodeExpr* const aselp = new AstArraySel{flp, refp, static_cast<int>(wordIndex)};
        // Use a mask & _ to extract the bit, V3Const can optimize this to combine terms
        AstConst* const maskp
            = new AstConst{flp, AstConst::WidthedValue{}, static_cast<int>(WORD_SIZE), 0};
        maskp->num().setBit(bitIndex, '1');
        AstNodeExpr* const termp = new AstAnd{flp, maskp, aselp};
        senTreep->addSensesp(new AstSenItem{flp, VEdgeType::ET_TRUE, termp});
    }
    return senTreep;
}

void TriggerKit::addExtraTriggerAssignment(AstVarScope* vscp, uint32_t index) const {
    const uint32_t wordIndex = index / WORD_SIZE;
    const uint32_t bitIndex = index % WORD_SIZE;
    FileLine* const flp = vscp->fileline();
    // Set the trigger bit
    AstVarRef* const refp = new AstVarRef{flp, m_vscp, VAccess::WRITE};
    AstNodeExpr* const wordp = new AstArraySel{flp, refp, static_cast<int>(wordIndex)};
    AstNodeExpr* const trigLhsp = new AstSel{flp, wordp, static_cast<int>(bitIndex), 1};
    AstNodeExpr* const trigRhsp = new AstVarRef{flp, vscp, VAccess::READ};
    AstNodeStmt* const setp = new AstAssign{flp, trigLhsp, trigRhsp};
    // Clear the input variable
    AstNodeExpr* const vscpLhsp = new AstVarRef{flp, vscp, VAccess::WRITE};
    AstNodeExpr* const vscpRhsp = new AstConst{flp, AstConst::BitFalse{}};
    AstNodeStmt* const clrp = new AstAssign{flp, vscpLhsp, vscpRhsp};
    // Note these are added in reverse order, so 'setp' executes before 'clrp'
    m_compp->stmtsp()->addHereThisAsNext(clrp);
    m_compp->stmtsp()->addHereThisAsNext(setp);
}

TriggerKit::TriggerKit(const std::string& name, bool slow, uint32_t nSenseWords,
                       uint32_t nExtraWords)
    : m_name{name}
    , m_slow{slow}
    , m_nSenseWords{nSenseWords}
    , m_nExtraWords{nExtraWords} {
    AstNetlist* const netlistp = v3Global.rootp();
    AstScope* const scopep = netlistp->topScopep()->scopep();
    FileLine* const flp = scopep->fileline();
    // Data type of a single trigger word
    m_wordDTypep = netlistp->findBitDType(WORD_SIZE, WORD_SIZE, VSigning::UNSIGNED);
    // Data type of a trigger vector
    AstRange* const rangep = new AstRange{flp, static_cast<int>(m_nTotalWords - 1), 0};
    m_trigDTypep = new AstUnpackArrayDType{flp, m_wordDTypep, rangep};
    netlistp->typeTablep()->addTypesp(m_trigDTypep);
    // The AstVarScope representing the trigger vector
    m_vscp = scopep->createTemp("__V" + m_name + "Triggered", m_trigDTypep);
    m_vscp->varp()->isInternal(true);
    // The trigger computation function
    m_compp = util::makeSubFunction(netlistp, "_eval_triggers__" + m_name, m_slow);
    // The debug dump function, always 'slow'
    m_dumpp = util::makeSubFunction(netlistp, "_dump_triggers__" + m_name, true);
    m_dumpp->isStatic(true);
    m_dumpp->ifdef("VL_DEBUG");
}

const TriggerKit TriggerKit::create(AstNetlist* netlistp,  //
                                    AstCFunc* const initFuncp,  //
                                    SenExprBuilder& senExprBuilder,  //
                                    const std::vector<const AstSenTree*>& senTreeps,  //
                                    const string& name,  //
                                    const ExtraTriggers& extraTriggers,  //
                                    bool slow) {
    FileLine* const flp = netlistp->topScopep()->fileline();

    // Number of extra triggers, rounded up to a full word. These occupy the lowest words.
    const uint32_t nExtraTriggers = vlstd::roundUpToMultipleOf<WORD_SIZE>(extraTriggers.size());
    const uint32_t nExtraWords = nExtraTriggers / WORD_SIZE;

    // Gather all the unique SenItems under the SenTrees
    // List of unique SenItems used by all 'senTreeps'
    std::vector<const AstSenItem*> senItemps;
    // Map from SenItem to tigger bit standing for that SenItem. There might
    // be duplicate SenItems, we map all of them to the same index.
    std::unordered_map<VNRef<const AstSenItem>, size_t> senItem2TrigIdx;
    for (const AstSenTree* const senTreep : senTreeps) {
        for (const AstSenItem *itemp = senTreep->sensesp(), *nextp; itemp; itemp = nextp) {
            nextp = VN_AS(itemp->nextp(), SenItem);
            UASSERT_OBJ(itemp->isClocked() || itemp->isHybrid(), itemp,
                        "Cannot create trigger expression for non-clocked sensitivity");

            const auto pair = senItem2TrigIdx.emplace(*itemp, nExtraTriggers + senItemps.size());
            if (pair.second) senItemps.push_back(itemp);
        }
    }
    UASSERT(senItemps.size() == senItem2TrigIdx.size(), "Inconsitent SenItem to trigger map");

    // Number of sense triggers, rounded up to a full word
    const uint32_t nSenseTriggers = vlstd::roundUpToMultipleOf<WORD_SIZE>(senItemps.size());
    const uint32_t nSenseWords = nSenseTriggers / WORD_SIZE;

    // Pad 'senItemps' to nSenseTriggers with nullptr
    senItemps.resize(nSenseTriggers);

    // We can now construct the trigger kit - this construct all items that will be kept
    TriggerKit kit{name, slow, nSenseWords, nExtraWords};

    // Construct the comp and dump functions

    // Add arguments to the dump function. The trigger vector is passed into
    // the dumping function via reference so one dump function can dump all
    // different copies of the trigger vector. To do so, it also needs the tag
    // string at runtime, which is the second argument.
    AstVarScope* const dumpTrgp
        = newArgument(kit.m_dumpp, kit.m_trigDTypep, "triggers", VDirection::CONSTREF);
    AstVarScope* const dumpTagp
        = newArgument(kit.m_dumpp, netlistp->findStringDType(), "tag", VDirection::CONSTREF);

    // Add a print to the dumping function if there are no triggers pending
    {
        AstIf* const ifp = new AstIf{flp, new AstLogNot{flp, kit.newAnySetCall(dumpTrgp)}};
        kit.m_dumpp->addStmtsp(ifp);
        AstCStmt* const cstmtp = new AstCStmt{flp};
        ifp->addThensp(cstmtp);
        cstmtp->add("VL_DBG_MSGS(\"         No '\" + ");
        cstmtp->add(new AstVarRef{flp, dumpTagp, VAccess::READ});
        cstmtp->add(" + \"\' region triggers active\\n\");");
    }

    // Adds a debug dumping statement for this trigger
    const auto addDebug = [&](uint32_t index, const string& text) {
        AstVarRef* const refp = new AstVarRef{flp, dumpTrgp, VAccess::READ};
        const int wrdIndex = static_cast<int>(index / WORD_SIZE);
        const int bitIndex = static_cast<int>(index % WORD_SIZE);
        AstNodeExpr* const aselp = new AstArraySel{flp, refp, wrdIndex};
        AstNodeExpr* const condp = new AstSel{flp, aselp, bitIndex, 1};
        AstIf* const ifp = new AstIf{flp, condp};
        kit.m_dumpp->addStmtsp(ifp);
        AstCStmt* const cstmtp = new AstCStmt{flp};
        ifp->addThensp(cstmtp);
        cstmtp->add("VL_DBG_MSGS(\"         '\" + ");
        cstmtp->add(new AstVarRef{flp, dumpTagp, VAccess::READ});
        cstmtp->add(" + \"' region trigger index " + std::to_string(index) + " is active: " + text
                    + "\\n\");");
    };

    // Add a print for each of the extra triggers
    for (unsigned i = 0; i < extraTriggers.size(); ++i) {
        addDebug(i, "Internal '" + name + "' trigger - " + extraTriggers.m_descriptions.at(i));
    }

    // Add sense trigger computation
    // List of trigger computation expressions
    std::vector<AstNodeExpr*> trigps;
    trigps.reserve(nSenseTriggers);
    // Statements to exectue at initialization time to fire initial triggers
    AstNodeStmt* initialTrigsp = nullptr;
    for (size_t i = 0; i < senItemps.size(); ++i) {
        const AstSenItem* const senItemp = senItemps[i];

        // If this is just paddign, use constant zero
        if (!senItemp) {
            trigps.emplace_back(new AstConst{flp, AstConst::BitFalse{}});
            continue;
        }

        // Index of this trigger in the trigger vector
        const uint32_t index = nExtraTriggers + i;

        // Create the trigger computation expression
        const auto& pair = senExprBuilder.build(senItemp);
        trigps.emplace_back(pair.first);

        // Add initialization time trigger
        if (pair.second || v3Global.opt.xInitialEdge()) {
            AstVarRef* const refp = new AstVarRef{flp, kit.m_vscp, VAccess::WRITE};
            const int wrdIndex = static_cast<int>(index / WORD_SIZE);
            const int bitIndex = static_cast<int>(index % WORD_SIZE);
            AstNodeExpr* const wordp = new AstArraySel{flp, refp, wrdIndex};
            AstNodeExpr* const lhsp = new AstSel{flp, wordp, bitIndex, 1};
            AstNodeExpr* const rhsp = new AstConst{flp, AstConst::BitTrue{}};
            initialTrigsp = AstNode::addNext(initialTrigsp, new AstAssign{flp, lhsp, rhsp});
        }

        // Add a debug statement for this trigger
        std::stringstream ss;
        ss << "@(";
        V3EmitV::verilogForTree(senItemp, ss);
        ss << ")";
        std::string desc = VString::quoteBackslash(ss.str());
        desc = VString::replaceSubstr(desc, "\n", "\\n");
        addDebug(index, desc);
    }
    UASSERT(trigps.size() == nSenseTriggers, "Inconsistent number of trigger expressions");

    // Assign trigger vector one word at a time
    AstNodeStmt* trigStmtsp = nullptr;
    for (size_t i = 0; i < nSenseTriggers; i += WORD_SIZE) {
        // Concatenate all bits in this trigger word using a balanced
        for (uint32_t level = 0; level < WORD_SIZE_LOG2; ++level) {
            const uint32_t stride = 1 << level;
            for (uint32_t j = 0; j < WORD_SIZE; j += 2 * stride) {
                FileLine* const flp = trigps[i + j]->fileline();
                trigps[i + j] = new AstConcat{flp, trigps[i + j + stride], trigps[i + j]};
                trigps[i + j + stride] = nullptr;
            }
        }

        // Set the whole word in the trigger vector
        const uint32_t wordIndex = nExtraWords + i / WORD_SIZE;
        AstVarRef* const refp = new AstVarRef{flp, kit.m_vscp, VAccess::WRITE};
        AstArraySel* const aselp = new AstArraySel{flp, refp, static_cast<int>(wordIndex)};
        trigStmtsp = AstNode::addNext(trigStmtsp, new AstAssign{flp, aselp, trigps[i]});
    }
    trigps.clear();

    // Construct the map from old SenTrees to new SenTrees
    {
        std::vector<uint32_t> indices;
        indices.reserve(32);
        for (const AstSenTree* const senTreep : senTreeps) {
            indices.clear();
            for (const AstSenItem *itemp = senTreep->sensesp(), *nextp; itemp; itemp = nextp) {
                nextp = VN_AS(itemp->nextp(), SenItem);
                indices.push_back(senItem2TrigIdx.at(*itemp));
            }
            kit.m_map[senTreep] = kit.newTriggerSenTree(kit.m_vscp, indices);
        }
    }

    // Get the SenExprBuilder results
    const SenExprBuilder::Results senResults = senExprBuilder.getAndClearResults();

    // Add the SenExprBuilder init statements to the static initialization functino
    for (AstNodeStmt* const nodep : senResults.m_inits) initFuncp->addStmtsp(nodep);

    // Assemble the trigger computation function
    {
        AstCFunc* const fp = kit.m_compp;
        // Profiling push
        if (v3Global.opt.profExec()) fp->addStmtsp(util::profExecSectionPush(flp, "trig " + name));
        // Trigger computation
        for (AstNodeStmt* const nodep : senResults.m_preUpdates) fp->addStmtsp(nodep);
        fp->addStmtsp(trigStmtsp);
        for (AstNodeStmt* const nodep : senResults.m_postUpdates) fp->addStmtsp(nodep);
        // Add the initialization time triggers
        if (initialTrigsp) {
            AstScope* const scopep = netlistp->topScopep()->scopep();
            AstVarScope* const vscp = scopep->createTemp("__V" + name + "DidInit", 1);
            AstVarRef* const condp = new AstVarRef{flp, vscp, VAccess::READ};
            AstIf* const ifp = new AstIf{flp, new AstNot{flp, condp}};
            fp->addStmtsp(ifp);
            ifp->branchPred(VBranchPred::BP_UNLIKELY);
            ifp->addThensp(util::setVar(vscp, 1));
            ifp->addThensp(initialTrigsp);
        }
        // Add a call to the dumping function if debug is enabled
        fp->addStmtsp(kit.newDumpCall(kit.m_vscp, name, true));
        // Profiling pop
        if (v3Global.opt.profExec()) fp->addStmtsp(util::profExecSectionPop(flp));
        // Done with the trigger computation function, split as might be large
        util::splitCheck(fp);
    };

    // The debug code might leak signal names, so simply delete it when using --protect-ids
    if (v3Global.opt.protectIds()) kit.m_dumpp->stmtsp()->unlinkFrBackWithNext()->deleteTree();
    // Done with the trigger dump function, split as might be large
    util::splitCheck(kit.m_dumpp);

    return kit;
}

}  // namespace V3Sched
