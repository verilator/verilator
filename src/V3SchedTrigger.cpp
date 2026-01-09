// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Create triggers for code scheduling
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2026 by Wilson Snyder. This program is free software; you
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
    varp->noReset(true);
    funcp->addVarsp(varp);
    AstVarScope* const vscp = new AstVarScope{flp, scopep, varp};
    scopep->addVarsp(vscp);
    return vscp;
}

}  // namespace

AstCFunc* TriggerKit::createDumpExtFunc() const {
    UASSERT(m_nPreWords, "Just call the regular dumping function if there are no pre triggers");

    AstNetlist* const netlistp = v3Global.rootp();
    FileLine* const flp = netlistp->topScopep()->fileline();
    AstNodeDType* const u32DTypep = netlistp->findUInt32DType();
    AstNodeDType* const strDtypep = netlistp->findStringDType();

    // Dumping function always slow
    const std::string name = "_dump_triggers__" + m_name + "_ext";
    AstCFunc* const funcp = util::makeSubFunction(netlistp, name, true);
    funcp->isStatic(true);
    funcp->ifdef("VL_DEBUG");

    // Add argument
    AstVarScope* const eVscp = newArgument(funcp, m_trigExtDTypep, "ext", VDirection::CONSTREF);
    AstVarScope* const tVscp = newArgument(funcp, strDtypep, "tag", VDirection::CONSTREF);

    // Creates read/write reference
    const auto rd = [flp](AstVarScope* vp) { return new AstVarRef{flp, vp, VAccess::READ}; };
    const auto wr = [flp](AstVarScope* vp) { return new AstVarRef{flp, vp, VAccess::WRITE}; };

    // This is a slow function, only for dumping, so we can just copy to locals

    // Copy the vec part, dump it
    {
        AstVarScope* const vVscp = newLocal(funcp, m_trigVecDTypep, "vec");
        AstVarScope* const iVscp = newLocal(funcp, u32DTypep, "i");
        funcp->addStmtsp(util::setVar(iVscp, 0));
        // Add loop
        AstLoop* const loopp = new AstLoop{flp};
        funcp->addStmtsp(loopp);
        // Loop body
        AstNodeExpr* const lhsp = new AstArraySel{flp, wr(vVscp), rd(iVscp)};
        AstNodeExpr* const rhsp = new AstArraySel{flp, rd(eVscp), rd(iVscp)};
        AstNodeExpr* const limp = new AstConst{flp, AstConst::WidthedValue{}, 32, m_nVecWords};
        loopp->addStmtsp(new AstAssign{flp, lhsp, rhsp});
        loopp->addStmtsp(util::incrementVar(iVscp));
        loopp->addStmtsp(new AstLoopTest{flp, loopp, new AstLt{flp, rd(iVscp), limp}});
        // Use the vec dumping function
        AstCCall* const callp = new AstCCall{flp, m_dumpp};
        callp->dtypeSetVoid();
        callp->addArgsp(rd(vVscp));
        callp->addArgsp(rd(tVscp));
        funcp->addStmtsp(callp->makeStmt());
    }

    // Copy the pre part, zero top bits, dump it
    {
        AstVarScope* const pVscp = newLocal(funcp, m_trigVecDTypep, "pre");
        AstVarScope* const jVscp = newLocal(funcp, u32DTypep, "j");
        funcp->addStmtsp(util::setVar(jVscp, 0));
        // Copy pre words
        {
            // Add loop
            AstLoop* const loopp = new AstLoop{flp};
            funcp->addStmtsp(loopp);
            // Loop body
            AstNodeExpr* const lhsp = new AstArraySel{flp, wr(pVscp), rd(jVscp)};
            AstNodeExpr* const rhsp = new AstArraySel{flp, rd(eVscp), rd(jVscp)};
            AstNodeExpr* const limp = new AstConst{flp, AstConst::WidthedValue{}, 32, m_nPreWords};
            loopp->addStmtsp(new AstAssign{flp, lhsp, rhsp});
            loopp->addStmtsp(util::incrementVar(jVscp));
            loopp->addStmtsp(new AstLoopTest{flp, loopp, new AstLt{flp, rd(jVscp), limp}});
        }
        // Zero the rest
        {
            // Add loop - copy
            AstLoop* const loopp = new AstLoop{flp};
            funcp->addStmtsp(loopp);
            // Loop body
            AstNodeExpr* const lhsp = new AstArraySel{flp, wr(pVscp), rd(jVscp)};
            AstNodeExpr* const rhsp = new AstConst{flp, AstConst::DTyped{}, m_wordDTypep};
            AstNodeExpr* const limp = new AstConst{flp, AstConst::WidthedValue{}, 32, m_nVecWords};
            loopp->addStmtsp(new AstAssign{flp, lhsp, rhsp});
            loopp->addStmtsp(util::incrementVar(jVscp));
            loopp->addStmtsp(new AstLoopTest{flp, loopp, new AstLt{flp, rd(jVscp), limp}});
        }
        // Use the vec dumping function
        AstCCall* const callp = new AstCCall{flp, m_dumpp};
        callp->dtypeSetVoid();
        callp->addArgsp(rd(pVscp));
        callp->addArgsp(
            new AstConcatN{flp, rd(tVscp), new AstConst{flp, AstConst::String{}, " pre"}});
        funcp->addStmtsp(callp->makeStmt());
    }

    return funcp;
}

AstCFunc* TriggerKit::createAnySetFunc(AstUnpackArrayDType* const dtypep) const {
    AstNetlist* const netlistp = v3Global.rootp();
    FileLine* const flp = netlistp->topScopep()->fileline();
    AstNodeDType* const u32DTypep = netlistp->findUInt32DType();

    // Create function
    std::string name = "_trigger_anySet__" + m_name;
    name += dtypep == m_trigVecDTypep ? "" : "_ext";
    AstCFunc* const funcp = util::makeSubFunction(netlistp, name, m_slow);
    funcp->isStatic(true);
    funcp->rtnType("bool");

    // Add argument
    AstVarScope* const iVscp = newArgument(funcp, dtypep, "in", VDirection::CONSTREF);

    // Add loop counter variable
    AstVarScope* const nVscp = newLocal(funcp, u32DTypep, "n");

    // Creates read reference
    const auto rd = [flp](AstVarScope* vp) { return new AstVarRef{flp, vp, VAccess::READ}; };

    // Function body
    AstLoop* const loopp = new AstLoop{flp};
    funcp->addStmtsp(util::setVar(nVscp, 0));
    funcp->addStmtsp(loopp);
    funcp->addStmtsp(new AstCReturn{flp, new AstConst{flp, AstConst::BitFalse{}}});

    // Loop body
    const uint32_t nWords = dtypep->elementsConst();
    AstNodeExpr* const condp = new AstArraySel{flp, rd(iVscp), rd(nVscp)};
    AstNodeStmt* const thenp = new AstCReturn{flp, new AstConst{flp, AstConst::BitTrue{}}};
    AstNodeExpr* const limp = new AstConst{flp, AstConst::WidthedValue{}, 32, nWords};
    loopp->addStmtsp(new AstIf{flp, condp, thenp});
    loopp->addStmtsp(util::incrementVar(nVscp));
    loopp->addStmtsp(new AstLoopTest{flp, loopp, new AstLt{flp, rd(nVscp), limp}});

    // Done
    return funcp;
}
AstCFunc* TriggerKit::createClearFunc() const {
    AstNetlist* const netlistp = v3Global.rootp();
    FileLine* const flp = netlistp->topScopep()->fileline();
    AstNodeDType* const u32DTypep = netlistp->findUInt32DType();

    // Create function
    AstCFunc* const funcp = util::makeSubFunction(netlistp, "_trigger_clear__" + m_name, m_slow);
    funcp->isStatic(true);

    // Add arguments
    AstVarScope* const oVscp = newArgument(funcp, m_trigVecDTypep, "out", VDirection::OUTPUT);

    // Add loop counter variable
    AstVarScope* const nVscp = newLocal(funcp, u32DTypep, "n");

    // Creates read/write reference
    const auto rd = [flp](AstVarScope* vp) { return new AstVarRef{flp, vp, VAccess::READ}; };
    const auto wr = [flp](AstVarScope* vp) { return new AstVarRef{flp, vp, VAccess::WRITE}; };

    // Function body
    AstLoop* const loopp = new AstLoop{flp};
    funcp->addStmtsp(util::setVar(nVscp, 0));
    funcp->addStmtsp(loopp);

    // Loop body
    AstNodeExpr* const lhsp = new AstArraySel{flp, wr(oVscp), rd(nVscp)};
    AstNodeExpr* const rhsp = new AstConst{flp, AstConst::DTyped{}, m_wordDTypep};
    AstNodeExpr* const limp = new AstConst{flp, AstConst::WidthedValue{}, 32, m_nVecWords};
    loopp->addStmtsp(new AstAssign{flp, lhsp, rhsp});
    loopp->addStmtsp(util::incrementVar(nVscp));
    loopp->addStmtsp(new AstLoopTest{flp, loopp, new AstLt{flp, rd(nVscp), limp}});

    // Done
    return funcp;
}
AstCFunc* TriggerKit::createOrIntoFunc(AstUnpackArrayDType* const iDtypep) const {
    AstNetlist* const netlistp = v3Global.rootp();
    FileLine* const flp = netlistp->topScopep()->fileline();
    AstNodeDType* const u32DTypep = netlistp->findUInt32DType();

    // Create function
    std::string name = "_trigger_orInto__" + m_name;
    name += iDtypep == m_trigVecDTypep ? "" : "_ext";
    AstCFunc* const funcp = util::makeSubFunction(netlistp, name, m_slow);
    funcp->isStatic(true);

    // Add arguments
    AstVarScope* const oVscp = newArgument(funcp, m_trigVecDTypep, "out", VDirection::INOUT);
    AstVarScope* const iVscp = newArgument(funcp, iDtypep, "in", VDirection::CONSTREF);

    // Add loop counter variable
    AstVarScope* const nVscp = newLocal(funcp, u32DTypep, "n");

    // Creates read/write reference
    const auto rd = [flp](AstVarScope* vp) { return new AstVarRef{flp, vp, VAccess::READ}; };
    const auto wr = [flp](AstVarScope* vp) { return new AstVarRef{flp, vp, VAccess::WRITE}; };

    // Function body
    AstLoop* const loopp = new AstLoop{flp};
    funcp->addStmtsp(util::setVar(nVscp, 0));
    funcp->addStmtsp(loopp);

    // Loop body
    AstNodeExpr* const lhsp = new AstArraySel{flp, wr(oVscp), rd(nVscp)};
    AstNodeExpr* const oWordp = new AstArraySel{flp, rd(oVscp), rd(nVscp)};
    AstNodeExpr* const iWordp = new AstArraySel{flp, rd(iVscp), rd(nVscp)};
    AstNodeExpr* const rhsp = new AstOr{flp, oWordp, iWordp};
    AstNodeExpr* const limp = new AstConst{flp, AstConst::WidthedValue{}, 32, m_nVecWords};
    loopp->addStmtsp(new AstAssign{flp, lhsp, rhsp});
    loopp->addStmtsp(util::incrementVar(nVscp));
    loopp->addStmtsp(new AstLoopTest{flp, loopp, new AstLt{flp, rd(nVscp), limp}});

    // Done
    return funcp;
}

AstNodeExpr* TriggerKit::newAnySetCall(AstVarScope* const vscp) const {
    FileLine* const flp = v3Global.rootp()->topScopep()->fileline();
    if (!m_nVecWords) return new AstConst{flp, AstConst::BitFalse{}};

    AstCFunc* funcp = nullptr;
    if (vscp->dtypep() == m_trigVecDTypep) {
        if (!m_anySetVecp) m_anySetVecp = createAnySetFunc(m_trigVecDTypep);
        funcp = m_anySetVecp;
    } else if (vscp->dtypep() == m_trigExtDTypep) {
        if (!m_anySetExtp) m_anySetExtp = createAnySetFunc(m_trigExtDTypep);
        funcp = m_anySetExtp;
    } else {
        vscp->v3fatalSrc("Bad trigger vector type");
    }
    AstCCall* const callp = new AstCCall{flp, funcp};
    callp->addArgsp(new AstVarRef{flp, vscp, VAccess::WRITE});
    callp->dtypeSetBit();
    return callp;
}
AstNodeStmt* TriggerKit::newClearCall(AstVarScope* const vscp) const {
    if (!m_nVecWords) return nullptr;
    UASSERT_OBJ(vscp->dtypep() == m_trigVecDTypep, vscp, "Bad trigger vector type");
    if (!m_clearp) m_clearp = createClearFunc();
    FileLine* const flp = v3Global.rootp()->topScopep()->fileline();
    AstCCall* const callp = new AstCCall{flp, m_clearp};
    callp->addArgsp(new AstVarRef{flp, vscp, VAccess::WRITE});
    callp->dtypeSetVoid();
    return callp->makeStmt();
}
AstNodeStmt* TriggerKit::newOrIntoCall(AstVarScope* const oVscp, AstVarScope* const iVscp) const {
    if (!m_nVecWords) return nullptr;
    UASSERT_OBJ(oVscp->dtypep() == m_trigVecDTypep, oVscp, "Bad trigger vector type");
    AstCFunc* funcp = nullptr;
    if (iVscp->dtypep() == m_trigVecDTypep) {
        if (!m_orIntoVecp) m_orIntoVecp = createOrIntoFunc(m_trigVecDTypep);
        funcp = m_orIntoVecp;
    } else if (iVscp->dtypep() == m_trigExtDTypep) {
        if (!m_orIntoExtp) m_orIntoExtp = createOrIntoFunc(m_trigExtDTypep);
        funcp = m_orIntoExtp;
    } else {
        iVscp->v3fatalSrc("Bad trigger vector type");
    }
    FileLine* const flp = v3Global.rootp()->topScopep()->fileline();
    AstCCall* const callp = new AstCCall{flp, funcp};
    callp->addArgsp(new AstVarRef{flp, oVscp, VAccess::WRITE});
    callp->addArgsp(new AstVarRef{flp, iVscp, VAccess::READ});
    callp->dtypeSetVoid();
    return callp->makeStmt();
}

AstNodeStmt* TriggerKit::newCompCall(AstVarScope* vscp) const {
    if (!m_nVecWords) return nullptr;
    // If there are pre triggers, we need the argument
    UASSERT(!m_nPreWords || vscp, "Need latched values for pre trigger compute");
    FileLine* const flp = v3Global.rootp()->topScopep()->fileline();
    AstCCall* const callp = new AstCCall{flp, m_compp};
    if (m_nPreWords) callp->addArgsp(new AstVarRef{flp, vscp, VAccess::READ});
    callp->dtypeSetVoid();
    return callp->makeStmt();
}

AstNodeStmt* TriggerKit::newDumpCall(AstVarScope* const vscp, const std::string& tag,
                                     bool debugOnly) const {
    if (!m_nVecWords) return nullptr;
    AstCFunc* funcp = nullptr;
    if (vscp->dtypep() == m_trigVecDTypep) {
        funcp = m_dumpp;
    } else if (vscp->dtypep() == m_trigExtDTypep) {
        if (!m_dumpExtp) m_dumpExtp = createDumpExtFunc();
        funcp = m_dumpExtp;
    } else {
        vscp->v3fatalSrc("Bad trigger vector type");
    }
    FileLine* const flp = v3Global.rootp()->topScopep()->fileline();
    AstCCall* const callp = new AstCCall{flp, funcp};
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

AstVarScope* TriggerKit::newTrigVec(const std::string& name) const {
    if (!m_nVecWords) return nullptr;
    AstScope* const scopep = v3Global.rootp()->topScopep()->scopep();
    return scopep->createTemp("__V" + name + "Triggered", m_trigVecDTypep);
}

AstSenTree* TriggerKit::newTriggerSenTree(AstVarScope* const vscp,
                                          const std::vector<uint32_t>& indices) const {
    AstNetlist* const netlistp = v3Global.rootp();
    AstTopScope* const topScopep = netlistp->topScopep();
    FileLine* const flp = topScopep->fileline();

    AstSenTree* const senTreep = new AstSenTree{flp, nullptr};
    topScopep->addSenTreesp(senTreep);
    for (const uint32_t index : indices) {
        UASSERT(index <= (m_nVecWords + m_nPreWords) * WORD_SIZE, "Invalid trigger index");
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

AstSenTree* TriggerKit::newExtraTriggerSenTree(AstVarScope* vscp, uint32_t index) const {
    UASSERT(index <= m_nExtraWords * WORD_SIZE, "Invalid external trigger index");
    return newTriggerSenTree(vscp, {index + m_nSenseWords * WORD_SIZE});
}

void TriggerKit::addExtraTriggerAssignment(AstVarScope* vscp, uint32_t index) const {
    index += m_nSenseWords * WORD_SIZE;
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
                       uint32_t nExtraWords, uint32_t nPreWords)
    : m_name{name}
    , m_slow{slow}
    , m_nSenseWords{nSenseWords}
    , m_nExtraWords{nExtraWords}
    , m_nPreWords{nPreWords} {
    // If no triggers, we don't need to generate anything
    if (!m_nVecWords) return;
    // Othewise construc the parts of the kit
    AstNetlist* const netlistp = v3Global.rootp();
    AstScope* const scopep = netlistp->topScopep()->scopep();
    FileLine* const flp = scopep->fileline();
    // Data type of a single trigger word
    m_wordDTypep = netlistp->findBitDType(WORD_SIZE, WORD_SIZE, VSigning::UNSIGNED);
    // Data type of trigger vector
    AstRange* const rp = new AstRange{flp, static_cast<int>(m_nVecWords - 1), 0};
    m_trigVecDTypep = new AstUnpackArrayDType{flp, m_wordDTypep, rp};
    netlistp->typeTablep()->addTypesp(m_trigVecDTypep);
    // Data type of extended trigger vector, which only differs if there are pre triggers
    if (m_nPreWords) {
        AstRange* const ep = new AstRange{flp, static_cast<int>(m_nVecWords + m_nPreWords - 1), 0};
        m_trigExtDTypep = new AstUnpackArrayDType{flp, m_wordDTypep, ep};
        netlistp->typeTablep()->addTypesp(m_trigExtDTypep);
    } else {
        m_trigExtDTypep = m_trigVecDTypep;
    }
    // The AstVarScope representing the extended trigger vector
    m_vscp = scopep->createTemp("__V" + m_name + "Triggered", m_trigExtDTypep);
    m_vscp->varp()->isInternal(true);
    // The trigger computation function
    m_compp = util::makeSubFunction(netlistp, "_eval_triggers__" + m_name, m_slow);
    // The debug dump function, always 'slow'
    m_dumpp = util::makeSubFunction(netlistp, "_dump_triggers__" + m_name, true);
    m_dumpp->isStatic(true);
    m_dumpp->ifdef("VL_DEBUG");
}

TriggerKit TriggerKit::create(AstNetlist* netlistp,  //
                              AstCFunc* const initFuncp,  //
                              SenExprBuilder& senExprBuilder,  //
                              const std::vector<const AstSenTree*>& preTreeps,  //
                              const std::vector<const AstSenTree*>& senTreeps,  //
                              const string& name,  //
                              const ExtraTriggers& extraTriggers,  //
                              bool slow) {
    // Need to gather all the unique SenItems under the given SenTrees

    // List of unique SenItems used by all 'senTreeps'
    std::vector<const AstSenItem*> senItemps;
    // Map from SenItem to trigger bit standing for that SenItem. There might
    // be duplicate SenItems, we map all of them to the same index.
    std::unordered_map<VNRef<const AstSenItem>, size_t> senItem2TrigIdx;

    // Process the 'pre' trees first, so they are at the begining of the vector
    for (const AstSenTree* const senTreep : preTreeps) {
        for (const AstSenItem *itemp = senTreep->sensesp(), *nextp; itemp; itemp = nextp) {
            nextp = VN_AS(itemp->nextp(), SenItem);
            UASSERT_OBJ(itemp->isClocked() || itemp->isHybrid(), itemp,
                        "Cannot create trigger expression for non-clocked sensitivity");
            const auto pair = senItem2TrigIdx.emplace(*itemp, senItemps.size());
            if (pair.second) senItemps.push_back(itemp);
        }
    }
    const uint32_t nPreSenItems = senItemps.size();
    V3Stats::addStat("Scheduling, '" + name + "' pre triggers", nPreSenItems);
    // Number of pre triggers, rounded up to a full word.
    const uint32_t nPreTriggers = vlstd::roundUpToMultipleOf<WORD_SIZE>(senItemps.size());
    // Pad 'senItemps' to nSenseTriggers with nullptr
    senItemps.resize(nPreTriggers);
    // Number of words for pre triggers
    const uint32_t nPreWords = nPreTriggers / WORD_SIZE;

    // Process the rest of the trees
    for (const AstSenTree* const senTreep : senTreeps) {
        for (const AstSenItem *itemp = senTreep->sensesp(), *nextp; itemp; itemp = nextp) {
            nextp = VN_AS(itemp->nextp(), SenItem);
            UASSERT_OBJ(itemp->isClocked() || itemp->isHybrid(), itemp,
                        "Cannot create trigger expression for non-clocked sensitivity");
            const auto pair = senItem2TrigIdx.emplace(*itemp, senItemps.size());
            if (pair.second) senItemps.push_back(itemp);
        }
    }
    const uint32_t nSenItems = senItemps.size() - nPreTriggers;
    V3Stats::addStat("Scheduling, '" + name + "' sense triggers", nSenItems + nPreSenItems);
    // Number of sense triggers, rounded up to a full word
    const uint32_t nSenseTriggers = vlstd::roundUpToMultipleOf<WORD_SIZE>(senItemps.size());
    // Pad 'senItemps' to nSenseTriggers with nullptr
    senItemps.resize(nSenseTriggers);
    // Number of words sense triggers (inclued pre)
    const uint32_t nSenseWords = nSenseTriggers / WORD_SIZE;

    // Allocate space for the extra triggers
    V3Stats::addStat("Scheduling, '" + name + "' extra triggers", extraTriggers.size());
    // Number of extra triggers, rounded up to a full word.
    const uint32_t nExtraTriggers = vlstd::roundUpToMultipleOf<WORD_SIZE>(extraTriggers.size());
    const uint32_t nExtraWords = nExtraTriggers / WORD_SIZE;

    // We can now construct the trigger kit - this constructs all items that will be kept
    TriggerKit kit{name, slow, nSenseWords, nExtraWords, nPreWords};

    // If there are no triggers we are done
    if (!kit.m_nVecWords) return kit;

    FileLine* const flp = netlistp->topScopep()->fileline();

    // Creates read/write reference
    const auto rd = [flp](AstVarScope* vp) { return new AstVarRef{flp, vp, VAccess::READ}; };
    const auto wr = [flp](AstVarScope* vp) { return new AstVarRef{flp, vp, VAccess::WRITE}; };

    // Construct the comp and dump functions

    // Add arguments to the dump function. The trigger vector is passed into
    // the dumping function via reference so one dump function can dump all
    // different copies of the trigger vector. To do so, it also needs the tag
    // string at runtime, which is the second argument.
    AstVarScope* const dumpTrgp
        = newArgument(kit.m_dumpp, kit.m_trigVecDTypep, "triggers", VDirection::CONSTREF);
    AstVarScope* const dumpTagp
        = newArgument(kit.m_dumpp, netlistp->findStringDType(), "tag", VDirection::CONSTREF);

    // Add a print to the dumping function if there are no triggers pending
    {
        AstIf* const ifp = new AstIf{flp, new AstLogNot{flp, kit.newAnySetCall(dumpTrgp)}};
        kit.m_dumpp->addStmtsp(ifp);
        AstCStmt* const cstmtp = new AstCStmt{flp};
        ifp->addThensp(cstmtp);
        cstmtp->add("VL_DBG_MSGS(\"         No '\" + ");
        cstmtp->add(rd(dumpTagp));
        cstmtp->add(" + \"\' region triggers active\\n\");");
    }

    // Adds a debug dumping statement for this trigger
    const auto addDebug = [&](uint32_t index, const string& text) {
        const int wrdIndex = static_cast<int>(index / WORD_SIZE);
        const int bitIndex = static_cast<int>(index % WORD_SIZE);
        AstNodeExpr* const aselp = new AstArraySel{flp, rd(dumpTrgp), wrdIndex};
        AstNodeExpr* const condp = new AstSel{flp, aselp, bitIndex, 1};
        AstIf* const ifp = new AstIf{flp, condp};
        kit.m_dumpp->addStmtsp(ifp);
        AstCStmt* const cstmtp = new AstCStmt{flp};
        ifp->addThensp(cstmtp);
        cstmtp->add("VL_DBG_MSGS(\"         '\" + ");
        cstmtp->add(rd(dumpTagp));
        cstmtp->add(" + \"' region trigger index " + std::to_string(index) + " is active: " + text
                    + "\\n\");");
    };

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

        // Create the trigger computation expression
        const auto& pair = senExprBuilder.build(senItemp);
        trigps.emplace_back(pair.first);

        // Add initialization time trigger
        if (pair.second || v3Global.opt.xInitialEdge()) {
            const int wrdIndex = static_cast<int>(i / WORD_SIZE);
            const int bitIndex = static_cast<int>(i % WORD_SIZE);
            AstNodeExpr* const wordp = new AstArraySel{flp, wr(kit.m_vscp), wrdIndex};
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
        addDebug(i, desc);
    }
    UASSERT(trigps.size() == nSenseTriggers, "Inconsistent number of trigger expressions");

    // Assign sense triggers vector one word at a time
    AstNodeStmt* trigStmtsp = nullptr;
    for (size_t i = 0; i < nSenseTriggers; i += WORD_SIZE) {
        // Concatenate all bits in this trigger word using a balanced
        for (uint32_t level = 0; level < WORD_SIZE_LOG2; ++level) {
            const uint32_t stride = 1 << level;
            for (uint32_t j = 0; j < WORD_SIZE; j += 2 * stride) {
                trigps[i + j] = new AstConcat{trigps[i + j]->fileline(), trigps[i + j + stride],
                                              trigps[i + j]};
                trigps[i + j + stride] = nullptr;
            }
        }

        // Set the whole word in the trigger vector
        const int wordIndex = static_cast<int>(i / WORD_SIZE);
        AstArraySel* const aselp = new AstArraySel{flp, wr(kit.m_vscp), wordIndex};
        trigStmtsp = AstNode::addNext(trigStmtsp, new AstAssign{flp, aselp, trigps[i]});
    }
    trigps.clear();

    // Add a print for each of the extra triggers
    for (unsigned i = 0; i < extraTriggers.size(); ++i) {
        addDebug(nSenseTriggers + i,
                 "Internal '" + name + "' trigger - " + extraTriggers.m_descriptions.at(i));
    }

    // Construct the maps from old SenTrees to new SenTrees
    {
        std::vector<uint32_t> indices;
        indices.reserve(32);
        // Map regular SenTrees to the Sense triggers
        for (const AstSenTree* const senTreep : senTreeps) {
            indices.clear();
            for (const AstSenItem *itemp = senTreep->sensesp(), *nextp; itemp; itemp = nextp) {
                nextp = VN_AS(itemp->nextp(), SenItem);
                indices.push_back(senItem2TrigIdx.at(*itemp));
            }
            kit.m_mapVec[senTreep] = kit.newTriggerSenTree(kit.m_vscp, indices);
        }
        // Map Pre SenTrees to the Pre triggers
        for (const AstSenTree* const senTreep : preTreeps) {
            indices.clear();
            for (const AstSenItem *itemp = senTreep->sensesp(), *nextp; itemp; itemp = nextp) {
                nextp = VN_AS(itemp->nextp(), SenItem);
                indices.push_back(senItem2TrigIdx.at(*itemp) + kit.m_nVecWords * WORD_SIZE);
            }
            kit.m_mapPre[senTreep] = kit.newTriggerSenTree(kit.m_vscp, indices);
        }
    }

    // Get the SenExprBuilder results
    const SenExprBuilder::Results senResults = senExprBuilder.getAndClearResults();

    // Add the SenExprBuilder init statements to the static initialization functino
    for (AstNodeStmt* const nodep : senResults.m_inits) initFuncp->addStmtsp(nodep);

    // Assemble the trigger computation function
    {
        AstCFunc* const fp = kit.m_compp;
        AstScope* const scopep = netlistp->topScopep()->scopep();
        // Profiling push
        if (v3Global.opt.profExec()) {
            fp->addStmtsp(AstCStmt::profExecSectionPush(flp, "trig " + name));
        }
        // Trigger computation
        for (AstNodeStmt* const nodep : senResults.m_preUpdates) fp->addStmtsp(nodep);
        fp->addStmtsp(trigStmtsp);
        for (AstNodeStmt* const nodep : senResults.m_postUpdates) fp->addStmtsp(nodep);
        // Add the initialization time triggers
        if (initialTrigsp) {
            AstVarScope* const initVscp = scopep->createTemp("__V" + name + "DidInit", 1);
            AstIf* const ifp = new AstIf{flp, new AstNot{flp, rd(initVscp)}};
            fp->addStmtsp(ifp);
            ifp->branchPred(VBranchPred::BP_UNLIKELY);
            ifp->addThensp(util::setVar(initVscp, 1));
            ifp->addThensp(initialTrigsp);
        }
        // If there are 'pre' triggers, compute them
        if (kit.m_nPreWords) {
            // Add an argument to the function that takes the latched values
            AstVarScope* const latchedp
                = newArgument(fp, kit.m_trigVecDTypep, "latched", VDirection::CONSTREF);
            // Add loop counter variable - this can't be local because we call util::splitCheck
            AstVarScope* const nVscp = scopep->createTemp("__V" + name + "TrigPreLoopCounter", 32);
            nVscp->varp()->noReset(true);
            // Add a loop to compute the pre words
            AstLoop* const loopp = new AstLoop{flp};
            fp->addStmtsp(util::setVar(nVscp, 0));
            fp->addStmtsp(loopp);
            // Loop body
            AstNodeExpr* const offsetp = new AstConst{flp, kit.m_nVecWords};
            AstNodeExpr* const lIdxp = new AstAdd{flp, rd(nVscp), offsetp};
            AstNodeExpr* const lhsp = new AstArraySel{flp, wr(kit.m_vscp), lIdxp};
            AstNodeExpr* const aWordp = new AstArraySel{flp, rd(kit.m_vscp), rd(nVscp)};
            AstNodeExpr* const bWordp = new AstArraySel{flp, rd(latchedp), rd(nVscp)};
            AstNodeExpr* const rhsp = new AstAnd{flp, aWordp, new AstNot{flp, bWordp}};
            AstNodeExpr* const limp = new AstConst{flp, AstConst::WidthedValue{}, 32, nPreWords};
            loopp->addStmtsp(new AstAssign{flp, lhsp, rhsp});
            loopp->addStmtsp(util::incrementVar(nVscp));
            loopp->addStmtsp(new AstLoopTest{flp, loopp, new AstLt{flp, rd(nVscp), limp}});
        }
        // Add a call to the dumping function if debug is enabled
        fp->addStmtsp(kit.newDumpCall(kit.m_vscp, name, true));
        // Profiling pop
        if (v3Global.opt.profExec()) {
            fp->addStmtsp(AstCStmt::profExecSectionPop(flp, "trig " + name));
        }
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
