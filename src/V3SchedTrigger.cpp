// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Create triggers for code scheduling
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
AstCFunc* TriggerKit::createOrIntoFunc(AstUnpackArrayDType* const oDtypep,
                                       AstUnpackArrayDType* const iDtypep) const {
    AstNetlist* const netlistp = v3Global.rootp();
    FileLine* const flp = netlistp->topScopep()->fileline();
    AstNodeDType* const u32DTypep = netlistp->findUInt32DType();

    // Create function
    std::string name = "_trigger_orInto__" + m_name;
    name += iDtypep == m_trigVecDTypep ? "_vec" : "_ext";
    name += oDtypep == m_trigVecDTypep ? "_vec" : "_ext";
    AstCFunc* const funcp = util::makeSubFunction(netlistp, name, m_slow);
    funcp->isStatic(true);

    // Add arguments
    AstVarScope* const oVscp = newArgument(funcp, oDtypep, "out", VDirection::INOUT);
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
    AstConst* const outputRangeLeftp = VN_AS(oDtypep->rangep()->leftp(), Const);
    AstConst* const inputRangeLeftp = VN_AS(iDtypep->rangep()->leftp(), Const);
    AstNodeExpr* const limp = outputRangeLeftp->num().toSInt() < inputRangeLeftp->num().toSInt()
                                  ? outputRangeLeftp->cloneTreePure(false)
                                  : inputRangeLeftp->cloneTreePure(false);
    loopp->addStmtsp(new AstAssign{flp, lhsp, rhsp});
    loopp->addStmtsp(util::incrementVar(nVscp));
    loopp->addStmtsp(new AstLoopTest{flp, loopp, new AstLte{flp, rd(nVscp), limp}});

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
    UASSERT_OBJ(iVscp->dtypep() == m_trigVecDTypep || iVscp->dtypep() == m_trigExtDTypep, iVscp,
                "Bad input trigger vector type");
    UASSERT_OBJ(oVscp->dtypep() == m_trigVecDTypep || oVscp->dtypep() == m_trigExtDTypep, oVscp,
                "Bad output trigger vector type");
    const size_t mask
        = ((oVscp->dtypep() == m_trigExtDTypep) << 1) | (iVscp->dtypep() == m_trigExtDTypep);
    AstCFunc*& funcp = m_orIntoVecps[mask];
    if (!funcp) {
        funcp = createOrIntoFunc(VN_AS(oVscp->dtypep(), UnpackArrayDType),
                                 VN_AS(iVscp->dtypep(), UnpackArrayDType));
    }
    FileLine* const flp = v3Global.rootp()->topScopep()->fileline();
    AstCCall* const callp = new AstCCall{flp, funcp};
    callp->addArgsp(new AstVarRef{flp, oVscp, VAccess::WRITE});
    callp->addArgsp(new AstVarRef{flp, iVscp, VAccess::READ});
    callp->dtypeSetVoid();
    return callp->makeStmt();
}

AstNodeStmt* TriggerKit::newCompBaseCall() const {
    if (!m_nVecWords) return nullptr;
    FileLine* const flp = v3Global.rootp()->topScopep()->fileline();
    AstCCall* const callp = new AstCCall{flp, m_compBasep};
    callp->dtypeSetVoid();
    return callp->makeStmt();
}

AstNodeStmt* TriggerKit::newCompExtCall(AstVarScope* vscp) const {
    if (!m_nPreWords) return nullptr;
    FileLine* const flp = v3Global.rootp()->topScopep()->fileline();
    AstCCall* const callp = new AstCCall{flp, m_compExtp};
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

void TriggerKit::addExtraTriggerAssignment(AstVarScope* vscp, uint32_t index, bool clear) const {
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
    if (clear) {
        // Clear the input variable
        AstNodeStmt* const clrp = new AstAssign{flp, new AstVarRef{flp, vscp, VAccess::WRITE},
                                                new AstConst{flp, AstConst::BitFalse{}}};
        // Note these are added in reverse order, so 'setp' executes before 'clrp'
        m_compBasep->stmtsp()->addHereThisAsNext(clrp);
    }
    m_compBasep->stmtsp()->addHereThisAsNext(setp);
}

TriggerKit::TriggerKit(const std::string& name, bool slow, uint32_t nSenseWords,
                       uint32_t nExtraWords, uint32_t nPreWords,
                       std::unordered_map<VNRef<const AstSenItem>, size_t> senItem2TrigIdx,
                       bool useAcc)
    : m_name{name}
    , m_slow{slow}
    , m_nSenseWords{nSenseWords}
    , m_nExtraWords{nExtraWords}
    , m_nPreWords{nPreWords}
    , m_senItem2TrigIdx{std::move(senItem2TrigIdx)} {
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
        m_compExtp = util::makeSubFunction(netlistp, "_eval_ext_triggers__" + m_name, m_slow);
    } else {
        m_trigExtDTypep = m_trigVecDTypep;
    }
    // The AstVarScope representing the extended trigger vector
    m_vscp = scopep->createTemp("__V" + m_name + "Triggered", m_trigExtDTypep);
    m_vscp->varp()->isInternal(true);
    // The trigger computation function
    m_compBasep = util::makeSubFunction(netlistp, "_eval_base_triggers__" + m_name, m_slow);
    // The debug dump function, always 'slow'
    m_dumpp = util::makeSubFunction(netlistp, "_dump_triggers__" + m_name, true);
    m_dumpp->isStatic(true);
    m_dumpp->ifdef("VL_DEBUG");
    if (useAcc) {
        m_vscAccp = scopep->createTemp("__V" + m_name + "TriggeredAcc", m_trigVecDTypep);
        m_vscAccp->varp()->isInternal(true);
    }
}

AstAssign* TriggerKit::createSenTrigVecAssignment(AstVarScope* const target,
                                                  std::vector<AstNodeExpr*>& trigps) {
    FileLine* const flp = target->fileline();
    AstAssign* trigStmtsp = nullptr;
    // Assign sense triggers vector one word at a time
    for (size_t i = 0; i < trigps.size(); i += WORD_SIZE) {
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
        AstArraySel* const aselp
            = new AstArraySel{flp, new AstVarRef{flp, target, VAccess::WRITE}, wordIndex};
        trigStmtsp = AstNode::addNext(trigStmtsp, new AstAssign{flp, aselp, trigps[i]});
    }
    return trigStmtsp;
}

TriggerKit TriggerKit::create(AstNetlist* netlistp,  //
                              AstCFunc* const initFuncp,  //
                              SenExprBuilder& senExprBuilder,  //
                              const std::vector<const AstSenTree*>& preTreeps,  //
                              const std::vector<const AstSenTree*>& senTreeps,  //
                              const string& name,  //
                              const ExtraTriggers& extraTriggers,  //
                              bool slow,  //
                              bool useAcc) {
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
    TriggerKit kit{name, slow, nSenseWords, nExtraWords, nPreWords, senItem2TrigIdx, useAcc};

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
            if (useAcc) {
                initFuncp->addStmtsp(new AstAssign{flp, lhsp, rhsp});
            } else {
                initialTrigsp = AstNode::addNext(initialTrigsp, new AstAssign{flp, lhsp, rhsp});
            }
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

    AstAssign* const trigStmtsp = createSenTrigVecAssignment(kit.m_vscp, trigps);

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
    const SenExprBuilder::Results senResults = senExprBuilder.getResultsAndClearUpdates();

    // Add the SenExprBuilder init statements to the static initialization functino
    for (AstNodeStmt* const nodep : senResults.m_inits) initFuncp->addStmtsp(nodep);

    // Assemble the base trigger computation function
    AstScope* const scopep = netlistp->topScopep()->scopep();
    {
        AstCFunc* const fp = kit.m_compBasep;
        // Profiling push
        if (v3Global.opt.profExec()) {
            fp->addStmtsp(AstCStmt::profExecSectionPush(flp, "trigBase " + name));
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
        if (!useAcc && !kit.m_nPreWords) {
            // Add a call to the dumping function if debug is enabled
            // But only if there are no preWords therefore there is only one eval function
            // If there are two of them let the caller call it
            // Also, when accumulator is being used skip this step and allow user to call the dump
            fp->addStmtsp(kit.newDumpCall(kit.m_vscp, name, true));
        }
        // Profiling pop
        if (v3Global.opt.profExec()) {
            fp->addStmtsp(AstCStmt::profExecSectionPop(flp, "trigBase " + name));
        }
        util::splitCheck(fp);
    };
    // If there are 'pre' triggers, compute them
    if (kit.m_nPreWords) {
        AstCFunc* const fp = kit.m_compExtp;
        // Profiling push
        if (v3Global.opt.profExec()) {
            fp->addStmtsp(AstCStmt::profExecSectionPush(flp, "trigExt " + name));
        }
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
        // Profiling pop
        if (v3Global.opt.profExec()) {
            fp->addStmtsp(AstCStmt::profExecSectionPop(flp, "trigExt " + name));
        }
        util::splitCheck(fp);
    }
    // Done with the trigger computation function, split as might be large

    // The debug code might leak signal names, so simply delete it when using --protect-ids
    if (v3Global.opt.protectIds()) kit.m_dumpp->stmtsp()->unlinkFrBackWithNext()->deleteTree();
    // Done with the trigger dump function, split as might be large
    util::splitCheck(kit.m_dumpp);

    return kit;
}

//  Find all CAwaits, clear SenTrees inside them, generate before-trigger functions (functions that
//  shall be called before awaiting for a VCMethod::SCHED_TRIGGER) and add thier calls before
//  proper CAwaits
class AwaitBeforeTrigVisitor final : public VNVisitor {
    const VNUser1InUse m_user1InUse;

    /**
     * AstCAwait::user1()       ->  bool.           True if node has been visited
     * AstSenTree::user1p()     ->  AstCFunc*.      Function that has to be called before awaiting
     *                                              for CAwait pointing to this SenTree
     * AstCFunc::user1p()       ->  AstVarScope*    Function's local temporary extended trigger
     *                                              vector variable scope
     */

    // Netlist - needed for using util::makeSubFunction()
    AstNetlist* const m_netlistp;
    // Trigger kit - for accessing trigger vectors and mapping senItems to thier indexes
    const TriggerKit& m_trigKit;
    // Expression builder - for building expressions from SenItems
    SenExprBuilder& m_senExprBuilder;
    // Generator of unique names for before-trigger function
    V3UniqueNames m_beforeTriggerFuncUniqueName;

    // Map containing every generated CFuncs and indexes of triggers used within it
    std::map<AstCFunc*, std::set<size_t>> m_funcToUsedTriggers;
    // Map from SenTree to coresponding scheduler
    std::map<const AstSenTree*, AstNodeExpr*> m_senTreeToSched;

    // For set of bits indexes (of sensitivity vector) return map from those indexes to set of
    // schedulers sensitive to these indexes.
    // Indices are split into word index and bit masking this index within given word
    std::map<size_t, std::map<size_t, std::set<AstNodeExpr*>>>
    getUsedTriggersToTrees(const std::set<size_t>& usedTriggers) {
        std::map<size_t, std::map<size_t, std::set<AstNodeExpr*>>> usedTrigsToUsingTrees;
        for (auto senTreeSched : m_senTreeToSched) {
            const AstSenTree* const senTreep = senTreeSched.first;
            AstNodeExpr* const shedp = senTreeSched.second;

            // Find all common SenItem indexes for `senTreep` and `usedTriggers`
            std::set<size_t> usedTriggersInSenTree;
            for (AstSenItem* senItemp = senTreep->sensesp(); senItemp;
                 senItemp = VN_AS(senItemp->nextp(), SenItem)) {
                const size_t idx = m_trigKit.senItem2TrigIdx(senItemp);
                if (usedTriggers.find(idx) != usedTriggers.end()) {
                    usedTrigsToUsingTrees[idx / TriggerKit::WORD_SIZE]
                                         [1 << (idx % TriggerKit::WORD_SIZE)]
                                             .insert(shedp);
                }
            }
        }
        return usedTrigsToUsingTrees;
    }

    // Returns a CCall to a before-trigger function for a given SenTree,
    // Constructs such a function if it doesn't exist yet
    AstCCall* getBeforeTriggerStmt(AstSenTree* const senTreep) {
        FileLine* const flp = senTreep->fileline();
        if (!senTreep->user1p()) {
            AstCFunc* const funcp = util::makeSubFunction(
                m_netlistp, m_beforeTriggerFuncUniqueName.get(senTreep), false);
            senTreep->user1p(funcp);

            // Create a local temporary extended vector
            AstVarScope* const vscAccp = m_trigKit.vscAccp();
            AstVarScope* const tmpp = vscAccp->scopep()->createTempLike("__VTmp", vscAccp);
            AstVar* const tmpVarp = tmpp->varp()->unlinkFrBack();
            funcp->user1p(tmpp);
            funcp->addVarsp(tmpVarp);
            tmpVarp->funcLocal(true);
            tmpVarp->noReset(true);

            AstVar* const argp = new AstVar{flp, VVarType::BLOCKTEMP, "__VeventDescription",
                                            senTreep->findBasicDType(VBasicDTypeKwd::CHARPTR)};
            argp->funcLocal(true);
            argp->direction(VDirection::INPUT);
            funcp->addArgsp(argp);
            // Scope is created in the constructor after iterate finishes

            static std::vector<AstNodeExpr*> trigps;  // Static to reduce amount of allocations

            // Puts `exprp` at `pos` and makes sure that trigps.size() is multiple of
            // TriggerKit::WORD_SIZE
            const auto emplaceAt = [flp](AstNodeExpr* const exprp, const size_t pos) {
                const size_t targetSize
                    = vlstd::roundUpToMultipleOf<TriggerKit::WORD_SIZE>(pos + 1);
                if (trigps.capacity() < targetSize) trigps.reserve(targetSize * 2);
                while (trigps.size() < targetSize) {
                    trigps.push_back(new AstConst{flp, AstConst::BitFalse{}});
                }
                trigps[pos]->deleteTree();
                trigps[pos] = exprp;
            };

            // Find all trigger indexes of SenItems inside `senTreep`
            // and add them to `trigps` and `m_funcToUsedTriggers[funcp]`
            for (const AstSenItem* itemp = senTreep->sensesp(); itemp;
                 itemp = VN_AS(itemp->nextp(), SenItem)) {
                const size_t idx = m_trigKit.senItem2TrigIdx(itemp);
                emplaceAt(m_senExprBuilder.build(itemp).first, idx);
                m_funcToUsedTriggers[funcp].insert(idx);
            }

            // Fill the function with neccessary statements
            SenExprBuilder::Results results = m_senExprBuilder.getResultsAndClearUpdates();
            for (AstNodeStmt* const stmtsp : results.m_inits) funcp->addStmtsp(stmtsp);
            for (AstNodeStmt* const stmtsp : results.m_preUpdates) funcp->addStmtsp(stmtsp);
            funcp->addStmtsp(TriggerKit::createSenTrigVecAssignment(tmpp, trigps));
            trigps.clear();
            for (AstNodeStmt* const stmtsp : results.m_postUpdates) funcp->addStmtsp(stmtsp);
        }
        AstCCall* const callp = new AstCCall{flp, VN_AS(senTreep->user1p(), CFunc)};
        callp->dtypeSetVoid();
        return callp;
    }

    void visit(AstCAwait* const nodep) override {
        if (nodep->user1SetOnce()) return;

        // Check whether it is a CAwait for a VCMethod::SCHED_TRIGGER
        if (const AstCMethodHard* const cMethodHardp = VN_CAST(nodep->exprp(), CMethodHard)) {
            if (cMethodHardp->method() == VCMethod::SCHED_TRIGGER) {
                AstCCall* const beforeTrigp = getBeforeTriggerStmt(nodep->sentreep());

                FileLine* const flp = nodep->fileline();
                // Add eventDescription argument value to a CCall - it is used for --runtime-debug
                if (AstNode* const pinp = cMethodHardp->pinsp()->nextp()->nextp()) {
                    beforeTrigp->addArgsp(VN_AS(pinp, NodeExpr)->cloneTree(false));
                } else {
                    beforeTrigp->addArgsp(new AstCExpr{flp, "nullptr"});
                }

                // Change CAwait Expression into StmtExpr that calls to a before-trigger function
                // first and then return CAwait
                VNRelinker relinker;
                nodep->unlinkFrBack(&relinker);
                AstExprStmt* const exprstmtp
                    = new AstExprStmt{flp, beforeTrigp->makeStmt(), nodep};
                relinker.relink(exprstmtp);
                m_senTreeToSched.emplace(nodep->sentreep(), cMethodHardp->fromp());
            }
        }
        nodep->clearSentreep();  // Clear as these sentrees will get deleted later
        iterate(nodep);
    }

    void visit(AstNode* const nodep) override { iterateChildren(nodep); }

public:
    AwaitBeforeTrigVisitor(AstNetlist* netlistp, SenExprBuilder& senExprBuilder,
                           const TriggerKit& trigKit)
        : m_netlistp{netlistp}
        , m_trigKit{trigKit}
        , m_senExprBuilder{senExprBuilder}
        , m_beforeTriggerFuncUniqueName{"__VbeforeTrig"} {
        iterate(netlistp);

        // In each of before-trigger functions check if anything was triggered and mark as ready
        // triggered schedulers
        for (const auto& funcToUsedTriggers : m_funcToUsedTriggers) {
            AstCFunc* const funcp = funcToUsedTriggers.first;

            std::map<size_t, std::map<size_t, std::set<AstNodeExpr*>>> usedTrigsToUsingTrees
                = getUsedTriggersToTrees(funcToUsedTriggers.second);

            FileLine* const flp = funcp->fileline();
            AstVarScope* const vscp = VN_AS(funcp->user1p(), VarScope);

            // Helper returning expression getting array index `idx` from `scocep` with access
            // `access`
            const auto getIdx = [flp](AstVarScope* const scocep, VAccess access, size_t idx) {
                return new AstArraySel{flp, new AstVarRef{flp, scocep, access},
                                       new AstConst{flp, AstConst::Unsized64{}, idx}};
            };

            // Get eventDescription argument
            AstVarScope* const argpVscp = new AstVarScope{flp, funcp->scopep(), funcp->argsp()};
            funcp->scopep()->addVarsp(argpVscp);

            // Mark as ready triggered schedulers
            for (const auto& triggersToTrees : usedTrigsToUsingTrees) {
                const size_t word = triggersToTrees.first;

                for (const auto& bitsToTrees : triggersToTrees.second) {
                    const size_t bit = bitsToTrees.first;
                    const auto& schedulers = bitsToTrees.second;

                    // Check if given bit is fired - single bits are checked since
                    // usually there is only a few of them (only one most of the times as we await
                    // only for one event)
                    AstConst* const maskConstp = new AstConst{flp, AstConst::Unsized64{}, bit};
                    AstAnd* const condp
                        = new AstAnd{flp, getIdx(vscp, VAccess::READ, word), maskConstp};
                    AstIf* const ifp = new AstIf{flp, condp};

                    // Call ready() on each scheduler sensitive to `condp`
                    for (AstNodeExpr* const schedp : schedulers) {
                        AstCMethodHard* const callp = new AstCMethodHard{
                            flp, schedp->cloneTree(false), VCMethod::SCHED_READY};
                        callp->dtypeSetVoid();
                        callp->addPinsp(new AstVarRef{flp, argpVscp, VAccess::READ});
                        ifp->addThensp(callp->makeStmt());
                    }
                    funcp->addStmtsp(ifp);
                }
            }

            AstVarScope* const vscAccp = m_trigKit.vscAccp();
            // Add touched values to accumulator
            for (const auto& triggersToTrees : usedTrigsToUsingTrees) {
                const size_t word = triggersToTrees.first;
                funcp->addStmtsp(new AstAssign{flp, getIdx(vscAccp, VAccess::WRITE, word),
                                               new AstOr{flp, getIdx(vscAccp, VAccess::READ, word),
                                                         getIdx(vscp, VAccess::READ, word)}});
            }
        }
    }
    ~AwaitBeforeTrigVisitor() override = default;
};

void beforeTrigVisitor(AstNetlist* netlistp, SenExprBuilder& senExprBuilder,
                       const TriggerKit& trigKit) {
    AwaitBeforeTrigVisitor{netlistp, senExprBuilder, trigKit};
}

}  // namespace V3Sched
