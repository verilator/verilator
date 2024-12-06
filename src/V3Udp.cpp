// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Implementation of Christofides algorithm to
//              approximate the solution to the traveling salesman problem.
//
// ISSUES: This isn't exactly Christofides algorithm; see the TODO
//         in perfectMatching(). True minimum-weight perfect matching
//         would produce a better result. How much better is TBD.
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2024 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Udp.h"

#include <vector>

VL_DEFINE_DEBUG_FUNCTIONS;

//V3Udp add the support for UDP table.
// For example:
// table
//    x 0 1  :   1;
//    0 ? 1  :   1;
//    0 1 0  :   0;
// endtable
// For every table line, for the input field,
// two number (mask number and compare number) will
//  be generated to help make a judegement whether
// the input field condition is satisfied. For example,
// for line x 0 1 : 1, mask = 011 cmp = 001, the condition
// is mask & inputvar == cmp. This passed should be added
// before V3Inline and V3Tristate.

class UdpVisitor final : public VNVisitor {
    AstVar* m_ifieldVarp = nullptr;  // input field var of table line.
    AstVar* m_ofieldVarp = nullptr;  // output filed var of table line.
    std::vector<AstVar*> m_inputVars;  // All the input vars in the AstPrimitive.
    std::vector<AstVar*> m_outputVars;  // All the output vars in the AstPrimitive.
    AstPrimitive* m_primp = nullptr;
    AstIf* m_lineStmtp = nullptr;  // stmt for every line in UDP Table.
    AstAlways* m_alwaysp = nullptr;  // UPD Table is realized under the always_latch.
    bool m_isFirstOutput = false;  // Whether the first IO port is output.
    int m_inputNum = 0;
    int m_outputNum = 0;

    void visit(AstPrimitive* nodep) override {
        m_primp = nodep;
        m_isFirstOutput = false;
        m_inputVars.clear();
        m_outputVars.clear();
        iterateChildren(nodep);
        m_primp = nullptr;
    }
    void visit(AstVar* nodep) override {
        // Push the input and output vars for primitive.
        if (m_primp) {
            if (nodep->isIO()) {
                if (nodep->isInput()) {
                    m_inputVars.push_back(nodep);
                } else {
                    m_outputVars.push_back(nodep);
                }
                if ((m_inputVars.size() == 0) && (m_outputVars.size() == 1)) {
                    m_isFirstOutput = true;
                }
            }
        }
        iterateChildren(nodep);
    }
    void visit(AstUdpTable* nodep) override {
        auto fl = nodep->fileline();
        m_lineStmtp = nullptr;
        m_inputNum = m_inputVars.size();
        m_outputNum = m_outputVars.size();
        if (m_outputNum != 1) {
            m_outputVars.back()->v3error(
                m_outputNum << " output ports for udp table, there must be one output port!");
        }
        if (!m_isFirstOutput && m_outputNum) {
            m_inputVars[0]->v3error("The first port must be the output port!");
        }
        m_ofieldVarp = m_outputVars[0];
        AstBasicDType* const bdtypep = VN_CAST(m_ofieldVarp->childDTypep(), BasicDType);
        if (bdtypep && bdtypep->isLogic()) {  // If output is reg.
            bdtypep->v3error("sequetial UDP is not suppoted currently!");
        }
        // Input var for the ifield,
        // add the input filed var and corresponding varref.
        AstNodeDType* const typep = nodep->findBitDType(m_inputNum, m_inputNum, VSigning::NOSIGN);
        m_ifieldVarp = new AstVar{fl, VVarType::MODULETEMP, "tableline__ifield__udptmp", typep};
        m_inputVars.back()->addNextHere(m_ifieldVarp);
        AstVarRef* const ifieldRefp = new AstVarRef{fl, m_ifieldVarp, VAccess::WRITE};
        auto itr = m_inputVars.begin();
        // relate the input vars with the input field var by concat
        AstNodeExpr* contactp = new AstVarRef{fl, *itr, VAccess::READ};
        while (++itr != m_inputVars.end()) {
            contactp = new AstConcat{fl, new AstVarRef{fl, *itr, VAccess::READ}, contactp};
        }
        AstNodeStmt* const ifieldStmtp = new AstAssignW{fl, ifieldRefp, contactp};
        // Use the always_latch to realize the UDP table.
        m_alwaysp = new AstAlways{fl, VAlwaysKwd::ALWAYS, nullptr, nullptr};
        ifieldStmtp->addNextHere(m_alwaysp);
        // Output var for the ofield
        iterateChildren(nodep);
        nodep->replaceWith(ifieldStmtp);
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }
    void visit(AstUdpTableLine* nodep) override {
        auto fl = nodep->fileline();
        AstNode* inodep = nodep->ifieldp();
        AstNode* onodep = nodep->ofieldp();
        std::vector<AstUdpTableLineVal*> ifieldNodes;
        std::vector<AstUdpTableLineVal*> ofieldNodes;
        while (inodep) {
            if (AstUdpTableLineVal* linevalp = VN_CAST(inodep, UdpTableLineVal)) {
                ifieldNodes.push_back(linevalp);
            }
            inodep = inodep->nextp();
        }
        if (ifieldNodes.size() != m_inputNum) {
            nodep->v3error(m_inputNum << " input val required, while there are "
                                      << ifieldNodes.size() << " input for the table line!");
        }
        while (onodep) {
            if (AstUdpTableLineVal* linevalp = VN_CAST(onodep, UdpTableLineVal)) {
                ofieldNodes.push_back(linevalp);
            }
            onodep = onodep->nextp();
        }
        // Build the ifield condition
        // For one table line, the match condition is
        // ifieldRefp & maskNum == cmpNum
        // For example: 0?1:1
        // maskNum is : 101
        // cmpNum is : 001
        V3Number maskNum{nodep, m_inputNum};
        V3Number cmpNum{nodep, m_inputNum};
        int bitIndex = 0;
        for (auto ivalp : ifieldNodes) {
            std::string bitval = ivalp->name().substr(0, 1);
            if (bitval == "0") {
                maskNum.setBit(bitIndex, 1);
                cmpNum.setBit(bitIndex, 0);
            } else if (bitval == "1") {
                maskNum.setBit(bitIndex, 1);
                cmpNum.setBit(bitIndex, 1);
            } else {
                maskNum.setBit(bitIndex, 0);
                cmpNum.setBit(bitIndex, 0);
            }
            bitIndex++;
        }
        AstConst* const maskConstp = new AstConst{fl, maskNum};
        AstConst* const cmpConstp = new AstConst{fl, cmpNum};
        AstNodeExpr* const condExprp = new AstEq{
            fl, new AstAnd{fl, maskConstp, new AstVarRef{fl, m_ifieldVarp, VAccess::READ}},
            cmpConstp};
        //Build the ofield val
        V3Number onum{nodep, 1};
        auto ovalp = ofieldNodes[0];
        std::string bitval = ovalp->name().substr(0, 1);
        if (bitval == "0") {
            onum.setBit(0, 0);
        } else if (bitval == "1") {
            onum.setBit(0, 1);
        } else {
            onum.setBit(0, 'x');
        }
        //Build the whole field line stmt.
        AstAssign* const thenStmtp = new AstAssign{
            fl, new AstVarRef{fl, m_ofieldVarp, VAccess::WRITE}, new AstConst{fl, onum}};
        AstIf* const ifStmtp = new AstIf{fl, condExprp, thenStmtp};
        if (!m_lineStmtp) {
            m_lineStmtp = ifStmtp;
            m_alwaysp->addStmtsp(m_lineStmtp);
        } else {
            m_lineStmtp->addElsesp(ifStmtp);
            m_lineStmtp = ifStmtp;
        }
    }
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit UdpVisitor(AstNetlist* nodep) { iterate(nodep); }
    ~UdpVisitor() override = default;
};

void V3Udp::udpResolve(AstNetlist* rootp) {
    UINFO(4, __FUNCTION__ << ": " << endl);
    { const UdpVisitor visitor{rootp}; }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("udpResolve", 0, dumpTreeEitherLevel() >= 3);
}
