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

#include <map>
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
// is mask & inputvar == cmp. This pass should be added
// before V3Inline and V3Tristate.

class UdpVisitor final : public VNVisitor {
    bool m_inInitial = false;
    AstVar* m_iFieldVarp = nullptr;  // Input field var of table line.
    AstVar* m_oFieldVarp = nullptr;  // Output filed var of table line.
    std::vector<AstVar*> m_inputVars;  // All the input vars in the AstPrimitive.
    std::vector<AstVar*> m_outputVars;  // All the output vars in the AstPrimitive.
    AstPrimitive* m_primp = nullptr;
    AstNodeStmt* m_comboNodeStmtp = nullptr;  // The stmt for all the combinational lines.
    AstIf* m_lineStmtp = nullptr;  // The stmt for the current combinational lines.
    bool m_isFirstOutput = false;  // Whether the first IO port is output.
    AstUdpTableLineVal* m_edgeTrigValp = nullptr;  // The edge trigger value.
    AstVar* m_trigVarp = nullptr;  // The edge trigger var.
    std::map<AstVar*, AstAlways*> m_trigAlwaysMapp;  // The always block map for r|f edge.
    std::map<AstAlways*, AstIf*>
        m_alwaysIfMapp;  // The map between always and if stmt for sequent line.
    AstVar* m_newOutVarp = nullptr;  // The output varp.
    uint32_t m_inputNum = 0;  // The input var number.
    uint32_t m_outputNum = 0;  // The output var number.
    AstVarRef* m_outputInitVerfp = nullptr;

    void visit(AstInitial* nodep) override {
        if (m_primp) { m_inInitial = true; }
        iterateChildren(nodep);
    }
    void visit(AstAssign* nodep) override {
        if (m_inInitial) { m_outputInitVerfp = VN_CAST(nodep->lhsp(), VarRef); }
        iterateChildren(nodep);
    }
    void visit(AstPrimitive* nodep) override {
        m_outputInitVerfp = nullptr;
        m_primp = nodep;
        m_isFirstOutput = false;
        iterateChildren(nodep);
        m_inputVars.clear();
        m_outputVars.clear();
        m_primp = nullptr;
        m_inInitial = false;
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
        m_comboNodeStmtp = nullptr;
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
        m_oFieldVarp = m_outputVars[0];
        // Input var for the iField,
        // Add the input filed var and corresponding varref.
        AstNodeDType* const typep = nodep->findBitDType(m_inputNum, m_inputNum, VSigning::NOSIGN);
        m_iFieldVarp = new AstVar{fl, VVarType::MODULETEMP, "tableline__ifield__udptmp", typep};
        m_inputVars.back()->addNextHere(m_iFieldVarp);
        AstVarRef* const iFieldRefp = new AstVarRef{fl, m_iFieldVarp, VAccess::WRITE};
        auto itr = m_inputVars.begin();
        // Relate the input vars with the input field var by concat
        AstNodeExpr* contactp = new AstVarRef{fl, *itr, VAccess::READ};
        while (++itr != m_inputVars.end()) {
            contactp = new AstConcat{fl, new AstVarRef{fl, *itr, VAccess::READ}, contactp};
        }
        AstNodeStmt* const iFieldStmtp = new AstAssignW{fl, iFieldRefp, contactp};
        AstNode* currentNode = iFieldStmtp;
        // Process every table line.
        iterateChildren(nodep);
        // First for the sequent parts;
        if (!m_alwaysIfMapp.empty()) {
            for (auto itr = m_alwaysIfMapp.begin(); itr != m_alwaysIfMapp.end(); itr++) {
                currentNode->addNextHere(itr->first);
                currentNode = itr->first;
            }
            AstAssignW* const sequentAssignStmtp
                = new AstAssignW{fl, new AstVarRef{fl, m_oFieldVarp, VAccess::WRITE},
                                 new AstVarRef{fl, m_newOutVarp, VAccess::READ}};
            currentNode->addNextHere(sequentAssignStmtp);
            currentNode = sequentAssignStmtp;
        }
        // Then for the comb parts.
        if (m_comboNodeStmtp) {
            // Use the always block to realize the UDP table.
            // For the mixtrigger, use the always latch.
            VAlwaysKwd alwaysKwd;
            if (!m_alwaysIfMapp.empty()) alwaysKwd = VAlwaysKwd::ALWAYS_LATCH;
            currentNode->addNextHere(new AstAlways{fl, alwaysKwd, nullptr, m_comboNodeStmtp});
        }
        // For initial block, initialize the tmp out var.
        if (m_outputInitVerfp && m_newOutVarp) {
            m_outputInitVerfp->replaceWith(
                new AstVarRef{nodep->fileline(), m_newOutVarp, VAccess::WRITE});
            VL_DO_DANGLING(pushDeletep(m_outputInitVerfp), m_outputInitVerfp);
        }

        nodep->replaceWith(iFieldStmtp);
        m_trigAlwaysMapp.clear();
        m_alwaysIfMapp.clear();
        m_newOutVarp = nullptr;
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }
    void visit(AstUdpTableLine* nodep) override { processLogic(nodep); }
    void visit(AstNode* nodep) override { iterateChildren(nodep); }
    // For logic processing.
    bool isEdgeTrig(std::string& valName) {
        auto isNum = [](char str) {
            if (str == '1' || str == '0') return true;
            return false;
        };
        if (valName == "r" || valName == "f") return true;
        if (valName.length() == 4) {
            std::string valNum = valName.substr(1, 2);
            if (valNum == "01" || valNum == "p" || valNum == "P" || valName == "R") {
                valName = "r";
                return true;
            }
            if (valNum == "10" || valNum == "n" || valNum == "N" || valNum == "F") {
                valName = "f";
                return true;
            }
            if (isNum(valNum[0]) && !isNum(valNum[1])) {
                if (valNum[0] == '1')
                    valName = "f";
                else
                    valName = "r";
                return true;
            }
            if (!isNum(valNum[0]) && isNum(valNum[1])) {
                if (valNum[1] == '1')
                    valName = "r";
                else
                    valName = "f";
                return true;
            }
            valName = "?";
        }
        return false;
    }
    bool isMultiSig(const std::string& valName) { return valName.length() >= 2; }
    bool isCombOutputSig(const std::string& valName) {
        return (valName == "0" || valName == "1" || valName == "x" || valName == "X");
    }
    bool isSequentOutputSig(const std::string& valName) {
        return (valName == "0" || valName == "1" || valName == "x" || valName == "X"
                || valName == "-");
    }
    void processLogic(AstUdpTableLine* nodep) {
        if (nodep->type() == AstUdpTableLine::UDP_SEQUENT && !m_oFieldVarp->isBitLogic()) {
            m_oFieldVarp->v3error("For sequential udp, the output var should be the reg type!");
        }
        AstNode* iNodep = nodep->iFieldp();
        AstNode* oNodep = nodep->oFieldp();
        std::vector<std::string> iFieldNames;
        std::vector<std::string> oFieldNames;
        m_edgeTrigValp = nullptr;
        m_trigVarp = nullptr;
        int index = 0;
        while (iNodep) {
            if (AstUdpTableLineVal* linevalp = VN_CAST(iNodep, UdpTableLineVal)) {
                std::string valName = linevalp->name();
                if (isEdgeTrig(valName)) {
                    if (!m_edgeTrigValp) {
                        m_edgeTrigValp = linevalp;
                        linevalp->name(valName);
                        m_trigVarp = m_inputVars[index];
                    } else {
                        iNodep->v3error("There can be only one edge tigger signal!");
                    }
                    iFieldNames.push_back(valName);
                } else if (isMultiSig(valName)) {
                    for (auto name : valName) {
                        std::string subName = std::string{name};
                        iFieldNames.push_back(subName);
                    }
                } else {
                    iFieldNames.push_back(valName);
                }
                ++index;
            }
            iNodep = iNodep->nextp();
        }
        if (iFieldNames.size() != m_inputNum) {
            nodep->v3error(m_inputNum << " input var required, while there are "
                                      << iFieldNames.size() << " input for the table line!");
        }
        while (oNodep) {
            if (AstUdpTableLineVal* linevalp = VN_CAST(oNodep, UdpTableLineVal)) {
                if (nodep->type() == AstUdpTableLine::UDP_COMB) {
                    if (oFieldNames.empty()) {
                        if (!isCombOutputSig(linevalp->name())) {
                            linevalp->v3error("Illegal value for combinational udp line output!");
                        }
                    }
                } else {
                    if (oFieldNames.size() == 1) {
                        if (!isSequentOutputSig(linevalp->name())) {
                            linevalp->v3error("Illegal value for sequential udp line output!");
                        }
                    }
                }
                oFieldNames.push_back(linevalp->name());
            }
            oNodep = oNodep->nextp();
        }
        if (nodep->type() == AstUdpTableLine::UDP_COMB) {
            if (m_edgeTrigValp) {
                m_edgeTrigValp->v3error(
                    "There should not be a edge trigger for combinational UDP table line!");
                m_edgeTrigValp = nullptr;
            }
        }
        if (!m_edgeTrigValp) {
            addCombLogic(nodep, iFieldNames, oFieldNames);
        } else {
            addEdgTriglogic(nodep, iFieldNames, oFieldNames);
        }
    }
    V3Number getMaskNum(AstNode* nodep, const std::vector<std::string>& fieldNames) {
        V3Number maskNum{nodep, (int)fieldNames.size()};
        int bitIndex = 0;
        for (auto name : fieldNames) {
            if (name == "0" || name == "r" || name == "f") {
                maskNum.setBit(bitIndex, 1);
            } else if (name == "1") {
                maskNum.setBit(bitIndex, 1);
            } else {
                maskNum.setBit(bitIndex, 0);
            }
            ++bitIndex;
        }
        return maskNum;
    }
    V3Number getCmpNum(AstNode* nodep, const std::vector<std::string>& fieldNames) {
        V3Number cmpNum{nodep, (int)fieldNames.size()};
        int bitIndex = 0;
        for (auto name : fieldNames) {
            if (name == "0" || name == "f") {
                cmpNum.setBit(bitIndex, 0);
            } else if (name == "1" || name == "r") {
                cmpNum.setBit(bitIndex, 1);
            } else {
                cmpNum.setBit(bitIndex, 0);
            }
            ++bitIndex;
        }
        return cmpNum;
    }
    V3Number getOutputNum(AstNode* nodep, const std::string& fieldNames) {
        V3Number outputNum{nodep, 1};
        if (fieldNames == "0") {
            outputNum.setBit(0, 0);
        } else if (fieldNames == "1") {
            outputNum.setBit(0, 1);
        } else {
            outputNum.setBit(0, 'x');
        }
        return outputNum;
    }
    void addEdgTriglogic(AstUdpTableLine* nodep, std::vector<std::string>& iFieldNames,
                         std::vector<std::string>& oFieldNames) {
        auto oValName = oFieldNames[1];
        auto oStateName = oFieldNames[0];
        if (oValName == "-") return;  // Do not need change if keep value.
        std::string trigStr = m_edgeTrigValp->name();
        auto fl = nodep->fileline();
        if (!m_newOutVarp) {  // Out var used for the current out state.
            AstNodeDType* const typep = nodep->findLogicDType(1, 1, VSigning::NOSIGN);
            m_newOutVarp
                = new AstVar{fl, VVarType::MODULETEMP, "tableline__ofield__udptmp", typep};
            m_iFieldVarp->addNextHere(m_newOutVarp);
        }
        VEdgeType edgetType = trigStr == "r" ? VEdgeType::ET_POSEDGE : VEdgeType::ET_NEGEDGE;
        AstAlways* alwaysp = nullptr;
        if (m_trigAlwaysMapp.find(m_trigVarp) == m_trigAlwaysMapp.end()) {
            AstVarRef* varRefp = new AstVarRef{fl, m_trigVarp, VAccess::READ};
            alwaysp = new AstAlways{fl, VAlwaysKwd::ALWAYS,
                                    new AstSenTree{fl, new AstSenItem{fl, edgetType, varRefp}},
                                    nullptr};
            m_trigAlwaysMapp[m_trigVarp] = alwaysp;
        } else {
            alwaysp = m_trigAlwaysMapp[m_trigVarp];
            AstSenItem* senItemp = alwaysp->sensesp()->sensesp();
            if (senItemp->edgeType() != edgetType) { senItemp->edgeType(VEdgeType::ET_BOTHEDGE); }
        }
        // Add the expression under always.
        // If condition for input field.
        AstConst* const maskConstp = new AstConst{fl, getMaskNum(nodep, iFieldNames)};
        AstConst* const cmpConstp = new AstConst{fl, getCmpNum(nodep, iFieldNames)};
        AstNodeExpr* condExprp = new AstEq{
            fl, new AstAnd{fl, maskConstp, new AstVarRef{fl, m_iFieldVarp, VAccess::READ}},
            cmpConstp};
        // If condition for current state.
        if (oStateName == "0" || oStateName == "1") {
            AstConst* const cmpStateCmpp
                = new AstConst{fl, V3Number{nodep, 1, (uint32_t)std::stoi(oStateName)}};
            AstNodeExpr* const cmpEqp
                = new AstEq{fl, new AstVarRef{fl, m_newOutVarp, VAccess::READ}, cmpStateCmpp};
            condExprp = new AstAnd{fl, condExprp, cmpEqp};
        }
        // If condition for clock trigger.
        /*
        uint32_t clkVal = trigStr == "r" ? 1 : 0;
        AstConst* const clkValuep = new AstConst{fl, V3Number{nodep, 1, clkVal}};
        AstNodeExpr* const clkEqp
            = new AstEq{fl, new AstVarRef{fl, m_trigVarp, VAccess::READ}, clkValuep};
        condExprp = new AstAnd{fl, condExprp, clkEqp};
        */
        //Add the stmp.
        AstAssignDly* const thenStmtp
            = new AstAssignDly{fl, new AstVarRef{fl, m_newOutVarp, VAccess::WRITE},
                               new AstConst{fl, getOutputNum(nodep, oValName)}};
        AstIf* const ifStmtp = new AstIf{fl, condExprp, thenStmtp};
        if (!alwaysp->stmtsp()) {
            alwaysp->addStmtsp(ifStmtp);
        } else {
            m_alwaysIfMapp[alwaysp]->addElsesp(ifStmtp);
        }
        m_alwaysIfMapp[alwaysp] = ifStmtp;
    }
    void addCombLogic(AstUdpTableLine* nodep, std::vector<std::string>& iFieldNames,
                      std::vector<std::string>& oFieldNames) {
        // Build the input field condition
        // For one table line, the match condition is
        // iFieldRefp & maskNum == cmpNum
        // For example: 0?1:1
        // maskNum is : 101
        // cmpNum is : 001
        auto oValName = oFieldNames.size() == 1 ? oFieldNames[0] : oFieldNames[1];
        if (oValName == "-") return;  // Ignore for keep original state.
        auto fl = nodep->fileline();
        AstConst* const maskConstp = new AstConst{fl, getMaskNum(nodep, iFieldNames)};
        AstConst* const cmpConstp = new AstConst{fl, getCmpNum(nodep, iFieldNames)};
        AstNodeExpr* const condExprp = new AstEq{
            fl, new AstAnd{fl, maskConstp, new AstVarRef{fl, m_iFieldVarp, VAccess::READ}},
            cmpConstp};
        //Build the whole field line stmt.
        AstAssign* const thenStmtp
            = new AstAssign{fl, new AstVarRef{fl, m_oFieldVarp, VAccess::WRITE},
                            new AstConst{fl, getOutputNum(nodep, oValName)}};
        AstIf* const ifStmtp = new AstIf{fl, condExprp, thenStmtp};
        if (!m_lineStmtp) {
            m_lineStmtp = ifStmtp;
            m_comboNodeStmtp = m_lineStmtp;
        } else {
            m_lineStmtp->addElsesp(ifStmtp);
            m_lineStmtp = ifStmtp;
        }
    }

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
