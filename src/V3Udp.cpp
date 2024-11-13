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
#include <map>

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
    AstVar* m_ifieldVarp = nullptr;  // Input field var of table line.
    AstVar* m_ofieldVarp = nullptr;  // Output filed var of table line.
    std::vector<AstVar*> m_inputVars;  // All the input vars in the AstPrimitive.
    std::vector<AstVar*> m_outputVars;  // All the output vars in the AstPrimitive.
    AstPrimitive* m_primp = nullptr;
    AstNodeStmt* m_comboNodeStmtp = nullptr; // The stmt for all the combinational lines.
    AstIf* m_lineStmtp = nullptr;  // The stmt for the current combinational lines.
    AstAlways* m_alwaysp = nullptr;  // The the always_latch realizing the combinational part.
    bool m_isFirstOutput = false;  // Whether the first IO port is output.
    AstUdpTableLineVal* m_edgeTrigValp = nullptr; // The edge trigger value.
    AstVar* m_trigVarp = nullptr; // The edge trigger var.
    std::map<AstVar*, std::pair<AstAlways*, AstAlways*>> m_trigAlwaysMapp; // The always block map for r|f edge.
    std::map<AstAlways*, AstIf*> m_alwaysIfMapp; // The map between always and if stmt for sequent line.
    AstVar* m_newOutVarp = nullptr; // The output varp.
    uint32_t m_inputNum = 0; // The input var number.
    uint32_t m_outputNum = 0; // The output var number.

    void visit(AstPrimitive* nodep) override {
        m_primp = nodep;
        m_isFirstOutput = false;
        iterateChildren(nodep);
        m_inputVars.clear();
        m_outputVars.clear();
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
        m_ofieldVarp = m_outputVars[0];
        // Input var for the ifield,
        // Add the input filed var and corresponding varref.
        AstNodeDType* const typep = nodep->findBitDType(m_inputNum, m_inputNum, VSigning::NOSIGN);
        m_ifieldVarp = new AstVar{fl, VVarType::MODULETEMP, "tableline__ifield__udptmp", typep};
        m_inputVars.back()->addNextHere(m_ifieldVarp);
        AstVarRef* const ifieldRefp = new AstVarRef{fl, m_ifieldVarp, VAccess::WRITE};
        auto itr = m_inputVars.begin();
        // Relate the input vars with the input field var by concat
        AstNodeExpr* contactp = new AstVarRef{fl, *itr, VAccess::READ};
        while (++itr != m_inputVars.end()) {
            contactp = new AstConcat{fl, new AstVarRef{fl, *itr, VAccess::READ}, contactp};
        }
        AstNodeStmt* const ifieldStmtp = new AstAssignW{fl, ifieldRefp, contactp};
        AstNode* currentNode = ifieldStmtp;
        // Process every table line.
        iterateChildren(nodep);
        // First for the sequent parts;
        if (!m_alwaysIfMapp.empty()) {
            for (auto itr = m_alwaysIfMapp.begin(); itr != m_alwaysIfMapp.end(); itr++) {
                currentNode->addNextHere(itr->first);
                currentNode = itr->first;
            }
            AstAssignW* const sequentAssignStmtp = new AstAssignW{
                fl, new AstVarRef{fl, m_ofieldVarp, VAccess::WRITE}, new AstVarRef{fl, m_newOutVarp, VAccess::READ}};
            currentNode->addNextHere(sequentAssignStmtp);
            currentNode = sequentAssignStmtp;
        }
        // Then for the comb parts.
        if (m_comboNodeStmtp) {
            // Use the always_latch to realize the UDP table.
            m_alwaysp = new AstAlways{fl, VAlwaysKwd::ALWAYS, nullptr, nullptr};
            currentNode->addNextHere(m_alwaysp);
            m_alwaysp->addStmtsp(m_comboNodeStmtp);
        }
        nodep->replaceWith(ifieldStmtp);
        m_trigAlwaysMapp.clear();
        m_alwaysIfMapp.clear();
        m_newOutVarp = nullptr;
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }
    void visit(AstUdpTableLine* nodep) override {
        processLogic(nodep);
    }
    void visit(AstNode* nodep) override { iterateChildren(nodep); }
// For logic processing.
    bool isEdgeTrig(std::string &varName) {
        auto isNum = [](char str) {
            if (str == '1' || str == '0') return true;
            return false;
        };
        if (varName == "r" || varName == "f" || varName == "R" || varName == "F") return true;
        if (varName.length() == 4) {
            std::string varNum = varName.substr(1,2);
            if (varNum == "01" || varNum == "p" || varNum == "P") {
                varName = "r";
                return true;
            }
            if (varNum == "10" || varNum == "n" || varNum == "N") {
                varName = "f";
                return true;
            }
            if (isNum(varNum[0]) && !isNum(varNum[1])) {
                if(varNum[0] == '1') varName = "f";
                else varName = "r";
                return true;
            }
            if (!isNum(varNum[0]) && isNum(varNum[1])) {
                if(varNum[1] == '1') varName = "r";
                else varName = "f";
                return true;
            }
            varName = "?";
        }
        return false;
    }
    bool isMultiSig(const std::string &varName) {
        return varName.length() >= 2;
    }
    bool isOutputSig(const std::string &varName) {
        return (varName == "0" || varName == "1" || \
        varName == "x" || varName == "X");
    }
    bool isLevelSig(const std::string &varName) {
        return (varName == "0" || varName == "1" || \
        varName == "x" || varName == "X" || \
        varName == "?" || varName == "b" || 
        varName == "B");
    }
    void processLogic(AstUdpTableLine* nodep) {
        auto fl = nodep->fileline();
        AstNode* inodep = nodep->ifieldp();
        AstNode* onodep = nodep->ofieldp();
        std::vector<std::string> ifieldNames;
        std::vector<std::string> ofieldNames;
        m_edgeTrigValp = nullptr;
        m_trigVarp = nullptr;
        int index = 0;
        while (inodep) {
            if (AstUdpTableLineVal* linevalp = VN_CAST(inodep, UdpTableLineVal)) {
                std::string varName = linevalp->name();
                if (isEdgeTrig(varName)) {
                    if(!m_edgeTrigValp) {
                        m_edgeTrigValp = linevalp;
                        linevalp->name(varName);
                        m_trigVarp = m_inputVars[index];
                    }
                    else inodep->v3error("There can be only one edge tigger signal!");
                }
                if (isMultiSig(varName)) {
                    for (auto name : varName) {
                        std::string subName = std::string{name};
                        if (!isLevelSig(subName)) {
                            linevalp->v3error("Illegal value for input value!");
                        }
                        ifieldNames.push_back(subName);
                    }
                } else {
                    if (!isLevelSig(varName)) {
                        linevalp->v3error("Illegal value for input value!");
                    }
                    ifieldNames.push_back(varName);
                }
                index++;
            }
            inodep = inodep->nextp();
        }
        if (ifieldNames.size() != m_inputNum) {
            nodep->v3error(m_inputNum << " input var required, while there are "
                                      << ifieldNames.size() << " input for the table line!");
        }
        while (onodep) {
            if (AstUdpTableLineVal* linevalp = VN_CAST(onodep, UdpTableLineVal)) {
                if (!isOutputSig(linevalp->name())) {
                    linevalp->v3error("Illegal value for input value!");
                }
                ofieldNames.push_back(linevalp->name());
            }
            onodep = onodep->nextp();
        }
        uint32_t outputNum = ofieldNames.size();
        if (nodep->type() == AstUdpTableLine::UDP_COMB) {
            if(outputNum != 1) {
                nodep->v3error("1 output var required, while there are "
                                        << outputNum << " input for combinational UDP table line!");                
            }
            if (m_edgeTrigValp) {
                nodep->v3error("There should not be a edge trigger for combinational UDP table line!");
            }
        } else {
            if(outputNum != 2) {
                nodep->v3error("2 output var required, while there are "
                                        << outputNum << " input for combinational UDP table line!");                
            }            
        }
        if (!m_edgeTrigValp) {
            addCombLogic(nodep, ifieldNames, ofieldNames);
        } else {
            addEdgTriglogic(nodep, ifieldNames, ofieldNames);
        }
    }
    V3Number getMaskNum(AstNode* nodep, const std::vector<std::string>& fieldNames) {
        V3Number maskNum{nodep, (int)fieldNames.size()};
        int bitIndex = 0;
        for (auto name : fieldNames) {
            if (name == "0") {
                maskNum.setBit(bitIndex, 1);
            } else if (name == "1") {
                maskNum.setBit(bitIndex, 1);
            } else {
                maskNum.setBit(bitIndex, 0);
            }
            bitIndex++;
        }
        return maskNum;
    }
    V3Number getCmpNum(AstNode* nodep, const std::vector<std::string>& fieldNames) {
        V3Number cmpNum{nodep, (int)fieldNames.size()};
        int bitIndex = 0;
        for (auto name : fieldNames) {
            if (name == "0") {
                cmpNum.setBit(bitIndex, 0);
            } else if (name == "1") {
                cmpNum.setBit(bitIndex, 1);
            } else {
                cmpNum.setBit(bitIndex, 0);
            }
            bitIndex++;
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
    void addEdgTriglogic(AstUdpTableLine* nodep,
        std::vector<std::string>& ifieldNames,
        std::vector<std::string>& ofieldNames) {
        auto ovalName = ofieldNames[1];
        auto ostateName = ofieldNames[0];
        if (ovalName == "-") return; // Do not need change if keep value.
        std::string trigStr = m_edgeTrigValp->name();
        auto fl = nodep->fileline();
        if(!m_newOutVarp) { // Out var used for the current out state.
            AstNodeDType* const typep = nodep->findLogicDType(1, 1, VSigning::NOSIGN);
            m_newOutVarp = new AstVar{fl, VVarType::MODULETEMP, "tableline__ofield__udptmp", typep};
            m_ifieldVarp->addNextHere(m_newOutVarp);
        }
        if (m_trigAlwaysMapp.find(m_trigVarp) == m_trigAlwaysMapp.end()) {
            m_trigAlwaysMapp[m_trigVarp] = std::make_pair(nullptr, nullptr);
        }
        AstAlways* alwaysp = nullptr;
        if (trigStr == "r") {
            if(m_trigAlwaysMapp[m_trigVarp].first == nullptr) {
                AstVarRef* varRefp = new AstVarRef{fl, m_trigVarp, VAccess::READ};
                m_trigAlwaysMapp[m_trigVarp].first = new AstAlways{fl, VAlwaysKwd::ALWAYS, \
                new AstSenTree{fl, new AstSenItem{fl, VEdgeType::ET_POSEDGE, varRefp}}, \
                nullptr};
            }
            alwaysp = m_trigAlwaysMapp[m_trigVarp].first;
        } else if (trigStr == "f") {
            if(m_trigAlwaysMapp[m_trigVarp].second == nullptr) {
                AstVarRef* varRefp = new AstVarRef{fl, m_trigVarp, VAccess::READ};
                m_trigAlwaysMapp[m_trigVarp].second = new AstAlways{fl, VAlwaysKwd::ALWAYS, \
                new AstSenTree{fl, new AstSenItem{fl, VEdgeType::ET_NEGEDGE, varRefp}}, \
                nullptr};
            }
            alwaysp = m_trigAlwaysMapp[m_trigVarp].second;
        }
        if(!alwaysp) return;
        // Add the expression under always.
        // If condition for ifield.
        AstConst* const maskConstp = new AstConst{fl, getMaskNum(nodep, ifieldNames)};
        AstConst* const cmpConstp = new AstConst{fl, getCmpNum(nodep, ifieldNames)};
        AstNodeExpr* condExprp = new AstEq{
            fl, new AstAnd{fl, maskConstp, new AstVarRef{fl, m_ifieldVarp, VAccess::READ}},
            cmpConstp};
        // If condition for current state.
        if (ostateName == "0" || ostateName == "1") {
            AstConst* const cmpStateCmpp = new AstConst{fl, V3Number{nodep, 1, (uint32_t)std::stoi(ostateName)}};
            AstNodeExpr* const cmpEqp = new AstEq{
                fl, new AstVarRef{fl, m_newOutVarp, VAccess::READ},
                cmpStateCmpp};
            condExprp = new AstAnd{fl, condExprp, cmpEqp};
        }
        //Add the stmp.
        AstAssignDly* const thenStmtp = new AstAssignDly{
            fl, new AstVarRef{fl, m_newOutVarp, VAccess::WRITE}, new AstConst{fl, getOutputNum(nodep, ovalName)}};
        AstIf* const ifStmtp = new AstIf{fl, condExprp, thenStmtp};
        if(!alwaysp->stmtsp()) {
            alwaysp->addStmtsp(ifStmtp);
        } else {
            m_alwaysIfMapp[alwaysp]->addElsesp(ifStmtp);
        }
        m_alwaysIfMapp[alwaysp] = ifStmtp;
    }
    void addCombLogic(AstUdpTableLine* nodep,
        std::vector<std::string>& ifieldNames,
        std::vector<std::string>& ofieldNames) {
        // Build the ifield condition
        // For one table line, the match condition is
        // ifieldRefp & maskNum == cmpNum
        // For example: 0?1:1
        // maskNum is : 101
        // cmpNum is : 001
        auto ovalName = ofieldNames.size() == 1? ofieldNames[0] : ofieldNames[1];
        if (ovalName == "-") return; // Ignore for keep original state.
        auto fl = nodep->fileline();
        AstConst* const maskConstp = new AstConst{fl, getMaskNum(nodep, ifieldNames)};
        AstConst* const cmpConstp = new AstConst{fl, getCmpNum(nodep, ifieldNames)};
        AstNodeExpr* const condExprp = new AstEq{
            fl, new AstAnd{fl, maskConstp, new AstVarRef{fl, m_ifieldVarp, VAccess::READ}},
            cmpConstp};
        //Build the whole field line stmt.
        AstAssign* const thenStmtp = new AstAssign{
            fl, new AstVarRef{fl, m_ofieldVarp, VAccess::WRITE}, new AstConst{fl, getOutputNum(nodep, ovalName)}};
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
