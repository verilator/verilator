// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Implementation of User defined primitives
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
// V3Udp's Transformations:
//
// For every table line create an always block containing if statements
// with condition depending on a combination of the input fields:
//
// 0 1 0 on a, b, c turns into !a&b&~c
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Udp.h"

#include "V3Error.h"

#include <vector>

VL_DEFINE_DEBUG_FUNCTIONS;

class UdpVisitor final : public VNVisitor {
    bool m_inInitial = false;  // Is inside of an initial block
    AstVar* m_oFieldVarp = nullptr;  // Output filed var of table line
    std::vector<AstVar*> m_inputVars;  // All the input vars in the AstPrimitive
    std::vector<AstVar*> m_outputVars;  // All the output vars in the AstPrimitive
    AstPrimitive* m_primp = nullptr;  // The current primitive
    bool m_isFirstOutput = false;  // Whether the first IO port is output
    AstVarRef* m_outputInitVerfp = nullptr;  // Initial output value for sequential UDP
    AstAlways* m_alwaysBlockp = nullptr;  // Main Always block in UDP transform

    void visit(AstInitial* nodep) override {
        VL_RESTORER(m_inInitial);
        if (m_primp) m_inInitial = true;
        iterateChildren(nodep);
    }
    void visit(AstAssign* nodep) override {
        if (m_inInitial) { m_outputInitVerfp = VN_CAST(nodep->lhsp(), VarRef); }
        iterateChildren(nodep);
    }
    void visit(AstPrimitive* nodep) override {
        UASSERT_OBJ(!m_primp, nodep, "Primitives cannot nest");
        VL_RESTORER(m_primp);
        VL_RESTORER(m_outputInitVerfp);
        VL_RESTORER(m_isFirstOutput);
        VL_RESTORER(m_inputVars);
        VL_RESTORER(m_outputVars);
        m_outputInitVerfp = nullptr;
        m_primp = nodep;
        m_isFirstOutput = false;
        iterateChildren(nodep);
        m_inputVars.clear();
        m_outputVars.clear();
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
        FileLine* const fl = nodep->fileline();
        if (m_outputVars.size() != 1) {
            m_outputVars.back()->v3error(
                m_outputVars.size()
                << " output ports for UDP table, there must be one output port");
        }
        if (!m_isFirstOutput && m_outputVars.size()) {
            m_inputVars[0]->v3error("First UDP port must be the output port");
        }
        m_oFieldVarp = m_outputVars[0];

        m_alwaysBlockp = new AstAlways{fl, VAlwaysKwd::ALWAYS, nullptr, nullptr};
        fl->warnOff(V3ErrorCode::LATCH, true);
        iterateChildren(nodep);

        nodep->replaceWith(m_alwaysBlockp);
    }
    void visit(AstUdpTableLine* nodep) override {
        FileLine* const fl = nodep->fileline();
        if (!nodep->udpIsCombo() && !m_oFieldVarp->isBitLogic()) {
            m_oFieldVarp->v3error("For sequential UDP, the output must be of 'reg' data type");
        }
        if (nodep->udpIsCombo() && m_oFieldVarp->isBitLogic()) {
            m_oFieldVarp->v3error(
                "For combinational UDP, the output must not be a 'reg' data type");
        }
        AstNode* iNodep = nodep->iFieldsp();
        AstNode* oNodep = nodep->oFieldsp();
        uint32_t inputvars = 0;
        AstSenTree* edgetrigp = nullptr;

        AstLogAnd* logandp = new AstLogAnd{fl, new AstConst{fl, AstConst::BitTrue{}},
                                           new AstConst{fl, AstConst::BitTrue{}}};

        for (AstVar* itr : m_inputVars) {
            if (!iNodep) break;
            inputvars++;
            if (AstUdpTableLineVal* linevalp = VN_CAST(iNodep, UdpTableLineVal)) {
                string valName = linevalp->name();
                AstVarRef* const referencep = new AstVarRef{fl, itr, VAccess::READ};
                if (isEdgeTrig(valName)) {
                    if (nodep->udpIsCombo()) {
                        linevalp->v3error(
                            "There should not be a edge trigger for combinational UDP table line");
                    }
                    if (edgetrigp) {
                        linevalp->v3error("There can be only one edge tigger signal");
                    }
                    edgetrigp = new AstSenTree{
                        fl, new AstSenItem{fl, VEdgeType::ET_BOTHEDGE,
                                           new AstVarRef{fl, itr, VAccess::READ}}};
                }
                if (valName == "0" || valName == "f")
                    logandp = new AstLogAnd{fl, logandp, new AstLogNot{fl, referencep}};
                else if (valName == "1" || valName == "r")
                    logandp = new AstLogAnd{fl, logandp, referencep};
            }
            iNodep = iNodep->nextp();
        }
        if (inputvars != m_inputVars.size()) {
            nodep->v3error("Incorrect number of input values, expected " << m_inputVars.size()
                                                                         << ", got " << inputvars);
        }

        string const oValName = nodep->udpIsCombo() ? oNodep->name() : oNodep->nextp()->name();
        if (oValName == "-") {
            if (edgetrigp) pushDeletep(edgetrigp);
            if (logandp) pushDeletep(logandp);
            return;
        }

        if (!nodep->udpIsCombo()) {
            AstVarRef* const referencep = new AstVarRef{fl, m_oFieldVarp, VAccess::READ};
            if (oNodep->name() == "0") {
                logandp = new AstLogAnd{fl, logandp, new AstLogNot{fl, referencep}};
            } else if (oNodep->name() == "1") {
                logandp = new AstLogAnd{fl, logandp, referencep};
            }
        }

        fl->warnOff(V3ErrorCode::LATCH, true);
        AstIf* const ifp
            = new AstIf{fl, logandp,
                        new AstAssign{fl, new AstVarRef{fl, m_oFieldVarp, VAccess::WRITE},
                                      new AstConst{fl, getOutputNum(nodep, oValName)}}};
        if (nodep->udpIsCombo()) {
            if (!isCombOutputSig(oValName)) {
                oNodep->v3error("Illegal value for combinational UDP line output");
            }
            m_alwaysBlockp->addStmtsp(ifp);
            return;
        }
        if (!isSequentOutputSig(oValName)) {
            oNodep->nextp()->v3error("Illegal value for sequential UDP line output");
        }
        m_alwaysBlockp->addNext(new AstAlways{fl, VAlwaysKwd::ALWAYS, edgetrigp, ifp});
    }
    void visit(AstNode* nodep) override { iterateChildren(nodep); }
    void visit(AstLogAnd* nodep) override { iterateChildren(nodep); }
    void visit(AstLogNot* nodep) override { iterateChildren(nodep); }
    // For logic processing.
    bool isEdgeTrig(std::string& valName) {
        if (valName == "*") return true;
        if (valName == "01" || valName == "p" || valName == "P" || valName == "r"
            || valName == "R") {
            valName = "r";
            return true;
        }
        if (valName == "10" || valName == "n" || valName == "N" || valName == "f"
            || valName == "F") {
            valName = "f";
            return true;
        }
        if (valName.size() == 2) {
            if (valName[0] == '1' || valName[1] == '0')
                valName = "f";
            else if (valName[0] == '0' || valName[1] == '1')
                valName = "r";
            return true;
        }
        if (valName[0] != '0' && valName[0] != '1') { valName = "?"; }
        return false;
    }
    bool isCombOutputSig(const std::string& valName) {
        return (valName == "0" || valName == "1" || valName == "x" || valName == "X");
    }
    bool isSequentOutputSig(const std::string& valName) {
        return (valName == "0" || valName == "1" || valName == "x" || valName == "X"
                || valName == "-");
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

public:
    // CONSTRUCTORS
    explicit UdpVisitor(AstNetlist* nodep) { iterate(nodep); }
    ~UdpVisitor() override = default;
};

void V3Udp::udpResolve(AstNetlist* rootp) {
    UINFO(4, __FUNCTION__ << ": " << endl);
    { const UdpVisitor visitor{rootp}; }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("udp", 0, dumpTreeEitherLevel() >= 3);
}
