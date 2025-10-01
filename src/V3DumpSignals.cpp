// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator:
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
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3DumpSignals.h"

#include "V3Global.h"

#include <fstream>
#include <iostream>
#include <string>

VL_DEFINE_DEBUG_FUNCTIONS;
V3Global v3global;

class DumpSignals final : public VNVisitor {
    bool m_firstModuleNode = true;
    bool m_foundCell = false;
    string m_currHier;
    std::ofstream m_signalFile;

    // Methods
    void processVar(AstVar* varp) {
        if (varp->basicp() && varp->basicp()->name() != "") {
            bool hasRangep = varp->basicp()->rangep() != nullptr;
            bool isSized = varp->basicp()->widthSized();
            if (hasRangep) {
                std::string varHier
                    = m_currHier + varp->name() + " : Type[" + varp->basicp()->name() + "] Width["
                      + std::to_string(varp->basicp()->rangep()->elementsConst()) + "]";
                m_signalFile << varHier << "\n";
            } else {
                if (varp->basicp()->implicit()) {
                    // Since Var is implicit set the width to 1 like in V3Width.cpp in the AstVar
                    // visitor
                    std::string varHier = m_currHier + varp->name() + " : Type["
                                          + varp->basicp()->name() + "] Width[" + std::to_string(1)
                                          + "]";
                    m_signalFile << varHier << "\n";
                } else {
                    std::string varHier = m_currHier + varp->name() + " : Type["
                                          + varp->basicp()->name() + "] Width["
                                          + std::to_string(varp->basicp()->width()) + "]";
                    m_signalFile << varHier << "\n";
                }
            }
        }
    }

    void processChildrenNode(AstNode* nodep) {
        for (AstNode* n = nodep->op2p(); n; n = n->nextp()) {
            if (VN_IS(n, Var)) {
                AstVar* varp = VN_AS(n, Var);
                if (!varp->isParam() && !varp->isGenVar() && !varp->isIfaceRef()
                    && !varp->isIfaceParent()) {
                    processVar(varp);
                }
            } else if (VN_IS(n, Cell)) {
                if (VN_IS(VN_AS(n, Cell)->modp(), Module)) {
                    m_foundCell = true;
                    std::string oldHier = m_currHier;
                    m_currHier += n->name() + ".";
                    diveIntoCellModp(VN_AS(n, Cell)->modp());
                    m_currHier = oldHier;
                }
            }
        }
    }

    void diveIntoCellModp(AstNodeModule* modp) { processChildrenNode(modp); }

    // VISITORS
    void visit(AstModule* nodep) override {
        if (m_firstModuleNode) {
            m_currHier = nodep->name() + ".";
            processChildrenNode(nodep);
            m_firstModuleNode = false;
        }
    }

    //-----------------
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    explicit DumpSignals(AstNetlist* nodep) {
        std::string filePath = v3global.opt.hierTopDataDir() + "/signalDump.log";
        m_signalFile.open(filePath);
        iterate(nodep);
    }

    ~DumpSignals() override {
        if (m_signalFile.is_open()) { m_signalFile.close(); }
    }
};

//##################################################################################
// DumpSignals class functions

void V3DumpSignals::dumpSignals(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    { DumpSignals{nodep}; }
    V3Global::dumpCheckGlobalTree("dumpSignals", 0, dumpTreeEitherLevel() >= 3);
}
