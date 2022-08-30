// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Collect and print statistics
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2005-2022 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3Stats.h"

#include "V3Ast.h"
#include "V3Global.h"

// This visitor does not edit nodes, and is called at error-exit, so should use constant iterators
#include "V3AstConstOnly.h"

#include <iomanip>
#include <map>

//######################################################################
// Stats class functions

class StatsVisitor final : public VNVisitor {
private:
    // NODE STATE/TYPES

    using NameMap = std::map<const std::string, int>;  // Number of times a name appears

    // STATE
    const string m_stage;  // Name of the stage we are scanning
    /// m_fast = true:  Counting only critical branch of fastpath
    /// m_fast = false:  Counting every node, ignoring structure of program
    const bool m_fast;

    const AstCFunc* m_cfuncp;  // Current CFUNC
    bool m_counting;  // Currently counting
    double m_instrs;  // Current instr count (for determining branch direction)
    bool m_tracingCall;  // Iterating into a CCall to a CFunc

    std::vector<VDouble0> m_statTypeCount;  // Nodes of given type
    VDouble0 m_statAbove[VNType::_ENUM_END][VNType::_ENUM_END];  // Nodes of given type
    std::array<VDouble0, VBranchPred::_ENUM_END> m_statPred;  // Nodes of given type
    VDouble0 m_statInstr;  // Instruction count
    VDouble0 m_statInstrFast;  // Instruction count, non-slow() eval functions only
    std::vector<VDouble0> m_statVarWidths;  // Variables of given width
    std::vector<NameMap> m_statVarWidthNames;  // Var names of given width
    VDouble0 m_statVarArray;  // Statistic tracking
    VDouble0 m_statVarBytes;  // Statistic tracking
    VDouble0 m_statVarClock;  // Statistic tracking
    VDouble0 m_statVarScpBytes;  // Statistic tracking

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    void allNodes(AstNode* nodep) {
        m_instrs += nodep->instrCount();
        if (m_counting) {
            ++m_statTypeCount[nodep->type()];
            if (nodep->firstAbovep()) {  // Grab only those above, not those "back"
                ++m_statAbove[nodep->firstAbovep()->type()][nodep->type()];
            }
            m_statInstr += nodep->instrCount();
            if (m_cfuncp && !m_cfuncp->slow()) m_statInstrFast += nodep->instrCount();
        }
    }

    // VISITORS
    virtual void visit(AstNodeModule* nodep) override {
        allNodes(nodep);
        if (!m_fast) {
            // Count all CFuncs below this module
            iterateChildrenConst(nodep);
        }
        // Else we recursively trace fast CFuncs from the top _eval
        // func, see visit(AstNetlist*)
    }
    virtual void visit(AstVar* nodep) override {
        allNodes(nodep);
        iterateChildrenConst(nodep);
        if (m_counting && nodep->dtypep()) {
            if (nodep->isUsedClock()) ++m_statVarClock;
            if (VN_IS(nodep->dtypeSkipRefp(), UnpackArrayDType)) {
                ++m_statVarArray;
            } else {
                m_statVarBytes += nodep->dtypeSkipRefp()->widthTotalBytes();
            }
            if (int(m_statVarWidths.size()) <= nodep->width()) {
                m_statVarWidths.resize(nodep->width() + 5);
                if (v3Global.opt.statsVars()) m_statVarWidthNames.resize(nodep->width() + 5);
            }
            ++m_statVarWidths.at(nodep->width());
            const string pn = nodep->prettyName();
            if (v3Global.opt.statsVars()) {
                NameMap& nameMapr = m_statVarWidthNames.at(nodep->width());
                if (nameMapr.find(pn) != nameMapr.end()) {
                    nameMapr[pn]++;
                } else {
                    nameMapr[pn] = 1;
                }
            }
        }
    }
    virtual void visit(AstVarScope* nodep) override {
        allNodes(nodep);
        iterateChildrenConst(nodep);
        if (m_counting) {
            if (VN_IS(nodep->varp()->dtypeSkipRefp(), BasicDType)) {
                m_statVarScpBytes += nodep->varp()->dtypeSkipRefp()->widthTotalBytes();
            }
        }
    }
    virtual void visit(AstNodeIf* nodep) override {
        UINFO(4, "   IF i=" << m_instrs << " " << nodep << endl);
        allNodes(nodep);
        // Condition is part of cost allocated to PREVIOUS block
        iterateAndNextConstNull(nodep->condp());
        // Track prediction
        if (m_counting) ++m_statPred[nodep->branchPred()];
        if (!m_fast) {
            // Count everything
            iterateChildrenConst(nodep);
        } else {
            // See which path we want to take
            // Need to do even if !m_counting because maybe determining upstream if/else
            double ifInstrs = 0.0;
            double elseInstrs = 0.0;
            if (!nodep->branchPred().unlikely()) {  // Check if
                VL_RESTORER(m_instrs);
                VL_RESTORER(m_counting);
                {
                    m_counting = false;
                    m_instrs = 0.0;
                    iterateAndNextConstNull(nodep->ifsp());
                    ifInstrs = m_instrs;
                }
            }
            if (!nodep->branchPred().likely()) {  // Check else
                VL_RESTORER(m_instrs);
                VL_RESTORER(m_counting);
                {
                    m_counting = false;
                    m_instrs = 0.0;
                    iterateAndNextConstNull(nodep->elsesp());
                    elseInstrs = m_instrs;
                }
            }
            // Now collect the stats
            if (m_counting) {
                if (ifInstrs >= elseInstrs) {
                    iterateAndNextConstNull(nodep->ifsp());
                } else {
                    iterateAndNextConstNull(nodep->elsesp());
                }
            }
        }
    }
    // While's we assume evaluate once.
    // virtual void visit(AstWhile* nodep) override {

    virtual void visit(AstNodeCCall* nodep) override {
        allNodes(nodep);
        iterateChildrenConst(nodep);
        if (m_fast && !nodep->funcp()->entryPoint()) {
            // Enter the function and trace it
            m_tracingCall = true;
            iterate(nodep->funcp());
        }
    }
    virtual void visit(AstCFunc* nodep) override {
        if (m_fast) {
            if (!m_tracingCall && !nodep->entryPoint()) return;
            m_tracingCall = false;
        }
        VL_RESTORER(m_cfuncp);
        {
            m_cfuncp = nodep;
            allNodes(nodep);
            iterateChildrenConst(nodep);
        }
    }
    virtual void visit(AstNode* nodep) override {
        allNodes(nodep);
        iterateChildrenConst(nodep);
    }
    virtual void visit(AstNetlist* nodep) override {
        if (m_fast && nodep->evalp()) {
            m_instrs = 0;
            m_counting = true;
            iterateChildrenConst(nodep->evalp());
            m_counting = false;
        }
        allNodes(nodep);
        iterateChildrenConst(nodep);
    }

public:
    // CONSTRUCTORS
    StatsVisitor(AstNetlist* nodep, const string& stage, bool fast)
        : m_stage{stage}
        , m_fast{fast} {
        UINFO(9, "Starting stats, fast=" << fast << endl);
        m_cfuncp = nullptr;
        m_counting = !m_fast;
        m_instrs = 0;
        m_tracingCall = false;
        // Initialize arrays
        m_statTypeCount.resize(VNType::_ENUM_END);
        // Process
        iterate(nodep);
    }
    virtual ~StatsVisitor() override {
        // Done. Publish statistics
        V3Stats::addStat(m_stage, "Instruction count, TOTAL", m_statInstr);
        V3Stats::addStat(m_stage, "Instruction count, fast critical", m_statInstrFast);
        // Vars
        V3Stats::addStat(m_stage, "Vars, unpacked arrayed", m_statVarArray);
        V3Stats::addStat(m_stage, "Vars, clock attribute", m_statVarClock);
        V3Stats::addStat(m_stage, "Var space, non-arrays, bytes", m_statVarBytes);
        if (m_statVarScpBytes != 0.0) {
            V3Stats::addStat(m_stage, "Var space, scoped, bytes", m_statVarScpBytes);
        }
        for (unsigned i = 0; i < m_statVarWidths.size(); i++) {
            const double count = double(m_statVarWidths.at(i));
            if (count != 0.0) {
                if (v3Global.opt.statsVars()) {
                    const NameMap& nameMapr = m_statVarWidthNames.at(i);
                    for (const auto& itr : nameMapr) {
                        std::ostringstream os;
                        os << "Vars, width " << std::setw(5) << std::dec << i << " " << itr.first;
                        V3Stats::addStat(m_stage, os.str(), itr.second);
                    }
                } else {
                    std::ostringstream os;
                    os << "Vars, width " << std::setw(5) << std::dec << i;
                    V3Stats::addStat(m_stage, os.str(), count);
                }
            }
        }
        // Node types
        for (int type = 0; type < VNType::_ENUM_END; type++) {
            const double count = double(m_statTypeCount.at(type));
            if (count != 0.0) {
                V3Stats::addStat(m_stage, std::string{"Node count, "} + VNType{type}.ascii(),
                                 count);
            }
        }
        for (int type = 0; type < VNType::_ENUM_END; type++) {
            for (int type2 = 0; type2 < VNType::_ENUM_END; type2++) {
                const double count = double(m_statAbove[type][type2]);
                if (count != 0.0) {
                    V3Stats::addStat(m_stage,
                                     (std::string{"Node pairs, "} + VNType{type}.ascii() + "_"
                                      + VNType(type2).ascii()),
                                     count);
                }
            }
        }
        // Branch pred
        for (int type = 0; type < VBranchPred::_ENUM_END; type++) {
            const double count = double(m_statPred[type]);
            if (count != 0.0) {
                V3Stats::addStat(m_stage,
                                 (std::string{"Branch prediction, "} + VBranchPred{type}.ascii()),
                                 count);
            }
        }
    }
};

//######################################################################
// Top Stats class

void V3Stats::statsStageAll(AstNetlist* nodep, const string& stage, bool fast) {
    { StatsVisitor{nodep, stage, fast}; }
}

void V3Stats::statsFinalAll(AstNetlist* nodep) {
    statsStageAll(nodep, "Final");
    statsStageAll(nodep, "Final_Fast", true);
}
