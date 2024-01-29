// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Collect and print statistics
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2005-2024 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "V3PchAstMT.h"

#include "V3Stats.h"

#include <iomanip>
#include <map>

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// Stats class functions

class StatsVisitor final : public VNVisitorConst {
    struct Counters final {
        // Nodes of given type
        uint64_t m_statTypeCount[VNType::_ENUM_END];
        // Nodes of given type with given type immediate child
        uint64_t m_statAbove[VNType::_ENUM_END][VNType::_ENUM_END];
        // Prediction of given type
        uint64_t m_statPred[VBranchPred::_ENUM_END];
    };

    // STATE
    const bool m_fastOnly;  // When true, consider only fast functions
    const AstNodeExpr* m_parentExprp = nullptr;  // Parent expression
    Counters m_counters;  // The actual counts we will display
    Counters m_dumpster;  // Alternate buffer to make discarding parts of the tree easier
    Counters* m_accump;  // The currently active accumulator
    std::vector<uint64_t> m_statVarWidths;  // Variables of given width
    std::vector<std::map<const std::string, uint32_t>>
        m_statVarWidthNames;  // Var names of given width

    // METHODS
    void countThenIterateChildren(AstNode* nodep) {
        ++m_accump->m_statTypeCount[nodep->type()];
        iterateChildrenConst(nodep);
    }

    // VISITORS
    void visit(AstVar* nodep) override {
        if (nodep->dtypep()) {
            if (m_statVarWidths.size() <= static_cast<size_t>(nodep->width())) {
                m_statVarWidths.resize(nodep->width() + 5);
                if (v3Global.opt.statsVars()) {  //
                    m_statVarWidthNames.resize(nodep->width() + 5);
                }
            }
            ++m_statVarWidths.at(nodep->width());
            if (v3Global.opt.statsVars()) {
                ++m_statVarWidthNames.at(nodep->width())[nodep->prettyName()];
            }
        }

        countThenIterateChildren(nodep);
    }

    void visit(AstNodeExpr* nodep) override {
        // Count expression combinations
        if (m_parentExprp) ++m_accump->m_statAbove[m_parentExprp->type()][nodep->type()];
        VL_RESTORER(m_parentExprp);
        m_parentExprp = nodep;
        countThenIterateChildren(nodep);
    }

    void visit(AstNodeIf* nodep) override {
        // Track prediction
        ++m_accump->m_statPred[nodep->branchPred()];
        countThenIterateChildren(nodep);
    }

    void visit(AstCFunc* nodep) override {
        VL_RESTORER(m_accump);
        if (m_fastOnly && !nodep->slow()) m_accump = &m_counters;
        countThenIterateChildren(nodep);
    }

    void visit(AstNode* nodep) override { countThenIterateChildren(nodep); }

public:
    // CONSTRUCTORS
    StatsVisitor(AstNetlist* nodep, const std::string& stage, bool fastOnly)
        : m_fastOnly{fastOnly}
        , m_accump{fastOnly ? &m_dumpster : &m_counters} {
        UINFO(9, "Starting stats, fastOnly=" << fastOnly << endl);
        memset(&m_counters, 0, sizeof(m_counters));
        memset(&m_dumpster, 0, sizeof(m_dumpster));

        iterateConst(nodep);

        // Shorthand
        const auto addStat = [&](const std::string& name, double count, unsigned precision = 0) {
            V3Stats::addStat(stage, name, count, precision);
        };

        // Variable widths
        for (unsigned i = 0; i < m_statVarWidths.size(); i++) {
            if (const uint64_t count = m_statVarWidths.at(i)) {
                std::stringstream ss;
                ss << "Vars, width " << std::setw(5) << std::dec << i;
                const std::string prefix = ss.str();
                if (v3Global.opt.statsVars()) {
                    for (const auto& it : m_statVarWidthNames.at(i)) {
                        addStat(prefix + " " + it.first, it.second);
                    }
                } else {
                    addStat(prefix, count);
                }
            }
        }

        // Node types (also total memory usage)
        const auto typeName = [](int type) { return std::string{VNType{type}.ascii()}; };
        const auto typeSize = [](int type) { return VNType{type}.typeInfo()->m_sizeof; };
        size_t totalNodeMemoryUsage = 0;
        for (int t = 0; t < VNType::_ENUM_END; ++t) {
            if (const uint64_t count = m_counters.m_statTypeCount[t]) {
                totalNodeMemoryUsage += count * typeSize(t);
                addStat("Node count, " + typeName(t), count);
            }
        }
        addStat("Node memory TOTAL (MiB)", totalNodeMemoryUsage >> 20);

        // Node Memory usage
        for (int t = 0; t < VNType::_ENUM_END; ++t) {
            if (const uint64_t count = m_counters.m_statTypeCount[t]) {
                const double share = 100.0 * count * typeSize(t) / totalNodeMemoryUsage;
                addStat("Node memory share (%), " + typeName(t), share, 2);
            }
        }

        // Expression combinations
        for (int t1 = 0; t1 < VNType::_ENUM_END; ++t1) {
            for (int t2 = 0; t2 < VNType::_ENUM_END; ++t2) {
                if (const uint64_t c = m_counters.m_statAbove[t1][t2]) {
                    addStat("Expr combination, " + typeName(t1) + " over " + typeName(t2), c);
                }
            }
        }

        // Branch predictions
        for (int t = 0; t < VBranchPred::_ENUM_END; ++t) {
            if (const uint64_t c = m_counters.m_statPred[t]) {
                addStat("Branch prediction, "s + VBranchPred{t}.ascii(), c);
            }
        }
    }
};

//######################################################################
// Top Stats class

void V3Stats::statsStageAll(AstNetlist* nodep, const std::string& stage, bool fastOnly) {
    StatsVisitor{nodep, stage, fastOnly};
}

void V3Stats::statsFinalAll(AstNetlist* nodep) {
    statsStageAll(nodep, "Final all");
    statsStageAll(nodep, "Final fast", true);
}
