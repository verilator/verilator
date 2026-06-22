// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Collect and print statistics
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2005-2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "V3PchAstMT.h"

#include "V3Stats.h"

#include <iomanip>
#include <map>

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// Statics

V3Mutex V3Stats::s_mutex;

//######################################################################
// Stats class functions

class StatsVisitor final : public VNVisitorConst {
    struct Counters final {
        // Nodes of given type
        std::array<uint64_t, VNType::NUM_TYPES()> m_statTypeCount{};
        // Prediction of given type
        std::array<uint64_t, VBranchPred::_ENUM_END> m_statPred{};
    };

    // STATE
    const bool m_fastOnly;  // When true, consider only fast functions
    bool m_empty = true;  // Netlist is empty
    Counters m_counters;  // The actual counts we will display
    Counters m_dumpster;  // Alternate buffer to make discarding parts of the tree easier
    Counters* m_accump;  // The currently active accumulator
    std::vector<uint64_t> m_statVarWidths;  // Variables of given width
    std::vector<uint64_t> m_constPoolConsts;  // Constant pool constants of given width
    // Constant pool tables of given width and depth
    std::map<std::pair<int, int>, uint64_t> m_constPoolTables;
    std::vector<std::map<const std::string, uint32_t>>
        m_statVarWidthNames;  // Var names of given width

    // METHODS
    void countThenIterateChildren(AstNode* nodep) {
        ++m_accump->m_statTypeCount[nodep->type()];
        if (nodep->type() != VNType::Netlist) m_empty = false;
        iterateChildrenConst(nodep);
    }

    // VISITORS
    void visit(AstVar* nodep) override {
        if (nodep->dtypep()) {
            if (nodep->constPoolEntry()) {
                // Count constant pool entries
                if (AstUnpackArrayDType* const uatp = VN_CAST(nodep->dtypep(), UnpackArrayDType)) {
                    const int width = uatp->subDTypep()->width();
                    const int depth = uatp->elementsConst();
                    ++m_constPoolTables[{width, depth}];
                } else {
                    if (m_constPoolConsts.size() <= static_cast<size_t>(nodep->width())) {
                        m_constPoolConsts.resize(nodep->width() + 5);
                    }
                    ++m_constPoolConsts.at(nodep->width());
                }
            } else {
                // Count proper variables
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
        }

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
        UINFO(9, "Starting stats, fastOnly=" << fastOnly);
        iterateConst(nodep);
        if (m_empty) return;

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

        // Constant pool constants
        for (size_t i = 0; i < m_constPoolConsts.size(); ++i) {
            const uint64_t count = m_constPoolConsts.at(i);
            if (!count) continue;
            std::stringstream ss;
            ss << "Vars Const, width " << std::setw(5) << std::dec << i;
            addStat(ss.str(), count);
        }

        // Constant pool tables
        for (const auto& it : m_constPoolTables) {
            const int depth = it.first.second;
            const int width = it.first.first;
            const int count = it.second;
            std::ostringstream ss;
            ss << "Vars Table, width " << std::setw(5) << std::dec << width  //
               << " x " << std::setw(5) << std::dec << depth;
            addStat(ss.str(), count);
        }

        // Node types (also total memory usage)
        const auto typeName
            = [](size_t t) { return std::string{VNType{static_cast<VNType::en>(t)}.ascii()}; };
        const auto typeSize
            = [](size_t t) { return VNType::typeInfo(static_cast<VNType::en>(t)).m_sizeof; };
        size_t totalNodeMemoryUsage = 0;
        for (size_t t = 0; t < VNType::NUM_TYPES(); ++t) {
            if (const uint64_t count = m_counters.m_statTypeCount[t]) {
                totalNodeMemoryUsage += count * typeSize(t);
                addStat("Node count, " + typeName(t), count);
            }
        }
        addStat("Node mem TOTAL (MiB)", totalNodeMemoryUsage >> 20);

        // Node Memory usage
        for (size_t t = 0; t < VNType::NUM_TYPES(); ++t) {
            if (const uint64_t count = m_counters.m_statTypeCount[t]) {
                const double share = 100.0 * count * typeSize(t) / totalNodeMemoryUsage;
                addStat("Node mem %, " + typeName(t), share, 2);
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

void V3Stats::statsFinalAll(AstNetlist* nodep) { statsStageAll(nodep, "Final"); }
