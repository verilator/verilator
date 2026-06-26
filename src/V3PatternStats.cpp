// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Dump data structure pattern frequencies for analysis
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

#include "V3PchAstNoMT.h"

#include "V3Ast.h"
#include "V3AstPatterns.h"
#include "V3Dfg.h"
#include "V3DfgPasses.h"
#include "V3File.h"

#include <memory>
#include <unordered_map>
#include <vector>

VL_DEFINE_DEBUG_FUNCTIONS;

//============================================================================
// Accumulates and dumps the pattern statistics

class V3PatternStats VL_NOT_FINAL {
public:
    static constexpr uint32_t MIN_PATTERN_DEPTH = 1;
    static constexpr uint32_t MAX_PATTERN_DEPTH = 4;

private:
    const std::string m_what;  // Description of what is being dumped
    // Maps from pattern to the number of times it appears, for each pattern depth
    std::vector<std::unordered_map<std::string, size_t>> m_patternCounts{MAX_PATTERN_DEPTH + 1};

    void dump(std::ostream& os) {
        using Line = std::pair<std::string, size_t>;
        for (uint32_t i = MIN_PATTERN_DEPTH; i <= MAX_PATTERN_DEPTH; ++i) {
            os << m_what << " patterns with depth " << i << '\n';

            // Pick up pattern accumulators with given depth
            auto& patternCounts = m_patternCounts[i];

            // Remove patterns also present at shallower depths
            for (uint32_t j = MIN_PATTERN_DEPTH; j < i; ++j) {
                for (const auto& pair : m_patternCounts[j]) patternCounts.erase(pair.first);
            }

            // Sort patterns, first by descending frequency, then lexically
            std::vector<Line> lines;
            lines.reserve(patternCounts.size());
            for (const auto& pair : patternCounts) lines.emplace_back(pair);
            std::sort(lines.begin(), lines.end(), [](const Line& a, const Line& b) {
                if (a.second != b.second) return a.second > b.second;
                return a.first < b.first;
            });

            // Print each pattern
            for (const auto& line : lines) {
                os << ' ' << std::setw(12) << std::right << line.second;
                os << ' ' << std::left << line.first << '\n';
            }

            // Trailing new-line to separate sections
            os << '\n';
        }
    }

public:
    V3PatternStats(const std::string& what)
        : m_what{what} {}
    ~V3PatternStats() = default;

    void accumulate(const std::string& pattern, uint32_t depth) {
        m_patternCounts[depth][pattern] += 1;
    }

    void dumpToFile(const std::string& filename) {
        // Open, write, close
        const std::unique_ptr<std::ofstream> ofp{V3File::new_ofstream(filename)};
        if (ofp->fail()) v3fatal("Can't write file: " << filename);
        dump(*ofp);
    }
};

//============================================================================
// V3AstPatterns top level

void V3AstPatterns::dumpAll(const AstNetlist* nodep, const std::string& suffix) {
    UINFO(2, __FUNCTION__ << ":");
    V3PatternStats patternStats{"AST"};
    nodep->foreach([&](const AstNodeExpr* exprp) {
        for (uint32_t i = V3PatternStats::MIN_PATTERN_DEPTH;
             i <= V3PatternStats::MAX_PATTERN_DEPTH; ++i) {
            patternStats.accumulate(exprp->patternString(i), i);
        }
    });
    const std::string fileName = v3Global.opt.hierTopDataDir() + "/" + v3Global.opt.prefix()
                                 + "__ast_patterns_" + suffix + ".txt";
    patternStats.dumpToFile(fileName);
    V3Global::dumpCheckGlobalTree("astpatterns", 0, false, false);
}

//============================================================================
// V3DfgPasses top level

void V3DfgPasses::dumpPatterns(const std::vector<std::unique_ptr<DfgGraph>>& graphs,
                               const std::string& suffix) {
    V3PatternStats patternStats{"DFG"};
    for (auto& cp : graphs) {
        cp->forEachVertex([&](const DfgVertex& vtx) {
            for (uint32_t i = V3PatternStats::MIN_PATTERN_DEPTH;
                 i <= V3PatternStats::MAX_PATTERN_DEPTH; ++i) {
                patternStats.accumulate(vtx.patternString(i), i);
            }
        });
    }
    const std::string fileName = v3Global.opt.hierTopDataDir() + "/" + v3Global.opt.prefix()
                                 + "__dfg_patterns" + suffix + ".txt";
    patternStats.dumpToFile(fileName);
}
