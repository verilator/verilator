// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Implementations of simple passes over DfgGraph
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

#ifndef VERILATOR_V3DFGPATTERNSTATS_H_
#define VERILATOR_V3DFGPATTERNSTATS_H_

#include "V3Dfg.h"
#include "V3DfgPasses.h"
#include "V3File.h"

#include <unordered_map>

class V3DfgPatternStats final {
    static constexpr uint32_t MIN_PATTERN_DEPTH = 1;
    static constexpr uint32_t MAX_PATTERN_DEPTH = 4;

    // Maps from pattern to the number of times it appears, for each pattern depth
    std::vector<std::unordered_map<std::string, size_t>> m_patterCounts{MAX_PATTERN_DEPTH + 1};

    void dump(std::ostream& os) {
        using Line = std::pair<std::string, size_t>;
        for (uint32_t i = MIN_PATTERN_DEPTH; i <= MAX_PATTERN_DEPTH; ++i) {
            os << "DFG patterns with depth " << i << '\n';

            // Pick up pattern accumulators with given depth
            auto& patternCounts = m_patterCounts[i];

            // Remove patterns also present at shallower depths
            for (uint32_t j = MIN_PATTERN_DEPTH; j < i; ++j) {
                for (const auto& pair : m_patterCounts[j]) patternCounts.erase(pair.first);
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
    V3DfgPatternStats() = default;
    ~V3DfgPatternStats() {
        // File to dump to
        const std::string filename
            = v3Global.opt.hierTopDataDir() + "/" + v3Global.opt.prefix() + "__dfg_patterns.txt";
        // Open, write, close
        const std::unique_ptr<std::ofstream> ofp{V3File::new_ofstream(filename)};
        if (ofp->fail()) v3fatal("Can't write file: " << filename);
        dump(*ofp);
    }

    void accumulate(const DfgGraph& dfg) {
        dfg.forEachVertex([&](const DfgVertex& vtx) {
            for (uint32_t i = MIN_PATTERN_DEPTH; i <= MAX_PATTERN_DEPTH; ++i) {
                m_patterCounts[i][vtx.patternString(i)] += 1;
            }
        });
    }
};

void V3DfgPasses::dumpPatterns(const std::vector<std::unique_ptr<DfgGraph>>& graphs) {
    V3DfgPatternStats patternStats;
    for (auto& cp : graphs) patternStats.accumulate(*cp);
}

#endif
