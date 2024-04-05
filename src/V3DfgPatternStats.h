// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Implementations of simple passes over DfgGraph
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

#ifndef VERILATOR_V3DFGPATTERNSTATS_H_
#define VERILATOR_V3DFGPATTERNSTATS_H_

#include "V3Dfg.h"

#include <algorithm>
#include <map>
#include <unordered_map>

class V3DfgPatternStats final {
    static constexpr uint32_t MIN_PATTERN_DEPTH = 1;
    static constexpr uint32_t MAX_PATTERN_DEPTH = 4;

    std::map<std::string, std::string> m_internedConsts;  // Interned constants
    std::map<const AstVar*, std::string> m_internedVars;  // Interned variables
    std::map<uint32_t, std::string> m_internedSelLsbs;  // Interned lsb value for selects
    std::map<uint32_t, std::string> m_internedWordWidths;  // Interned widths
    std::map<uint32_t, std::string> m_internedWideWidths;  // Interned widths
    std::map<const DfgVertex*, std::string> m_internedVertices;  // Interned vertices

    // Maps from pattern to the number of times it appears, for each pattern depth
    std::vector<std::unordered_map<std::string, size_t>> m_patterCounts{MAX_PATTERN_DEPTH + 1};

    static std::string toLetters(size_t value, bool lowerCase = false) {
        const char base = lowerCase ? 'a' : 'A';
        std::string s;
        do { s += static_cast<char>(base + value % 26); } while (value /= 26);
        return s;
    }

    const std::string& internConst(const DfgConst& vtx) {
        const auto pair = m_internedConsts.emplace(vtx.num().ascii(false), "c");
        if (pair.second) pair.first->second += toLetters(m_internedConsts.size() - 1);
        return pair.first->second;
    }

    const std::string& internVar(const DfgVertexVar& vtx) {
        const auto pair = m_internedVars.emplace(vtx.varp(), "v");
        if (pair.second) pair.first->second += toLetters(m_internedVars.size() - 1);
        return pair.first->second;
    }

    const std::string& internSelLsb(uint32_t value) {
        const auto pair = m_internedSelLsbs.emplace(value, "");
        if (pair.second) pair.first->second += toLetters(m_internedSelLsbs.size() - 1);
        return pair.first->second;
    }

    const std::string& internWordWidth(uint32_t value) {
        const auto pair = m_internedWordWidths.emplace(value, "");
        if (pair.second) pair.first->second += toLetters(m_internedWordWidths.size() - 1, true);
        return pair.first->second;
    }

    const std::string& internWideWidth(uint32_t value) {
        const auto pair = m_internedWideWidths.emplace(value, "");
        if (pair.second) pair.first->second += toLetters(m_internedWideWidths.size() - 1);
        return pair.first->second;
    }

    const std::string& internVertex(const DfgVertex& vtx) {
        const auto pair = m_internedVertices.emplace(&vtx, "_");
        if (pair.second) pair.first->second += toLetters(m_internedVertices.size() - 1);
        return pair.first->second;
    }

    // Render the vertx into ss, and return true if the recursion reached the given depth,
    // meaning an S-expression with that nesting level has been rendered.
    bool render(std::ostringstream& ss, const DfgVertex& vtx, uint32_t depth) {
        bool deep = depth == 0;

        if (const DfgConst* const constp = vtx.cast<DfgConst>()) {
            // Base case 1: constant
            if (constp->isZero()) {
                ss << "'0";
            } else if (constp->isOnes()) {
                ss << "'1";
            } else {
                ss << internConst(*constp);
            }
        } else if (const DfgVertexVar* const varp = vtx.cast<DfgVertexVar>()) {
            // Base case 2: variable
            ss << internVar(*varp);
        } else if (depth == 0) {
            // Base case 3: deep vertex
            ss << internVertex(vtx);
        } else {
            // Recursively print an S-expression for the vertex

            // S-expression begin
            ss << '(';
            // Name
            ss << vtx.typeName();
            // Specials
            if (const DfgSel* const selp = vtx.cast<DfgSel>()) {
                ss << '@';
                if (selp->lsb() == 0) {
                    ss << '0';
                } else {
                    ss << internSelLsb(selp->lsb());
                }
            }

            // Operands
            vtx.forEachSource([&](const DfgVertex& src) {
                ss << ' ';
                if (render(ss, src, depth - 1)) deep = true;
            });
            // S-expression end
            ss << ')';

            // Mark it if it has multiple sinks
            if (vtx.hasMultipleSinks()) ss << '*';
        }

        // Annotate type
        ss << ':';
        const AstNodeDType* const dtypep = vtx.dtypep();
        if (!VN_IS(dtypep, BasicDType)) {
            dtypep->dumpSmall(ss);
        } else {
            const uint32_t width = dtypep->width();
            if (width == 1) {
                ss << '1';
            } else if (width <= VL_QUADSIZE) {
                ss << internWordWidth(width);
            } else {
                ss << internWideWidth(width);
            }
        }

        // Done
        return deep;
    }

public:
    V3DfgPatternStats() = default;

    void accumulate(const DfgGraph& dfg) {
        dfg.forEachVertex([&](const DfgVertex& vtx) {
            for (uint32_t i = MIN_PATTERN_DEPTH; i <= MAX_PATTERN_DEPTH; ++i) {
                std::ostringstream ss;
                if (render(ss, vtx, i)) m_patterCounts[i][ss.str()] += 1;
                m_internedConsts.clear();
                m_internedVars.clear();
                m_internedSelLsbs.clear();
                m_internedWordWidths.clear();
                m_internedWideWidths.clear();
                m_internedVertices.clear();
            }
        });
    }

    void dump(const std::string& stage, std::ostream& os) {
        using Line = std::pair<std::string, size_t>;
        for (uint32_t i = MIN_PATTERN_DEPTH; i <= MAX_PATTERN_DEPTH; ++i) {
            os << "DFG '" << stage << "' patterns with depth " << i << '\n';

            // Pick up pattern accumulators with given depth
            const auto& patternCounts = m_patterCounts[i];

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
};

#endif
