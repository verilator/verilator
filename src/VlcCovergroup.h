// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: verilator_coverage: Covergroup data containers
//
// Code available from: https://verilator.org
//*************************************************************************
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2003-2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#ifndef VERILATOR_VLCCOVERGROUP_H_
#define VERILATOR_VLCCOVERGROUP_H_

#include "config_build.h"
#include "verilatedos.h"

#include <iomanip>
#include <map>
#include <sstream>
#include <vector>

//********************************************************************
// VlcCgBin - One coverage bin within a coverpoint

class VlcCgBin final {
    // MEMBERS
    string m_name;
    string m_binType;  //< "ignore", "illegal", or "" (normal)
    bool m_covered = false;
    uint64_t m_count = 0;

public:
    // CONSTRUCTORS
    VlcCgBin(const string& name, const string& binType, bool covered, uint64_t count)
        : m_name{name}
        , m_binType{binType}
        , m_covered{covered}
        , m_count{count} {}
    ~VlcCgBin() = default;

    // ACCESSORS
    const string& name() const { return m_name; }
    const string& binType() const { return m_binType; }
    bool covered() const { return m_covered; }
    uint64_t count() const { return m_count; }
};

//********************************************************************
// VlcCgCoverpoint - One coverpoint or cross within a covergroup type

class VlcCgCoverpoint final {
    // MEMBERS
    string m_name;
    bool m_isCross = false;
    std::vector<VlcCgBin> m_bins;
    uint64_t m_normalTotal = 0;
    uint64_t m_normalCovered = 0;

public:
    // CONSTRUCTORS
    VlcCgCoverpoint(const string& name, bool isCross)
        : m_name{name}
        , m_isCross{isCross} {}
    ~VlcCgCoverpoint() = default;

    // ACCESSORS
    const string& name() const { return m_name; }
    bool isCross() const { return m_isCross; }
    const std::vector<VlcCgBin>& bins() const { return m_bins; }
    uint64_t normalTotal() const { return m_normalTotal; }
    uint64_t normalCovered() const { return m_normalCovered; }

    // METHODS
    void addBin(const string& name, const string& binType, bool covered, uint64_t count) {
        m_bins.emplace_back(name, binType, covered, count);
        if (binType.empty()) {
            ++m_normalTotal;
            if (covered) ++m_normalCovered;
        }
    }
};

//********************************************************************
// VlcCovergroupType - One covergroup type aggregated across all tests

class VlcCovergroupType final {
    // MEMBERS
    string m_typeName;
    string m_filename;
    int m_lineno = 0;
    std::vector<VlcCgCoverpoint> m_coverpoints;
    std::map<string, size_t> m_cpIndex;  //< Coverpoint name -> index into m_coverpoints

public:
    // CONSTRUCTORS
    VlcCovergroupType(const string& typeName, const string& filename, int lineno)
        : m_typeName{typeName}
        , m_filename{filename}
        , m_lineno{lineno} {}
    ~VlcCovergroupType() = default;

    // ACCESSORS
    const string& typeName() const { return m_typeName; }
    const string& filename() const { return m_filename; }
    int lineno() const { return m_lineno; }
    const std::vector<VlcCgCoverpoint>& coverpoints() const { return m_coverpoints; }

    // METHODS
    VlcCgCoverpoint& findNewCoverpoint(const string& name, bool isCross) {
        const auto it = m_cpIndex.find(name);
        if (it != m_cpIndex.end()) return m_coverpoints[it->second];
        const size_t idx = m_coverpoints.size();
        m_cpIndex[name] = idx;
        m_coverpoints.emplace_back(name, isCross);
        return m_coverpoints[idx];
    }
    uint64_t normalTotal() const {
        uint64_t total = 0;
        for (const auto& cp : m_coverpoints) total += cp.normalTotal();
        return total;
    }
    uint64_t normalCovered() const {
        uint64_t covered = 0;
        for (const auto& cp : m_coverpoints) covered += cp.normalCovered();
        return covered;
    }
};

//********************************************************************
// VlcCovergroups - Container of all covergroup types

class VlcCovergroups final {
    // MEMBERS
    std::map<string, VlcCovergroupType> m_cgMap;  //< Sorted by type name

    // METHODS - FORMATTING
    static string pctStr(uint64_t covered, uint64_t total) {
        std::ostringstream oss;
        const double pct = (total == 0) ? 100.0 : (100.0 * covered / total);
        oss << std::fixed << std::setprecision(2) << pct;
        return oss.str();
    }

public:
    // CONSTRUCTORS
    VlcCovergroups() = default;
    ~VlcCovergroups() = default;

    // METHODS
    bool empty() const { return m_cgMap.empty(); }
    VlcCovergroupType& findNewCovergroupType(const string& typeName, const string& filename,
                                             int lineno) {
        const auto it = m_cgMap.find(typeName);
        if (it != m_cgMap.end()) return it->second;
        return m_cgMap.emplace(typeName, VlcCovergroupType{typeName, filename, lineno})
            .first->second;
    }
    void dump(std::ostream& os) const {
        uint64_t grandTotal = 0, grandCovered = 0, grandIgnored = 0, grandIllegal = 0;
        for (const auto& cgPair : m_cgMap) {
            const VlcCovergroupType& cg = cgPair.second;
            grandTotal += cg.normalTotal();
            grandCovered += cg.normalCovered();
            for (const auto& cp : cg.coverpoints()) {
                for (const auto& bin : cp.bins()) {
                    if (bin.binType() == "ignore")
                        ++grandIgnored;
                    else if (bin.binType() == "illegal")
                        ++grandIllegal;
                }
            }
        }

        const string divider(78, '-');

        os << "COVERGROUP COVERAGE REPORT\n";
        os << "==========================\n";
        os << "\n";
        os << "TOTAL: " << grandCovered << "/" << grandTotal << " bins covered ("
           << pctStr(grandCovered, grandTotal) << "%)\n";
        if (grandIgnored || grandIllegal)
            os << "       (" << grandIgnored << " ignored, " << grandIllegal << " illegal)\n";

        for (const auto& cgPair : m_cgMap) {
            const VlcCovergroupType& cg = cgPair.second;
            const uint64_t cgTotal = cg.normalTotal();
            const uint64_t cgCovered = cg.normalCovered();

            os << "\n" << divider << "\n";
            os << "Covergroup Type: " << cg.typeName() << "  [" << cg.filename() << ":"
               << cg.lineno() << "]\n";
            os << "  Type Coverage: " << cgCovered << "/" << cgTotal << " bins ("
               << pctStr(cgCovered, cgTotal) << "%)\n";

            for (const auto& cp : cg.coverpoints()) {
                os << "\n";
                os << "  " << (cp.isCross() ? "Cross" : "Coverpoint") << ": " << cp.name() << "\n";
                os << "    Coverage: " << cp.normalCovered() << "/" << cp.normalTotal()
                   << " bins (" << pctStr(cp.normalCovered(), cp.normalTotal()) << "%)\n";
                os << "    Bins:\n";

                size_t maxNameLen = 0;
                for (const auto& bin : cp.bins())
                    if (bin.name().size() > maxNameLen) maxNameLen = bin.name().size();

                for (const auto& bin : cp.bins()) {
                    const char* status;
                    if (bin.binType() == "ignore")
                        status = "IGNORE ";
                    else if (bin.binType() == "illegal")
                        status = "ILLEGAL";
                    else if (bin.covered())
                        status = "COVERED";
                    else
                        status = "ZERO   ";
                    os << "      " << status << "  " << std::left
                       << std::setw(static_cast<int>(maxNameLen)) << bin.name() << std::right
                       << "  " << bin.count() << " hits\n";
                }
            }
        }
        os << "\n" << divider << "\n";
    }
};

//######################################################################

#endif  // guard
