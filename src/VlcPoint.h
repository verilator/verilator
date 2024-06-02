// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: verilator_coverage: Coverage points
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

#ifndef VERILATOR_VLCPOINT_H_
#define VERILATOR_VLCPOINT_H_

#include "config_build.h"
#include "verilatedos.h"

#include <iomanip>
#include <map>
#include <unordered_map>
#include <vector>

#ifndef V3ERROR_NO_GLOBAL_
#define V3ERROR_NO_GLOBAL_
#endif
#include "verilated_cov_key.h"

#include "V3Error.h"

//********************************************************************
// VlcPoint - A coverage point (across all tests)

class VlcPoint final {
    // MEMBERS
    string m_name;  //< Name of the point
    uint64_t m_pointNum;  //< Point number
    uint64_t m_testsCovering = 0;  //< Number tests with non-zero coverage of this point
    uint64_t m_count = 0;  //< Count of hits across all tests

public:
    // CONSTRUCTORS
    VlcPoint(const string& name, uint64_t pointNum)
        : m_name{name}
        , m_pointNum{pointNum} {}
    ~VlcPoint() = default;
    // ACCESSORS
    const string& name() const { return m_name; }
    uint64_t pointNum() const { return m_pointNum; }
    uint64_t testsCovering() const { return m_testsCovering; }
    void countInc(uint64_t inc) { m_count += inc; }
    uint64_t count() const { return m_count; }
    void testsCoveringInc() { m_testsCovering++; }
    bool ok(unsigned annotateMin) const {
        const std::string threshStr = thresh();
        unsigned threshi = !threshStr.empty() ? std::atoi(threshStr.c_str()) : annotateMin;
        return m_count >= threshi;
    }
    // KEY ACCESSORS
    string filename() const { return keyExtract(VL_CIK_FILENAME); }
    string comment() const { return keyExtract(VL_CIK_COMMENT); }
    string type() const { return keyExtract(VL_CIK_TYPE); }
    string thresh() const { return keyExtract(VL_CIK_THRESH); }  // string as maybe ""
    string linescov() const { return keyExtract(VL_CIK_LINESCOV); }
    int lineno() const { return std::atoi(keyExtract(VL_CIK_LINENO).c_str()); }
    int column() const { return std::atoi(keyExtract(VL_CIK_COLUMN).c_str()); }
    // METHODS
    string keyExtract(const char* shortKey) const {
        // Hot function
        const size_t shortLen = std::strlen(shortKey);
        const string namestr = name();
        for (const char* cp = namestr.c_str(); *cp; ++cp) {
            if (*cp == '\001') {
                if (0 == std::strncmp(cp + 1, shortKey, shortLen) && cp[shortLen + 1] == '\002') {
                    cp += shortLen + 2;  // Skip \001+short+\002
                    const char* ep = cp;
                    while (*ep && *ep != '\001') ++ep;
                    return string(cp, ep - cp);
                }
            }
        }
        return "";
    }
    static void dumpHeader(std::ostream& os) {
        os << "Points:\n";
        os << "  Num,    TestsCover,    Count,  Name\n";
    }
    void dump(std::ostream& os) const {
        os << "  " << std::setw(8) << std::setfill('0') << pointNum();
        os << ",  " << std::setw(7) << std::setfill(' ') << testsCovering();
        os << ",  " << std::setw(7) << std::setfill(' ') << count();
        os << ",  \"" << name() << "\"\n";
    }
    void dumpAnnotate(std::ostream& os, unsigned annotateMin) const {
        os << (ok(annotateMin) ? "+" : "-");
        os << std::setw(6) << std::setfill('0') << count();
        os << "  point: comment=" << comment();
        os << "\n";
    }
};

//********************************************************************
// VlcPoints - Container of all points

class VlcPoints final {
    // MEMBERS
    using NameMap = std::map<const std::string, uint64_t>;  // Sorted by name (ordered)
    NameMap m_nameMap;  //< Name to point-number
    std::vector<VlcPoint> m_points;  //< List of all points
    uint64_t m_numPoints = 0;  //< Total unique points

    static int debug() { return V3Error::debugDefault(); }

public:
    // ITERATORS
    using ByName = NameMap;
    using iterator = ByName::iterator;
    ByName::iterator begin() { return m_nameMap.begin(); }
    ByName::iterator end() { return m_nameMap.end(); }

    // CONSTRUCTORS
    VlcPoints() = default;
    ~VlcPoints() = default;

    // METHODS
    void dump() {
        UINFO(2, "dumpPoints...\n");
        VlcPoint::dumpHeader(std::cout);
        for (const auto& i : *this) {
            const VlcPoint& point = pointNumber(i.second);
            point.dump(std::cout);
        }
    }
    VlcPoint& pointNumber(uint64_t num) { return m_points[num]; }
    uint64_t findAddPoint(const string& name, uint64_t count) {
        const auto pair = m_nameMap.emplace(name, m_numPoints);
        if (pair.second) m_points.emplace_back(name, m_numPoints++);
        const uint64_t pointnum = pair.first->second;
        m_points[pointnum].countInc(count);
        return pointnum;
    }
};

//######################################################################

#endif  // guard
