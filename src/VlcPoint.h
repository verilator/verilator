// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: verilator_coverage: Coverage points
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2022 by Wilson Snyder. This program is free software; you
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

#define V3ERROR_NO_GLOBAL_
#include "verilated_cov_key.h"

#include "V3Error.h"

//********************************************************************
// VlcPoint - A coverage point (across all tests)

class VlcPoint final {
private:
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
    static void dumpHeader() {
        cout << "Points:\n";
        cout << "  Num,    TestsCover,    Count,  Name\n";
    }
    void dump() const {
        cout << "  " << std::setw(8) << std::setfill('0') << pointNum();
        cout << ",  " << std::setw(7) << std::setfill(' ') << testsCovering();
        cout << ",  " << std::setw(7) << std::setfill(' ') << count();
        cout << ",  \"" << name() << "\"\n";
    }
};

//********************************************************************
// VlcPoints - Container of all points

class VlcPoints final {
private:
    // MEMBERS
    using NameMap = std::map<const std::string, uint64_t>;  // Sorted by name (ordered)
    NameMap m_nameMap;  //< Name to point-number
    std::vector<VlcPoint> m_points;  //< List of all points
    uint64_t m_numPoints = 0;  //< Total unique points

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
        VlcPoint::dumpHeader();
        for (const auto& i : *this) {
            const VlcPoint& point = pointNumber(i.second);
            point.dump();
        }
    }
    VlcPoint& pointNumber(uint64_t num) { return m_points[num]; }
    uint64_t findAddPoint(const string& name, uint64_t count) {
        uint64_t pointnum;
        const auto iter = m_nameMap.find(name);
        if (iter != m_nameMap.end()) {
            pointnum = iter->second;
            m_points[pointnum].countInc(count);
        } else {
            pointnum = m_numPoints++;
            VlcPoint point{name, pointnum};
            point.countInc(count);
            m_points.push_back(point);
            m_nameMap.emplace(point.name(), point.pointNum());
        }
        return pointnum;
    }
};

//######################################################################

#endif  // guard
