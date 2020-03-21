// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: verilator_coverage: Coverage points
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2020 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#ifndef _VLCPOINT_H_
#define _VLCPOINT_H_ 1

#include "config_build.h"
#include "verilatedos.h"

#include "verilated_cov_key.h"

#include <vector>
#include <iomanip>
#include VL_INCLUDE_UNORDERED_MAP

//********************************************************************
// VlcPoint - A coverage point (across all tests)

class VlcPoint {
private:
    // MEMBERS
    string m_name;  //< Name of the point
    vluint64_t m_pointNum;  //< Point number
    vluint64_t m_testsCovering;  //< Number tests with non-zero coverage of this point
    vluint64_t m_count;  //< Count of hits across all tests

public:
    // CONSTRUCTORS
    VlcPoint(const string& name, int pointNum) {
        m_name = name;
        m_pointNum = pointNum;
        m_testsCovering = 0;
        m_count = 0;
    }
    ~VlcPoint() {}
    // ACCESSORS
    const string& name() const { return m_name; }
    vluint64_t pointNum() const { return m_pointNum; }
    vluint64_t testsCovering() const { return m_testsCovering; }
    void countInc(vluint64_t inc) { m_count += inc; }
    vluint64_t count() const { return m_count; }
    void testsCoveringInc() { m_testsCovering++; }
    // KEY ACCESSORS
    string filename() const { return keyExtract(VL_CIK_FILENAME); }
    string comment() const { return keyExtract(VL_CIK_COMMENT); }
    string type() const { return keyExtract(VL_CIK_TYPE); }
    string thresh() const { return keyExtract(VL_CIK_THRESH); }  // string as maybe ""
    int lineno() const { return atoi(keyExtract(VL_CIK_LINENO).c_str()); }
    int column() const { return atoi(keyExtract(VL_CIK_COLUMN).c_str()); }
    // METHODS
    string keyExtract(const char* shortKey) const {
        // Hot function
        size_t shortLen = strlen(shortKey);
        const string namestr = name();
        for (const char* cp = namestr.c_str(); *cp; ++cp) {
            if (*cp == '\001') {
                if (0 == strncmp(cp + 1, shortKey, shortLen)
                    && cp[shortLen + 1] == '\002') {
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
        cout << "  Num,    TestsCover,    Count,  Name" << endl;
    }
    void dump() const {
        cout << "  " << std::setw(8) << std::setfill('0') << pointNum();
        cout << ",  " << std::setw(7) << std::setfill(' ') << testsCovering();
        cout << ",  " << std::setw(7) << std::setfill(' ') << count();
        cout << ",  \"" << name() << "\"" << endl;
    }
};

//********************************************************************
// VlcPoints - Container of all points

class VlcPoints {
private:
    // MEMBERS
    typedef std::map<string, vluint64_t> NameMap;  // Sorted by name (ordered)
    NameMap m_nameMap;  //< Name to point-number
    std::vector<VlcPoint> m_points;  //< List of all points
    vluint64_t m_numPoints;  //< Total unique points

public:
    // ITERATORS
    typedef NameMap ByName;
    typedef ByName::iterator iterator;
    ByName::iterator begin() { return m_nameMap.begin(); }
    ByName::iterator end() { return m_nameMap.end(); }

public:
    // CONSTRUCTORS
    VlcPoints() : m_numPoints(0) {}
    ~VlcPoints() {}

    // METHODS
    void dump() {
        UINFO(2, "dumpPoints...\n");
        VlcPoint::dumpHeader();
        for (VlcPoints::ByName::const_iterator it = begin(); it != end(); ++it) {
            const VlcPoint& point = pointNumber(it->second);
            point.dump();
        }
    }
    VlcPoint& pointNumber(vluint64_t num) { return m_points[num]; }
    vluint64_t findAddPoint(const string& name, vluint64_t count) {
        vluint64_t pointnum;
        NameMap::const_iterator iter = m_nameMap.find(name);
        if (iter != m_nameMap.end()) {
            pointnum = iter->second;
            m_points[pointnum].countInc(count);
        } else {
            pointnum = m_numPoints++;
            VlcPoint point(name, pointnum);
            point.countInc(count);
            m_points.push_back(point);
            m_nameMap.insert(make_pair(point.name(), point.pointNum()));
        }
        return pointnum;
    }
};

//######################################################################

#endif  // guard
