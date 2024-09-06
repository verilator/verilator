// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: verilator_coverage: Source file to annotate with line coverage
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

#ifndef VERILATOR_VLCSOURCE_H_
#define VERILATOR_VLCSOURCE_H_

#include "config_build.h"
#include "verilatedos.h"

#include "VlcPoint.h"

#include <limits>
#include <map>
#include <set>
#include <utility>
#include <vector>

class VlcPoint;

//********************************************************************
// VlcColumnCount - count at specific source file, line and column

class VlcSourceCount final {
    // TYPES
    using PointsSet = std::set<const VlcPoint*>;

    // MEMBERS
    const int m_lineno;  ///< Line number
    uint64_t m_maxCount = 0;  ///< Max count
    uint64_t m_minCount = std::numeric_limits<uint64_t>::max();  ///< Min count
    PointsSet m_points;  // Points on this line

public:
    // CONSTRUCTORS
    explicit VlcSourceCount(int lineno)
        : m_lineno{lineno} {}
    ~VlcSourceCount() = default;

    // ACCESSORS
    int lineno() const { return m_lineno; }
    uint64_t maxCount() const { return m_maxCount; }
    uint64_t minCount() const { return m_minCount; }

    // METHODS
    void insertPoint(const VlcPoint* pointp) {
        m_maxCount = std::max(m_maxCount, pointp->count());
        m_minCount = std::min(m_minCount, pointp->count());
        m_points.emplace(pointp);
    }
    const PointsSet& points() { return m_points; }
};

//********************************************************************
// VlcSource - source file to annotate

class VlcSource final {
public:
    // TYPES
    using LinenoMap = std::map<int, VlcSourceCount>;  // Map of {column}

private:
    // MEMBERS
    string m_name;  //< Name of the source file
    LinenoMap m_lines;  //< Map of each annotated line
    bool m_needed = false;  //< Need to annotate; has low coverage

public:
    // CONSTRUCTORS
    explicit VlcSource(const string& name)
        : m_name{name} {}
    ~VlcSource() = default;

    // ACCESSORS
    const string& name() const { return m_name; }
    bool needed() const { return m_needed; }
    void needed(bool flag) { m_needed = flag; }
    LinenoMap& lines() { return m_lines; }

    // METHODS
    void insertPoint(int lineno, const VlcPoint* pointp) {
        VlcSourceCount& sc = m_lines.emplace(lineno, lineno).first->second;
        sc.insertPoint(pointp);
    }
};

//********************************************************************
// VlcSources - Container of all source files

class VlcSources final {
public:
    // TYPES
    using NameMap = std::map<const std::string, VlcSource>;

private:
    // MEMBERS
    NameMap m_sources;  //< List of all sources

public:
    // ITERATORS
    using iterator = NameMap::iterator;
    NameMap::iterator begin() { return m_sources.begin(); }
    NameMap::iterator end() { return m_sources.end(); }

    // CONSTRUCTORS
    VlcSources() = default;
    ~VlcSources() = default;

    // METHODS
    VlcSource& findNewSource(const string& name) {
        NameMap::iterator iter = m_sources.find(name);
        if (iter != m_sources.end()) {
            return iter->second;
        } else {
            iter = m_sources.emplace(name, VlcSource{name}).first;
            return iter->second;
        }
    }
};

//######################################################################

#endif  // Guard
