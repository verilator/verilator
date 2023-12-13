// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: verilator_coverage: Source file to annotate with line coverage
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2023 by Wilson Snyder. This program is free software; you
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

#include <map>
#include <set>
#include <utility>
#include <vector>

class VlcPoint;

//********************************************************************
// VlcColumnCount - count at specific source file, line and column

class VlcSourceCount final {
private:
    // TYPES
    using PointsSet = std::set<const VlcPoint*>;

    // MEMBERS
    int m_lineno;  ///< Line number
    uint64_t m_count = 0;  ///< Count
    bool m_ok = false;  ///< Coverage is above threshold
    PointsSet m_points;  // Points on this line

public:
    // CONSTRUCTORS
    explicit VlcSourceCount(int lineno)
        : m_lineno{lineno} {}
    ~VlcSourceCount() = default;

    // ACCESSORS
    int lineno() const { return m_lineno; }
    uint64_t count() const { return m_count; }
    bool ok() const { return m_ok; }

    // METHODS
    void incCount(uint64_t count, bool ok) {
        if (!m_count) {
            m_count = count;
            m_ok = ok;
        } else {
            m_count = std::min(m_count, count);
            if (!ok) m_ok = false;
        }
    }
    void insertPoint(const VlcPoint* pointp) { m_points.emplace(pointp); }
    PointsSet& points() { return m_points; }
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
    void needed(bool flag) { m_needed = flag; }
    bool needed() const { return m_needed; }
    LinenoMap& lines() { return m_lines; }

    // METHODS
    void lineIncCount(int lineno, uint64_t count, bool ok, const VlcPoint* pointp) {
        auto lit = m_lines.find(lineno);
        if (lit == m_lines.end()) lit = m_lines.emplace(lineno, VlcSourceCount{lineno}).first;
        VlcSourceCount& sc = lit->second;
        sc.incCount(count, ok);
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
