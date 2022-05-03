// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: verilator_coverage: Source file to annotate with line coverage
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

#ifndef VERILATOR_VLCSOURCE_H_
#define VERILATOR_VLCSOURCE_H_

#include "config_build.h"
#include "verilatedos.h"

#include <map>
#include <utility>
#include <vector>

//********************************************************************
// VlcColumnCount - count at specific source file, line and column

class VlcSourceCount final {
private:
    // MEMBERS
    int m_lineno;  ///< Line number
    int m_column;  ///< Column number
    uint64_t m_count = 0;  ///< Count
    bool m_ok = false;  ///< Coverage is above threshold

public:
    // CONSTRUCTORS
    VlcSourceCount(int lineno, int column)
        : m_lineno{lineno}
        , m_column{column} {}
    ~VlcSourceCount() = default;

    // ACCESSORS
    int lineno() const { return m_lineno; }
    int column() const { return m_column; }
    uint64_t count() const { return m_count; }
    bool ok() const { return m_ok; }

    // METHODS
    void incCount(uint64_t count, bool ok) {
        m_count += count;
        if (ok) m_ok = true;
    }
};

//********************************************************************
// VlcSource - source file to annotate

class VlcSource final {
public:
    // TYPES
    using ColumnMap = std::map<int, VlcSourceCount>;  // Map of {column}
    using LinenoMap = std::map<int, ColumnMap>;  // Map of {lineno}{column}

private:
    // MEMBERS
    string m_name;  //< Name of the source file
    bool m_needed = false;  //< Need to annotate; has low coverage
    LinenoMap m_lines;  //< Map of each annotated line

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
    void incCount(int lineno, int column, uint64_t count, bool ok) {
        LinenoMap::iterator lit = m_lines.find(lineno);
        if (lit == m_lines.end()) lit = m_lines.insert(std::make_pair(lineno, ColumnMap())).first;
        ColumnMap& cmap = lit->second;
        ColumnMap::iterator cit = cmap.find(column);
        if (cit == cmap.end()) {
            cit = cmap.insert(std::make_pair(column, VlcSourceCount(lineno, column))).first;
        }
        VlcSourceCount& sc = cit->second;
        sc.incCount(count, ok);
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
            iter = m_sources.insert(std::make_pair(name, VlcSource(name))).first;
            return iter->second;
        }
    }
};

//######################################################################

#endif  // Guard
