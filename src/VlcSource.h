// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: verilator_coverage: Source file to annotate with line coverage
//
// Code available from: http://www.veripool.org/verilator
//
//*************************************************************************
//
// Copyright 2003-2015 by Wilson Snyder.  This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
//
// Verilator is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
//*************************************************************************

#ifndef _VLCSOURCE_H_
#define _VLCSOURCE_H_ 1

#include "config_build.h"
#include "verilatedos.h"
#include <map>
#include <vector>

//********************************************************************
// VlcColumnCount - count at specific source file, line and column

class VlcSourceCount {
private:
    // MEMBERS
    int		m_lineno;	///< Line number
    int		m_column;	///< Column number
    vluint64_t	m_count;	///< Count
    bool	m_ok;		///< Coverage is above threshold

public:
    // CONSTRUCTORS
    VlcSourceCount(int lineno, int column) {
	m_lineno = lineno;
	m_column = column;
	m_count = 0;
	m_ok = false;
    }
    ~VlcSourceCount() {}

    // ACCESSORS
    int lineno() const { return m_lineno; }
    int column() const { return m_column; }
    vluint64_t count() const { return m_count; }
    bool ok() const { return m_ok; }

    // METHODS
    void incCount(vluint64_t count, bool ok) {
	m_count += count;
	if (ok) m_ok = true;
    }
};

//********************************************************************
// VlcSource - source file to annotate

class VlcSource {
public:
    // TYPES
    typedef map<int,VlcSourceCount> ColumnMap;	// Map of {column}
    typedef map<int,ColumnMap> LinenoMap;	// Map of {lineno}{column}

private:
    // MEMBERS
    string	m_name;		//< Name of the source file
    bool	m_needed;	//< Need to annotate; has low coverage
    LinenoMap	m_lines;	//< Map of each annotated line

public:
    // CONSTRUCTORS
    VlcSource(const string& name) {
	m_name = name;
	m_needed = false;
    }
    ~VlcSource() {}

    // ACCESSORS
    const string& name() const { return m_name; }
    void needed(bool flag) { m_needed = flag; }
    bool needed() const { return m_needed; }
    LinenoMap& lines() { return m_lines; }

    // METHODS
    void incCount(int lineno, int column, vluint64_t count, bool ok) {
	LinenoMap::iterator lit = m_lines.find(lineno);
	if (lit == m_lines.end()) {
	    lit = m_lines.insert(make_pair(lineno,ColumnMap())).first;
	}
	ColumnMap& cmap = lit->second;
	ColumnMap::iterator cit = cmap.find(column);
	if (cit == cmap.end()) {
	    cit = cmap.insert(make_pair(column,VlcSourceCount(lineno, column))).first;
	}
	VlcSourceCount& sc = cit->second;
	sc.incCount(count,ok);
    }
};

//********************************************************************
// VlcSources - Container of all source files

class VlcSources {
public:
    // TYPES
    typedef map<string,VlcSource> NameMap;
private:
    // MEMBERS
    NameMap	m_sources;	//< List of all sources

public:
    // ITERATORS
    typedef NameMap::iterator iterator;
    NameMap::iterator begin() { return m_sources.begin(); }
    NameMap::iterator end() { return m_sources.end(); }

public:
    // CONSTRUCTORS
    VlcSources() {}
    ~VlcSources() {}

    // METHODS
    VlcSource& findNewSource(const string& name) {
	NameMap::iterator iter = m_sources.find(name);
	if (iter != m_sources.end()) {
	    return iter->second;
	}
	else {
	    iter = m_sources.insert(make_pair(name, VlcSource(name))).first;
	    return iter->second;
	}
    }
};

//######################################################################

#endif // Guard
