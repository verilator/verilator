// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Link modules/signals together
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2026 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#ifndef VERILATOR_V3LIBMAP_H_
#define VERILATOR_V3LIBMAP_H_

#include "config_build.h"
#include "verilatedos.h"

#include <vector>

class AstNetlist;
class VInFilter;
class V3ParseSym;

//============================================================================

// State to pass between config parsing and cell linking visitors.
class LibMapping final {
    const string m_pattern;  // Pattern to match
    const string m_libname;  // Library name
    const string m_base;  // Relative path of the libmap file

public:
    LibMapping(const string& pattern_, const string& libname_, const string& base_)
        : m_pattern{pattern_}
        , m_libname{libname_}
        , m_base{base_} {}
    string pattern() const { return m_pattern; }
    string libname() const { return m_libname; }
    string base() const { return m_base; }
};

class V3LibMap final {
private:
    // STATE
    // 33.3.1.1 File path resolution
    //   If a file name potentially matches multiple file path specifications, the path
    //   specifications shall be resolved in the following order: a) File path specifications that
    //   end with an explicit file name b) File path specifications that end with a wildcarded file
    //   name c) File path specifications that end with a directory name
    std::vector<LibMapping> m_explicitMappings;
    std::vector<LibMapping> m_wildcardMappings;
    std::vector<LibMapping> m_directoryMappings;

    // METHODS
public:
    string matchMapping(const string& filename);
    void addPattern(const string& pattern, const string& libname, const string& base);

    static void map(AstNetlist* nodep) VL_MT_DISABLED;
};

#endif  // Guard
