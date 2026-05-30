// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Dumpvars helpers
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2003-2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#ifndef VERILATOR_V3DUMPVARS_H_
#define VERILATOR_V3DUMPVARS_H_

#include "config_build.h"
#include "verilatedos.h"

// Tagged $dumpvars target string.  During compile-time resolution in V3LinkDot
// each target is tagged with a prefix that tells EmitC how to emit the
// corresponding runtime code.
struct VDumpVarsTag final {
    const char* const prefix;
    const size_t prefixLen;
    template <size_t N>
    constexpr VDumpVarsTag(const char (&s)[N])
        : prefix{s}
        , prefixLen{N - 1} {}
    bool matches(const string& target) const { return target.compare(0, prefixLen, prefix) == 0; }
    string make(const string& target) const { return string{prefix, prefixLen} + target; }
    string strip(const string& target) const {
        return matches(target) ? target.substr(prefixLen) : target;
    }
};

// Fully resolved to a compile-time hierarchy path
constexpr VDumpVarsTag kDumpvarsResolved{"@dumpvars:"};
// First component must match the C++ wrapper root name at runtime
constexpr VDumpVarsTag kDumpvarsRuntimeRoot{"@dumpvars_root:"};

#endif  // Guard
