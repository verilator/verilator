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
// corresponding runtime code.  The three tag types are:
//   Resolved    – fully resolved to a compile-time hierarchy path
//   RuntimeRoot – first component must match the C++ wrapper root name at runtime
//   Missing     – proven invalid at compile time; emit VL_FATAL_MT at runtime
struct DumpvarsTag final {
    const char* const prefix;
    const size_t prefixLen;
    template <size_t N>
    constexpr DumpvarsTag(const char (&s)[N])
        : prefix{s}
        , prefixLen{N - 1} {}
    bool matches(const string& target) const { return target.compare(0, prefixLen, prefix) == 0; }
    string make(const string& target) const { return string{prefix, prefixLen} + target; }
    string strip(const string& target) const {
        return matches(target) ? target.substr(prefixLen) : target;
    }
};

constexpr DumpvarsTag kDumpvarsResolved{"@dumpvars:"};
constexpr DumpvarsTag kDumpvarsRuntimeRoot{"@dumpvars_root:"};
constexpr DumpvarsTag kDumpvarsMissing{"@dumpvars_missing:"};

#endif  // Guard
