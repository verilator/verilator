// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// Copyright 2003-2021 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
///
/// \file
/// \brief Verilator: Include to allow symbol inspection
///
///     This file is for inclusion by files that need to inspect the symbol
///     table.  It is not included in verilated.h (instead see
///     verilated_sym_props.h) as it requires some heavyweight C++ classes.
///
///     These classes are thread safe and read only. It is constructed only
///     when a model is built (from the main thread).
///
/// Code available from: https://verilator.org
///
//*************************************************************************

#ifndef VERILATOR_VERILATED_SYMS_H_
#define VERILATOR_VERILATED_SYMS_H_  ///< Header Guard

#include "verilatedos.h"
#include "verilated_heavy.h"
#include "verilated_sym_props.h"

#include <map>
#include <unordered_map>
#include <vector>

//======================================================================
/// Types

/// Class to sort maps keyed by const char*'s
struct VerilatedCStrCmp {
    bool operator()(const char* a, const char* b) const { return std::strcmp(a, b) < 0; }
};

/// Map of sorted scope names to find associated scope class
// This is a class instead of typedef/using to allow forward declaration in verilated.h
class VerilatedScopeNameMap final
    : public std::map<const char*, const VerilatedScope*, VerilatedCStrCmp> {
public:
    VerilatedScopeNameMap() = default;
    ~VerilatedScopeNameMap() = default;
};

/// Map of sorted variable names to find associated variable class
// This is a class instead of typedef/using to allow forward declaration in verilated.h
class VerilatedVarNameMap final : public std::map<const char*, VerilatedVar, VerilatedCStrCmp> {
public:
    VerilatedVarNameMap() = default;
    ~VerilatedVarNameMap() = default;
};

/// Map of parent scope to vector of children scopes
// This is a class instead of typedef/using to allow forward declaration in verilated.h
class VerilatedHierarchyMap final
    : public std::unordered_map<const VerilatedScope*, std::vector<const VerilatedScope*>> {
public:
    VerilatedHierarchyMap() = default;
    ~VerilatedHierarchyMap() = default;
};

#endif  // Guard
