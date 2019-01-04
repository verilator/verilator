// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// Copyright 2003-2019 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License.
// Version 2.0.
//
// Verilator is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
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
/// Code available from: http://www.veripool.org/verilator
///
//*************************************************************************


#ifndef _VERILATED_SYMS_H_
#define _VERILATED_SYMS_H_ 1  ///< Header Guard

#include "verilatedos.h"
#include "verilated_heavy.h"
#include "verilated_sym_props.h"

#include <map>

//======================================================================
/// Types

/// Class to sort maps keyed by const char*'s
struct VerilatedCStrCmp {
    bool operator() (const char *a, const char *b) const {
        return std::strcmp(a, b) < 0;
    }
};

/// Map of sorted scope names to find associated scope class
class VerilatedScopeNameMap
    : public std::map<const char*, const VerilatedScope*, VerilatedCStrCmp> {
public:
    VerilatedScopeNameMap() {}
    ~VerilatedScopeNameMap() {}
};

/// Map of sorted variable names to find associated variable class
class VerilatedVarNameMap
    : public std::map<const char*, VerilatedVar, VerilatedCStrCmp> {
public:
    VerilatedVarNameMap() {}
    ~VerilatedVarNameMap() {}
};

#endif  // Guard
