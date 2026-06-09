// -*- mode: C++; c-file-style: "cc-mode" -*-
//=============================================================================
//
// Code available from: https://verilator.org
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2024-2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//=============================================================================
///
/// \file
/// \brief Verilated functional-coverage model interfaces
///
/// Defines interface classes to runtime covergroup coverage-collection classes.
/// These are used to query coverage achievement at runtime, and (future)
/// when writing coverage to the coverage database.
///
//=============================================================================

#ifndef VERILATOR_VERILATED_COV_MODEL_H_
#define VERILATOR_VERILATED_COV_MODEL_H_

#include "verilatedos.h"

#include <cstdint>
#include <string>

// Per-bin classification.  A bin's kind is which set it lives in (structural),
// not a per-bin field.  Only Normal feeds coverage(); the rest are recorded.
enum class VlCovBinKind : uint8_t {
    NORMAL = 0,  // Base coverage-collecting bin
    DEFAULT = 1,  // Bin declared with 'default' range (which is excluded per LRM)
    IGNORE = 2,  // Ignore bin
    ILLEGAL = 3  // Illegal bin
};

//=============================================================================
// VlCoverpointIf
/// Read-side view of a coverpoint.  The writer queries bins by index; the
/// implementor computes names/kinds on demand.  Bounded bin count, so random
/// access by index is the primary usage.

class VlCoverpointIf VL_NOT_FINAL {
public:
    // CONSTRUCTORS
    virtual ~VlCoverpointIf() = default;

    // METHODS
    // All bins, across every set; index range [0, binCount())
    virtual int binCount() const = 0;
    // Bin name in declaration order (e.g. "myBin" or "b[3]")
    virtual std::string binName(int i) const = 0;
    virtual VlCovBinKind binKind(int i) const = 0;
    // Bins covered / effective total (Normal set only) for the coverage calc
    virtual void coverageParts(double& covered, double& total) const = 0;
};

#endif  // Guard
