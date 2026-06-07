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
/// Read-side reflection seam: abstract interfaces a coverage writer queries,
/// implemented by the collection runtime (VlCoverpoint, and later VlCoverCross
/// and the covergroup type/instance nodes).  Carries no implementation and
/// depends on nothing in verilated_cov.h, so a writer or a second back-end can
/// compile against it independently.
///
/// Step 1 declares only the slice the runtime implements today; it grows a
/// slice per phase as consumers (writer, cross) arrive.
///
//=============================================================================

#ifndef VERILATOR_VERILATED_COV_MODEL_H_
#define VERILATOR_VERILATED_COV_MODEL_H_

#include "verilatedos.h"

#include <cstdint>
#include <string>

// Per-bin classification.  A bin's kind is which set it lives in (structural),
// not a per-bin field.  Only Normal feeds coverage(); the rest are recorded.
enum class VlCovBinKind : uint8_t { Normal = 0, Default = 1, Ignore = 2, Illegal = 3 };

//=============================================================================
// VlCoverpointIf
/// Read-side view of a coverpoint.  The writer queries bins by index; the
/// implementor computes names/kinds on demand.  Bounded bin count, so random
/// access by index is the primary API.

class VlCoverpointIf VL_NOT_FINAL {
public:
    virtual ~VlCoverpointIf() = default;
    // All bins, across every set; index range [0, binCount())
    virtual int binCount() const = 0;
    // Bin name, computed into the caller's reusable buffer (no per-bin alloc after
    // warmup); returns buf.c_str()
    virtual const char* binName(int i, std::string& buf) const = 0;
    virtual VlCovBinKind binKind(int i) const = 0;
    // Bins covered / effective total (Normal set only) for the coverage calc
    virtual void coverageParts(double& covered, double& total) const = 0;
};

#endif  // Guard
