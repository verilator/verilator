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
/// \brief Verilated functional-coverage collection runtime
///
/// VlCoverpoint owns per-instance bin-count storage for one coverpoint,
/// computes coverage, builds bin names on demand, and registers bins with the
/// coverage database.  It implements the VlCoverpointIf read interface.
///
/// Generated covergroup code holds one VlCoverpoint per coverpoint, configures
/// it in the constructor (init + add*Namer), increments bins from sample(),
/// and registers via registerBins().
///
//=============================================================================

#ifndef VERILATOR_VERILATED_COVERGROUP_H_
#define VERILATOR_VERILATED_COVERGROUP_H_

#include "verilatedos.h"

#include "verilated_cov_model.h"

#include <cstdint>
#include <string>
#include <vector>

class VerilatedCovContext;

// How a namer builds the names of the bins it covers.
enum class VlCovBinNaming : uint8_t {
    Single,  // "<name>"      one bin
    Array,  // "<name>[i]"   bins b[N] value array
};

// Names a contiguous run of bins; carries the run's own source location.
// All name strings are borrowed literals from the generated code.
struct VlCovNamer final {
    VlCovBinKind set;  // which set the bins belong to
    int count;  // bins this namer covers (1 for Single)
    int base;  // first bin index (declaration order), assigned on append
    VlCovBinNaming naming;
    const char* name;  // bin name (Single) or array base name (Array)
    const char* file;
    int line;
    int col;
};

//=============================================================================
// VlCoverpoint
/// Per-instance coverpoint runtime.  Bins are stored in declaration order; a
/// bin's set/name come from the owning namer.  coverage() is O(1) via the
/// incrementally-maintained covered count.

class VlCoverpoint final : public VlCoverpointIf {
    std::string m_hier;  // "covergroup.coverpoint"
    uint32_t m_atLeast = 1;  // option.at_least (coverpoint-wide)
    int m_total = 0;  // bins across all sets
    int m_normal = 0;  // Normal bins (coverage denominator)
    int m_numCovered = 0;  // Normal bins with count >= m_atLeast
    int m_nextBase = 0;  // running append cursor
    std::vector<uint32_t> m_counts;  // [m_total], one per bin
    std::vector<VlCovNamer> m_namers;  // appended in declaration order

    const VlCovNamer& namerFor(int i) const;  // linear scan (namer count is tiny)
    void addNamer(VlCovBinKind set, int count, VlCovBinNaming naming, const char* name,
                  const char* file, int line, int col);

public:
    VlCoverpoint() = default;

    // ---- configuration (from generated constructor) ----
    void init(const char* hier, uint32_t atLeast, int nBins);
    void addSingleNamer(VlCovBinKind set, const char* name, const char* file, int line, int col) {
        addNamer(set, 1, VlCovBinNaming::Single, name, file, line, col);
    }
    void addArrayNamer(VlCovBinKind set, int count, const char* name, const char* file, int line,
                       int col) {
        addNamer(set, count, VlCovBinNaming::Array, name, file, line, col);
    }
    void registerBins(VerilatedCovContext* covcontextp, const char* page);

    // ---- hot path (from generated sample()) ----
    void incrementBin(int i) {  // Normal bin: maintains covered count
        if (m_counts[i]++ == m_atLeast - 1) ++m_numCovered;
    }
    void recordHit(int i) { ++m_counts[i]; }  // Ignore/Illegal/Default: count only

    // ---- VlCoverpointIf ----
    int binCount() const override { return m_total; }
    const char* binName(int i, std::string& buf) const override;
    VlCovBinKind binKind(int i) const override { return namerFor(i).set; }
    void coverageParts(double& covered, double& total) const override {
        covered = m_numCovered;
        total = m_normal;
    }
};

#endif  // Guard
