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

// Specifies the naming scheme for a range of bins, allowing the
// specific name to be computed on-demand.
// All name strings are borrowed literals from the generated code.
class VlCovNamer final {
    // MEMBERS
    VlCovBinKind m_set;  // which set the bins belong to
    int m_count;  // bins this namer covers (1 for Single)
    int m_base;  // first bin index (declaration order), assigned on append
    VlCovBinNaming m_naming;  // how bin names are built
    const char* m_name;  // bin name (Single) or array base name (Array)
    const char* m_file;  // declaration file
    int m_line;  // declaration line
    int m_col;  // declaration column

public:
    // CONSTRUCTORS
    VlCovNamer(VlCovBinKind set, int count, int base, VlCovBinNaming naming, const char* name,
               const char* file, int line, int col)
        : m_set{set}
        , m_count{count}
        , m_base{base}
        , m_naming{naming}
        , m_name{name}
        , m_file{file}
        , m_line{line}
        , m_col{col} {}

    // METHODS
    VlCovBinKind set() const { return m_set; }
    int count() const { return m_count; }
    int base() const { return m_base; }
    VlCovBinNaming naming() const { return m_naming; }
    const char* name() const { return m_name; }
    const char* file() const { return m_file; }
    int line() const { return m_line; }
    int col() const { return m_col; }
};

//=============================================================================
// VlCoverpoint
/// Per-instance coverpoint runtime.  Bins are stored in declaration order; a
/// bin's set/name come from the owning namer.  coverage() is computed on demand
/// by scanning bin counts, keeping the sample() hot path a plain counter bump.

// Base coverpoint runtime (read side + collection logic, no hit-list storage).
// VlCoverpointT<MaxHits> adds the inline hit-list array and the incrementBin write
// path; the cross holds VlCoverpoint* and reads via hitCount()/hitList().
class VlCoverpoint VL_NOT_FINAL : public VlCoverpointIf {
protected:
    // MEMBERS (protected so VlCoverpointT::incrementBin can update them)
    std::string m_hier;  // "covergroup.coverpoint"
    uint32_t m_atLeast = 1;  // option.at_least (coverpoint-wide)
    int m_total = 0;  // bins across all sets
    int m_normal = 0;  // Normal bins (coverage denominator)
    int m_nextBase = 0;  // running append cursor
    int m_nextCrossIdx = 0;  // running cross-index cursor (Normal bins only)
    std::vector<uint32_t> m_counts;  // [m_total], one per bin
    std::vector<VlCovNamer> m_namers;  // appended in declaration order
    std::vector<int> m_crossIdx;  // [m_total] full bin idx -> cross idx (Normal-only), -1 otherwise
    int m_hitCount = 0;  // entries valid in the hit list this sample

private:
    // PRIVATE METHODS
    const VlCovNamer& namerFor(int i) const;  // obtain the bin-specific name producer
    void addNamer(VlCovBinKind set, int count, VlCovBinNaming naming, const char* name,
                  const char* file, int line, int col);

public:
    // CONSTRUCTORS
    VlCoverpoint() = default;

    // METHODS
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
    // Clear the hit list at the start of each sample() for a cross-fed coverpoint.
    void clearHitList() { m_hitCount = 0; }
    // Ignore/Illegal/Default: count only; never propagates to cross coverage.
    void recordHit(int i) { ++m_counts[i]; }
    // incrementBin (Normal bin: count + hit-list append) lives in VlCoverpointT<MaxHits>,
    // where MaxHits is the gen-time max per-sample bin overlap.

    // ---- cross support (read by VlCoverCross) ----
    int hitCount() const { return m_hitCount; }
    virtual const int* hitList() const = 0;  // provided by VlCoverpointT
    int normalBinCount() const { return m_normal; }  // cross dimension size (Normal bins)
    std::string normalBinName(int crossIdx) const;  // name of the crossIdx-th Normal bin

    // ---- VlCoverpointIf ----
    int binCount() const override { return m_total; }
    std::string binName(int i) const override;
    // Deliberately not on VlCoverpointIf: only registerBins() needs it, via the
    // concrete coverpoint.  A cross has all-Normal bins and exposes no kind, so the
    // interface omits it; add it back only if a writer needs it polymorphically.
    VlCovBinKind binKind(int i) const { return namerFor(i).set(); }
    void coverageParts(double& covered, double& total) const override {
        // Count Normal bins that reached option.at_least on demand, so the hot
        // path (incrementBin) stays a plain counter bump.
        int numCovered = 0;
        for (const VlCovNamer& nm : m_namers) {
            if (nm.set() != VlCovBinKind::KIND_NORMAL) continue;
            for (int i = nm.base(); i < nm.base() + nm.count(); ++i) {
                if (m_counts[i] >= m_atLeast) ++numCovered;
            }
        }
        covered = numCovered;
        total = m_normal;
    }
};

//=============================================================================
// VlCoverpointT
/// Concrete coverpoint with an inline hit-list array sized to MaxHits -- the
/// gen-time maximum number of Normal bins one sample value can match (1 for the
/// common non-overlapping case).  The bound is a compile-time constant, so for
/// MaxHits == 1 incrementBin collapses to a single store.  Generated code holds
/// the coverpoint as VlCoverpointT<K> and calls incrementBin via the concrete
/// type; the cross reads it polymorphically through VlCoverpoint*.

template <int MaxHits>
class VlCoverpointT final : public VlCoverpoint {
    // MEMBERS
    int m_hits[MaxHits];  // cross indices of Normal bins hit this sample

public:
    // CONSTRUCTORS
    VlCoverpointT() = default;

    // METHODS
    // Normal bin: bump count and append the bin's cross index to the hit list.
    // m_hitCount can never exceed MaxHits (the gen-time overlap bound), so no hit
    // is ever dropped; the bound check is a compile-time-folded safety net.
    void incrementBin(int i) {
        ++m_counts[i];
        const int cx = m_crossIdx[i];
        if (cx >= 0 && m_hitCount < MaxHits) m_hits[m_hitCount++] = cx;
    }
    const int* hitList() const override { return m_hits; }
};

//=============================================================================
// VlCoverCross
/// Per-instance auto cross runtime.  Holds flat uint32_t[] storage over the
/// Cartesian product of the feeding coverpoints' Normal bins.  Each sample()
/// walks the coverpoint hit lists (O(hits), not O(product)).  Bin names are
/// built on demand from the coverpoints, so no per-bin name is stored.

class VlCoverCross final : public VlCoverpointIf {
    // MEMBERS
    std::string m_hier;  // "covergroup.cross"
    const char* m_file = nullptr;  // cross declaration file (registration metadata)
    int m_line = 0;  // cross declaration line
    int m_col = 0;  // cross declaration column
    int m_dims = 0;  // number of feeding coverpoints
    int64_t m_numAutoBins = 0;  // product of per-dim Normal bin counts
    int m_numCovered = 0;  // distinct bins hit >= 1 (maintained incrementally)
    std::vector<int> m_cpBinCounts;  // [m_dims] Normal bin count per dimension
    std::vector<int64_t> m_stride;  // [m_dims] flat-index stride per dimension
    std::vector<uint32_t> m_flatCounts;  // [m_numAutoBins] per-bin hit counts
    std::vector<VlCoverpoint*> m_cps;  // feeding coverpoints (the only name source)

    // PRIVATE METHODS
    void iterateProduct(VlCoverpoint* const* cps, int dim, int64_t baseIdx);
    void incrementTuple(int64_t idx) {
        if (m_flatCounts[idx]++ == 0) ++m_numCovered;
    }

public:
    // CONSTRUCTORS
    VlCoverCross() = default;

    // METHODS
    // ---- configuration (from generated constructor, after coverpoints init'd) ----
    void init(const char* hier, int dims, VlCoverpoint* const* cps, const char* file, int line,
              int col);
    void registerBins(VerilatedCovContext* covcontextp, const char* page);

    // ---- hot path (from generated sample(), after all coverpoints sampled) ----
    void sample(VlCoverpoint* const* cps);

    // ---- VlCoverpointIf ----
    // A cross is a coverpoint whose bins are the auto cross bins (all Normal).
    int binCount() const override { return static_cast<int>(m_numAutoBins); }
    std::string binName(int flat) const override;
    void coverageParts(double& covered, double& total) const override {
        covered = m_numCovered;
        total = static_cast<double>(m_numAutoBins);
    }
};

#endif  // Guard
