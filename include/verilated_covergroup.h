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
/// Collection and coverage queries are always available; only registerBins(),
/// which publishes bin counters to the coverage database, requires VM_COVERAGE.
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
    uint32_t m_count;  // bins this namer covers (1 for Single)
    uint32_t m_base;  // first bin index (declaration order), assigned on append
    VlCovBinNaming m_naming;  // how bin names are built
    const char* m_name;  // bin name (Single) or array base name (Array)
    const char* m_file;  // declaration file
    int m_line;  // declaration line
    int m_col;  // declaration column

public:
    // CONSTRUCTORS
    VlCovNamer(VlCovBinKind set, uint32_t count, uint32_t base, VlCovBinNaming naming,
               const char* name, const char* file, int line, int col)
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
    uint32_t count() const { return m_count; }
    uint32_t base() const { return m_base; }
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
    uint32_t m_total = 0;  // bins across all sets
    uint32_t m_normal = 0;  // Normal bins (coverage denominator)
    uint32_t m_nextBase = 0;  // running append cursor
    std::vector<uint32_t> m_counts;  // [m_total], one per bin
    std::vector<VlCovNamer> m_namers;  // appended in declaration order
    // [m_total] full bin idx -> cross idx (Normal-only), -1 otherwise.  The only
    // signed index here: -1 marks a non-Normal bin, which incrementBin filters on.
    std::vector<int> m_crossIdx;
    // [m_normal] inverse of m_crossIdx: cross idx -> full bin idx, appended in cross-index order
    std::vector<uint32_t> m_crossToBin;
    uint32_t m_hitCount = 0;  // entries valid in the hit list this sample

private:
    // PRIVATE METHODS
    const VlCovNamer& namerFor(uint32_t i) const;  // obtain the bin-specific name producer
    void addNamer(VlCovBinKind set, uint32_t count, VlCovBinNaming naming, const char* name,
                  const char* file, int line, int col);

public:
    // CONSTRUCTORS
    VlCoverpoint() = default;

    // METHODS
    // ---- configuration (from generated constructor) ----
    void init(const char* hier, uint32_t atLeast, uint32_t nBins);
    void addSingleNamer(VlCovBinKind set, const char* name, const char* file, int line, int col) {
        addNamer(set, 1, VlCovBinNaming::Single, name, file, line, col);
    }
    void addArrayNamer(VlCovBinKind set, uint32_t count, const char* name, const char* file,
                       int line, int col) {
        addNamer(set, count, VlCovBinNaming::Array, name, file, line, col);
    }
    void registerBins(VerilatedCovContext* covcontextp, const char* page);

    // ---- hot path (from generated sample()) ----
    // Clear the hit list at the start of each sample() for a cross-fed coverpoint.
    void clearHitList() { m_hitCount = 0; }
    // Ignore/Illegal/Default: count only; never propagates to cross coverage.
    void recordHit(uint32_t i) { ++m_counts[i]; }
    // incrementBin (Normal bin: count + hit-list append) lives in VlCoverpointT<MaxHits>,
    // where MaxHits is the gen-time max per-sample bin overlap.

    // ---- cross support (read by VlCoverCross) ----
    uint32_t hitCount() const { return m_hitCount; }
    virtual const uint32_t* hitList() const = 0;  // provided by VlCoverpointT
    uint32_t normalBinCount() const { return m_normal; }  // cross dimension size (Normal bins)
    std::string normalBinName(uint32_t crossIdx) const;  // name of the crossIdx-th Normal bin

    // ---- VlCoverpointIf ----
    uint32_t binCount() const override { return m_total; }
    std::string binName(uint32_t i) const override;
    // Deliberately not on VlCoverpointIf: only registerBins() needs it, via the
    // concrete coverpoint.  A cross has all-Normal bins and exposes no kind, so the
    // interface omits it; add it back only if a writer needs it polymorphically.
    VlCovBinKind binKind(uint32_t i) const { return namerFor(i).set(); }
    void coverageParts(double& covered, double& total) const override {
        // Count Normal bins that reached option.at_least on demand, so the hot
        // path (incrementBin) stays a plain counter bump.
        uint32_t numCovered = 0;
        for (const VlCovNamer& nm : m_namers) {
            if (nm.set() != VlCovBinKind::KIND_NORMAL) continue;
            for (uint32_t i = nm.base(); i < nm.base() + nm.count(); ++i) {
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

template <uint32_t MaxHits>
class VlCoverpointT final : public VlCoverpoint {
    // MEMBERS
    uint32_t m_hits[MaxHits];  // cross indices of Normal bins hit this sample

public:
    // CONSTRUCTORS
    VlCoverpointT() = default;

    // METHODS
    // Normal bin: bump count and append the bin's cross index to the hit list.
    // m_hitCount can never exceed MaxHits (the gen-time overlap bound), so no hit
    // is ever dropped; the bound check is a compile-time-folded safety net.
    void incrementBin(uint32_t i) {
        ++m_counts[i];
        // m_crossIdx is signed only to carry the -1 "not a Normal bin" marker;
        // the >= 0 test below is what makes every stored hit index unsigned-safe.
        const int cx = m_crossIdx[i];
        if (cx >= 0 && m_hitCount < MaxHits) m_hits[m_hitCount++] = static_cast<uint32_t>(cx);
    }
    const uint32_t* hitList() const override { return m_hits; }
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
    const char* m_file = nullptr;  // Cross declaration file (registration metadata)
    int m_line = 0;  // Cross declaration line
    int m_col = 0;  // Cross declaration column
    uint32_t m_dims = 0;  // Number of feeding coverpoints
    // Cross bin indexes are unsigned, like the coverpoint bin indexes they are
    // built from.  init() fatals if the product would exceed UINT32_MAX, so every
    // index computed here provably fits.  That bound is far beyond anything
    // storable anyway: m_flatCounts alone would need 16GB.
    uint32_t m_numAutoBins = 0;  // Product of per-dim Normal bin counts
    uint32_t m_numCovered = 0;  // Distinct bins hit >= 1 (maintained incrementally)
    std::vector<uint32_t> m_cpBinCounts;  // [m_dims] Normal bin count per dimension
    std::vector<uint32_t> m_stride;  // [m_dims] Flat-index stride per dimension
    std::vector<uint32_t> m_flatCounts;  // [m_numAutoBins] Per-bin hit counts
    std::vector<VlCoverpoint*> m_cps;  // Feeding coverpoints (the only name source)

    // PRIVATE METHODS
    void iterateProduct(VlCoverpoint* const* cps, uint32_t dim, uint32_t baseIdx);
    void incrementTuple(uint32_t idx) {
        if (m_flatCounts[idx]++ == 0) ++m_numCovered;
    }

public:
    // CONSTRUCTORS
    VlCoverCross() = default;

    // METHODS
    // ---- configuration (from generated constructor, after coverpoints init'd) ----
    void init(const char* hier, uint32_t dims, VlCoverpoint* const* cps, const char* file,
              int line, int col);
    void registerBins(VerilatedCovContext* covcontextp, const char* page);

    // ---- hot path (from generated sample(), after all coverpoints sampled) ----
    void sample(VlCoverpoint* const* cps);

    // ---- VlCoverpointIf ----
    // A cross is a coverpoint whose bins are the auto cross bins (all Normal).
    uint32_t binCount() const override { return m_numAutoBins; }
    std::string binName(uint32_t flat) const override;
    void coverageParts(double& covered, double& total) const override {
        covered = m_numCovered;
        total = m_numAutoBins;
    }
};

#endif  // Guard
