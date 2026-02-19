// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// Code available from: https://verilator.org
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2001-2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
///
/// \file
/// \brief Verilated covergroup runtime support header
///
/// This file is included automatically by Verilator in some of the C++ files
/// it generates if covergroup features are used.
///
/// This file is not part of the Verilated public-facing API.
/// It is only for internal use.
///
//*************************************************************************
#ifndef VERILATOR_VERILATED_COVERGROUP_H_
#define VERILATOR_VERILATED_COVERGROUP_H_

#include "verilated.h"

#include <algorithm>
#include <cstdint>
#include <set>
#include <string>
#include <vector>

//=============================================================================
// VlCovBinRange - A single value range [low:high] for a coverage bin

struct VlCovBinRange final {
    uint64_t m_low;
    uint64_t m_high;
    VlCovBinRange(uint64_t low, uint64_t high)
        : m_low{low}
        , m_high{high} {}
    VlCovBinRange(uint64_t val)  // Implicit: single value
        : m_low{val}
        , m_high{val} {}
    bool contains(uint64_t val) const { return val >= m_low && val <= m_high; }
    uint64_t span() const { return m_high - m_low + 1; }
};

//=============================================================================
// VlCovBinKind - Bin classification

enum class VlCovBinKind : uint8_t {
    BINS = 0,
    ILLEGAL_BINS = 1,
    IGNORE_BINS = 2
};

//=============================================================================
// VlCovBinDef - Definition of a single named bin (may expand to multiple bins)

class VlCovBinDef final {
    std::string m_name;
    std::vector<VlCovBinRange> m_ranges;
    VlCovBinKind m_kind = VlCovBinKind::BINS;
    bool m_isArray = false;
    uint32_t m_arraySize = 0;
    bool m_isDefault = false;

    // Expanded state (after finalize)
    uint32_t m_baseBinIdx = 0;
    uint32_t m_nExpandedBins = 0;

public:
    VlCovBinDef(const std::string& name, VlCovBinKind kind)
        : m_name{name}
        , m_kind{kind} {}

    // Setup
    void addRange(uint64_t low, uint64_t high) { m_ranges.emplace_back(low, high); }
    void addRange(uint64_t val) { m_ranges.emplace_back(val); }
    void setArray(bool isArray, uint32_t size = 0) {
        m_isArray = isArray;
        m_arraySize = size;
    }
    void setDefault(bool isDefault) { m_isDefault = isDefault; }

    // Accessors
    const std::string& name() const { return m_name; }
    VlCovBinKind kind() const { return m_kind; }
    bool isArray() const { return m_isArray; }
    bool isDefault() const { return m_isDefault; }

    // Finalize: expand array bins, compute bin count
    uint32_t finalize(uint32_t baseBinIdx) {
        m_baseBinIdx = baseBinIdx;
        if (m_isDefault) {
            m_nExpandedBins = 1;
        } else if (m_isArray) {
            uint64_t totalValues = 0;
            for (const auto& r : m_ranges) totalValues += r.span();
            if (m_arraySize > 0 && m_arraySize < totalValues) {
                m_nExpandedBins = m_arraySize;
            } else {
                m_nExpandedBins = static_cast<uint32_t>(totalValues);
            }
        } else {
            m_nExpandedBins = 1;
        }
        return m_nExpandedBins;
    }

    uint32_t baseBinIdx() const { return m_baseBinIdx; }
    uint32_t nExpandedBins() const { return m_nExpandedBins; }

    // Sample: return local bin index, or -1 if no match
    int32_t sample(uint64_t value) const {
        if (m_isDefault) return 0;

        if (m_isArray) {
            uint32_t idx = 0;
            for (const auto& r : m_ranges) {
                if (value >= r.m_low && value <= r.m_high) {
                    uint32_t offset = static_cast<uint32_t>(value - r.m_low);
                    uint32_t localIdx = idx + offset;
                    if (m_arraySize > 0 && localIdx >= m_arraySize) return -1;
                    return static_cast<int32_t>(localIdx);
                }
                idx += static_cast<uint32_t>(r.span());
            }
            return -1;
        } else {
            for (const auto& r : m_ranges) {
                if (r.contains(value)) return 0;
            }
            return -1;
        }
    }

    std::string expandedBinName(uint32_t localIdx) const {
        if (m_isArray) return m_name + "[" + std::to_string(localIdx) + "]";
        return m_name;
    }
};

//=============================================================================
// VlCoverpoint - Runtime coverpoint with bins and hit tracking

class VlCoverpoint final {
    std::string m_name;
    std::vector<VlCovBinDef> m_binDefs;
    std::vector<VlCovBinDef> m_ignoreBinDefs;
    std::vector<VlCovBinDef> m_illegalBinDefs;

    // Expanded runtime state
    uint32_t m_nBins = 0;
    std::vector<uint32_t> m_hits;
    std::set<uint32_t> m_unhit;
    bool m_finalized = false;

    // Cached coverage
    mutable double m_cachedCoverage = 0.0;
    mutable bool m_coverageValid = false;

public:
    explicit VlCoverpoint(const std::string& name)
        : m_name{name} {}

    VlCovBinDef& addBin(const std::string& name, VlCovBinKind kind = VlCovBinKind::BINS) {
        switch (kind) {
        case VlCovBinKind::IGNORE_BINS: {
            m_ignoreBinDefs.emplace_back(name, kind);
            return m_ignoreBinDefs.back();
        }
        case VlCovBinKind::ILLEGAL_BINS: {
            m_illegalBinDefs.emplace_back(name, kind);
            return m_illegalBinDefs.back();
        }
        default: {
            m_binDefs.emplace_back(name, kind);
            return m_binDefs.back();
        }
        }
    }

    void finalize() {
        m_nBins = 0;
        for (auto& def : m_binDefs) m_nBins += def.finalize(m_nBins);
        uint32_t ignoreBase = 0;
        for (auto& def : m_ignoreBinDefs) ignoreBase += def.finalize(ignoreBase);
        uint32_t illegalBase = 0;
        for (auto& def : m_illegalBinDefs) illegalBase += def.finalize(illegalBase);

        m_hits.assign(m_nBins, 0);
        for (uint32_t i = 0; i < m_nBins; ++i) m_unhit.insert(i);
        m_finalized = true;
    }

    void sample(uint64_t value) {
        if (VL_UNLIKELY(!m_finalized)) return;

        // Check ignore bins first
        for (const auto& def : m_ignoreBinDefs) {
            if (def.sample(value) >= 0) return;
        }

        // Check illegal bins
        for (const auto& def : m_illegalBinDefs) {
            if (def.sample(value) >= 0) {
                const std::string msg
                    = "illegal_bins hit in coverpoint '" + m_name + "'";
                VL_WARN_MT(__FILE__, __LINE__, "", msg.c_str());
                return;
            }
        }

        // Check regular bins
        for (const auto& def : m_binDefs) {
            const int32_t localIdx = def.sample(value);
            if (localIdx >= 0) {
                const uint32_t globalIdx = def.baseBinIdx() + static_cast<uint32_t>(localIdx);
                if (globalIdx < m_nBins) {
                    ++m_hits[globalIdx];
                    m_unhit.erase(globalIdx);
                    m_coverageValid = false;
                }
                return;
            }
        }
    }

    double getCoverage() const {
        if (m_nBins == 0) return 100.0;
        if (!m_coverageValid) {
            m_cachedCoverage
                = static_cast<double>(m_nBins - m_unhit.size()) / m_nBins * 100.0;
            m_coverageValid = true;
        }
        return m_cachedCoverage;
    }

    const std::string& name() const { return m_name; }
    uint32_t nBins() const { return m_nBins; }
    uint32_t nHitBins() const { return m_nBins - static_cast<uint32_t>(m_unhit.size()); }
    uint32_t hitCount(uint32_t binIdx) const {
        return (binIdx < m_hits.size()) ? m_hits[binIdx] : 0;
    }
};

//=============================================================================
// VlCovergroup - Runtime covergroup container

class VlCovergroup final {
    std::string m_name;
    std::string m_instName;
    std::vector<VlCoverpoint*> m_coverpoints;  // Owned pointers
    bool m_finalized = false;

    // Cached coverage
    mutable double m_cachedCoverage = 0.0;
    mutable bool m_coverageValid = false;

public:
    VlCovergroup() = default;
    explicit VlCovergroup(const std::string& name)
        : m_name{name} {}
    ~VlCovergroup() {
        for (auto* cpp : m_coverpoints) delete cpp;
    }
    VL_UNCOPYABLE(VlCovergroup);
    VlCovergroup(VlCovergroup&& other) noexcept
        : m_name{std::move(other.m_name)}
        , m_instName{std::move(other.m_instName)}
        , m_coverpoints{std::move(other.m_coverpoints)}
        , m_finalized{other.m_finalized}
        , m_cachedCoverage{other.m_cachedCoverage}
        , m_coverageValid{other.m_coverageValid} {
        other.m_coverpoints.clear();
    }
    VlCovergroup& operator=(VlCovergroup&& other) noexcept {
        if (this != &other) {
            for (auto* cpp : m_coverpoints) delete cpp;
            m_name = std::move(other.m_name);
            m_instName = std::move(other.m_instName);
            m_coverpoints = std::move(other.m_coverpoints);
            m_finalized = other.m_finalized;
            m_cachedCoverage = other.m_cachedCoverage;
            m_coverageValid = other.m_coverageValid;
            other.m_coverpoints.clear();
        }
        return *this;
    }

    // Setup
    VlCoverpoint* addCoverpoint(const std::string& name) {
        auto* cpp = new VlCoverpoint{name};
        m_coverpoints.push_back(cpp);
        return cpp;
    }

    void finalize() {
        for (auto* cpp : m_coverpoints) cpp->finalize();
        m_finalized = true;
    }

    // Sampling
    void sampleCoverpoint(uint32_t cpIdx, uint64_t value) {
        if (VL_LIKELY(cpIdx < m_coverpoints.size())) {
            m_coverpoints[cpIdx]->sample(value);
            m_coverageValid = false;
        }
    }

    // Coverage
    double getCoverage() const {
        if (m_coverpoints.empty()) return 100.0;
        if (!m_coverageValid) {
            double sum = 0.0;
            for (const auto* cpp : m_coverpoints) sum += cpp->getCoverage();
            m_cachedCoverage = sum / m_coverpoints.size();
            m_coverageValid = true;
        }
        return m_cachedCoverage;
    }
    double getInstCoverage() const { return getCoverage(); }

    // Instance naming
    void setInstName(const std::string& name) { m_instName = name; }
    const std::string& instName() const { return m_instName; }
    const std::string& name() const { return m_name; }

    // Accessors
    uint32_t numCoverpoints() const { return static_cast<uint32_t>(m_coverpoints.size()); }
    VlCoverpoint* coverpoint(uint32_t idx) {
        return (idx < m_coverpoints.size()) ? m_coverpoints[idx] : nullptr;
    }
    const VlCoverpoint* coverpoint(uint32_t idx) const {
        return (idx < m_coverpoints.size()) ? m_coverpoints[idx] : nullptr;
    }
};

//=============================================================================
// VL_TO_STRING specialization for VlCovergroup (required by generated code)

inline std::string VL_TO_STRING(const VlCovergroup& obj) {
    return std::string{"VlCovergroup:"} + obj.name();
}

#endif  // Guard
