// -*- mode: C++; c-file-style: "cc-mode" -*-
//=============================================================================
//
// Code available from: https://verilator.org
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026-2026 by Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//=============================================================================
///
/// \file
/// \brief Verilated functional coverage support header
///
/// This file provides runtime support for SystemVerilog functional coverage
/// constructs (covergroups, coverpoints, bins, cross coverage).
///
//=============================================================================

#ifndef VERILATOR_VERILATED_FUNCCOV_H_
#define VERILATOR_VERILATED_FUNCCOV_H_

#include "verilatedos.h"

#include "verilated.h"
#include "verilated_cov.h"

#include <map>
#include <string>
#include <vector>

//=============================================================================
// VerilatedCoverBin - Represents a single bin in a coverpoint

class VerilatedCoverBin VL_NOT_FINAL {
private:
    std::string m_name;  // Bin name
    std::string m_rangeStr;  // String representation of range (e.g., "0:15")
    uint32_t m_count = 0;  // Hit count
    uint32_t* m_countp = nullptr;  // Pointer to counter (for coverage registration)

public:
    VerilatedCoverBin(const std::string& name, const std::string& rangeStr)
        : m_name{name}
        , m_rangeStr{rangeStr}
        , m_countp{&m_count} {}

    virtual ~VerilatedCoverBin() = default;

    // Accessors
    const std::string& name() const { return m_name; }
    const std::string& rangeStr() const { return m_rangeStr; }
    uint32_t count() const { return m_count; }
    uint32_t* countp() { return m_countp; }

    // Increment hit count
    void hit() { ++m_count; }

    // Check if value matches this bin (to be overridden by specific bin types)
    virtual bool matches(uint64_t value) const { return false; }
};

//=============================================================================
// VerilatedCoverRangeBin - Bin that matches a value range

class VerilatedCoverRangeBin final : public VerilatedCoverBin {
private:
    uint64_t m_min;
    uint64_t m_max;

public:
    VerilatedCoverRangeBin(const std::string& name, uint64_t min, uint64_t max)
        : VerilatedCoverBin(name, std::to_string(min) + ":" + std::to_string(max))
        , m_min{min}
        , m_max{max} {}

    bool matches(uint64_t value) const override { return value >= m_min && value <= m_max; }
};

//=============================================================================
// VerilatedCoverpoint - Represents a coverage point

class VerilatedCoverpoint VL_NOT_FINAL {
private:
    std::string m_name;  // Coverpoint name
    std::vector<VerilatedCoverBin*> m_bins;  // Bins in this coverpoint
    bool m_enabled = true;  // Coverage collection enabled

public:
    explicit VerilatedCoverpoint(const std::string& name)
        : m_name{name} {}

    ~VerilatedCoverpoint() {
        for (auto* bin : m_bins) delete bin;
    }

    // Accessors
    const std::string& name() const { return m_name; }
    const std::vector<VerilatedCoverBin*>& bins() const { return m_bins; }
    bool enabled() const { return m_enabled; }
    void enabled(bool flag) { m_enabled = flag; }

    // Add a bin to this coverpoint
    void addBin(VerilatedCoverBin* binp) { m_bins.push_back(binp); }

    // Sample a value and update bin counts
    void sample(uint64_t value) {
        if (!m_enabled) return;
        for (auto* bin : m_bins) {
            if (bin->matches(value)) { bin->hit(); }
        }
    }

    // Compute coverage percentage
    double getCoverage(uint32_t atLeast = 1) const {
        if (m_bins.empty()) return 100.0;
        int coveredBins = 0;
        for (const auto* bin : m_bins) {
            if (bin->count() >= atLeast) ++coveredBins;
        }
        return (100.0 * coveredBins) / m_bins.size();
    }

    // Register bins with coverage infrastructure
    void registerCoverage(VerilatedCovContext* contextp, const std::string& hier,
                          const std::string& cgName) {
        for (auto* bin : m_bins) {
            const std::string fullName = cgName + "." + m_name;
            const std::string& binName = bin->name();
            const std::string& binRange = bin->rangeStr();
            VL_COVER_INSERT(contextp, hier.c_str(), bin->countp(), "type", "coverpoint", "name",
                            fullName.c_str(), "bin", binName.c_str(), "range", binRange.c_str());
        }
    }
};

//=============================================================================
// VerilatedCoverCross - Represents cross coverage between coverpoints

class VerilatedCoverCross VL_NOT_FINAL {
private:
    std::string m_name;  // Cross name
    std::vector<VerilatedCoverpoint*> m_coverpoints;  // Coverpoints being crossed
    std::map<std::string, uint32_t> m_crossBins;  // Sparse storage: "<bin1,bin2>" -> count
    bool m_enabled = true;

public:
    explicit VerilatedCoverCross(const std::string& name)
        : m_name{name} {}

    // Accessors
    const std::string& name() const { return m_name; }
    bool enabled() const { return m_enabled; }
    void enabled(bool flag) { m_enabled = flag; }

    // Add a coverpoint to cross
    void addCoverpoint(VerilatedCoverpoint* cpp) { m_coverpoints.push_back(cpp); }

    // Sample cross product (to be called after coverpoints are sampled)
    void sample(const std::vector<uint64_t>& values) {
        if (!m_enabled || values.size() != m_coverpoints.size()) return;

        // Build cross bin key from matched bins
        std::string key = "<";
        bool first = true;
        for (size_t i = 0; i < values.size(); ++i) {
            // Find which bin matched for this coverpoint
            for (const auto* bin : m_coverpoints[i]->bins()) {
                if (bin->matches(values[i])) {
                    if (!first) key += ",";
                    key += bin->name();
                    first = false;
                    break;
                }
            }
        }
        key += ">";

        // Increment cross bin count
        m_crossBins[key]++;
    }

    // Compute coverage percentage
    double getCoverage(uint32_t atLeast = 1) const {
        if (m_crossBins.empty()) return 100.0;
        int coveredBins = 0;
        for (const auto& pair : m_crossBins) {
            if (pair.second >= atLeast) ++coveredBins;
        }
        // Total possible bins is product of coverpoint bin counts
        size_t totalBins = 1;
        for (const auto* cp : m_coverpoints) { totalBins *= cp->bins().size(); }
        return (100.0 * coveredBins) / totalBins;
    }

    // Register cross bins with coverage infrastructure
    void registerCoverage(VerilatedCovContext* contextp, const std::string& hier,
                          const std::string& cgName) {
        // Cross bins are registered dynamically as they're hit
        // For now, we'll register them all upfront (can be optimized later)
        std::string fullName = cgName + "." + m_name;
        for (const auto& pair : m_crossBins) {
            // Note: We need a persistent counter, so we use the map value's address
            // This is safe because std::map doesn't reallocate on insert
            const std::string& binName = pair.first;
            VL_COVER_INSERT(contextp, hier.c_str(), const_cast<uint32_t*>(&pair.second), "type",
                            "cross", "name", fullName.c_str(), "bin", binName.c_str());
        }
    }
};

//=============================================================================
// VerilatedCovergroup - Represents a covergroup instance

class VerilatedCovergroup VL_NOT_FINAL {
private:
    std::string m_name;  // Covergroup type name
    std::string m_instName;  // Instance name
    std::vector<VerilatedCoverpoint*> m_coverpoints;
    std::vector<VerilatedCoverCross*> m_crosses;
    bool m_enabled = true;

    // Coverage options
    uint32_t m_weight = 1;
    uint32_t m_goal = 100;
    uint32_t m_atLeast = 1;
    std::string m_comment;

public:
    explicit VerilatedCovergroup(const std::string& name)
        : m_name{name}
        , m_instName{name} {}

    ~VerilatedCovergroup() {
        for (auto* cp : m_coverpoints) delete cp;
        for (auto* cross : m_crosses) delete cross;
    }

    // Accessors
    const std::string& name() const { return m_name; }
    const std::string& instName() const { return m_instName; }
    void instName(const std::string& name) { m_instName = name; }
    bool enabled() const { return m_enabled; }

    // Options
    void weight(uint32_t w) { m_weight = w; }
    void goal(uint32_t g) { m_goal = g; }
    void atLeast(uint32_t a) { m_atLeast = a; }
    void comment(const std::string& c) { m_comment = c; }

    // Add components
    void addCoverpoint(VerilatedCoverpoint* cpp) { m_coverpoints.push_back(cpp); }
    void addCross(VerilatedCoverCross* cross) { m_crosses.push_back(cross); }

    // Predefined methods per IEEE 1800-2023 Section 19.9
    void sample() {
        if (!m_enabled) return;
        // Sampling is done by generated code calling coverpoint sample() methods
    }

    void start() { m_enabled = true; }
    void stop() { m_enabled = false; }

    void set_inst_name(const std::string& name) { m_instName = name; }

    // Get type coverage (0-100)
    double get_coverage() const {
        if (m_coverpoints.empty()) return 100.0;
        double totalCov = 0.0;
        uint32_t totalWeight = 0;
        for (const auto* cp : m_coverpoints) {
            totalCov += cp->getCoverage(m_atLeast) * m_weight;
            totalWeight += m_weight;
        }
        for (const auto* cross : m_crosses) {
            totalCov += cross->getCoverage(m_atLeast) * m_weight;
            totalWeight += m_weight;
        }
        return totalWeight > 0 ? totalCov / totalWeight : 100.0;
    }

    // Get instance coverage (same as type coverage for now)
    double get_inst_coverage() const { return get_coverage(); }

    // Register all coverage points with coverage infrastructure
    void registerCoverage(VerilatedCovContext* contextp, const std::string& hier) {
        // Register covergroup metadata
        // (Will be extended when we add metadata output)

        // Register all coverpoints
        for (auto* cp : m_coverpoints) { cp->registerCoverage(contextp, hier, m_name); }

        // Register all crosses
        for (auto* cross : m_crosses) { cross->registerCoverage(contextp, hier, m_name); }
    }
};

#endif  // guard
