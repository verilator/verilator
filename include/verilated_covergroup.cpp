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
/// \brief Verilated functional-coverage collection runtime implementation
///
/// Compiled and linked when "verilator --coverage" is used with covergroups.
///
//=============================================================================

#include "verilatedos.h"

#include "verilated_covergroup.h"

#include "verilated_cov.h"

void VlCoverpoint::init(const char* hier, uint32_t atLeast, int nBins) {
    m_hier = hier;
    m_atLeast = atLeast;
    m_total = nBins;
    m_counts.assign(nBins, 0);
    m_crossIdx.assign(nBins, -1);
}

void VlCoverpoint::addNamer(VlCovBinKind set, int count, VlCovBinNaming naming, const char* name,
                            const char* file, int line, int col) {
    m_namers.emplace_back(set, count, m_nextBase, naming, name, file, line, col);
    if (set == VlCovBinKind::KIND_NORMAL) {
        // Assign each Normal bin its cross index (Normal-only re-indexing); ignore/
        // illegal/default bins keep -1 and never enter a cross.
        for (int b = m_nextBase; b < m_nextBase + count; ++b) m_crossIdx[b] = m_nextCrossIdx++;
        m_normal += count;
    }
    m_nextBase += count;
}

std::string VlCoverpoint::normalBinName(int crossIdx) const {
    // Map a cross (Normal-only) index back to its full bin index, then build its name.
    // Called only at cross registration, so a linear scan is acceptable.
    for (int i = 0; i < m_total; ++i) {
        if (m_crossIdx[i] == crossIdx) return binName(i);
    }
    VL_UNREACHABLE;  // LCOV_EXCL_LINE
}

const VlCovNamer& VlCoverpoint::namerFor(int i) const {
    // Namers are appended in ascending, contiguous index order covering [0, m_total),
    // and i is always a valid bin index, so the matching namer always exists.
    for (const VlCovNamer& nm : m_namers) {
        if (i < nm.base() + nm.count()) return nm;
    }
    VL_UNREACHABLE;  // LCOV_EXCL_LINE
}

std::string VlCoverpoint::binName(int i) const {
    const VlCovNamer& nm = namerFor(i);
    std::string name = nm.name();
    if (nm.naming() == VlCovBinNaming::Array) name += '[' + std::to_string(i - nm.base()) + ']';
    return name;
}

void VlCoverpoint::registerBins(VerilatedCovContext* covcontextp, const char* page) {
    for (int i = 0; i < binCount(); ++i) {
        const VlCovNamer& nm = namerFor(i);
        const VlCovBinKind kind = binKind(i);
        const std::string binp = binName(i);
        const std::string full = m_hier + "." + binp;
        const std::string lineStr = std::to_string(nm.line());
        const std::string colStr = std::to_string(nm.col());
        if (kind == VlCovBinKind::KIND_NORMAL) {
            VL_COVER_INSERT(covcontextp, full.c_str(), &m_counts[i], "page", page, "filename",
                            nm.file(), "lineno", lineStr.c_str(), "column", colStr.c_str(), "bin",
                            binp.c_str());
        } else {
            const char* const binType = kind == VlCovBinKind::KIND_IGNORE    ? "ignore"
                                        : kind == VlCovBinKind::KIND_ILLEGAL ? "illegal"
                                                                             : "default";
            VL_COVER_INSERT(covcontextp, full.c_str(), &m_counts[i], "page", page, "filename",
                            nm.file(), "lineno", lineStr.c_str(), "column", colStr.c_str(), "bin",
                            binp.c_str(), "bin_type", binType);
        }
    }
}

//=============================================================================
// VlCoverCross

void VlCoverCross::init(const char* hier, int dims, VlCoverpoint* const* cps, const char* file,
                        int line, int col) {
    m_hier = hier;
    m_file = file;
    m_line = line;
    m_col = col;
    m_dims = dims;
    m_cps.assign(cps, cps + dims);
    m_cpBinCounts.resize(dims);
    m_numAutoBins = 1;
    for (int d = 0; d < dims; ++d) {
        m_cpBinCounts[d] = cps[d]->normalBinCount();
        m_numAutoBins *= m_cpBinCounts[d];
    }
    // stride[d] = product of the Normal bin counts of all dimensions after d.
    m_stride.assign(dims, 1);
    for (int d = dims - 2; d >= 0; --d) m_stride[d] = m_stride[d + 1] * m_cpBinCounts[d + 1];
    m_flatCounts.assign(m_numAutoBins, 0);
}

void VlCoverCross::iterateProduct(VlCoverpoint* const* cps, int dim, int64_t baseIdx) {
    const int hits = cps[dim]->hitCount();
    const int* const list = cps[dim]->hitList();
    const bool last = (dim == m_dims - 1);
    const int64_t stride = m_stride[dim];
    for (int hit = 0; hit < hits; ++hit) {
        const int64_t idx = baseIdx + static_cast<int64_t>(list[hit]) * stride;
        if (last) {
            incrementTuple(idx);
        } else {
            iterateProduct(cps, dim + 1, idx);
        }
    }
}

void VlCoverCross::sample(VlCoverpoint* const* cps) {
    // Fast path: if any dimension had no Normal-bin hit, the cross cannot hit.
    for (int d = 0; d < m_dims; ++d) {
        if (cps[d]->hitCount() == 0) return;
    }
    iterateProduct(cps, 0, 0);
}

std::string VlCoverCross::binName(int flat) const {
    // Built on demand by concatenating each coverpoint's own bin name.
    std::string name;
    for (int d = 0; d < m_dims; ++d) {
        const int crossIdx = static_cast<int>((flat / m_stride[d]) % m_cpBinCounts[d]);
        if (d > 0) name += "_x_";
        name += m_cps[d]->normalBinName(crossIdx);
    }
    return name;
}

void VlCoverCross::registerBins(VerilatedCovContext* covcontextp, const char* page) {
    // Register every auto cross bin (zero-count bins included), so the report
    // shows the full Cartesian product of cross bins.  Names are built on the fly.
    const std::string lineStr = std::to_string(m_line);
    const std::string colStr = std::to_string(m_col);
    for (int flat = 0; flat < binCount(); ++flat) {
        const std::string bin = binName(flat);  // "b1_x_b2_x_..."
        // cross_bins metadata: the same components joined by ',' (not read by the report)
        std::string crossBins;
        for (int d = 0; d < m_dims; ++d) {
            const int crossIdx = static_cast<int>((flat / m_stride[d]) % m_cpBinCounts[d]);
            if (d > 0) crossBins += ",";
            crossBins += m_cps[d]->normalBinName(crossIdx);
        }
        const std::string full = m_hier + "." + bin;
        VL_COVER_INSERT(covcontextp, full.c_str(), &m_flatCounts[flat], "page", page, "filename",
                        m_file, "lineno", lineStr.c_str(), "column", colStr.c_str(), "bin",
                        bin.c_str(), "cross", "1", "cross_bins", crossBins.c_str());
    }
}
