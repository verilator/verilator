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
}

void VlCoverpoint::addNamer(VlCovBinKind set, int count, VlCovBinNaming naming, const char* name,
                            const char* file, int line, int col) {
    m_namers.push_back(VlCovNamer{set, count, m_nextBase, naming, name, file, line, col});
    m_nextBase += count;
    if (set == VlCovBinKind::Normal) m_normal += count;
}

const VlCovNamer& VlCoverpoint::namerFor(int i) const {
    // Namers are appended in ascending, contiguous index order covering [0, m_total),
    // and i is always a valid bin index, so the matching namer always exists.
    for (const VlCovNamer& nm : m_namers) {
        if (i < nm.base + nm.count) return nm;
    }
    VL_UNREACHABLE;
}

const char* VlCoverpoint::binName(int i, std::string& buf) const {
    const VlCovNamer& nm = namerFor(i);
    buf = nm.name;
    if (nm.naming == VlCovBinNaming::Array) buf += '[' + std::to_string(i - nm.base) + ']';
    return buf.c_str();
}

void VlCoverpoint::registerBins(VerilatedCovContext* covcontextp, const char* page) {
    std::string buf;
    for (int i = 0; i < binCount(); ++i) {
        const VlCovNamer& nm = namerFor(i);
        const VlCovBinKind kind = binKind(i);
        const char* const binp = binName(i, buf);
        const std::string full = m_hier + "." + binp;
        const std::string lineStr = std::to_string(nm.line);
        const std::string colStr = std::to_string(nm.col);
        if (kind == VlCovBinKind::Normal) {
            VL_COVER_INSERT(covcontextp, full.c_str(), &m_counts[i], "page", page, "filename",
                            nm.file, "lineno", lineStr.c_str(), "column", colStr.c_str(), "bin",
                            binp);
        } else {
            const char* const binType = kind == VlCovBinKind::Ignore    ? "ignore"
                                        : kind == VlCovBinKind::Illegal ? "illegal"
                                                                        : "default";
            VL_COVER_INSERT(covcontextp, full.c_str(), &m_counts[i], "page", page, "filename",
                            nm.file, "lineno", lineStr.c_str(), "column", colStr.c_str(), "bin",
                            binp, "bin_type", binType);
        }
    }
}
