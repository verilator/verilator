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
/// Linked when covergroups are present.  The coverage-database registration
/// is compiled only with "verilator --coverage".
///
//=============================================================================

#include "verilatedos.h"

#include "verilated_covergroup.h"

#if VM_COVERAGE
# include "verilated_cov.h"
#endif

void VlCoverpoint::init(const char* hier, uint32_t atLeast, int nBins) {
    m_hier = hier;
    m_atLeast = atLeast;
    m_total = nBins;
    m_counts.assign(nBins, 0);
}

void VlCoverpoint::addNamer(VlCovBinKind set, int count, VlCovBinNaming naming, const char* name,
                            const char* file, int line, int col) {
    m_namers.emplace_back(set, count, m_nextBase, naming, name, file, line, col);
    m_nextBase += count;
    if (set == VlCovBinKind::KIND_NORMAL) m_normal += count;
}

const VlCovNamer& VlCoverpoint::namerFor(int i) const {
    // Namers are appended in ascending, contiguous index order covering [0, m_total),
    // and i is always a valid bin index, so the matching namer always exists.
    for (const VlCovNamer& nm : m_namers) {
        if (i < nm.base() + nm.count()) return nm;
    }
    VL_UNREACHABLE;
}

std::string VlCoverpoint::binName(int i) const {
    const VlCovNamer& nm = namerFor(i);
    std::string name = nm.name();
    if (nm.naming() == VlCovBinNaming::Array) name += '[' + std::to_string(i - nm.base()) + ']';
    return name;
}

#if VM_COVERAGE
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
#endif  // VM_COVERAGE
