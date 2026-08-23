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

#include "verilated.h"

// This file is compiled whenever covergroups are used, with or without
// "verilator --coverage" (see V3Global::verilatedCppFiles).  Bin counts are
// owned by the covergroup instance nodes in the VerilatedContext's registry, so
// sampling, bin naming, and coverage queries such as get_inst_coverage() all
// work with no coverage database present.  VL_COVER_INSERT does not copy a
// count; it hands the database the address of a counter the registry owns and
// reads it at write time.  Only that publication step needs the database, so
// only the registerBins() bodies -- and this include -- are gated on
// VM_COVERAGE.
#if VM_COVERAGE
#include "verilated_cov.h"
#endif

void VlCoverpoint::init(const char* hier, uint32_t atLeast, uint32_t nBins) {
    m_hier = hier;
    m_atLeast = atLeast;
    m_total = nBins;
    m_counts.assign(nBins, 0);
    m_crossIdx.assign(nBins, -1);
    m_crossToBin.clear();
}

void VlCoverpoint::addNamer(VlCovBinKind set, uint32_t count, VlCovBinNaming naming,
                            const char* name, const char* file, int line, int col) {
    m_namers.emplace_back(set, count, m_nextBase, naming, name, file, line, col);
    if (set == VlCovBinKind::KIND_NORMAL) {
        // Assign each Normal bin a cross index, and record the inverse map.
        for (uint32_t b = m_nextBase; b < m_nextBase + count; ++b) {
            m_crossIdx[b] = static_cast<int>(m_crossToBin.size());
            m_crossToBin.push_back(b);
        }
        m_normal += count;
    }
    m_nextBase += count;
}

std::string VlCoverpoint::normalBinName(uint32_t crossIdx) const {
    // Build the bin name based on the bin index
    return binName(m_crossToBin[crossIdx]);
}

const VlCovNamer& VlCoverpoint::namerFor(uint32_t i) const {
    // Namers are appended in ascending order covering [0, m_total),
    for (const VlCovNamer& nm : m_namers) {
        if (i < nm.base() + nm.count()) return nm;
    }
    VL_UNREACHABLE;  // LCOV_EXCL_LINE
}

std::string VlCoverpoint::binName(uint32_t i) const {
    const VlCovNamer& nm = namerFor(i);
    std::string name = nm.name();
    if (nm.naming() == VlCovBinNaming::Array) name += '[' + std::to_string(i - nm.base()) + ']';
    return name;
}

#if VM_COVERAGE
void VlCoverpoint::registerBins(VerilatedCovContext* covcontextp, const char* page) {
    for (uint32_t i = 0; i < binCount(); ++i) {
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

//=============================================================================
// VlCoverCross

void VlCoverCross::init(const char* hier, uint32_t dims, VlCoverpoint* const* cps,
                        const char* file, int line, int col) {
    m_hier = hier;
    m_file = file;
    m_line = line;
    m_col = col;
    m_dims = dims;
    m_cps.assign(cps, cps + dims);
    m_cpBinCounts.resize(dims);
    // Accumulate in 64 bits so the overflow check itself cannot overflow.
    uint64_t product = 1;
    for (uint32_t d = 0; d < dims; ++d) {
        m_cpBinCounts[d] = cps[d]->normalBinCount();
        product *= m_cpBinCounts[d];
        if (VL_UNLIKELY(product > UINT32_MAX)) {  // LCOV_EXCL_START
            VL_FATAL_MT(file, line, "", "Cross has too many auto bins to represent");
        }  // LCOV_EXCL_STOP
    }
    m_numAutoBins = static_cast<uint32_t>(product);
    // stride[d] = product of the Normal bin counts of all dimensions after d.
    // Counts down with an offset so the unsigned index never wraps below zero.
    m_stride.assign(dims, 1);
    for (uint32_t d = dims; d > 1; --d) m_stride[d - 2] = m_stride[d - 1] * m_cpBinCounts[d - 1];
    m_flatCounts.assign(m_numAutoBins, 0);
}

void VlCoverCross::iterateProduct(uint32_t dim, uint32_t baseIdx) {
    const VlCoverpoint* const cpp = m_cps[dim];
    const uint32_t hits = cpp->hitCount();
    const uint32_t* const list = cpp->hitList();
    const bool last = (dim == m_dims - 1);
    const uint32_t stride = m_stride[dim];
    for (uint32_t hit = 0; hit < hits; ++hit) {
        const uint32_t idx = baseIdx + list[hit] * stride;
        if (last) {
            incrementTuple(idx);
        } else {
            iterateProduct(dim + 1, idx);
        }
    }
}

void VlCoverCross::sample() {
    // Fast path: if any dimension had no Normal-bin hit, the cross cannot hit.
    for (uint32_t d = 0; d < m_dims; ++d) {
        if (m_cps[d]->hitCount() == 0) return;
    }
    iterateProduct(0, 0);
}

std::string VlCoverCross::binName(uint32_t flat) const {
    // Built on demand by concatenating each coverpoint's own bin name.
    std::string name;
    for (uint32_t d = 0; d < m_dims; ++d) {
        const uint32_t crossIdx = (flat / m_stride[d]) % m_cpBinCounts[d];
        if (d > 0) name += "_x_";
        name += m_cps[d]->normalBinName(crossIdx);
    }
    return name;
}

#if VM_COVERAGE
void VlCoverCross::registerBins(VerilatedCovContext* covcontextp, const char* page) {
    // Register every auto cross bin (zero-count bins included), so the report
    // shows the full Cartesian product of cross bins.  Names are built on the fly.
    const std::string lineStr = std::to_string(m_line);
    const std::string colStr = std::to_string(m_col);
    for (uint32_t flat = 0; flat < binCount(); ++flat) {
        const std::string bin = binName(flat);  // "b1_x_b2_x_..."
        // cross_bins metadata: the same components joined by ',' (not read by the report)
        std::string crossBins;
        for (uint32_t d = 0; d < m_dims; ++d) {
            const uint32_t crossIdx = (flat / m_stride[d]) % m_cpBinCounts[d];
            if (d > 0) crossBins += ",";
            crossBins += m_cps[d]->normalBinName(crossIdx);
        }
        const std::string full = m_hier + "." + bin;
        VL_COVER_INSERT(covcontextp, full.c_str(), &m_flatCounts[flat], "page", page, "filename",
                        m_file, "lineno", lineStr.c_str(), "column", colStr.c_str(), "bin",
                        bin.c_str(), "cross", "1", "cross_bins", crossBins.c_str());
    }
}
#endif  // VM_COVERAGE

//=============================================================================
// VlCovergroupType / VlCovRegistry

VlCovergroupInst* VlCovergroupType::newInstance() {
    const uint32_t slot = static_cast<uint32_t>(m_insts.size());
    VlCovergroupInst* const instp = new VlCovergroupInst{this, slot, m_nextInstId++};
    m_insts.emplace_back(instp);
    ++m_createdInsts;
    return instp;
}

void VlCovergroupType::foldResidue(const VlCovergroupInst* instp) {
    double covered = 0.0;
    double total = 0.0;
    instp->coverageParts(covered, total);
    // Nothing coverable: excluded from both sums, so it moves neither the mean
    // nor the denominator.  Never-sampled is different: it has bins, none hit,
    // and folds as 0%.
    if (total == 0.0) return;
    // TODO(P5): IEEE 1800-2023 19.5 defines covergroup coverage as the weighted
    // mean of the per-item ratios, not the ratio of the summed parts.  This
    // matches what the generated get_inst_coverage() computes today, so that a
    // live instance and the same instance one delta after death never disagree.
    m_retired.sumCoverage += 100.0 * covered / total;
    ++m_retired.count;
}

// Runs when the last handle to instp drops, possibly after ~VlCovRegistry, on a
// type teardown leaked to keep this valid (see ~VlCovRegistry).  That late case
// needs no special handling: the leaked type is self-consistent.
void VlCovergroupType::retire(VlCovergroupInst* instp) {
    foldResidue(instp);  // Before unlink: reads instp's items, freed below

#if VM_COVERAGE
    // registerBins() gave the coverage database raw &m_counts[i], read at
    // write() time.  Keep the node alive, marked dead so it counts as neither
    // live nor residue.  Freeing here needs the coverage-writer rework.
    instp->m_retained = true;
#else
    // Move out first, so the node destructs at end of scope with m_insts
    // already consistent rather than mid-swap.
    const uint32_t slot = instp->m_slot;
    const std::unique_ptr<VlCovergroupInst> dying = std::move(m_insts[slot]);
    if (slot != m_insts.size() - 1) {
        m_insts[slot] = std::move(m_insts.back());
        m_insts[slot]->m_slot = slot;  // Moved node's slot is now stale
    }
    m_insts.pop_back();
#endif
}

uint32_t VlCovergroupType::liveInstanceCount() const {
    uint32_t live = 0;
    // Under VM_COVERAGE m_insts also holds retained (dead) nodes; otherwise
    // retained() is never set and this equals m_insts.size().
    for (const auto& instp : m_insts) {
        if (!instp->retained()) ++live;
    }
    return live;
}

bool VlCovergroupType::anyAttached() const {
    for (const auto& instp : m_insts) {
        if (instp->m_attachCount > 0) return true;
    }
    return false;
}

double VlCovergroupType::retiredCoverage() const {
    if (m_retired.count == 0) return -1.0;
    return m_retired.sumCoverage / static_cast<double>(m_retired.count);
}

// Defined here, not in verilated.cpp, so that the registry costs nothing in a model with no
// covergroups: this file is linked only when covergroups are used (or --coverage is on).
// Mirrors VerilatedContext::coveragep(), which lives in verilated_cov.cpp for the same reason.
VlCovRegistry* VerilatedContext::covergroupRegistryp() VL_MT_SAFE {
    static VerilatedMutex s_mutex;
    // cppcheck-suppress identicalInnerCondition
    if (VL_UNLIKELY(!m_covergroupsp)) {
        const VerilatedLockGuard lock{s_mutex};
        // cppcheck-suppress identicalInnerCondition
        if (VL_LIKELY(!m_covergroupsp)) {  // LCOV_EXCL_LINE // Not redundant, prevents race
            m_covergroupsp.reset(new VlCovRegistry{});
        }
    }
    return static_cast<VlCovRegistry*>(m_covergroupsp.get());
}

VlCovergroupInst* VlCovRegistry::newCovergroupInst(const char* typeName) {
    VlCovergroupType*& typep = m_byName[typeName];
    if (!typep) {  // First instance of this type
        m_types.emplace_back(new VlCovergroupType{});
        typep = m_types.back().get();
    }
    return typep->newInstance();
}

// A covergroup object can outlive the registry: models must be destroyed before
// their context, and a user who gets that backwards drops covergroup handles
// after ~VerilatedContext.  Those handle destructors call attachDec(), which
// reads the instance node and its type -- so freeing the nodes here is itself
// what would make the wrong ordering a use-after-free, and a "retirement
// disarmed" flag could not help.  Instead, leak any type that still has an
// attached node, keeping the type, its nodes and their items valid; the late
// retire() then frees the nodes itself, so only the type object leaks.
VlCovRegistry::~VlCovRegistry() {
    for (auto& typep : m_types) {
        // Normally nothing is still attached; if something is, the model
        // outlived its context and those handles still reach this type.
        if (VL_UNLIKELY(typep->anyAttached())) {
            VlCovergroupType* const leakedp = typep.release();
            static_cast<void>(leakedp);  // Deliberate leak
        }
    }
}

VlCovergroupType* VlCovRegistry::findType(const char* typeName) const {
    const auto it = m_byName.find(typeName);
    return it == m_byName.end() ? nullptr : it->second;
}

uint32_t VlCovRegistry::liveInstanceCount() const {
    uint32_t total = 0;
    for (const auto& typep : m_types) total += typep->liveInstanceCount();
    return total;
}

uint32_t VlCovRegistry::createdInstanceCount() const {
    uint32_t total = 0;
    for (const auto& typep : m_types) total += typep->createdInstanceCount();
    return total;
}

uint32_t VlCovRegistry::liveInstanceCount(const char* typeName) const {
    const VlCovergroupType* const typep = findType(typeName);
    return typep ? typep->liveInstanceCount() : 0;
}

uint32_t VlCovRegistry::createdInstanceCount(const char* typeName) const {
    const VlCovergroupType* const typep = findType(typeName);
    return typep ? typep->createdInstanceCount() : 0;
}

uint32_t VlCovRegistry::retiredInstanceCount(const char* typeName) const {
    const VlCovergroupType* const typep = findType(typeName);
    return typep ? typep->retiredInstanceCount() : 0;
}

double VlCovRegistry::retiredCoverage(const char* typeName) const {
    const VlCovergroupType* const typep = findType(typeName);
    return typep ? typep->retiredCoverage() : -1.0;
}
