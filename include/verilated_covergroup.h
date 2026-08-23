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

#include "verilated.h"
#include "verilated_cov_model.h"

#include <cstdint>
#include <memory>
#include <string>
#include <unordered_map>
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
    std::vector<VlCoverpoint*> m_cps;  // Feeding coverpoints, set by init()

    // PRIVATE METHODS
    void iterateProduct(uint32_t dim, uint32_t baseIdx);
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
    // Reads the feeding coverpoints from m_cps, so the caller passes nothing per sample.
    void sample();

    // ---- VlCoverpointIf ----
    // A cross is a coverpoint whose bins are the auto cross bins (all Normal).
    uint32_t binCount() const override { return m_numAutoBins; }
    std::string binName(uint32_t flat) const override;
    void coverageParts(double& covered, double& total) const override {
        covered = m_numCovered;
        total = m_numAutoBins;
    }
};

class VlCovergroupType;

//=============================================================================
// VlCovergroupInst
/// One covergroup instance: owns the coverpoint/cross runtimes created by one
/// SV 'new'.  The generated class holds borrowed pointers to them, so the bins
/// outlive the SV object -- the coverage database registers raw count pointers
/// and reads them at write() time, long after the object may have been freed.
///
/// Attach-counted: every VlCovInstHandle bound here holds one count, and the
/// node is retired (see VlCovergroupType::retire) when the last one drops.

class VlCovergroupInst final {
    // MEMBERS
    // Coverpoint and cross runtimes of this instance; creation == declaration order
    std::vector<std::unique_ptr<VlCoverpointIf>> m_items;
    VlCovergroupType* const m_typep;  // Owning type; outlives this node
    const uint32_t m_instId;  // Stable identity across churn; NOT the slot
    uint32_t m_slot;  // Index into m_typep->m_insts; rewritten by unlink-by-swap
    uint32_t m_attachCount = 1;  // SV handles bound here; 1 from construction
    bool m_retained = false;  // VM_COVERAGE: dead, but kept for registered count pointers

    // Reads m_items to fold the residue; rewrites m_slot/m_retained on unlink.
    friend class VlCovergroupType;

public:
    // CONSTRUCTORS
    VlCovergroupInst(VlCovergroupType* typep, uint32_t slot, uint32_t instId)
        : m_typep{typep}
        , m_instId{instId}
        , m_slot{slot} {}
    VL_UNCOPYABLE(VlCovergroupInst);

    // METHODS
    // ---- construction (from the generated covergroup constructor) ----
    template <uint32_t MaxHits>
    VlCoverpointT<MaxHits>* addCoverpoint() {
        VlCoverpointT<MaxHits>* const cpp = new VlCoverpointT<MaxHits>{};
        m_items.emplace_back(cpp);
        return cpp;  // borrowed by the generated class
    }
    VlCoverCross* addCross() {
        VlCoverCross* const cxp = new VlCoverCross{};
        m_items.emplace_back(cxp);
        return cxp;  // borrowed by the generated class
    }

    // ---- attach counting (from VlCovInstHandle) ----
    void attachInc() { ++m_attachCount; }
    // Drops one handle; true if it was the last and the caller must retire the
    // node.  Retiring is the caller's job because VlCovergroupType is incomplete
    // here, and because it frees 'this'.
    bool attachDec() { return --m_attachCount == 0; }

    // ---- introspection ----
    VlCovergroupType* typep() const { return m_typep; }
    uint32_t instId() const { return m_instId; }
    // True once retired but kept alive because the coverage database holds raw
    // pointers into this node's bin counts (VM_COVERAGE); see retire().
    bool retained() const { return m_retained; }
    // Sum of the instance's items' covered/total bin counts.  Matches what the
    // generated get_inst_coverage() computes; see foldResidue().
    void coverageParts(double& covered, double& total) const {
        covered = 0.0;
        total = 0.0;
        for (const auto& itemp : m_items) {
            double c = 0.0;
            double t = 0.0;
            itemp->coverageParts(c, t);
            covered += c;
            total += t;
        }
    }
};

//=============================================================================
// VlCovRetiredAvg
/// Per-type residue: what survives an instance's death.  Fixed size, so it does
/// not grow with churn.  Weight is 1 everywhere until option.weight is plumbed.

struct VlCovRetiredAvg final {
    uint64_t count = 0;  // Retired instances that contributed (nonzero denominator)
    double sumCoverage = 0.0;  // Sigma of per-instance coverage, each in 0..100
};

//=============================================================================
// VlCovergroupType
/// One covergroup type: owns its live instances, in creation order, plus the
/// residue of the ones that have died.

class VlCovergroupType final {
    // MEMBERS
    // Live nodes, and -- under VM_COVERAGE -- retired-but-retained ones.  Slot
    // order is creation order only until the first unlink-by-swap.
    std::vector<std::unique_ptr<VlCovergroupInst>> m_insts;
    uint32_t m_createdInsts = 0;  // Instances ever created; never decremented
    uint32_t m_nextInstId = 0;  // Monotonic; slots are reused, ids never are
    VlCovRetiredAvg m_retired;  // Contribution of every instance that has died

    // PRIVATE METHODS
    // Harvest instp's contribution into m_retired.  Must run before instp is
    // unlinked: it reads the instance's items.
    void foldResidue(const VlCovergroupInst* instp);

public:
    // CONSTRUCTORS
    VlCovergroupType() = default;
    VL_UNCOPYABLE(VlCovergroupType);

    // METHODS
    VlCovergroupInst* newInstance();
    // Called when the last handle to instp drops.  Folds the residue, then
    // unlinks and frees the node -- except under VM_COVERAGE, where the coverage
    // database still holds raw pointers into it and it is only marked retained.
    void retire(VlCovergroupInst* instp);
    // True if any node here still has an SV handle bound to it, and so can be
    // retired again after the registry is destroyed.  See ~VlCovRegistry.
    bool anyAttached() const;

    // ---- introspection ----
    // Test and debug only; generated code never calls these, and SV reaches them
    // only via explicit $c.  They let a regression test pin node accumulation
    // (otherwise visible only as memory growth) and the residue fold.
    //
    // Instance nodes still reachable from SV.  Under VM_COVERAGE this is smaller
    // than m_insts.size(), which also holds retained (dead) nodes.
    uint32_t liveInstanceCount() const;
    // Instances ever created, live or not.  Wraps after 4G instances, which no
    // introspection use cares about.
    uint32_t createdInstanceCount() const { return m_createdInsts; }
    // Instances that have died and contributed to the residue.
    uint32_t retiredInstanceCount() const { return static_cast<uint32_t>(m_retired.count); }
    // Mean coverage over the retired instances only, in 0..100; -1.0 if none.
    double retiredCoverage() const;
};

//=============================================================================
// VlCovRegistry
/// Every covergroup type and instance in one VerilatedContext.  Owned by the
/// VerilatedContext (not by the coverage database, which is only linked under
/// --coverage and is a *consumer* of this data), reached through
/// VerilatedContext::covergroupRegistryp().

class VlCovRegistry final : public VerilatedVirtualBase {
    // MEMBERS
    std::vector<std::unique_ptr<VlCovergroupType>> m_types;  // Creation order
    std::unordered_map<std::string, VlCovergroupType*> m_byName;  // Lookup, borrowed

    // PRIVATE METHODS
    VlCovergroupType* findType(const char* typeName) const;  // nullptr if unknown

public:
    // CONSTRUCTORS
    VlCovRegistry() = default;
    ~VlCovRegistry() override;
    VL_UNCOPYABLE(VlCovRegistry);

    // METHODS
    // Find-or-create the type node, then add an instance to it.  typeName is the
    // generated covergroup class name, already --protect-ids obfuscated, and is
    // the same string that keys the coverage database's hier/page.
    VlCovergroupInst* newCovergroupInst(const char* typeName);

    // ---- introspection (see VlCovergroupType) ----
    // typeName is the obfuscated generated name, so a test using these under
    // --protect-ids must pass the obfuscated string; the no-argument form does not.
    uint32_t liveInstanceCount() const;  // Summed over every type
    uint32_t createdInstanceCount() const;  // Summed over every type
    uint32_t liveInstanceCount(const char* typeName) const;  // 0 if type unknown
    uint32_t createdInstanceCount(const char* typeName) const;  // 0 if type unknown
    uint32_t retiredInstanceCount(const char* typeName) const;  // 0 if type unknown
    double retiredCoverage(const char* typeName) const;  // -1.0 if type unknown or none
};

//=============================================================================
// VlCovInstHandle
/// The generated covergroup class's link to its instance node.  Attach-counting:
/// the registry owns the node, but the handles are what keep it reachable, and
/// the last one to go retires it.
///
/// Must stay copyable: every generated clone() copy-constructs.  A copy shares
/// the node, and so the bin counts -- pre-existing covergroup-copy aliasing.
/// Attach counting makes that lifetime-safe, not correct.

class VlCovInstHandle final {
    // MEMBERS
    VlCovergroupInst* m_p = nullptr;  // Attach-counted; the registry owns the node

    // PRIVATE METHODS
    // Drop one attach count, retiring the node if that was the last handle.
    // Nothing may touch instp afterwards: retire() may have freed it.
    static void release(VlCovergroupInst* instp) {
        if (VL_UNCOVERABLE(!instp)) return;  // Never attach()ed; codegen always does
        if (instp->attachDec()) instp->typep()->retire(instp);
    }

public:
    // CONSTRUCTORS
    VlCovInstHandle() = default;
    VlCovInstHandle(const VlCovInstHandle& o)
        : m_p{o.m_p} {
        if (VL_UNCOVERABLE(!m_p)) return;  // Unbound source; see release above
        m_p->attachInc();
    }
    // Deleted, not implemented: nothing generates an assignment, and the
    // implicit one would copy m_p raw -- no attachInc, no release.
    VlCovInstHandle& operator=(const VlCovInstHandle&) = delete;
    ~VlCovInstHandle() { release(m_p); }

    // METHODS
    // Bind to a freshly created node, taking over the attach count of 1 it was
    // created with.  Called once, from the generated covergroup constructor.
    void attach(VlCovergroupInst* p) { m_p = p; }
    VlCovergroupInst* p() const { return m_p; }
};

#endif  // Guard
