// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Converting cyclic DFGs into acyclic DFGs
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2003-2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Dfg.h"
#include "V3DfgPasses.h"
#include "V3Error.h"
#include "V3Hash.h"

#include <algorithm>
#include <fstream>
#include <queue>
#include <unordered_map>
#include <vector>

VL_DEFINE_DEBUG_FUNCTIONS;

namespace V3DfgBreakCycles {

// Mutable map from vertices to the SCC index they belong to. Initialized
// from a proper analysis, then updated as we break cycles. After updates
// the information is consertvative, meaning a vertex that is marked as
// cyclic might not actually be if an SCC split into multple SCCs after a
// fixup. However it should always be true that if a vertex is thought to
// be non-cyclic based on this datastructure, then it indeed is not cyclic.
class SccInfo final {
    DfgGraph& m_dfg;  // The annotated graph
    // The map from vertices to their SCC index (0 if trivial SCC - non cyclic)
    std::unordered_map<const DfgVertex*, uint64_t> m_vtx2Scc;
    size_t m_nCyclicVertices = 0;  // Number of vertices in non-trivial SCCs

public:
    SccInfo(DfgGraph& dfg)
        : m_dfg{dfg} {
        // Initialize m_vtx2Scc for the graph from a proper analysis
        DfgUserMap<uint64_t> vtx2Scc = dfg.makeUserMap<uint64_t>();
        V3DfgPasses::colorStronglyConnectedComponents(dfg, vtx2Scc);
        m_dfg.forEachVertex([&](const DfgVertex& vtx) {
            const uint64_t sccIdx = vtx2Scc[vtx];
            m_vtx2Scc[&vtx] = sccIdx;
            if (sccIdx) ++m_nCyclicVertices;
        });
    }

    // Is the graph cyclic still?
    bool isCyclic() const { return m_nCyclicVertices; }

    // Returns the index of the SCC the given vertex is a part of
    // This is 0 iff the vertex is in a trivial SCC (no cycles through vertex)
    uint64_t get(const DfgVertex& vtx) const { return m_vtx2Scc.at(&vtx); }

    // Add a new vertex to graph that is part of the given SCC
    void add(const DfgVertex& vtx, uint64_t sccIdx) {
        const bool newEntry = m_vtx2Scc.emplace(&vtx, sccIdx).second;
        UASSERT_OBJ(newEntry, &vtx, "Vertex already inserted");
        if (sccIdx) ++m_nCyclicVertices;
    }

    bool stillCyclicFwd(const DfgVertex& vtx) const {
        // If it only reads non-cyclic vertices, it has also become acyclic
        return vtx.foreachSource([&](const DfgVertex& src) {  //
            return m_vtx2Scc.at(&src);
        });
    }

    bool stillCyclicBwd(const DfgVertex& vtx) const {
        // If itonly drives non-cyclic vertices, it has also become acyclic
        return vtx.foreachSink([&](const DfgVertex& dst) {  //
            return m_vtx2Scc.at(&dst);
        });
    }

    // The given vertex is known to have become acyclic after some edits,
    // propagate through graph to mark connected vertices as well.
    void updateAcyclic(const DfgVertex& vtx) {
        // Mark as acyclic
        uint64_t& sccIdxr = m_vtx2Scc.at(&vtx);
        UASSERT_OBJ(sccIdxr, &vtx, "Vertex should be cyclic");
        sccIdxr = 0;
        --m_nCyclicVertices;
        // Propagate the update through the graph forward
        vtx.foreachSink([&](const DfgVertex& dst) {
            // Sink was known to be acyclic, stop
            if (!m_vtx2Scc.at(&dst)) return false;
            if (!stillCyclicFwd(dst)) updateAcyclic(dst);
            return false;
        });
        // Propagate the update through the graph backward
        vtx.foreachSource([&](const DfgVertex& src) {
            // Source was known to be acyclic, stop
            if (!m_vtx2Scc.at(&src)) return false;
            if (!stillCyclicBwd(src)) updateAcyclic(src);
            return false;
        });
    }

    // Update after replacing 'vtxp' with 'replacement'
    void updateReplacement(const DfgVertex& vtx, DfgVertex& replacement) {
        updateAcyclic(vtx);
        if (!get(replacement)) {
            replacement.foreachSink([&](DfgVertex& dst) {
                if (!get(dst)) return false;
                if (!stillCyclicFwd(dst)) updateAcyclic(dst);
                return false;
            });
        }
    }

    /*
       Check stored information is consistent with actual SCCs. Note we
       can't detect during updates if an SCC has split into multiple SCCs.
       Consider:
          A -- E -- G
         / \       / \
        B   C     H   I
         \ /       \ /
          D -- F -- J
       If we fixed up E, the original SCC would split into two, (A,B,C,D)
       and (G,H,I,J), but also F would no longer be cyclic. For this reason,
       we can only assert that anything that we think is not cyclic based
       on the SccInfo must indeed be not cyclic, but might still think a
       vertex is cyclic based on the SccInfo but it actually isn't.
    */
    void validate() const {
        // Re-compute the actual SCCs
        DfgUserMap<uint64_t> actual = m_dfg.makeUserMap<uint64_t>();
        V3DfgPasses::colorStronglyConnectedComponents(m_dfg, actual);
        // Assert that if we think a vertex is not cyclic, it indeed is not
        m_dfg.forEachVertex([&](const DfgVertex& vtx) {
            // 'think not cyclic' implies 'actually not cyclic'
            UASSERT_OBJ(m_vtx2Scc.at(&vtx) || !actual.at(vtx), &vtx, "Inconsisten SccInfo");
        });
    }
};

class TraceDriver final : public DfgVisitor {
    // TYPES
    // Key for caching the result of a trace
    struct CacheKey final {
        DfgVertex* m_vtxp;
        uint32_t m_lsb;
        uint32_t m_msb;

        CacheKey() = delete;
        CacheKey(DfgVertex* vtxp, uint32_t lsb, uint32_t msb)
            : m_vtxp{vtxp}
            , m_lsb{lsb}
            , m_msb{msb} {}

        struct Hash final {
            size_t operator()(const CacheKey& item) const {
                // cppcheck-suppress unreadVariable
                V3Hash hash{item.m_vtxp};
                hash += item.m_lsb;
                hash += item.m_msb;
                return hash.value();
            }
        };

        struct Equal final {
            bool operator()(const CacheKey& a, const CacheKey& b) const {
                return a.m_vtxp == b.m_vtxp && a.m_lsb == b.m_lsb && a.m_msb == b.m_msb;
            }
        };
    };

    // STATE
    DfgGraph& m_dfg;  // The graph being processed
    SccInfo& m_sccInfo;  // The SccInfo instance
    // The strongly connected component we are currently trying to escape
    uint64_t m_component = 0;
    uint32_t m_lsb = 0;  // LSB to extract from the currently visited Vertex
    uint32_t m_msb = 0;  // MSB to extract from the currently visited Vertex
    std::vector<uint32_t> m_idxs;  // Indices to extract from the currently visited Vertex
    // Result of tracing the currently visited Vertex. Use SET_RESULT below!
    DfgVertex* m_resp = nullptr;
    DfgVertex* m_defaultp = nullptr;  // When tracing a variable, this is its 'defaultp', if any
    // Result cache for reusing already traced vertices
    std::unordered_map<CacheKey, DfgVertex*, CacheKey::Hash, CacheKey::Equal> m_cache;

#ifdef VL_DEBUG
    std::ofstream m_lineCoverageFile;  // Line coverage file, just for testing
#endif

    // METHODS

    // Create and return a new Vertex. Always use this to create new vertices.
    // Fileline is taken from 'refp', but 'refp' is otherwise not used.
    // Also adds the vertex to m_sccInfo with scc index 0, indicating the new
    // vertex is not part of a strongly connected component. This should always
    // be true, as all the vertices we create here are driven from outside the
    // component we are trying to escape, and will sink into that component.
    // Given those are separate SCCs, these new vertices must be acyclic.
    template <typename Vertex>
    Vertex* make(const DfgVertex* refp, uint32_t width) {
        static_assert(std::is_base_of<DfgVertex, Vertex>::value  //
                          && !std::is_base_of<DfgVertexVar, Vertex>::value,
                      "Should only make operation vertices and constants");

        if VL_CONSTEXPR_CXX17 (std::is_same<DfgConst, Vertex>::value) {
            DfgConst* const vtxp = new DfgConst{m_dfg, refp->fileline(), width, 0};
            m_sccInfo.add(*vtxp, 0);
            return reinterpret_cast<Vertex*>(vtxp);
        } else {
            // TODO: this is a gross hack around lack of C++17 'if constexpr' Vtx is always Vertex
            // when this code is actually executed, but needs a fudged type to type check when
            // Vertex is DfgConst, in which case this code is unreachable ...
            using Vtx = typename std::conditional<std::is_same<DfgConst, Vertex>::value, DfgSel,
                                                  Vertex>::type;
            Vtx* const vtxp = new Vtx{m_dfg, refp->fileline(), DfgDataType::packed(width)};
            m_sccInfo.add(*vtxp, 0);
            return reinterpret_cast<Vertex*>(vtxp);
        }
    }

    // Create temporary capable of holding the result of 'vtxp'
    DfgVertexVar* createTmp(const char* prefix, DfgVertex* vtxp) {
        AstNode* nodep = v3Global.rootp();
        const std::string name = m_dfg.makeUniqueName(prefix, nodep->user2Inc());
        FileLine* const flp = vtxp->fileline();
        DfgVertex::ScopeCache scopeCache;
        AstScope* const scopep = vtxp->scopep(scopeCache);
        DfgVertexVar* const varp = m_dfg.makeNewVar(flp, name, vtxp->dtype(), scopep);
        varp->vscp()->varp()->isInternal(true);
        varp->tmpForp(varp->vscp());
        m_sccInfo.add(*varp, 0);
        return varp;
    }

    // Trace drivers of the given packed vertex, at the given bit range.
    DfgVertex* trace(DfgVertex* const vtxp, const uint32_t msb, const uint32_t lsb) {
        UASSERT_OBJ(vtxp->isPacked(), vtxp, "Can only trace packed type vertices");
        UASSERT_OBJ(vtxp->size() > msb, vtxp, "Traced Vertex too narrow");

        // Get the cache entry, which is the resulting driver that is not part of
        // the same component as vtxp
        DfgVertex*& respr = m_cache
                                .emplace(std::piecewise_construct,  //
                                         std::forward_as_tuple(vtxp, msb, lsb),  //
                                         std::forward_as_tuple(nullptr))
                                .first->second;

        // Trace the vertex
        if (respr) {
            // If already traced this vtxp/msb/lsb, just use the result.
            // This is important to avoid combinatorial explosion when the
            // same sub-expression is needed multiple times.
        } else if (m_sccInfo.get(*vtxp) != m_component) {
            // If the currently traced vertex is in a different component,
            // then we found what we were looking for.
            respr = vtxp;
            // If the result is a splice, we need to insert a temporary for it
            // as a splice cannot be fed into arbitray logic
            if (DfgVertexSplice* const splicep = respr->cast<DfgVertexSplice>()) {
                DfgVertexVar* const tmpp = createTmp("TraceDriver", splicep);
                // Note: we can't do 'splicep->replaceWith(tmpp)', as other
                // variable sinks of the splice might have a defaultp driver.
                tmpp->srcp(splicep);
                respr = tmpp;
            }
            // Apply a Sel to extract the relevant bits if only a part is needed
            if (msb != respr->width() - 1 || lsb != 0) {
                DfgSel* const selp = make<DfgSel>(respr, msb - lsb + 1);
                selp->fromp(respr);
                selp->lsb(lsb);
                respr = selp;
            }
        } else {
            // Otherwise visit the vertex to trace it
            VL_RESTORER(m_msb);
            VL_RESTORER(m_lsb);
            VL_RESTORER_CLEAR(m_idxs);
            VL_RESTORER(m_resp);
            m_msb = msb;
            m_lsb = lsb;
            m_resp = nullptr;
            iterate(vtxp);
            respr = m_resp;
        }
        // We only ever trace drivers of bits that are known to be independent
        // of the cycles, so we should always be able to find an acyclic driver.
        UASSERT_OBJ(respr, vtxp, "Tracing driver failed for " << vtxp->typeName());
        UASSERT_OBJ(respr->width() == (msb - lsb + 1), vtxp, "Wrong result width");
        return respr;
    }

    // Trace drivers of the given array vertex, at the current m_idxs, m_msb, m_lsb.
    DfgVertex* traceSameIdx(DfgVertex* const vtxp) {
        UASSERT_OBJ(vtxp->isArray(), vtxp, "Should be an array vertex");
        UASSERT_OBJ(!m_idxs.empty(), vtxp, "Should have a pending index");
        VL_RESTORER(m_resp);
        m_resp = nullptr;
        iterate(vtxp);  // Resolve the element, the array visitors set 'm_resp'
        UASSERT_OBJ(m_resp, vtxp, "Tracing driver failed for " << vtxp->typeName());
        UASSERT_OBJ(m_resp->width() == (m_msb - m_lsb + 1), vtxp, "Wrong result width");
        return m_resp;
    }

    // Trace drivers of the given array vertex, pushing the given index, at current m_msb, m_lsb.
    DfgVertex* tracePushIdx(DfgVertex* const vtxp, const uint32_t idx) {
        const size_t nIdxs = m_idxs.size();
        m_idxs.push_back(idx);
        DfgVertex* const resp = traceSameIdx(vtxp);
        m_idxs.pop_back();
        UASSERT_OBJ(m_idxs.size() == nIdxs, vtxp, "Index stack size mismatch");
        return resp;
    }

    // Trace drivers of the given vertex, popping the innermost index, at current m_msb, m_lsb.
    DfgVertex* tracePopIdx(DfgVertex* const vtxp) {
        UASSERT_OBJ(!m_idxs.empty(), vtxp, "Should have a pending index");
        const size_t nIdxs = m_idxs.size();
        const uint32_t idx = m_idxs.back();
        m_idxs.pop_back();
        DfgVertex* const resp = m_idxs.empty() ? trace(vtxp, m_msb, m_lsb) : traceSameIdx(vtxp);
        m_idxs.push_back(idx);
        UASSERT_OBJ(m_idxs.size() == nIdxs, vtxp, "Index stack size mismatch");
        return resp;
    }

    template <typename Vertex>
    Vertex* traceBitwiseBinary(Vertex* vtxp) {
        static_assert(std::is_base_of<DfgVertexBinary, Vertex>::value,
                      "Should only call on DfgVertexBinary");
        Vertex* const resp = make<Vertex>(vtxp, m_msb - m_lsb + 1);
        resp->rhsp(trace(vtxp->rhsp(), m_msb, m_lsb));
        resp->lhsp(trace(vtxp->lhsp(), m_msb, m_lsb));
        return resp;
    }

    template <typename Vertex>
    DfgVertex* traceAddSub(Vertex* vtxp) {
        static_assert(std::is_base_of<DfgVertexBinary, Vertex>::value,
                      "Should only call on DfgVertexBinary");
        Vertex* const opp = make<Vertex>(vtxp, m_msb + 1);
        opp->rhsp(trace(vtxp->rhsp(), m_msb, 0));
        opp->lhsp(trace(vtxp->lhsp(), m_msb, 0));
        DfgSel* const selp = make<DfgSel>(vtxp, m_msb - m_lsb + 1);
        selp->fromp(opp);
        selp->lsb(m_lsb);
        return selp;
    }

    template <typename Vertex>
    Vertex* traceReduction(Vertex* vtxp) {
        static_assert(std::is_base_of<DfgVertexUnary, Vertex>::value,
                      "Should only call on DfgVertexUnary");
        Vertex* const resp = make<Vertex>(vtxp, 1);
        resp->srcp(trace(vtxp->srcp(), vtxp->srcp()->width() - 1, 0));
        return resp;
    }

    template <typename Vertex>
    Vertex* traceCmp(Vertex* vtxp) {
        static_assert(std::is_base_of<DfgVertexBinary, Vertex>::value,
                      "Should only call on DfgVertexBinary");
        Vertex* const resp = make<Vertex>(vtxp, m_msb - m_lsb + 1);
        resp->rhsp(trace(vtxp->rhsp(), vtxp->rhsp()->width() - 1, 0));
        resp->lhsp(trace(vtxp->lhsp(), vtxp->lhsp()->width() - 1, 0));
        return resp;
    }

    // Use this macro to set the result in 'visit' methods. This also emits
    // a line to m_lineCoverageFile for testing.
    // TODO: Use C++20 std::source_location instead of a macro
#ifdef VL_DEBUG
#define SET_RESULT(vtxp) \
    do { \
        m_resp = vtxp; \
        if (VL_UNLIKELY(m_lineCoverageFile.is_open())) m_lineCoverageFile << __LINE__ << '\n'; \
    } while (false)
#else
#define SET_RESULT(vtxp) m_resp = vtxp;
#endif

    // VISITORS
    void visit(DfgVertex* vtxp) override {  // LCOV_EXCL_START
        vtxp->v3fatalSrc("TraceDriver - Unhandled vertex type: " << vtxp->typeName());
    }  // LCOV_EXCL_STOP

    void visit(DfgSplicePacked* vtxp) override {
        struct Driver final {
            DfgVertex* m_vtxp;
            uint32_t m_lsb;  // LSB of driven range (internal, not Verilog)
            uint32_t m_msb;  // MSB of driven range (internal, not Verilog)
            Driver() = delete;
            Driver(DfgVertex* vtxp, uint32_t lsb, uint32_t msb)
                : m_vtxp{vtxp}
                , m_lsb{lsb}
                , m_msb{msb} {}
        };
        std::vector<Driver> drivers;

        // Look at all the drivers, one might cover the whole range, but also gather all drivers
        bool tryWholeDefault = m_defaultp;
        const bool done = vtxp->foreachDriver([&](DfgVertex& src, uint32_t lsb) {
            const uint32_t msb = lsb + src.width() - 1;
            drivers.emplace_back(&src, lsb, msb);
            // Check if this driver covers any of the bits, then we can't use whole default
            if (m_msb >= lsb && msb >= m_lsb) tryWholeDefault = false;
            // If it does not cover the whole searched bit range, move on
            if (m_lsb < lsb || msb < m_msb) return false;
            // Driver covers whole search range, trace that and we are done
            SET_RESULT(trace(&src, m_msb - lsb, m_lsb - lsb));
            return true;
        });
        if (done) return;

        // Trace the default driver if no other drivers cover the searched range
        if (tryWholeDefault) {
            SET_RESULT(trace(m_defaultp, m_msb, m_lsb));
            return;
        }

        // Hard case: We need to combine multiple drivers to produce the searched bit range

        // Sort drivers (they are non-overlapping)
        std::sort(drivers.begin(), drivers.end(), [](const Driver& a, const Driver& b) {  //
            return a.m_lsb < b.m_lsb;
        });

        // Gather terms
        std::vector<DfgVertex*> termps;
        uint32_t lsb = m_lsb;
        for (const Driver& driver : drivers) {
            // Driver is below the searched LSB, move on
            if (lsb > driver.m_msb) continue;
            // Driver is above the searched MSB, done
            if (driver.m_lsb > m_msb) break;
            // Gap below this driver, trace default to fill it
            if (driver.m_lsb > lsb) {
                UASSERT_OBJ(m_defaultp, vtxp, "Should have a default driver if needs tracing");
                termps.emplace_back(trace(m_defaultp, driver.m_lsb - 1, lsb));
                lsb = driver.m_lsb;
            }
            // Driver covers searched range, pick the needed/available bits
            const uint32_t lim = std::min(m_msb, driver.m_msb);
            termps.emplace_back(trace(driver.m_vtxp, lim - driver.m_lsb, lsb - driver.m_lsb));
            lsb = lim + 1;
        }
        if (m_msb >= lsb) {
            UASSERT_OBJ(m_defaultp, vtxp, "Should have a default driver if needs tracing");
            termps.emplace_back(trace(m_defaultp, m_msb, lsb));
        }

        // The earlier cheks cover the case when either a whole driver or the default covers
        // the whole range, so there should be at least 2 terms required here.
        UASSERT_OBJ(termps.size() >= 2, vtxp, "Should have returned in special cases");

        // Concatenate all terms and set result
        DfgVertex* resp = termps.front();
        for (size_t i = 1; i < termps.size(); ++i) {
            DfgVertex* const termp = termps[i];
            DfgConcat* const catp = make<DfgConcat>(termp, resp->width() + termp->width());
            catp->rhsp(resp);
            catp->lhsp(termp);
            resp = catp;
        }
        SET_RESULT(resp);
    }

    void visit(DfgSpliceArray* vtxp) override {
        // Explicit per-element driver (a UnitArray wrapping the element value)
        if (DfgVertex* const driverp = vtxp->driverAt(m_idxs.back())) {
            // Consume this index, then trace the element value
            SET_RESULT(tracePopIdx(driverp->as<DfgUnitArray>()->srcp()));
            return;
        }
        // TODO: this is unreachable, as syntheis can't create it today.
        // // Element not driven explicitly, so it comes from the default array. Keep the
        // // index pending (the default is the whole array, indexed the same way) and
        // // continue tracing it.
        // UASSERT_OBJ(m_defaultp, vtxp, "Independent array element should have a driver or
        // default"); SET RESULT(traceSameIdx(m_defaultp));
    }

    void visit(DfgVertexVar* vtxp) override {
        UASSERT_OBJ(!vtxp->isVolatile(), vtxp, "Should not trace through volatile variable");
        VL_RESTORER(m_defaultp);
        m_defaultp = vtxp->defaultp();
        DfgVertex* const drvp = vtxp->srcp() ? vtxp->srcp() : m_defaultp;
        UASSERT_OBJ(drvp, vtxp, "Should not have to trace undriven variable");
        // Packed variable: trace the driver. Array variable: continue navigating it at
        // the pending element (both at the same bit range).
        SET_RESULT(m_idxs.empty() ? trace(drvp, m_msb, m_lsb) : traceSameIdx(drvp));
    }

    void visit(DfgArraySel* vtxp) override {
        // If constant index, push it and trace the selected element through the array
        // structure of 'fromp'. This handles arbitrarily nested (multi-dimensional)
        // arrays, as each nested ArraySel pushes a further index.
        if (const DfgConst* const idxp = vtxp->bitp()->cast<DfgConst>()) {
            SET_RESULT(tracePushIdx(vtxp->fromp(), idxp->toU32()));
            return;
        }

        // If index is not constant, independence was proven only if the 'fromp' is
        // independent, so no need to trace that, just reference it with the traced
        // index. This only happens at the packed ArraySel leaf.
        UASSERT_OBJ(m_idxs.empty(), vtxp, "Non-constant index below an outer array index");
        DfgArraySel* const resp = make<DfgArraySel>(vtxp, vtxp->width());
        resp->fromp(vtxp->fromp());
        resp->bitp(trace(vtxp->bitp(), vtxp->bitp()->width() - 1, 0));
        DfgSel* const selp = make<DfgSel>(vtxp, m_msb - m_lsb + 1);
        selp->fromp(resp);
        selp->lsb(m_lsb);
        SET_RESULT(selp);
    }

    void visit(DfgUnitArray* vtxp) override {
        // Single-element array adapter, the pending index must be 0, unwrap the element
        UASSERT_OBJ(m_idxs.back() == 0, vtxp, "UnitArray element index should be 0");
        SET_RESULT(tracePopIdx(vtxp->srcp()));
    }

    void visit(DfgConcat* vtxp) override {
        DfgVertex* const rhsp = vtxp->rhsp();
        DfgVertex* const lhsp = vtxp->lhsp();
        const uint32_t rWidth = rhsp->width();
        // If the traced bits are wholly in the RHS
        if (rWidth > m_msb) {
            SET_RESULT(trace(rhsp, m_msb, m_lsb));
            return;
        }
        // If the traced bits are wholly in the LHS
        if (m_lsb >= rWidth) {
            SET_RESULT(trace(lhsp, m_msb - rWidth, m_lsb - rWidth));
            return;
        }
        // The traced bit spans both sides, trace both
        DfgConcat* const resp = make<DfgConcat>(vtxp, m_msb - m_lsb + 1);
        resp->rhsp(trace(rhsp, rWidth - 1, m_lsb));
        resp->lhsp(trace(lhsp, m_msb - rWidth, 0));
        SET_RESULT(resp);
    }

    void visit(DfgRep* vtxp) override {
        DfgVertex* const srcp = vtxp->srcp();
        const uint32_t sWidth = srcp->width();
        // If we need more bits than the source, then we need the whole source
        if (m_msb - m_lsb + 1 > sWidth) {
            DfgRep* const repp = make<DfgRep>(vtxp, vtxp->width());
            repp->srcp(trace(srcp, sWidth - 1, 0));
            DfgSel* const resp = make<DfgSel>(vtxp, m_msb - m_lsb + 1);
            resp->fromp(repp);
            resp->lsb(m_lsb);
            SET_RESULT(resp);
            return;
        }
        // If the requested bits are within the same repliacted word
        if (m_msb / sWidth == m_lsb / sWidth) {
            SET_RESULT(trace(srcp, m_msb % sWidth, m_lsb % sWidth));
            return;
        }
        // The requested bits span two replicated words
        DfgConcat* const resp = make<DfgConcat>(vtxp, m_msb - m_lsb + 1);
        resp->rhsp(trace(srcp, sWidth - 1, m_lsb % sWidth));
        resp->lhsp(trace(srcp, m_msb % sWidth, 0));
        SET_RESULT(resp);
    }

    void visit(DfgExtend* vtxp) override {
        DfgVertex* const srcp = vtxp->srcp();
        const uint32_t sWidth = srcp->width();
        // If the traced bits are wholly in the input
        if (sWidth > m_msb) {
            SET_RESULT(trace(srcp, m_msb, m_lsb));
            return;
        }
        // If the traced bits are wholly in the extension
        if (m_lsb >= sWidth) {
            SET_RESULT(make<DfgConst>(vtxp, m_msb - m_lsb + 1));
            return;
        }
        // The traced bits span both sides
        DfgExtend* const resp = make<DfgExtend>(vtxp, m_msb - m_lsb + 1);
        resp->srcp(trace(srcp, sWidth - 1, m_lsb));
        SET_RESULT(resp);
    }

    void visit(DfgExtendS* vtxp) override {
        DfgVertex* const srcp = vtxp->srcp();
        const uint32_t sWidth = srcp->width();
        // If the traced bits are wholly in the input
        if (sWidth > m_msb) {
            SET_RESULT(trace(srcp, m_msb, m_lsb));
            return;
        }
        // If the traced bits are wholly in the extension
        if (m_lsb >= sWidth) {
            DfgVertex* const sp = trace(srcp, sWidth - 1, sWidth - 1);
            if (m_msb == m_lsb) {
                SET_RESULT(sp);
            } else {
                DfgExtendS* const resp = make<DfgExtendS>(vtxp, m_msb - m_lsb + 1);
                resp->srcp(sp);
                SET_RESULT(resp);
            }
            return;
        }
        // The traced bits span both sides
        DfgExtendS* const resp = make<DfgExtendS>(vtxp, m_msb - m_lsb + 1);
        resp->srcp(trace(srcp, sWidth - 1, m_lsb));
        SET_RESULT(resp);
    }

    void visit(DfgSel* vtxp) override {
        const uint32_t lsb = vtxp->lsb();
        SET_RESULT(trace(vtxp->srcp(), m_msb + lsb, m_lsb + lsb));
    }

    void visit(DfgNot* vtxp) override {
        DfgNot* const resp = make<DfgNot>(vtxp, m_msb - m_lsb + 1);
        resp->srcp(trace(vtxp->srcp(), m_msb, m_lsb));
        SET_RESULT(resp);
    }

    void visit(DfgAnd* vtxp) override { SET_RESULT(traceBitwiseBinary(vtxp)); }
    void visit(DfgOr* vtxp) override { SET_RESULT(traceBitwiseBinary(vtxp)); }
    void visit(DfgXor* vtxp) override { SET_RESULT(traceBitwiseBinary(vtxp)); }
    void visit(DfgAdd* vtxp) override { SET_RESULT(traceAddSub(vtxp)); }
    void visit(DfgSub* vtxp) override { SET_RESULT(traceAddSub(vtxp)); }
    void visit(DfgRedAnd* vtxp) override { SET_RESULT(traceReduction(vtxp)); }
    void visit(DfgRedOr* vtxp) override { SET_RESULT(traceReduction(vtxp)); }
    void visit(DfgRedXor* vtxp) override { SET_RESULT(traceReduction(vtxp)); }
    void visit(DfgEq* vtxp) override { SET_RESULT(traceCmp(vtxp)); }
    void visit(DfgNeq* vtxp) override { SET_RESULT(traceCmp(vtxp)); }
    void visit(DfgLt* vtxp) override { SET_RESULT(traceCmp(vtxp)); }
    void visit(DfgLte* vtxp) override { SET_RESULT(traceCmp(vtxp)); }
    void visit(DfgGt* vtxp) override { SET_RESULT(traceCmp(vtxp)); }
    void visit(DfgGte* vtxp) override { SET_RESULT(traceCmp(vtxp)); }

    void visit(DfgShiftRS* vtxp) override {
        DfgVertex* const lhsp = vtxp->lhsp();
        if (const DfgConst* const rConstp = vtxp->rhsp()->cast<DfgConst>()) {
            const uint32_t shiftAmnt = rConstp->toU32();
            // Width of lower half of result
            const uint32_t lowerWidth = shiftAmnt > vtxp->width() ? 0 : vtxp->width() - shiftAmnt;
            // If the traced bits are wholly in the input
            if (lowerWidth > m_msb) {
                SET_RESULT(trace(lhsp, m_msb + shiftAmnt, m_lsb + shiftAmnt));
                return;
            }
            // If the traced bits are wholly in the extension
            if (m_lsb >= lowerWidth) {
                DfgExtendS* const resp = make<DfgExtendS>(vtxp, m_msb - m_lsb + 1);
                resp->srcp(trace(lhsp, lhsp->width() - 1, lhsp->width() - 1));
                SET_RESULT(resp);
                return;
            }
            // The traced bits span both sides
            DfgExtendS* const resp = make<DfgExtendS>(vtxp, m_msb - m_lsb + 1);
            resp->srcp(trace(lhsp, lowerWidth - 1 + shiftAmnt, m_lsb + shiftAmnt));
            SET_RESULT(resp);
            return;
        }

        DfgShiftRS* const shiftrsp = make<DfgShiftRS>(vtxp, vtxp->lhsp()->width() - m_lsb);
        shiftrsp->rhsp(trace(vtxp->rhsp(), vtxp->rhsp()->width() - 1, 0));
        shiftrsp->lhsp(trace(vtxp->lhsp(), vtxp->lhsp()->width() - 1, m_lsb));
        if (m_msb == vtxp->lhsp()->width() - 1) {
            SET_RESULT(shiftrsp);
            return;
        }
        DfgSel* const selp = make<DfgSel>(vtxp, m_msb - m_lsb + 1);
        selp->fromp(shiftrsp);
        selp->lsb(0);
        SET_RESULT(selp);
    }

    void visit(DfgShiftR* vtxp) override {
        DfgVertex* const lhsp = vtxp->lhsp();
        if (const DfgConst* const rConstp = vtxp->rhsp()->cast<DfgConst>()) {
            const uint32_t shiftAmnt = rConstp->toU32();
            // Width of lower half of result
            const uint32_t lowerWidth = shiftAmnt > vtxp->width() ? 0 : vtxp->width() - shiftAmnt;
            // If the traced bits are wholly in the input
            if (lowerWidth > m_msb) {
                SET_RESULT(trace(lhsp, m_msb + shiftAmnt, m_lsb + shiftAmnt));
                return;
            }
            // If the traced bits are wholly in the extension
            if (m_lsb >= lowerWidth) {
                SET_RESULT(make<DfgConst>(vtxp, m_msb - m_lsb + 1));
                return;
            }
            // The traced bits span both sides
            DfgExtend* const resp = make<DfgExtend>(vtxp, m_msb - m_lsb + 1);
            resp->srcp(trace(lhsp, lowerWidth - 1 + shiftAmnt, m_lsb + shiftAmnt));
            SET_RESULT(resp);
            return;
        }

        DfgShiftR* const shiftrp = make<DfgShiftR>(vtxp, vtxp->lhsp()->width() - m_lsb);
        shiftrp->rhsp(trace(vtxp->rhsp(), vtxp->rhsp()->width() - 1, 0));
        shiftrp->lhsp(trace(vtxp->lhsp(), vtxp->lhsp()->width() - 1, m_lsb));
        if (m_msb == vtxp->lhsp()->width() - 1) {
            SET_RESULT(shiftrp);
            return;
        }
        DfgSel* const selp = make<DfgSel>(vtxp, m_msb - m_lsb + 1);
        selp->fromp(shiftrp);
        selp->lsb(0);
        SET_RESULT(selp);
    }

    void visit(DfgShiftL* vtxp) override {
        DfgVertex* const lhsp = vtxp->lhsp();
        if (const DfgConst* const rConstp = vtxp->rhsp()->cast<DfgConst>()) {
            const uint32_t shiftAmnt = rConstp->toU32();
            // Width of lower half of result
            const uint32_t lowerWidth = shiftAmnt > vtxp->width() ? vtxp->width() : shiftAmnt;
            // If the traced bits are wholly in the input
            if (m_lsb >= lowerWidth) {
                SET_RESULT(trace(lhsp, m_msb - shiftAmnt, m_lsb - shiftAmnt));
                return;
            }
            // If the traced bits are wholly in the extension
            if (lowerWidth > m_msb) {
                SET_RESULT(make<DfgConst>(vtxp, m_msb - m_lsb + 1));
                return;
            }
            // The traced bits span both sides
            DfgConcat* const resp = make<DfgConcat>(vtxp, m_msb - m_lsb + 1);
            resp->rhsp(make<DfgConst>(vtxp, resp->width() - (m_msb - lowerWidth + 1)));
            resp->lhsp(trace(lhsp, m_msb - shiftAmnt, lowerWidth - shiftAmnt));
            SET_RESULT(resp);
            return;
        }

        DfgShiftL* const shiftlp = make<DfgShiftL>(vtxp, m_msb + 1);
        shiftlp->rhsp(trace(vtxp->rhsp(), vtxp->rhsp()->width() - 1, 0));
        shiftlp->lhsp(trace(vtxp->lhsp(), m_msb, 0));
        if (m_lsb == 0) {
            SET_RESULT(shiftlp);
            return;
        }
        DfgSel* const selp = make<DfgSel>(vtxp, m_msb - m_lsb + 1);
        selp->fromp(shiftlp);
        selp->lsb(m_lsb);
        SET_RESULT(selp);
    }

    void visit(DfgCond* vtxp) override {
        DfgCond* const resp = make<DfgCond>(vtxp, m_msb - m_lsb + 1);
        resp->condp(trace(vtxp->condp(), vtxp->condp()->width() - 1, 0));
        resp->thenp(trace(vtxp->thenp(), m_msb, m_lsb));
        resp->elsep(trace(vtxp->elsep(), m_msb, m_lsb));
        SET_RESULT(resp);
    }

    void visit(DfgMatchMasked* vtxp) override {
        DfgMatchMasked* const resp = make<DfgMatchMasked>(vtxp, vtxp->width());
        resp->lhsp(trace(vtxp->lhsp(), vtxp->lhsp()->width() - 1, 0));
        resp->matchp(trace(vtxp->matchp(), vtxp->matchp()->width() - 1, 0));
        DfgSel* const selp = make<DfgSel>(vtxp, m_msb - m_lsb + 1);
        selp->fromp(resp);
        selp->lsb(m_lsb);
        SET_RESULT(selp);
    }

#undef SET_RESULT

public:
    // CONSTRUCTOR
    TraceDriver(DfgGraph& dfg, SccInfo& sccInfo)
        : m_dfg{dfg}
        , m_sccInfo{sccInfo} {
#ifdef VL_DEBUG
        if (v3Global.opt.debugCheck()) {
            m_lineCoverageFile.open(  //
                v3Global.opt.makeDir() + "/" + v3Global.opt.prefix()
                    + "__V3DfgBreakCycles-TraceDriver-line-coverage.txt",  //
                std::ios_base::out | std::ios_base::app);
        }
#endif
    }

    // Given a Vertex that is part of an SCC, return a vertex that is equivalent
    // to 'vtxp[lsb +: width]', but is not part of the same SCC. This should only
    // be called if the bit range is known to be independent of the SCC, so the
    // trace can always succeed.
    DfgVertex* apply(DfgVertex& vtx, uint32_t lsb, uint32_t width) {
        VL_RESTORER(m_component);
        m_component = m_sccInfo.get(vtx);
        return trace(&vtx, lsb + width - 1, lsb);
    }
};

// A bit mask for each bit in a value, which can be either packed or aggregate type
class BitMask final {
    // TYPES
    const DfgDataType& m_dtype;
    union {
        V3Number m_num;  // The bits, if packed
        std::vector<BitMask> m_sub;  // The per element masks, if aggregate
    };

public:
    // CONSTRUCTOR
    BitMask(FileLine* flp, const DfgDataType& dtype)
        : m_dtype{dtype} {
        UASSERT_OBJ(!m_dtype.isNull(), flp, "Expected non-null data type");
        if (m_dtype.isPacked()) {
            new (&m_num) V3Number{flp, static_cast<int>(m_dtype.size()), 0};
        } else {
            new (&m_sub) std::vector<BitMask>{};
            m_sub.reserve(m_dtype.size());
            for (uint32_t i = 0; i < m_dtype.size(); ++i)
                m_sub.emplace_back(flp, m_dtype.elemDtype());
        }
    }
    BitMask(const DfgVertex& vtx)
        : BitMask{vtx.fileline(), vtx.dtype()} {}
    BitMask(const BitMask& other)
        : m_dtype{other.m_dtype} {
        if (m_dtype.isPacked()) {
            new (&m_num) V3Number{other.m_num};
        } else {
            new (&m_sub) std::vector<BitMask>{other.m_sub};
        }
    }
    BitMask& operator=(const BitMask& other) {
        if (this != &other) {
            UASSERT(m_dtype == other.m_dtype, "Expected same data type");
            if (other.m_dtype.isPacked()) {
                m_num = other.m_num;
            } else {
                m_sub = other.m_sub;
            }
        }
        return *this;
    }
    ~BitMask() {
        if (m_dtype.isPacked()) {
            m_num.~V3Number();
        } else {
            m_sub.~vector<BitMask>();
        }
    }

    // METHODS
    V3Number& num() {
        UASSERT(m_dtype.isPacked(), "Expected packed data type");
        return m_num;
    }
    const V3Number& num() const {
        UASSERT(m_dtype.isPacked(), "Expected packed data type");
        return m_num;
    }
    std::vector<BitMask>& sub() {
        UASSERT(m_dtype.isArray(), "Expected array data type");
        return m_sub;
    }

    bool isZero() const {
        if (m_dtype.isPacked()) return m_num.isEqZero();

        for (const BitMask& sub : m_sub) {
            if (!sub.isZero()) return false;
        }
        return true;
    }
    bool isOnes() const {
        if (m_dtype.isPacked()) return m_num.isEqAllOnes();

        for (const BitMask& sub : m_sub) {
            if (!sub.isOnes()) return false;
        }
        return true;
    }
    void setZero() {
        if (m_dtype.isPacked()) {
            m_num.setAllBits0();
        } else {
            for (BitMask& sub : m_sub) sub.setZero();
        }
    }
    void setOnes() {
        if (m_dtype.isPacked()) {
            m_num.setAllBits1();
        } else {
            for (BitMask& sub : m_sub) sub.setOnes();
        }
    }

    bool operator==(const BitMask& other) const {
        UASSERT(m_dtype == other.m_dtype, "Expected same data type");
        if (m_dtype.isPacked()) return m_num.isCaseEq(other.m_num);
        return m_sub == other.m_sub;
    }
    bool operator!=(const BitMask& other) const { return !(*this == other); }

    // 'this' has a clear bit where 'that' has a set bit, that is,
    // 'this' has a proper subset of bits set compared to 'that'.
    bool isContractionOf(const BitMask& that) const {
        UASSERT(m_dtype == that.m_dtype, "Expected same data type");
        if (m_dtype.isPacked()) {
            const size_t words = VL_WORDS_I(m_dtype.size());
            for (size_t i = 0; i < words; ++i) {
                if (~m_num.edataWord(i) & that.m_num.edataWord(i)) return true;
            }
            return false;
        }

        UASSERT(m_dtype.isArray(), "Expected array data type");
        for (size_t i = 0; i < m_sub.size(); ++i) {
            if (m_sub[i].isContractionOf(that.m_sub[i])) return true;
        }
        return false;
    }

    std::string toString() const {
        if (m_dtype.isPacked()) return "0x" + m_num.displayed(m_num.fileline(), "%x");
        std::string result;
        result += "{";
        for (const BitMask& sub : m_sub) {
            if (&sub != &m_sub.front()) result += ", ";
            result += sub.toString();
        }
        result += "}";
        return result;
    }
};

class IndependentBits final : public DfgVisitor {
    // TYPES
    struct VertexState final {
        size_t m_rpoNumber = 0;  // Reverse Postorder Number of vertex
        bool m_isOnWorkList = false;  // Whether the vertex is on the work list
    };

    // STATE
    const SccInfo& m_sccInfo;  // The SccInfo instance
    // Vertex to current bit mask map. The mask is set for the bits that are independent of the SCC
    std::unordered_map<const DfgVertex*, BitMask> m_vtxp2Mask;
    // Work list for the traversal (min-queue of vertex RPO numbers)
    std::priority_queue<size_t, std::vector<size_t>, std::greater<size_t>> m_workQueue;
    std::unordered_map<const DfgVertex*, VertexState> m_vtxp2State;  // State of each vertex

#ifdef VL_DEBUG
    std::ofstream m_lineCoverageFile;  // Line coverage file, just for testing
#endif

    // METHODS

    // Retrieve the mask for the given vertex (create it with value 0 if needed)
    BitMask& mask(const DfgVertex& vtx) {
        // Look up (or create) mask for 'vtx'
        return m_vtxp2Mask
            .emplace(std::piecewise_construct,  //
                     std::forward_as_tuple(&vtx), std::forward_as_tuple(vtx))
            .first->second;
    }

    // Use this macro to call 'mask' in 'visit' methods. This also emits
    // a line to m_lineCoverageFile for testing.
    // TODO: Use C++20 std::source_location instead of a macro
#ifdef VL_DEBUG
#define MASK(vtxp) \
    ([this](const DfgVertex& vtx) -> BitMask& { \
        if (VL_UNLIKELY(m_lineCoverageFile.is_open())) m_lineCoverageFile << __LINE__ << '\n'; \
        return mask(vtx); \
    }(*vtxp))
#else
#define MASK(vtxp) mask(*vtxp)
#endif

    // Clear all bits at or below the most significant clear bit
    void floodTowardsLsb(V3Number& num) {
        for (int i = num.width() - 1; i >= 0; --i) {
            if (num.bitIs1(i)) continue;
            num.opSetRange(0, i + 1, '0');
            break;
        }
    }

    // Clear all bits at or above the least significant clear bit
    void floodTowardsMsb(V3Number& num) {
        for (int i = 0; i < num.width(); ++i) {
            if (num.bitIs1(i)) continue;
            num.opSetRange(i, num.width() - i, '0');
            break;
        }
    }

    void propagateFromDriver(BitMask& m, const DfgVertex* srcp) {
        // If there is no driver, we are done
        if (!srcp) return;
        // If it is driven by a splice, we need to combine the masks of the drivers
        if (const DfgSplicePacked* const splicep = srcp->cast<DfgSplicePacked>()) {
            splicep->foreachDriver([&](const DfgVertex& src, uint32_t lo) {
                m.num().opSelInto(MASK(&src).num(), lo, src.width());
                return false;
            });
            return;
        }
        if (const DfgSpliceArray* const splicep = srcp->cast<DfgSpliceArray>()) {
            splicep->foreachDriver([&](const DfgVertex& src, uint32_t lo) {
                if (const DfgUnitArray* const uap = src.cast<DfgUnitArray>()) {
                    m.sub().at(lo) = MASK(uap->srcp());
                } else {
                    // m.sub().at(lo) = Can't happen MASK(&src);
                }
                return false;
            });
            return;
        }
        // Otherwise, we just use the mask of the single driver
        m = MASK(srcp);
    }

    // VISITORS
    void visit(DfgVertex* vtxp) override {  // LCOV_EXCL_START
        UINFO(9, "IndependentBits - Unhandled vertex type: " << vtxp->typeName());
        // Conservative assumption about all bits being dependent prevails
    }  // LCOV_EXCL_STOP

    void visit(DfgVertexVar* vtxp) override {
        // We cannot trace through a volatile variable, so pretend all bits are dependent
        if (vtxp->isVolatile()) return;

        BitMask& m = MASK(vtxp);
        DfgVertex* const srcp = vtxp->srcp();
        DfgVertex* const defaultp = vtxp->defaultp();
        // If there is a default driver, we start from that
        if (defaultp) m = MASK(defaultp);
        // Then propagate mask from the driver
        propagateFromDriver(m, srcp);
    }

    void visit(DfgVertexSplice* vtxp) override {
        propagateFromDriver(MASK(vtxp), vtxp);  // Needed to continue traversal
    }

    void visit(DfgUnitArray* vtxp) override { MASK(vtxp).sub().at(0) = MASK(vtxp->srcp()); }

    void visit(DfgArraySel* vtxp) override {
        DfgVertex* const fromp = vtxp->fromp();

        // If constant index, copy mask of relevant element
        if (const DfgConst* const idxp = vtxp->bitp()->cast<DfgConst>()) {
            MASK(vtxp) = MASK(vtxp->fromp()).sub().at(idxp->toSizeT());
            return;
        }

        // If index is not constant, independent only if the index is indenpendent, and the array
        // is independent. TODO: could relax by '&' reducing, not sure if worth it.
        if (MASK(vtxp->bitp()).isOnes() && MASK(fromp).isOnes()) MASK(vtxp).setOnes();
    }

    void visit(DfgConcat* vtxp) override {
        const DfgVertex* const rhsp = vtxp->rhsp();
        const DfgVertex* const lhsp = vtxp->lhsp();
        V3Number& m = MASK(vtxp).num();
        m.opSelInto(MASK(rhsp).num(), 0, rhsp->width());
        m.opSelInto(MASK(lhsp).num(), rhsp->width(), lhsp->width());
    }

    void visit(DfgRep* vtxp) override {
        const uint32_t count = vtxp->count();
        const DfgVertex* const srcp = vtxp->srcp();
        const uint32_t sWidth = srcp->width();
        V3Number& vMask = MASK(vtxp).num();
        V3Number& sMask = MASK(srcp).num();
        for (uint32_t i = 0; i < count; ++i) vMask.opSelInto(sMask, i * sWidth, sWidth);
    }

    void visit(DfgSel* vtxp) override {
        const uint32_t lsb = vtxp->lsb();
        const uint32_t msb = lsb + vtxp->width() - 1;
        MASK(vtxp).num().opSel(MASK(vtxp->fromp()).num(), msb, lsb);
    }

    void visit(DfgExtend* vtxp) override {
        const DfgVertex* const srcp = vtxp->srcp();
        const uint32_t sWidth = srcp->width();
        V3Number& s = MASK(srcp).num();
        V3Number& m = MASK(vtxp).num();
        m.opSelInto(s, 0, sWidth);
        m.opSetRange(sWidth, vtxp->width() - sWidth, '1');
    }
    void visit(DfgExtendS* vtxp) override {
        const DfgVertex* const srcp = vtxp->srcp();
        const uint32_t sWidth = srcp->width();
        V3Number& s = MASK(srcp).num();
        V3Number& m = MASK(vtxp).num();
        m.opSelInto(s, 0, sWidth);
        m.opSetRange(sWidth, vtxp->width() - sWidth, s.bitIs0(sWidth - 1) ? '0' : '1');
    }

    void visit(DfgNot* vtxp) override {  //
        MASK(vtxp) = MASK(vtxp->srcp());
    }

    void visit(DfgAnd* vtxp) override {  //
        MASK(vtxp).num().opAnd(MASK(vtxp->lhsp()).num(), MASK(vtxp->rhsp()).num());
    }
    void visit(DfgOr* vtxp) override {  //
        MASK(vtxp).num().opAnd(MASK(vtxp->lhsp()).num(), MASK(vtxp->rhsp()).num());
    }
    void visit(DfgXor* vtxp) override {  //
        MASK(vtxp).num().opAnd(MASK(vtxp->lhsp()).num(), MASK(vtxp->rhsp()).num());
    }

    void visit(DfgAdd* vtxp) override {
        V3Number& m = MASK(vtxp).num();
        m.opAnd(MASK(vtxp->lhsp()).num(), MASK(vtxp->rhsp()).num());
        floodTowardsMsb(m);
    }
    void visit(DfgSub* vtxp) override {  // Same as Add: 2's complement (a - b) == (a + ~b + 1)
        V3Number& m = MASK(vtxp).num();
        m.opAnd(MASK(vtxp->lhsp()).num(), MASK(vtxp->rhsp()).num());
        floodTowardsMsb(m);
    }

    void visit(DfgRedAnd* vtxp) override {
        const bool independent = MASK(vtxp->lhsp()).isOnes();
        if (independent) MASK(vtxp).setOnes();
    }
    void visit(DfgRedOr* vtxp) override {
        const bool independent = MASK(vtxp->lhsp()).isOnes();
        if (independent) MASK(vtxp).setOnes();
    }
    void visit(DfgRedXor* vtxp) override {
        const bool independent = MASK(vtxp->lhsp()).isOnes();
        if (independent) MASK(vtxp).setOnes();
    }

    void visit(DfgEq* vtxp) override {
        const bool independent = MASK(vtxp->lhsp()).isOnes() && MASK(vtxp->rhsp()).isOnes();
        if (independent) MASK(vtxp).setOnes();
    }
    void visit(DfgNeq* vtxp) override {
        const bool independent = MASK(vtxp->lhsp()).isOnes() && MASK(vtxp->rhsp()).isOnes();
        if (independent) MASK(vtxp).setOnes();
    }
    void visit(DfgLt* vtxp) override {
        const bool independent = MASK(vtxp->lhsp()).isOnes() && MASK(vtxp->rhsp()).isOnes();
        if (independent) MASK(vtxp).setOnes();
    }
    void visit(DfgLte* vtxp) override {
        const bool independent = MASK(vtxp->lhsp()).isOnes() && MASK(vtxp->rhsp()).isOnes();
        if (independent) MASK(vtxp).setOnes();
    }
    void visit(DfgGt* vtxp) override {
        const bool independent = MASK(vtxp->lhsp()).isOnes() && MASK(vtxp->rhsp()).isOnes();
        if (independent) MASK(vtxp).setOnes();
    }
    void visit(DfgGte* vtxp) override {
        const bool independent = MASK(vtxp->lhsp()).isOnes() && MASK(vtxp->rhsp()).isOnes();
        if (independent) MASK(vtxp).setOnes();
    }

    void visit(DfgShiftRS* vtxp) override {
        DfgVertex* const rhsp = vtxp->rhsp();
        DfgVertex* const lhsp = vtxp->lhsp();
        const uint32_t width = vtxp->width();

        // Constant shift can be computed precisely
        if (DfgConst* const rConstp = rhsp->cast<DfgConst>()) {
            const uint32_t shiftAmount = rConstp->toU32();
            if (shiftAmount >= width) {
                if (MASK(lhsp).num().bitIs1(width - 1)) { MASK(vtxp).setOnes(); }
            } else {
                V3Number& m = MASK(vtxp).num();
                m.opShiftRS(MASK(lhsp).num(), rConstp->num(), width);
                m.opSetRange(width - shiftAmount, shiftAmount, '1');
            }
            return;
        }

        // Otherwise, as the shift amount is non-negative, all independent
        // and consecutive top bits in the lhs yield an independent result
        // if the shift amount is independent.
        if (MASK(rhsp).isOnes()) {
            V3Number& m = MASK(vtxp).num();
            m = MASK(lhsp).num();
            floodTowardsLsb(m);
        }
    }

    void visit(DfgShiftR* vtxp) override {
        DfgVertex* const rhsp = vtxp->rhsp();
        DfgVertex* const lhsp = vtxp->lhsp();
        const uint32_t width = vtxp->width();

        // Constant shift can be computed precisely
        if (DfgConst* const rConstp = rhsp->cast<DfgConst>()) {
            const uint32_t shiftAmount = rConstp->toU32();
            if (shiftAmount >= width) {
                MASK(vtxp).setOnes();
            } else {
                V3Number& m = MASK(vtxp).num();
                m.opShiftR(MASK(lhsp).num(), rConstp->num());
                m.opSetRange(width - shiftAmount, shiftAmount, '1');
            }
            return;
        }

        // Otherwise, as the shift amount is non-negative, all independent
        // and consecutive top bits in the lhs yield an independent result
        // if the shift amount is independent.
        if (MASK(rhsp).isOnes()) {
            V3Number& m = MASK(vtxp).num();
            m = MASK(lhsp).num();
            floodTowardsLsb(m);
        }
    }

    void visit(DfgShiftL* vtxp) override {
        DfgVertex* const rhsp = vtxp->rhsp();
        DfgVertex* const lhsp = vtxp->lhsp();
        const uint32_t width = vtxp->width();

        // Constant shift can be computed precisely
        if (DfgConst* const rConstp = rhsp->cast<DfgConst>()) {
            const uint32_t shiftAmount = rConstp->toU32();
            if (shiftAmount >= width) {
                MASK(vtxp).setOnes();
            } else {
                V3Number& m = MASK(vtxp).num();
                m.opShiftL(MASK(lhsp).num(), rConstp->num());
                m.opSetRange(0, shiftAmount, '1');
            }
            return;
        }

        // Otherwise, as the shift amount is non-negative, all independent
        // and consecutive bottom bits in the lhs yield an independent result
        // if the shift amount is independent.
        if (MASK(rhsp).isOnes()) {
            V3Number& m = MASK(vtxp).num();
            m = MASK(lhsp).num();
            floodTowardsMsb(m);
        }
    }

    void visit(DfgCond* vtxp) override {
        if (MASK(vtxp->condp()).isOnes()) {
            MASK(vtxp).num().opAnd(MASK(vtxp->thenp()).num(), MASK(vtxp->elsep()).num());
        }
    }

    void visit(DfgMatchMasked* vtxp) override {
        if (MASK(vtxp->lhsp()).isOnes() && MASK(vtxp->matchp()).isOnes()) { MASK(vtxp).setOnes(); }
    }

#undef MASK

    // Enqueue sinks of vertex to work list for traversal - only called from constructor
    void enqueueSinks(DfgVertex& vtx) {
        vtx.foreachSink([&](DfgVertex& sink) {
            // Ignore if sink is not part of an SCC, already has all bits marked independent
            if (!m_sccInfo.get(sink)) return false;
            // Otherwise just enqueue it
            VertexState& state = m_vtxp2State.at(&sink);
            if (!state.m_isOnWorkList) {
                UINFO(9, "Enqueuing vertex " << &sink << " " << sink.typeName());
                m_workQueue.push(state.m_rpoNumber);
            }
            state.m_isOnWorkList = true;
            return false;
        });
    };

    void dfsPostOrder(std::unordered_set<DfgVertex*>& visited,  //
                      std::vector<DfgVertex*>& postOrderEnumeration,  //
                      DfgVertex& vtx) {
        // Mark visited, skip if already visited
        if (!visited.insert(&vtx).second) return;
        // Visit un-visited successors
        vtx.foreachSink([&](DfgVertex& snk) {
            dfsPostOrder(visited, postOrderEnumeration, snk);
            return false;
        });
        // Add to post order enumeration
        postOrderEnumeration.emplace_back(&vtx);
    };

    IndependentBits(DfgGraph& dfg, const SccInfo& sccInfo)
        : m_sccInfo{sccInfo} {

#ifdef VL_DEBUG
        if (v3Global.opt.debugCheck()) {
            m_lineCoverageFile.open(  //
                v3Global.opt.makeDir() + "/" + v3Global.opt.prefix()
                    + "__V3DfgBreakCycles-IndependentBits-line-coverage.txt",  //
                std::ios_base::out | std::ios_base::app);
        }
#endif

        // Compute Reverse-Postorder enumeration of vertices
        std::vector<DfgVertex*> rpoEnumeration;
        std::unordered_set<DfgVertex*> visited;
        dfg.forEachVertex([&](DfgVertex& vtx) {
            if (!vtx.nInputs()) dfsPostOrder(visited, rpoEnumeration, vtx);
        });
        dfg.forEachVertex([&](DfgVertex& vtx) {  //
            dfsPostOrder(visited, rpoEnumeration, vtx);
        });
        std::reverse(rpoEnumeration.begin(), rpoEnumeration.end());
        UASSERT(rpoEnumeration.size() == dfg.size(), "Inconsistent vertex count");

        // Initialzie VertexState for each vertex
        for (size_t i = 0; i < rpoEnumeration.size(); ++i) {
            VertexState& state = m_vtxp2State[rpoEnumeration[i]];
            state.m_rpoNumber = i;
            state.m_isOnWorkList = false;
        }

        // Set up the initial conditions:
        // - For vertices not in an SCC, mark all bits as independent
        // - For vertices in an SCC, dispatch to analyse at least once, as some vertices
        //   always assign constants bits, which are always independent (eg Extend/Shift)
        // Enqueue sinks of all SCC vertices that have at least one independent bit
        for (DfgVertex* const vtxp : rpoEnumeration) {
            if (m_sccInfo.get(*vtxp)) continue;
            mask(*vtxp).setOnes();
        }
        for (DfgVertex* const vtxp : rpoEnumeration) {
            if (!m_sccInfo.get(*vtxp)) continue;
            iterate(vtxp);
            UINFO(9, "Initial independent bits of " << vtxp << " " << vtxp->typeName()
                                                    << " are: " << mask(*vtxp).toString());
            if (!mask(*vtxp).isZero()) enqueueSinks(*vtxp);
        }

        // Propagate independent bits until no more changes are made
        while (!m_workQueue.empty()) {
            // Grab next item
            DfgVertex* const currp = rpoEnumeration[m_workQueue.top()];
            m_workQueue.pop();
            m_vtxp2State.at(currp).m_isOnWorkList = false;
            // Should not enqueue vertices that are not in an SCC
            UASSERT_OBJ(m_sccInfo.get(*currp), currp, "Vertex should be in an SCC");

            // Grab current mask of item
            const BitMask& currMask = mask(*currp);
            // Remember current mask so we can check if it changed
            const BitMask prevMask = currMask;

            UINFO(9, "Analyzing independent bits of " << currp << " " << currp->typeName());

            // Dispatch it to update the mask in the visit methods
            iterate(currp);

            // If mask changed, enqueue sinks
            if (prevMask != currMask) {
                UINFO(9, "Independent bits of "  //
                             << currp << " " << currp->typeName() << " changed"  //
                             << "\n    form: " << prevMask.toString()
                             << "\n      to: " << currMask.toString());
                enqueueSinks(*currp);
                // Check the mask only ever expands (no bit goes 1 -> 0)
                if (VL_UNLIKELY(v3Global.opt.debugCheck())) {
                    UASSERT_OBJ(!currMask.isContractionOf(prevMask), currp,
                                "Mask should only expand");
                }
            }
        }
    }

public:
    // Given a DfgGraph, and a map from vertices to the SCCs they reside in,
    // returns a map from vertices to a bit mask, where a bit in the mask is
    // set if the corresponding bit in that vertex is known to be independent
    // of the values of vertices in the same SCC as the vertex resides in.
    static std::unordered_map<const DfgVertex*, BitMask> apply(DfgGraph& dfg,
                                                               const SccInfo& sccInfo) {
        return std::move(IndependentBits{dfg, sccInfo}.m_vtxp2Mask);
    }
};

class FixUp final {
    DfgGraph& m_dfg;  // The graph being processed
    SccInfo& m_sccInfo;  // The SccInfo instance
    TraceDriver m_traceDriver{m_dfg, m_sccInfo};
    // The independent bits map
    const std::unordered_map<const DfgVertex*, BitMask> m_independentBits
        = IndependentBits::apply(m_dfg, m_sccInfo);
    size_t m_nImprovements = 0;  // Number of improvements made

    // Returns a bitmask set if that bit of 'vtx' is used (has a sink)
    static BitMask computeUsedBits(DfgVertex& vtx) {
        BitMask result{vtx};
        vtx.foreachSink([&result](DfgVertex& sink) {
            // If used via a Sel, mark the selected bits used
            if (const DfgSel* const selp = sink.cast<DfgSel>()) {
                result.num().opSetRange(selp->lsb(), selp->width(), '1');
                return false;
            }
            // Used without a Sel, so all bits are used
            result.setOnes();
            return true;
        });
        return result;
    }

    static std::string debugStr(const DfgVertex& vtx) {  // LCOV_EXCL_START
        if (const DfgArraySel* const aselp = vtx.cast<DfgArraySel>()) {
            const size_t i = aselp->bitp()->as<DfgConst>()->toSizeT();
            return debugStr(*aselp->fromp()) + "[" + std::to_string(i) + "]";
        }
        if (const DfgVertexVar* const varp = vtx.cast<DfgVertexVar>()) {
            return varp->vscp()->name();
        }
        vtx.v3fatalSrc("Unhandled node type");
    }  // LCOV_EXCL_STOP

    // Trace drivers of independent bits of 'vtxp' in the range '[hi:lo]'
    // append replacement terms to 'termps'.
    void gatherTerms(std::vector<DfgVertex*>& termps, DfgVertex& vtx, const V3Number& indpBits,
                     const uint32_t hi, const uint32_t lo) {
        // Iterate through consecutive dependent/non-dependet ranges within [hi:lo]
        bool isIndependent = indpBits.bitIs1(lo);
        uint32_t lsb = lo;
        for (uint32_t msb = lo; msb <= hi; ++msb) {
            const bool endRange = msb == hi || isIndependent != indpBits.bitIs1(msb + 1);
            if (!endRange) continue;
            const uint32_t width = msb - lsb + 1;
            // Compute the term to use for this range
            if (isIndependent) {
                // If the range is independent of the cycles, trace its driver
                ++m_nImprovements;
                termps.emplace_back(m_traceDriver.apply(vtx, lsb, width));
            } else {
                // If dependent, fall back on using the part of the variable
                DfgSel* const selp = new DfgSel{m_dfg, vtx.fileline(), DfgDataType::packed(width)};
                // Same component as 'vtxp', as reads 'vtxp' and will replace 'vtxp'
                m_sccInfo.add(*selp, m_sccInfo.get(vtx));
                // Do not connect selp->fromp yet, need to do afer replacing 'vtxp'
                selp->lsb(lsb);
                termps.emplace_back(selp);
            }
            // Next iteration
            isIndependent = !isIndependent;
            lsb = msb + 1;
        }
    }

    void fixUpPacked(DfgVertex& vtx) {
        UASSERT_OBJ(vtx.isPacked(), &vtx, "Should be a packed type");
        UASSERT_OBJ(!vtx.is<DfgSplicePacked>(), &vtx, "Should not be a splice");

        // Get which bits of 'vtxp' are independent of the SCCs
        const BitMask& indpBits = m_independentBits.at(&vtx);
        UINFO(9, "Independent bits of '" << debugStr(vtx) << "' are " << indpBits.toString());
        // Can't do anything if all bits are dependent
        if (indpBits.isZero()) return;

        // Figure out which bits of 'vtxp' are used
        const BitMask usedBits = computeUsedBits(vtx);
        UINFO(9, "Used        bits of '" << debugStr(vtx) << "' are " << usedBits.toString());

        // Nothing to do if no used bits are independen (all used bits are dependent)
        V3Number usedAndIndependent{vtx.fileline(), static_cast<int>(vtx.width()), 0};
        usedAndIndependent.opAnd(usedBits.num(), indpBits.num());
        if (usedAndIndependent.isEqZero()) return;

        // We are computing the terms to concatenate and replace 'vtxp' with
        std::vector<DfgVertex*> termps;

        // Iterate through consecutive used/unused ranges
        FileLine* const flp = vtx.fileline();
        const uint32_t width = vtx.width();
        bool isUsed = usedBits.num().bitIs1(0);  // Is current range used
        uint32_t lsb = 0;  // LSB of current range
        for (uint32_t msb = 0; msb < width; ++msb) {
            const bool endRange = msb == width - 1 || isUsed != usedBits.num().bitIs1(msb + 1);
            if (!endRange) continue;
            if (isUsed) {
                // The range is used, compute the replacement terms
                gatherTerms(termps, vtx, indpBits.num(), msb, lsb);
            } else {
                // The range is not used, just use constant 0 as a placeholder
                DfgConst* const constp = new DfgConst{m_dfg, flp, msb - lsb + 1, 0};
                m_sccInfo.add(*constp, 0);
                termps.emplace_back(constp);
            }
            // Next iteration
            isUsed = !isUsed;
            lsb = msb + 1;
        }

        // Concatenate all the terms to create the replacement
        DfgVertex* replacementp = termps.front();
        const uint64_t vComp = m_sccInfo.get(vtx);
        for (size_t i = 1; i < termps.size(); ++i) {
            DfgVertex* const termp = termps[i];
            const uint32_t catWidth = replacementp->width() + termp->width();
            DfgConcat* const catp = new DfgConcat{m_dfg, flp, DfgDataType::packed(catWidth)};
            catp->rhsp(replacementp);
            catp->lhsp(termp);
            // Need to figure out which component the replacement vertex
            // belongs to. If any of the terms are of the original
            // component, it's part of that component, otherwise its not
            // cyclic (all terms are from outside the original component,
            // and feed into the original component).
            const uint64_t tComp = m_sccInfo.get(*termp);
            const uint64_t rComp = m_sccInfo.get(*replacementp);
            m_sccInfo.add(*catp, tComp == vComp || rComp == vComp ? vComp : 0);
            replacementp = catp;
        }

        // Replace the vertex
        vtx.replaceWith(replacementp);
        // Connect the Sel nodes in the replacement
        for (DfgVertex* const termp : termps) {
            if (DfgSel* const selp = termp->cast<DfgSel>()) {
                if (!selp->fromp()) selp->fromp(&vtx);
            }
        }

        // If the vertex still has sinks, then the replacement is still cyclic, and vice versa
        UASSERT_OBJ(!vtx.hasSinks() == !m_sccInfo.get(*replacementp), &vtx,
                    "Replacement vertex SCC inconsistent");

        // If we broke the cycle through this vertex, update the SccInfo
        if (!vtx.hasSinks()) m_sccInfo.updateReplacement(vtx, *replacementp);
    }

    void main(DfgVertexVar& var) {
        UINFO(9, "FixUp of " << var.vscp()->name());

        if (var.is<DfgVarPacked>()) {
            // For Packed variables, fix up as whole
            fixUpPacked(var);
        } else if (var.is<DfgVarArray>()) {
            // For array variables, fix up element-wise
            const uint64_t component = m_sccInfo.get(var);
            var.foreachSink([&](DfgVertex& sink) {
                // Ignore if sink is not part of same cycle
                if (m_sccInfo.get(sink) != component) return false;
                // Only handle ArraySels with constant index
                DfgArraySel* const aselp = sink.cast<DfgArraySel>();
                if (!aselp) return false;
                if (!aselp->bitp()->is<DfgConst>()) return false;
                // Fix up the word
                fixUpPacked(*aselp);
                return false;
            });
        }

        UINFO(9, "FixUp made " << m_nImprovements << " improvements");
    }

    FixUp(DfgGraph& dfg, SccInfo& sccInfo)
        : m_dfg{dfg}
        , m_sccInfo{sccInfo} {}

public:
    // Compute which bits of vertices are independent of the SCC they reside
    // in, and replace rferences to used independent bits with an equivalent
    // vertex that is not part of the same SCC.
    static size_t apply(DfgGraph& dfg, SccInfo& sccInfo) {
        if (!sccInfo.isCyclic()) return 0;

        FixUp fixUp{dfg, sccInfo};

        // TODO: Compute minimal feedback vertex set and cut only those.
        //       Sadly that is a computationally hard problem.

        // Fix up cyclic variables, stop as soon as the graph becomes acyclic
        for (DfgVertexVar& vtx : dfg.varVertices()) {
            if (!sccInfo.get(vtx)) continue;
            fixUp.main(vtx);
            if (!sccInfo.isCyclic()) break;
        }
        // Return the number of improvements made
        return fixUp.m_nImprovements;
    }
};

void breakCycles(DfgGraph& dfg, V3DfgBreakCyclesContext& ctx) {
    // Shorthand for dumping graph at given dump level
    const auto dump = [&](int level, const DfgGraph& dfg, const std::string& name) {
        if (dumpDfgLevel() >= level) dfg.dumpDotFilePrefixed("breakCycles-" + name);
    };

    // AstNetlist/AstNodeModule user2 used as sequence numbers for temporaries
    const VNUser2InUse user2InUse;

    // Show input for debugging
    dump(7, dfg, "input");

    // How many improvements have we made
    size_t nImprovements = 0;
    size_t prevNImprovements;

    // Iterate while an improvement can be made and the graph is still cyclic
    do {
        // Compute SCCs
        SccInfo sccInfo{dfg};

        // Fix up independent ranges in vertices
        UINFO(9, "New iteration after " << nImprovements << " improvements");
        prevNImprovements = nImprovements;
        const size_t nFixed = FixUp::apply(dfg, sccInfo);
        if (nFixed) {
            nImprovements += nFixed;
            ctx.m_nImprovements += nFixed;
            dump(9, dfg, "FixUp");
        }

        // Validate SccInfo if in debug mode
        if (v3Global.opt.debugCheck()) sccInfo.validate();

        // Congrats if it has become acyclic
        if (!sccInfo.isCyclic()) {
            UINFO(7, "Graph became acyclic after " << nImprovements << " improvements");
            dump(7, dfg, "result-acyclic");
            ++ctx.m_nFixed;
            return;
        }
    } while (nImprovements != prevNImprovements);

    // Debug dump
    if (dumpDfgLevel() >= 9) {
        const SccInfo sccInfo{dfg};
        dfg.dumpDotFilePrefixed("breakCycles-remaining", [&](const DfgVertex& vtx) {
            return sccInfo.get(vtx);  //
        });
    }

    // Accounting
    if (nImprovements) {
        UINFO(7, "Graph was improved " << nImprovements << " times");
        dump(7, dfg, "result-improved");
        ++ctx.m_nImproved;
    } else {
        UINFO(7, "Graph NOT improved");
        ++ctx.m_nUnchanged;
    }

    // Break any remaining cycles by inserting a DfgPrev for variables still in a cycle.
    // Doing this unconditionally is both safe and sufficient:
    //  - Safe: a DfgPrev makes the variable's readers read its stored value instead
    //    of its in-graph driver, while the variable itself is still assigned. This
    //    merely reconstructs the cyclic variable-level dataflow, which the scheduler
    //    will resolve via its settle loop, so the computation is equivalent.
    //  - Sufficient: every cycle must pass through a variable, and in particular
    //    through a non-temporary one (synthesis doesn't create cycles within a single
    //    logic block).
    // Also note that synthesized logic that depends on an in-graph update will read
    // the synthesis temporary, not the real variable (which is what we are cutting),
    // so the graph still holds all updates in a form visible to later optimizers.

    // Gather all non-temporary variables as candidate cut points, prefer those that
    // are kept regardless. Breaking a cycle there is essentially free, as they must be
    // materialized anyway, whereas cutting an internal variable forces it to survive
    // via its DfgPrev when it could otherwise be inlined away later.
    std::vector<DfgVertexVar*> varps;
    for (DfgVertexVar& vtx : dfg.varVertices()) {
        if (!vtx.tmpForp()) varps.push_back(&vtx);
    }
    std::stable_partition(varps.begin(), varps.end(), [](const DfgVertexVar* varp) {
        return varp->hasExtRefs() || varp->isVolatile();
    });

    // Insert DfgPrev vertices until the graph becomes acyclic
    SccInfo sccInfo{dfg};
    for (DfgVertexVar* const varp : varps) {
        // Stop as soon as it becomes acyclic
        if (!sccInfo.isCyclic()) break;

        // Ignore if variable is not part of a cycle
        if (!sccInfo.get(*varp)) continue;

        // Insert a DfgPrev vertex for the variable
        DfgPrev* const prevp = new DfgPrev{dfg, varp->vscp()};
        sccInfo.add(*prevp, 0);
        varp->replaceWith(prevp);
        ++ctx.m_nPrevInserted;

        // Update SCC info
        sccInfo.updateReplacement(*varp, *prevp);
    }
    // Validate SccInfo if in debug mode
    if (v3Global.opt.debugCheck()) sccInfo.validate();
    UASSERT(!sccInfo.isCyclic(), "Graph should become acyclic");

    dump(7, dfg, "result-withprev");
}

}  //namespace V3DfgBreakCycles
void V3DfgPasses::breakCycles(DfgGraph& dfg, V3DfgContext& ctx) {
    V3DfgBreakCycles::breakCycles(dfg, ctx.m_breakCyclesContext);
    if (v3Global.opt.debugCheck()) V3DfgPasses::typeCheck(dfg);
    V3DfgPasses::removeUnused(dfg);
}
