// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Converting cyclic DFGs into acyclic DFGs
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2026 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Dfg.h"
#include "V3DfgPasses.h"
#include "V3Error.h"
#include "V3Hash.h"

#include <algorithm>
#include <deque>
#include <fstream>
#include <unordered_map>
#include <vector>

VL_DEFINE_DEBUG_FUNCTIONS;

namespace V3DfgBreakCycles {

// Throughout these algorithm, we use the DfgUserMap as a map to the SCC number
using Vtx2Scc = DfgUserMap<uint64_t>;

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
    Vtx2Scc& m_vtx2Scc;  // The Vertex to SCC map
    // The strongly connected component we are currently trying to escape
    uint64_t m_component = 0;
    uint32_t m_lsb = 0;  // LSB to extract from the currently visited Vertex
    uint32_t m_msb = 0;  // MSB to extract from the currently visited Vertex
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
    // Also sets m_vtx2Scc[vtx] to 0, indicating the new vertex is not part of
    // a strongly connected component. This should always be true, as all the
    // vertices we create here are driven from outside the component we are
    // trying to escape, and will sink into that component. Given those are
    // separate SCCs, these new vertices must be acyclic.
    template <typename Vertex>
    Vertex* make(const DfgVertex* refp, uint32_t width) {
        static_assert(std::is_base_of<DfgVertex, Vertex>::value  //
                          && !std::is_base_of<DfgVertexVar, Vertex>::value,
                      "Should only make operation vertices and constants");

        if VL_CONSTEXPR_CXX17 (std::is_same<DfgConst, Vertex>::value) {
            DfgConst* const vtxp = new DfgConst{m_dfg, refp->fileline(), width, 0};
            m_vtx2Scc[vtxp] = 0;
            return reinterpret_cast<Vertex*>(vtxp);
        } else {
            // TODO: this is a gross hack around lack of C++17 'if constexpr' Vtx is always Vertex
            // when this code is actually executed, but needs a fudged type to type check when
            // Vertex is DfgConst, in which case this code is unreachable ...
            using Vtx = typename std::conditional<std::is_same<DfgConst, Vertex>::value, DfgSel,
                                                  Vertex>::type;
            Vtx* const vtxp = new Vtx{m_dfg, refp->fileline(), DfgDataType::packed(width)};
            m_vtx2Scc[vtxp] = 0;
            return reinterpret_cast<Vertex*>(vtxp);
        }
    }

    // Create temporary capable of holding the result of 'vtxp'
    DfgVertexVar* createTmp(const char* prefix, DfgVertex* vtxp) {
        AstNode* nodep = m_dfg.modulep();
        if (!nodep) nodep = v3Global.rootp();
        const std::string name = m_dfg.makeUniqueName(prefix, nodep->user2Inc());
        FileLine* const flp = vtxp->fileline();
        DfgVertex::ScopeCache scopeCache;
        AstScope* const scopep = m_dfg.modulep() ? nullptr : vtxp->scopep(scopeCache);
        DfgVertexVar* const varp = m_dfg.makeNewVar(flp, name, vtxp->dtype(), scopep);
        varp->varp()->isInternal(true);
        varp->tmpForp(varp->nodep());
        m_vtx2Scc[varp] = 0;
        return varp;
    }

    // Continue tracing drivers of the given vertex, at the given LSB.
    // Every visitor should call this to continue the traversal.
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
        } else if (m_vtx2Scc.at(vtxp) != m_component) {
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
        for (const Driver& driver : drivers) {
            // Driver is below the searched LSB, move on
            if (m_lsb > driver.m_msb) continue;
            // Driver is above the searched MSB, done
            if (driver.m_lsb > m_msb) break;
            // Gap below this driver, trace default to fill it
            if (driver.m_lsb > m_lsb) {
                UASSERT_OBJ(m_defaultp, vtxp, "Should have a default driver if needs tracing");
                termps.emplace_back(trace(m_defaultp, driver.m_lsb - 1, m_lsb));
                m_lsb = driver.m_lsb;
            }
            // Driver covers searched range, pick the needed/available bits
            uint32_t lim = std::min(m_msb, driver.m_msb);
            termps.emplace_back(trace(driver.m_vtxp, lim - driver.m_lsb, m_lsb - driver.m_lsb));
            m_lsb = lim + 1;
        }
        if (m_msb >= m_lsb) {
            UASSERT_OBJ(m_defaultp, vtxp, "Should have a default driver if needs tracing");
            termps.emplace_back(trace(m_defaultp, m_msb, m_lsb));
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

    void visit(DfgVarPacked* vtxp) override {
        UASSERT_OBJ(!vtxp->isVolatile(), vtxp, "Should not trace through volatile VarPacked");
        VL_RESTORER(m_defaultp);
        m_defaultp = vtxp->defaultp();
        SET_RESULT(trace(vtxp->srcp(), m_msb, m_lsb));
    }

    void visit(DfgArraySel* vtxp) override {
        // Only constant select
        const DfgConst* const idxp = vtxp->bitp()->cast<DfgConst>();
        if (!idxp) return;
        // From a variable
        const DfgVarArray* varp = vtxp->fromp()->cast<DfgVarArray>();
        if (!varp) return;
        UASSERT_OBJ(!varp->isVolatile(), vtxp, "Should not trace through volatile VarArray");
        // Skip through intermediate variables
        while (varp->srcp() && varp->srcp()->is<DfgVarArray>()) {
            varp = varp->srcp()->as<DfgVarArray>();
            UASSERT_OBJ(!varp->isVolatile(), vtxp, "Should not trace through volatile VarArray");
        }
        // Find driver
        const DfgVertex* srcp = varp->srcp();
        if (const DfgSpliceArray* const splicep = srcp->cast<DfgSpliceArray>()) {
            srcp = splicep->driverAt(idxp->toSizeT());
        }
        // Trace the driver, which at this point must be a UnitArray
        SET_RESULT(trace(srcp->as<DfgUnitArray>()->srcp(), m_msb, m_lsb));
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

    void visit(DfgReplicate* vtxp) override {
        DfgVertex* const srcp = vtxp->srcp();
        const uint32_t sWidth = srcp->width();
        // If we need more bits than the source, then we need the whole source
        if (m_msb - m_lsb + 1 > sWidth) {
            DfgReplicate* const repp = make<DfgReplicate>(vtxp, vtxp->width());
            repp->srcp(trace(srcp, sWidth - 1, 0));
            repp->countp(vtxp->countp());  // Always a DfgConst
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

#undef SET_RESULT

public:
    // CONSTRUCTOR
    TraceDriver(DfgGraph& dfg, Vtx2Scc& vtx2Scc)
        : m_dfg{dfg}
        , m_vtx2Scc{vtx2Scc} {
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
        m_component = m_vtx2Scc.at(&vtx);
        return trace(&vtx, lsb + width - 1, lsb);
    }
};

class IndependentBits final : public DfgVisitor {
    // STATE
    const Vtx2Scc& m_vtx2Scc;  // The Vertex to SCC map
    // Vertex to current bit mask map. The mask is set for the bits that are independent of the SCC
    std::unordered_map<const DfgVertex*, V3Number> m_vtxp2Mask;
    std::deque<DfgVertex*> m_workList;  // Work list for the traversal
    std::unordered_map<DfgVertex*, bool> m_onWorkList;  // Marks vertices on the work list

#ifdef VL_DEBUG
    std::ofstream m_lineCoverageFile;  // Line coverage file, just for testing
#endif

    // METHODS
    // Predicate to check if a vertex should be analysed directly
    bool handledDirectly(const DfgVertex& vtx) const {
        if (!vtx.isPacked()) return false;
        if (vtx.is<DfgSplicePacked>()) return false;
        return true;
    }

    // Retrieve the mask for the given vertex (create it with value 0 if needed)
    V3Number& mask(const DfgVertex& vtx) {
        UASSERT_OBJ(handledDirectly(vtx), &vtx, "Vertex should not be handled direclty");
        // Look up (or create) mask for 'vtxp'
        return m_vtxp2Mask
            .emplace(std::piecewise_construct,  //
                     std::forward_as_tuple(&vtx),  //
                     std::forward_as_tuple(vtx.fileline(), static_cast<int>(vtx.width()), 0))  //
            .first->second;
    }

    // Use this macro to call 'mask' in 'visit' methods. This also emits
    // a line to m_lineCoverageFile for testing.
    // TODO: Use C++20 std::source_location instead of a macro
#ifdef VL_DEBUG
#define MASK(vtxp) \
    ([this](const DfgVertex& vtx) -> V3Number& { \
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

    void propagateFromDriver(V3Number& m, const DfgVertex* srcp) {
        // If there is no driver, we are done
        if (!srcp) return;
        // If it is driven by a splice, we need to combine the masks of the drivers
        if (const DfgSplicePacked* const splicep = srcp->cast<DfgSplicePacked>()) {
            splicep->foreachDriver([&](const DfgVertex& src, uint32_t lo) {
                m.opSelInto(MASK(&src), lo, src.width());
                return false;
            });
            return;
        }
        // Otherwise, we just use the mask of the single driver
        m = MASK(srcp);
    }

    // VISITORS
    void visit(DfgVertex* vtxp) override {  // LCOV_EXCL_START
        UASSERT_OBJ(handledDirectly(*vtxp), vtxp, "Vertex should be handled direclty");
        UINFO(9, "IndependentBits - Unhandled vertex type: " << vtxp->typeName());
        // Conservative assumption about all bits being dependent prevails
    }  // LCOV_EXCL_STOP

    void visit(DfgVarPacked* vtxp) override {
        // We cannot trace through a volatile variable, so pretend all bits are dependent
        if (vtxp->isVolatile()) return;
        V3Number& m = MASK(vtxp);
        DfgVertex* const srcp = vtxp->srcp();
        DfgVertex* const defaultp = vtxp->defaultp();
        // If there is a default driver, we start from that
        if (defaultp) m = MASK(defaultp);
        // Then propagate mask from the driver
        propagateFromDriver(m, srcp);
    }

    void visit(DfgArraySel* vtxp) override {
        // Only constant select
        const DfgConst* const idxp = vtxp->bitp()->cast<DfgConst>();
        if (!idxp) return;
        // From a variable
        const DfgVarArray* varp = vtxp->fromp()->cast<DfgVarArray>();
        if (!varp) return;
        // We cannot trace through a volatile variable, so pretend all bits are dependent
        if (varp->isVolatile()) return;
        // Skip through intermediate variables
        while (varp->srcp() && varp->srcp()->is<DfgVarArray>()) {
            varp = varp->srcp()->as<DfgVarArray>();
            if (varp->isVolatile()) return;
        }
        // Find driver
        const DfgVertex* srcp = varp->srcp();
        if (!srcp) return;
        if (const DfgSpliceArray* const splicep = srcp->cast<DfgSpliceArray>()) {
            srcp = splicep->driverAt(idxp->toSizeT());
            if (!srcp) return;
        }
        const DfgUnitArray* uap = srcp->cast<DfgUnitArray>();
        if (!uap) return;
        srcp = uap->srcp();
        // Propagate from driver
        propagateFromDriver(MASK(vtxp), srcp);
    }

    void visit(DfgConcat* vtxp) override {
        const DfgVertex* const rhsp = vtxp->rhsp();
        const DfgVertex* const lhsp = vtxp->lhsp();
        V3Number& m = MASK(vtxp);
        m.opSelInto(MASK(rhsp), 0, rhsp->width());
        m.opSelInto(MASK(lhsp), rhsp->width(), lhsp->width());
    }

    void visit(DfgReplicate* vtxp) override {
        const uint32_t count = vtxp->countp()->as<DfgConst>()->toU32();
        const DfgVertex* const srcp = vtxp->srcp();
        const uint32_t sWidth = srcp->width();
        V3Number& vMask = MASK(vtxp);
        V3Number& sMask = MASK(srcp);
        for (uint32_t i = 0; i < count; ++i) vMask.opSelInto(sMask, i * sWidth, sWidth);
    }

    void visit(DfgSel* vtxp) override {
        const uint32_t lsb = vtxp->lsb();
        const uint32_t msb = lsb + vtxp->width() - 1;
        MASK(vtxp).opSel(MASK(vtxp->fromp()), msb, lsb);
    }

    void visit(DfgExtend* vtxp) override {
        const DfgVertex* const srcp = vtxp->srcp();
        const uint32_t sWidth = srcp->width();
        V3Number& s = MASK(srcp);
        V3Number& m = MASK(vtxp);
        m.opSelInto(s, 0, sWidth);
        m.opSetRange(sWidth, vtxp->width() - sWidth, '1');
    }
    void visit(DfgExtendS* vtxp) override {
        const DfgVertex* const srcp = vtxp->srcp();
        const uint32_t sWidth = srcp->width();
        V3Number& s = MASK(srcp);
        V3Number& m = MASK(vtxp);
        m.opSelInto(s, 0, sWidth);
        m.opSetRange(sWidth, vtxp->width() - sWidth, s.bitIs0(sWidth - 1) ? '0' : '1');
    }

    void visit(DfgNot* vtxp) override {  //
        MASK(vtxp) = MASK(vtxp->srcp());
    }

    void visit(DfgAnd* vtxp) override {  //
        MASK(vtxp).opAnd(MASK(vtxp->lhsp()), MASK(vtxp->rhsp()));
    }
    void visit(DfgOr* vtxp) override {  //
        MASK(vtxp).opAnd(MASK(vtxp->lhsp()), MASK(vtxp->rhsp()));
    }
    void visit(DfgXor* vtxp) override {  //
        MASK(vtxp).opAnd(MASK(vtxp->lhsp()), MASK(vtxp->rhsp()));
    }

    void visit(DfgAdd* vtxp) override {
        V3Number& m = MASK(vtxp);
        m.opAnd(MASK(vtxp->lhsp()), MASK(vtxp->rhsp()));
        floodTowardsMsb(m);
    }
    void visit(DfgSub* vtxp) override {  // Same as Add: 2's complement (a - b) == (a + ~b + 1)
        V3Number& m = MASK(vtxp);
        m.opAnd(MASK(vtxp->lhsp()), MASK(vtxp->rhsp()));
        floodTowardsMsb(m);
    }

    void visit(DfgRedAnd* vtxp) override {  //
        if (MASK(vtxp->lhsp()).isEqAllOnes()) {  //
            MASK(vtxp).setAllBits1();
        }
    }
    void visit(DfgRedOr* vtxp) override {  //
        if (MASK(vtxp->lhsp()).isEqAllOnes()) {  //
            MASK(vtxp).setAllBits1();
        }
    }
    void visit(DfgRedXor* vtxp) override {  //
        if (MASK(vtxp->lhsp()).isEqAllOnes()) {  //
            MASK(vtxp).setAllBits1();
        }
    }

    void visit(DfgEq* vtxp) override {
        const bool independent
            = MASK(vtxp->lhsp()).isEqAllOnes() && MASK(vtxp->rhsp()).isEqAllOnes();
        MASK(vtxp).setBit(0, independent ? '1' : '0');
    }
    void visit(DfgNeq* vtxp) override {
        const bool independent
            = MASK(vtxp->lhsp()).isEqAllOnes() && MASK(vtxp->rhsp()).isEqAllOnes();
        MASK(vtxp).setBit(0, independent ? '1' : '0');
    }
    void visit(DfgLt* vtxp) override {
        const bool independent
            = MASK(vtxp->lhsp()).isEqAllOnes() && MASK(vtxp->rhsp()).isEqAllOnes();
        MASK(vtxp).setBit(0, independent ? '1' : '0');
    }
    void visit(DfgLte* vtxp) override {
        const bool independent
            = MASK(vtxp->lhsp()).isEqAllOnes() && MASK(vtxp->rhsp()).isEqAllOnes();
        MASK(vtxp).setBit(0, independent ? '1' : '0');
    }
    void visit(DfgGt* vtxp) override {
        const bool independent
            = MASK(vtxp->lhsp()).isEqAllOnes() && MASK(vtxp->rhsp()).isEqAllOnes();
        MASK(vtxp).setBit(0, independent ? '1' : '0');
    }
    void visit(DfgGte* vtxp) override {
        const bool independent
            = MASK(vtxp->lhsp()).isEqAllOnes() && MASK(vtxp->rhsp()).isEqAllOnes();
        MASK(vtxp).setBit(0, independent ? '1' : '0');
    }

    void visit(DfgShiftR* vtxp) override {
        DfgVertex* const rhsp = vtxp->rhsp();
        DfgVertex* const lhsp = vtxp->lhsp();
        const uint32_t width = vtxp->width();

        // Constant shift can be computed precisely
        if (DfgConst* const rConstp = rhsp->cast<DfgConst>()) {
            const uint32_t shiftAmount = rConstp->toU32();
            V3Number& m = MASK(vtxp);
            if (shiftAmount >= width) {
                m.setAllBits1();
            } else {
                m.opShiftR(MASK(lhsp), rConstp->num());
                m.opSetRange(width - shiftAmount, shiftAmount, '1');
            }
            return;
        }

        // Otherwise, as the shift amount is non-negative, all independent
        // and consecutive top bits in the lhs yield an independent result
        // if the shift amount is independent.
        if (MASK(rhsp).isEqAllOnes()) {
            V3Number& m = MASK(vtxp);
            m = MASK(lhsp);
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
            V3Number& m = MASK(vtxp);
            if (shiftAmount >= width) {
                m.setAllBits1();
            } else {
                m.opShiftL(MASK(lhsp), rConstp->num());
                m.opSetRange(0, shiftAmount, '1');
            }
            return;
        }

        // Otherwise, as the shift amount is non-negative, all independent
        // and consecutive bottom bits in the lhs yield an independent result
        // if the shift amount is independent.
        if (MASK(rhsp).isEqAllOnes()) {
            V3Number& m = MASK(vtxp);
            m = MASK(lhsp);
            floodTowardsMsb(m);
        }
    }

    void visit(DfgCond* vtxp) override {
        if (MASK(vtxp->condp()).isEqAllOnes()) {
            MASK(vtxp).opAnd(MASK(vtxp->thenp()), MASK(vtxp->elsep()));
        }
    }

#undef MASK

    // Enqueue sinks of vertex to work list for traversal - only called from constructor
    void enqueueSinks(DfgVertex& vtx) {
        vtx.foreachSink([&](DfgVertex& sink) {
            // Ignore if sink is not part of an SCC, already has all bits marked independent
            if (!m_vtx2Scc.at(sink)) return false;
            // If a vertex is not handled directly, recursively enqueue its sinks instead
            if (!handledDirectly(sink)) {
                enqueueSinks(sink);
                return false;
            }
            // Otherwise just enqueue it
            bool& onWorkList = m_onWorkList[&sink];
            if (!onWorkList) {
                UINFO(9, "Enqueuing vertex " << &sink << " " << sink.typeName());
                m_workList.emplace_back(&sink);
            }
            onWorkList = true;
            return false;
        });
    };

    IndependentBits(DfgGraph& dfg, const Vtx2Scc& vtx2Scc)
        : m_vtx2Scc{vtx2Scc} {

#ifdef VL_DEBUG
        if (v3Global.opt.debugCheck()) {
            m_lineCoverageFile.open(  //
                v3Global.opt.makeDir() + "/" + v3Global.opt.prefix()
                    + "__V3DfgBreakCycles-IndependentBits-line-coverage.txt",  //
                std::ios_base::out | std::ios_base::app);
        }
#endif

        // Set up the initial conditions:
        // - For vertices not in an SCC, mark all bits as independent
        // - For vertices in an SCC, dispatch to analyse at least once, as some vertices
        //   always assign constants bits, which are always independent (eg Extend/Shift)
        // Enqueue sinks of all SCC vertices that have at least one independent bit
        dfg.forEachVertex([&](DfgVertex& vtx) {
            if (!handledDirectly(vtx)) return;
            if (m_vtx2Scc.at(&vtx)) return;
            mask(vtx).setAllBits1();
        });
        dfg.forEachVertex([&](DfgVertex& vtx) {
            if (!handledDirectly(vtx)) return;
            if (!m_vtx2Scc.at(&vtx)) return;
            iterate(&vtx);
            UINFO(9, "Initial independent bits of " << &vtx << " " << vtx.typeName() << " are: "
                                                    << mask(vtx).displayed(vtx.fileline(), "%b"));
            if (!mask(vtx).isEqZero()) enqueueSinks(vtx);
        });

        // Propagate independent bits until no more changes are made
        while (!m_workList.empty()) {
            // Grab next item
            DfgVertex* const currp = m_workList.front();
            m_workList.pop_front();
            m_onWorkList[currp] = false;
            // Should not enqueue vertices that are not in an SCC
            UASSERT_OBJ(m_vtx2Scc.at(currp), currp, "Vertex should be in an SCC");
            // Should only enqueue packed vertices
            UASSERT_OBJ(handledDirectly(*currp), currp, "Vertex should be handled directly");

            // Grab current mask of item
            const V3Number& currMask = mask(*currp);
            // Remember current mask so we can check if it changed
            const V3Number prevMask = currMask;

            UINFO(9, "Analyzing independent bits of " << currp << " " << currp->typeName());

            // Dispatch it to update the mask in the visit methods
            iterate(currp);

            // If mask changed, enqueue sinks
            if (!prevMask.isCaseEq(currMask)) {
                UINFO(9, "Independent bits of "  //
                             << currp << " " << currp->typeName() << " changed"  //
                             << "\n    form: " << prevMask.displayed(currp->fileline(), "%b")
                             << "\n      to: " << currMask.displayed(currp->fileline(), "%b"));
                enqueueSinks(*currp);
                // Check the mask only ever expands (no bit goes 1 -> 0)
                if (VL_UNLIKELY(v3Global.opt.debugCheck())) {
                    V3Number notCurr{currMask};
                    notCurr.opNot(currMask);
                    V3Number prevAndNotCurr{currMask};
                    prevAndNotCurr.opAnd(prevMask, notCurr);
                    UASSERT_OBJ(prevAndNotCurr.isEqZero(), currp, "Mask should only expand");
                }
            }
        }
    }

public:
    // Given a DfgGraph, and a map from vertices to the SCCs they reside in,
    // returns a map from vertices to a bit mask, where a bit in the mask is
    // set if the corresponding bit in that vertex is known to be independent
    // of the values of vertices in the same SCC as the vertex resides in.
    static std::unordered_map<const DfgVertex*, V3Number> apply(DfgGraph& dfg,
                                                                const Vtx2Scc& vtx2Scc) {
        return std::move(IndependentBits{dfg, vtx2Scc}.m_vtxp2Mask);
    }
};

class FixUp final {
    DfgGraph& m_dfg;  // The graph being processed
    Vtx2Scc& m_vtx2Scc;  // The Vertex to SCC map
    TraceDriver m_traceDriver{m_dfg, m_vtx2Scc};
    // The independent bits map
    const std::unordered_map<const DfgVertex*, V3Number> m_independentBits
        = IndependentBits::apply(m_dfg, m_vtx2Scc);
    size_t m_nImprovements = 0;  // Number of improvements mde

    // Returns a bitmask set if that bit of 'vtx' is used (has a sink)
    static V3Number computeUsedBits(DfgVertex& vtx) {
        V3Number result{vtx.fileline(), static_cast<int>(vtx.width()), 0};
        vtx.foreachSink([&result](DfgVertex& sink) {
            // If used via a Sel, mark the selected bits used
            if (const DfgSel* const selp = sink.cast<DfgSel>()) {
                result.opSetRange(selp->lsb(), selp->width(), '1');
                return false;
            }
            // Used without a Sel, so all bits are used
            result.setAllBits1();
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
            return varp->nodep()->name();
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
                m_vtx2Scc[selp] = m_vtx2Scc.at(vtx);
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
        const V3Number& indpBits = m_independentBits.at(&vtx);
        UINFO(9, "Independent bits of '" << debugStr(vtx) << "' are "
                                         << indpBits.displayed(vtx.fileline(), "%b"));
        // Can't do anything if all bits are dependent
        if (indpBits.isEqZero()) return;

        // Figure out which bits of 'vtxp' are used
        const V3Number usedBits = computeUsedBits(vtx);
        UINFO(9, "Used        bits of '" << debugStr(vtx) << "' are "
                                         << usedBits.displayed(vtx.fileline(), "%b"));

        // Nothing to do if no used bits are independen (all used bits are dependent)
        V3Number usedAndIndependent{vtx.fileline(), static_cast<int>(vtx.width()), 0};
        usedAndIndependent.opAnd(usedBits, indpBits);
        if (usedAndIndependent.isEqZero()) return;

        // We are computing the terms to concatenate and replace 'vtxp' with
        std::vector<DfgVertex*> termps;

        // Iterate through consecutive used/unused ranges
        FileLine* const flp = vtx.fileline();
        const uint32_t width = vtx.width();
        bool isUsed = usedBits.bitIs1(0);  // Is current range used
        uint32_t lsb = 0;  // LSB of current range
        for (uint32_t msb = 0; msb < width; ++msb) {
            const bool endRange = msb == width - 1 || isUsed != usedBits.bitIs1(msb + 1);
            if (!endRange) continue;
            if (isUsed) {
                // The range is used, compute the replacement terms
                gatherTerms(termps, vtx, indpBits, msb, lsb);
            } else {
                // The range is not used, just use constant 0 as a placeholder
                DfgConst* const constp = new DfgConst{m_dfg, flp, msb - lsb + 1, 0};
                m_vtx2Scc[constp] = 0;
                termps.emplace_back(constp);
            }
            // Next iteration
            isUsed = !isUsed;
            lsb = msb + 1;
        }

        // Concatenate all the terms to create the replacement
        DfgVertex* replacementp = termps.front();
        const uint64_t vComp = m_vtx2Scc.at(vtx);
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
            const uint64_t tComp = m_vtx2Scc.at(termp);
            const uint64_t rComp = m_vtx2Scc.at(replacementp);
            m_vtx2Scc[catp] = tComp == vComp || rComp == vComp ? vComp : 0;
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
    }

    void main(DfgVertexVar& var) {
        UINFO(9, "FixUp of " << var.nodep()->name());

        if (var.is<DfgVarPacked>()) {
            // For Packed variables, fix up as whole
            fixUpPacked(var);
        } else if (var.is<DfgVarArray>()) {
            // For array variables, fix up element-wise
            const uint64_t component = m_vtx2Scc.at(var);
            var.foreachSink([&](DfgVertex& sink) {
                // Ignore if sink is not part of same cycle
                if (m_vtx2Scc.at(sink) != component) return false;
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

    FixUp(DfgGraph& dfg, Vtx2Scc& vtx2Scc)
        : m_dfg{dfg}
        , m_vtx2Scc{vtx2Scc} {}

public:
    // Compute which bits of vertices are independent of the SCC they reside
    // in, and replace rferences to used independent bits with an equivalent
    // vertex that is not part of the same SCC.
    static size_t apply(DfgGraph& dfg, Vtx2Scc& vtx2Scc) {
        FixUp fixUp{dfg, vtx2Scc};

        // TODO: Compute minimal feedback vertex set and cut only those.
        //       Sadly that is a computationally hard problem.

        // Fix up cyclic variables
        for (DfgVertexVar& vtx : dfg.varVertices()) {
            if (vtx2Scc.at(vtx)) fixUp.main(vtx);
        }
        // Return the number of improvements made
        return fixUp.m_nImprovements;
    }
};

std::pair<std::unique_ptr<DfgGraph>, bool>  //
breakCycles(const DfgGraph& dfg, V3DfgContext& ctx) {
    // Shorthand for dumping graph at given dump level
    const auto dump = [&](int level, const DfgGraph& dfg, const std::string& name) {
        if (dumpDfgLevel() >= level) dfg.dumpDotFilePrefixed(ctx.prefix() + "breakCycles-" + name);
    };

    // Can't do much with trivial things ('a = a' or 'a[1] = a[0]'), so bail
    if (dfg.size() <= 2) {
        UINFO(7, "Graph is trivial");
        dump(9, dfg, "trivial");
        ++ctx.m_breakCyclesContext.m_nTrivial;
        return {nullptr, false};
    }

    // AstNetlist/AstNodeModule user2 used as sequence numbers for temporaries
    const VNUser2InUse user2InUse;

    // Show input for debugging
    dump(7, dfg, "input");

    // We might fail to make any improvements, so first create a clone of the
    // graph. This is what we will be working on, and return if successful.
    // Do not touch the input graph.
    std::unique_ptr<DfgGraph> resultp = dfg.clone();
    // Just shorthand for code below
    DfgGraph& res = *resultp;
    dump(9, res, "clone");

    // How many improvements have we made
    size_t nImprovements = 0;
    size_t prevNImprovements;

    // Iterate while an improvement can be made and the graph is still cyclic
    do {
        // Color SCCs (populates DfgVertex::user<uint64_t>())
        Vtx2Scc vtx2Scc = res.makeUserMap<uint64_t>();
        const uint32_t numNonTrivialSCCs
            = V3DfgPasses::colorStronglyConnectedComponents(res, vtx2Scc);

        // Congrats if it has become acyclic
        if (!numNonTrivialSCCs) {
            UINFO(7, "Graph became acyclic after " << nImprovements << " improvements");
            dump(7, res, "result-acyclic");
            ++ctx.m_breakCyclesContext.m_nFixed;
            return {std::move(resultp), true};
        }

        // Fix up independent ranges in vertices
        UINFO(9, "New iteration after " << nImprovements << " improvements");
        prevNImprovements = nImprovements;
        const size_t nFixed = FixUp::apply(res, vtx2Scc);
        if (nFixed) {
            nImprovements += nFixed;
            ctx.m_breakCyclesContext.m_nImprovements += nFixed;
            dump(9, res, "FixUp");
        }
    } while (nImprovements != prevNImprovements);

    if (dumpDfgLevel() >= 9) {
        Vtx2Scc vtx2Scc = res.makeUserMap<uint64_t>();
        V3DfgPasses::colorStronglyConnectedComponents(res, vtx2Scc);
        res.dumpDotFilePrefixed(ctx.prefix() + "breakCycles-remaining", [&](const DfgVertex& vtx) {
            return vtx2Scc[vtx];  //
        });
    }

    // If an improvement was made, return the still cyclic improved graph
    if (nImprovements) {
        UINFO(7, "Graph was improved " << nImprovements << " times");
        dump(7, res, "result-improved");
        ++ctx.m_breakCyclesContext.m_nImproved;
        return {std::move(resultp), false};
    }

    // No improvement was made
    UINFO(7, "Graph NOT improved");
    dump(7, res, "result-original");
    ++ctx.m_breakCyclesContext.m_nUnchanged;
    return {nullptr, false};
}

}  //namespace V3DfgBreakCycles

std::pair<std::unique_ptr<DfgGraph>, bool>  //
V3DfgPasses::breakCycles(const DfgGraph& dfg, V3DfgContext& ctx) {
    auto pair = V3DfgBreakCycles::breakCycles(dfg, ctx);
    if (pair.first) {
        if (v3Global.opt.debugCheck()) V3DfgPasses::typeCheck(*pair.first);
        V3DfgPasses::removeUnused(*pair.first);
    }
    return pair;
}
