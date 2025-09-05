// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Converting cyclic DFGs into acyclic DFGs
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2025 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Dfg.h"
#include "V3DfgPasses.h"
#include "V3Hash.h"

#include <algorithm>
#include <deque>
#include <fstream>
#include <limits>
#include <unordered_map>
#include <vector>

VL_DEFINE_DEBUG_FUNCTIONS;

// Throughout these algorithm, we use the DfgUserMap as a map to the SCC number
using Vtx2Scc = DfgUserMap<uint64_t>;

class TraceDriver final : public DfgVisitor {
    // TYPES

    // Structure denoting currently visited vertex with the MSB and LSB we are searching for
    struct Visited final {
        DfgVertex* m_vtxp;
        uint32_t m_lsb;
        uint32_t m_msb;

        Visited() = delete;
        Visited(DfgVertex* vtxp, uint32_t lsb, uint32_t msb)
            : m_vtxp{vtxp}
            , m_lsb{lsb}
            , m_msb{msb} {}

        struct Hash final {
            size_t operator()(const Visited& item) const {
                // cppcheck-suppress unreadVariable
                V3Hash hash{item.m_vtxp};
                hash += item.m_lsb;
                hash += item.m_msb;
                return hash.value();
            }
        };

        struct Equal final {
            bool operator()(const Visited& a, const Visited& b) const {
                return a.m_vtxp == b.m_vtxp && a.m_lsb == b.m_lsb && a.m_msb == b.m_msb;
            }
        };
    };

    // STATE
    DfgGraph& m_dfg;  // The graph being processed
    Vtx2Scc& m_vtx2Scc;  // The Vertex to SCC map
    // The strongly connected component we are trying to escape
    const uint64_t m_component;
    const bool m_aggressive;  // Trace aggressively, creating intermediate ops
    uint32_t m_lsb = 0;  // LSB to extract from the currently visited Vertex
    uint32_t m_msb = 0;  // MSB to extract from the currently visited Vertex
    DfgVertex* m_defaultp = nullptr;  // When tracing a variable, this is its 'defaultp', if any
    // Result of tracing the currently visited Vertex. Use SET_RESULT below!
    DfgVertex* m_resp = nullptr;
    std::vector<DfgVertex*> m_newVtxps;  // New vertices created during the traversal

    std::vector<Visited> m_stack;  // Stack of currently visited vertices
    // Denotes if a 'Visited' entry appear in m_stack
    std::unordered_map<Visited, bool, Visited::Hash, Visited::Equal> m_visited;

#ifdef VL_DEBUG
    std::ofstream m_lineCoverageFile;  // Line coverage file, just for testing
#endif

    // METHODS

    // Create and return a new Vertex and add it to m_newVtxps. Fileline is
    // taken from 'refp', but 'refp' is otherwise not used. You should
    // always use this to create new vertices, so unused ones (if a trace
    // eventually fails) can be cleaned up at the end. This also sets the
    // vertex user<uint64_t> to 0, indicating the new vertex is not part of a
    // strongly connected component. This should always be true, as all the
    // vertices we create here are driven from outside the component we are
    // trying to escape, and will sink into that component. Given those are
    // separate SCCs, these new vertices must be acyclic.
    template <typename Vertex>
    Vertex* make(const DfgVertex* refp, uint32_t width) {
        static_assert(std::is_base_of<DfgVertex, Vertex>::value  //
                          && !std::is_base_of<DfgVertexVar, Vertex>::value,
                      "Should only make operation vertices and constants");

        constexpr bool okWithoutAggressive =  //
            std::is_same<DfgConst, Vertex>::value  //
            || std::is_same<DfgSel, Vertex>::value  //
            || std::is_same<DfgConcat, Vertex>::value  //
            || std::is_same<DfgExtend, Vertex>::value;

        UASSERT_OBJ(
            okWithoutAggressive || m_aggressive, refp,
            "Should only create Const, Sel, Concat, Exend Vertices without aggressive mode");

        if VL_CONSTEXPR_CXX17 (std::is_same<DfgConst, Vertex>::value) {
            DfgConst* const vtxp = new DfgConst{m_dfg, refp->fileline(), width, 0};
            m_vtx2Scc[vtxp] = 0;
            m_newVtxps.emplace_back(vtxp);
            return reinterpret_cast<Vertex*>(vtxp);
        } else {
            // TODO: this is a gross hack around lack of C++17 'if constexpr' Vtx is always Vertex
            // when this code is actually executed, but needs a fudged type to type check when
            // Vertex is DfgConst, in which case this code is unreachable ...
            using Vtx = typename std::conditional<std::is_same<DfgConst, Vertex>::value, DfgSel,
                                                  Vertex>::type;
            Vtx* const vtxp = new Vtx{m_dfg, refp->fileline(), DfgDataType::packed(width)};
            m_vtx2Scc[vtxp] = 0;
            m_newVtxps.emplace_back(vtxp);
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
        return varp;
    }

    // Continue tracing drivers of the given vertex, at the given LSB. Every
    // visitor should call this to continue the traversal, then immediately
    // return after the call. 'visit' methods should not call 'iterate', call
    // this method instead, which checks for cycles.
    DfgVertex* trace(DfgVertex* const vtxp, const uint32_t msb, const uint32_t lsb) {
        UASSERT_OBJ(vtxp->isPacked(), vtxp, "Can only trace packed type vertices");
        UASSERT_OBJ(vtxp->size() > msb, vtxp, "Traced Vertex too narrow");

        // Push to stack
        m_stack.emplace_back(vtxp, msb, lsb);
        bool& onStackr = m_visited[m_stack.back()];

        // Check for true combinational cycles
        if (onStackr) {
            // Pop from stack
            m_stack.pop_back();

            // Note: could issue a "proper combinational cycle" error here,
            // but constructing a legible error message is hard as the Vertex
            // Filelines can be very rough after optimizations (could consider
            // reporting only the variables involved). Also this pass might
            // run mulitple times and report the same error again. There will
            // be an UNOPTFLAT issued during scheduling anyway, and the true
            // cycle might still settle at run-time.

            // Stop trace
            return nullptr;
        }

        // Trace the vertex
        onStackr = true;

        // If the currently traced vertex is in a different component,
        // then we found what we were looking for.
        if (m_vtx2Scc[vtxp] != m_component) {
            m_resp = vtxp;
            // If the result is a splice, we need to insert a temporary for it
            // as a splice cannot be fed into arbitray logic
            if (DfgVertexSplice* const splicep = m_resp->cast<DfgVertexSplice>()) {
                DfgVertexVar* const tmpp = createTmp("TraceDriver", splicep);
                splicep->replaceWith(tmpp);
                tmpp->srcp(splicep);
                m_resp = tmpp;
            }
            // Apply a Sel to extract the relevant bits if only a part is needed
            if (msb != m_resp->width() - 1 || lsb != 0) {
                DfgSel* const selp = make<DfgSel>(m_resp, msb - lsb + 1);
                selp->fromp(m_resp);
                selp->lsb(lsb);
                m_resp = selp;
            }
        } else {
            // Otherwise visit the vertex
            VL_RESTORER(m_msb);
            VL_RESTORER(m_lsb);
            m_msb = msb;
            m_lsb = lsb;
            m_resp = nullptr;
            iterate(vtxp);
        }
        UASSERT_OBJ(!m_resp || m_resp->width() == (msb - lsb + 1), vtxp, "Wrong result width");

        // Pop from stack
        onStackr = false;
        m_stack.pop_back();

        // Done
        if (!m_resp) {
            UINFO(9, "TraceDriver - Failed to trace vertex of type: " << vtxp->typeName());
        }
        return m_resp;
    }

    template <typename Vertex>
    Vertex* traceBitwiseBinary(Vertex* vtxp) {
        static_assert(std::is_base_of<DfgVertexBinary, Vertex>::value,
                      "Should only call on DfgVertexBinary");
        if (DfgVertex* const rp = trace(vtxp->rhsp(), m_msb, m_lsb)) {
            if (DfgVertex* const lp = trace(vtxp->lhsp(), m_msb, m_lsb)) {
                Vertex* const resp = make<Vertex>(vtxp, m_msb - m_lsb + 1);
                resp->rhsp(rp);
                resp->lhsp(lp);
                return resp;
            }
        }
        return nullptr;
    }

    template <typename Vertex>
    DfgVertex* traceAddSub(Vertex* vtxp) {
        static_assert(std::is_base_of<DfgVertexBinary, Vertex>::value,
                      "Should only call on DfgVertexBinary");
        if (DfgVertex* const rp = trace(vtxp->rhsp(), m_msb, 0)) {
            if (DfgVertex* const lp = trace(vtxp->lhsp(), m_msb, 0)) {
                Vertex* const opp = make<Vertex>(vtxp, m_msb + 1);
                opp->rhsp(rp);
                opp->lhsp(lp);
                DfgSel* const selp = make<DfgSel>(vtxp, m_msb - m_lsb + 1);
                selp->fromp(opp);
                selp->lsb(m_lsb);
                return selp;
            }
        }
        return nullptr;
    }

    template <typename Vertex>
    Vertex* traceCmp(Vertex* vtxp) {
        static_assert(std::is_base_of<DfgVertexBinary, Vertex>::value,
                      "Should only call on DfgVertexBinary");
        if (DfgVertex* const rp = trace(vtxp->rhsp(), vtxp->rhsp()->width() - 1, 0)) {
            if (DfgVertex* const lp = trace(vtxp->lhsp(), vtxp->lhsp()->width() - 1, 0)) {
                Vertex* const resp = make<Vertex>(vtxp, m_msb - m_lsb + 1);
                resp->rhsp(rp);
                resp->lhsp(lp);
                return resp;
            }
        }
        return nullptr;
    }

    // Predicate to do determine if vtxp[$bits(vtxp)-1:idx] is known to be zero
    // Somewhat rudimentary but sufficient for current purposes.
    static bool knownToBeZeroAtAndAbove(const DfgVertex* vtxp, uint32_t idx) {
        if (const DfgConcat* const catp = vtxp->cast<DfgConcat>()) {
            const DfgConst* const lConstp = catp->lhsp()->cast<DfgConst>();
            return lConstp && idx >= catp->rhsp()->width() && lConstp->isZero();
        }
        if (const DfgExtend* const extp = vtxp->cast<DfgExtend>()) {
            return idx >= extp->srcp()->width();
        }
        return false;
    }

    // Like knownToBeZeroAtAndAbove, but checks vtxp[idx:0]
    static bool knownToBeZeroAtAndBelow(const DfgVertex* vtxp, uint32_t idx) {
        if (const DfgConcat* const catp = vtxp->cast<DfgConcat>()) {
            const DfgConst* const rConstp = catp->rhsp()->cast<DfgConst>();
            return rConstp && idx < rConstp->width() && rConstp->isZero();
        }
        return false;
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
    void visit(DfgVertex* vtxp) override {
        // Base case: cannot continue ...
        UINFO(9, "TraceDriver - Unhandled vertex type: " << vtxp->typeName());
    }

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

        // Look at all the drivers, one might cover the whole range, but also gathe all drivers
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

        // Sort ragnes (they are non-overlapping)
        std::sort(drivers.begin(), drivers.end(),
                  [](const Driver& a, const Driver& b) { return a.m_lsb < b.m_lsb; });

        // Gather terms
        std::vector<DfgVertex*> termps;
        for (const Driver& driver : drivers) {
            // Driver is below the searched LSB, move on
            if (m_lsb > driver.m_msb) continue;
            // Driver is above the searched MSB, done
            if (driver.m_lsb > m_msb) break;
            // Gap below this driver, trace default to fill it
            if (driver.m_lsb > m_lsb) {
                if (!m_defaultp) return;
                DfgVertex* const termp = trace(m_defaultp, driver.m_lsb - 1, m_lsb);
                if (!termp) return;
                termps.emplace_back(termp);
                m_lsb = driver.m_lsb;
            }
            // Driver covers searched range, pick the needed/available bits
            uint32_t lim = std::min(m_msb, driver.m_msb);
            DfgVertex* const termp
                = trace(driver.m_vtxp, lim - driver.m_lsb, m_lsb - driver.m_lsb);
            if (!termp) return;
            termps.emplace_back(termp);
            m_lsb = lim + 1;
        }
        if (m_msb >= m_lsb) {
            if (!m_defaultp) return;
            DfgVertex* const termp = trace(m_defaultp, m_msb, m_lsb);
            if (!termp) return;
            termps.emplace_back(termp);
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
        VL_RESTORER(m_defaultp);
        m_defaultp = vtxp->defaultp();
        if (DfgVertex* const srcp = vtxp->srcp()) {
            SET_RESULT(trace(srcp, m_msb, m_lsb));
            return;
        }
    }

    void visit(DfgArraySel* vtxp) override {
        // Only constant select
        const DfgConst* const idxp = vtxp->bitp()->cast<DfgConst>();
        if (!idxp) return;
        // From a variable
        const DfgVarArray* varp = vtxp->fromp()->cast<DfgVarArray>();
        if (!varp) return;
        // Skip through intermediate variables
        while (varp->srcp() && varp->srcp()->is<DfgVarArray>()) {
            varp = varp->srcp()->as<DfgVarArray>();
        }
        // Find driver
        if (!varp->srcp()) return;

        // Driver might be a splice
        if (const DfgSpliceArray* const splicep = varp->srcp()->cast<DfgSpliceArray>()) {
            const DfgVertex* const driverp = splicep->driverAt(idxp->toSizeT());
            if (!driverp) return;
            const DfgUnitArray* const uap = driverp->cast<DfgUnitArray>();
            if (!uap) return;
            // Trace the driver
            SET_RESULT(trace(uap->srcp(), m_msb, m_lsb));
            return;
        }

        // Or a unit array
        const DfgUnitArray* const uap = varp->srcp()->cast<DfgUnitArray>();
        if (!uap) return;
        // Trace the driver
        UASSERT_OBJ(idxp->toSizeT() == 0, vtxp, "Array Index out of range");
        SET_RESULT(trace(uap->srcp(), m_msb, m_lsb));
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
        // The traced bit spans both sides, attempt to trace both
        if (DfgVertex* const rp = trace(rhsp, rWidth - 1, m_lsb)) {
            if (DfgVertex* const lp = trace(lhsp, m_msb - rWidth, 0)) {
                DfgConcat* const resp = make<DfgConcat>(vtxp, m_msb - m_lsb + 1);
                resp->rhsp(rp);
                resp->lhsp(lp);
                SET_RESULT(resp);
                return;
            }
        }
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
        if (DfgVertex* const sp = trace(srcp, sWidth - 1, m_lsb)) {
            DfgExtend* const resp = make<DfgExtend>(vtxp, m_msb - m_lsb + 1);
            resp->srcp(sp);
            SET_RESULT(resp);
            return;
        }
    }

    void visit(DfgSel* vtxp) override {
        const uint32_t lsb = vtxp->lsb();
        SET_RESULT(trace(vtxp->srcp(), m_msb + lsb, m_lsb + lsb));
        return;
    }

    void visit(DfgNot* vtxp) override {
        if (!m_aggressive) return;
        if (DfgVertex* const sp = trace(vtxp->srcp(), m_msb, m_lsb)) {
            DfgNot* const resp = make<DfgNot>(vtxp, m_msb - m_lsb + 1);
            resp->srcp(sp);
            SET_RESULT(resp);
            return;
        }
    }

    void visit(DfgAnd* vtxp) override {
        if (!m_aggressive) return;
        SET_RESULT(traceBitwiseBinary(vtxp));
    }
    void visit(DfgOr* vtxp) override {
        if (!m_aggressive) return;
        SET_RESULT(traceBitwiseBinary(vtxp));
    }
    void visit(DfgXor* vtxp) override {
        if (!m_aggressive) return;
        SET_RESULT(traceBitwiseBinary(vtxp));
    }
    void visit(DfgAdd* vtxp) override {
        if (!m_aggressive) return;
        SET_RESULT(traceAddSub(vtxp));
    }
    void visit(DfgSub* vtxp) override {
        if (!m_aggressive) return;
        SET_RESULT(traceAddSub(vtxp));
    }
    void visit(DfgEq* vtxp) override {
        if (!m_aggressive) return;
        SET_RESULT(traceCmp(vtxp));
    }
    void visit(DfgNeq* vtxp) override {
        if (!m_aggressive) return;
        SET_RESULT(traceCmp(vtxp));
    }
    void visit(DfgLt* vtxp) override {
        if (!m_aggressive) return;
        SET_RESULT(traceCmp(vtxp));
    }
    void visit(DfgLte* vtxp) override {
        if (!m_aggressive) return;
        SET_RESULT(traceCmp(vtxp));
    }
    void visit(DfgGt* vtxp) override {
        if (!m_aggressive) return;
        SET_RESULT(traceCmp(vtxp));
    }
    void visit(DfgGte* vtxp) override {
        if (!m_aggressive) return;
        SET_RESULT(traceCmp(vtxp));
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
            if (DfgVertex* const sp = trace(lhsp, lowerWidth - 1 + shiftAmnt, m_lsb + shiftAmnt)) {
                DfgExtend* const resp = make<DfgExtend>(vtxp, m_msb - m_lsb + 1);
                resp->srcp(sp);
                SET_RESULT(resp);
                return;
            }
            return;
        }

        // The shift amount is non-negative, so we can conclude zero if all
        // bits at and above the LSB we seek are zeroes
        if (knownToBeZeroAtAndAbove(lhsp, m_lsb)) {
            SET_RESULT(make<DfgConst>(vtxp, m_msb - m_lsb + 1));
            return;
        }
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
            if (DfgVertex* const sp = trace(lhsp, m_msb - shiftAmnt, lowerWidth - shiftAmnt)) {
                DfgConcat* const resp = make<DfgConcat>(vtxp, m_msb - m_lsb + 1);
                resp->rhsp(make<DfgConst>(vtxp, resp->width() - sp->width()));
                resp->lhsp(sp);
                SET_RESULT(resp);
                return;
            }
            return;
        }

        // The shift amount is non-negative, so we can conclude zero if all
        // bits at and below the MSB we seek are zeroes
        if (knownToBeZeroAtAndBelow(lhsp, m_msb)) {
            SET_RESULT(make<DfgConst>(vtxp, m_msb - m_lsb + 1));
            return;
        }
    }

    void visit(DfgCond* vtxp) override {
        if (!m_aggressive) return;
        if (DfgVertex* const condp = trace(vtxp->condp(), 0, 0)) {
            if (DfgVertex* const thenp = trace(vtxp->thenp(), m_msb, m_lsb)) {
                if (DfgVertex* const elsep = trace(vtxp->elsep(), m_msb, m_lsb)) {
                    DfgCond* const resp = make<DfgCond>(vtxp, m_msb - m_lsb + 1);
                    resp->condp(condp);
                    resp->thenp(thenp);
                    resp->elsep(elsep);
                    SET_RESULT(resp);
                    return;
                }
            }
        }
    }

#undef SET_RESULT

    // CONSTRUCTOR
    TraceDriver(DfgGraph& dfg, Vtx2Scc& vtx2Scc, uint64_t component, bool aggressive)
        : m_dfg{dfg}
        , m_vtx2Scc{vtx2Scc}
        , m_component{component}
        , m_aggressive{aggressive} {
#ifdef VL_DEBUG
        if (v3Global.opt.debugCheck()) {
            m_lineCoverageFile.open(  //
                v3Global.opt.makeDir() + "/" + v3Global.opt.prefix()
                    + "__V3DfgBreakCycles-TraceDriver-line-coverage.txt",  //
                std::ios_base::out | std::ios_base::app);
        }
#endif
    }

public:
    // Given a Vertex that is part of an SCC denoted by vtx2Scc,
    // return a vertex that is equivalent to 'vtxp[lsb +: width]', but is not
    // part of the same SCC. Returns nullptr if such a vertex cannot be
    // computed. This can add new vertices to the graph. The 'aggressive' flag
    // enables creating many intermediate operations. This should only be set
    // if it is reasonably certain the tracing will succeed, otherwise we can
    // waste a lot of compute.
    static DfgVertex* apply(DfgGraph& dfg, Vtx2Scc& vtx2Scc, DfgVertex& vtx, uint32_t lsb,
                            uint32_t width, bool aggressive) {
        TraceDriver traceDriver{dfg, vtx2Scc, vtx2Scc[vtx], aggressive};
        // Find the out-of-component driver of the given vertex
        DfgVertex* const resultp = traceDriver.trace(&vtx, lsb + width - 1, lsb);
        // Delete unused newly created vertices (these can be created if a
        // partial trace succeded, but an eventual one falied). Because new
        // vertices should be created depth first, it is enough to do a single
        // reverse pass over the collectoin
        for (DfgVertex* const newp : vlstd::reverse_view(traceDriver.m_newVtxps)) {
            // Keep the actual result!
            if (newp == resultp) continue;
            // Keep used ones!
            if (newp->hasSinks()) continue;
            // Delete it
            VL_DO_DANGLING(newp->unlinkDelete(dfg), newp);
        }
        // Return the result
        return resultp;
    }
};

class IndependentBits final : public DfgVisitor {
    // STATE
    const Vtx2Scc& m_vtx2Scc;  // The Vertex to SCC map
    const uint64_t m_component;  // The component the start vertex is part of
    // Vertex to current bit mask map. The mask is set for the bits that **depend** on 'm_varp'.
    std::unordered_map<const DfgVertex*, V3Number> m_vtxp2Mask;

    std::ofstream m_lineCoverageFile;  // Line coverage file, just for testing

    // METHODS
    // Retrieve the mask for the given vertex (create it with value 0 if needed)
    V3Number& mask(const DfgVertex* vtxp) {
        // Look up (or create) mask for 'vtxp'
        auto pair = m_vtxp2Mask.emplace(
            std::piecewise_construct,  //
            std::forward_as_tuple(vtxp),  //
            std::forward_as_tuple(vtxp->fileline(), static_cast<int>(vtxp->width()), 0));
        // Initialize to all ones if the vertex is part of the same component, otherwise zeroes
        if (pair.second && m_vtx2Scc.at(vtxp) == m_component) { pair.first->second.setAllBits1(); }
        return pair.first->second;
    }

    // Use this macro to call 'mask' in 'visit' methods. This also emits
    // a line to m_lineCoverageFile for testing.
    // TODO: Use C++20 std::source_location instead of a macro
#ifdef VL_DEBUG
#define MASK(vtxp) \
    ([this](const DfgVertex* p) -> V3Number& { \
        if (VL_UNLIKELY(m_lineCoverageFile.is_open())) m_lineCoverageFile << __LINE__ << '\n'; \
        return mask(p); \
    }(vtxp))
#else
#define MASK(vtxp) mask(vtxp)
#endif

    // Set all bits at or below the most signicant set bit
    void floodTowardsLsb(V3Number& num) {
        bool set = false;
        for (int i = num.width() - 1; i >= 0; --i) {
            if (num.bitIs1(i)) set = true;
            if (set) num.setBit(i, '1');
        }
    }

    // Set all bits at or above the least signicant set bit
    void floodTowardsMsb(V3Number& num) {
        bool set = false;
        for (int i = 0; i < num.width(); ++i) {
            if (num.bitIs1(i)) set = true;
            if (set) num.setBit(i, '1');
        }
    }

    // VISITORS
    void visit(DfgVertex* vtxp) override {
        UINFO(9, "IndependentBits - Unhandled vertex type: " << vtxp->typeName());
        // Conservative assumption about all bits being dependent prevails
    }

    void visit(DfgSplicePacked* vtxp) override {
        // Combine the masks of all drivers
        V3Number& m = MASK(vtxp);
        vtxp->foreachDriver([&](DfgVertex& src, uint32_t lo) {
            m.opSelInto(MASK(&src), lo, src.width());
            return false;
        });
    }

    void visit(DfgVarPacked* vtxp) override {
        DfgVertex* const srcp = vtxp->srcp();
        if (srcp && srcp->is<DfgSpliceArray>()) return;

        V3Number& m = MASK(vtxp);
        DfgVertex* const defaultp = vtxp->defaultp();
        if (defaultp) m = MASK(defaultp);
        if (!srcp) return;

        if (DfgSplicePacked* const splicep = srcp->cast<DfgSplicePacked>()) {
            splicep->foreachDriver([&](DfgVertex& src, uint32_t lo) {
                m.opSelInto(MASK(&src), lo, src.width());
                return false;
            });
            return;
        }

        m = MASK(srcp);
    }

    void visit(DfgArraySel* vtxp) override {
        // Only constant select
        const DfgConst* const idxp = vtxp->bitp()->cast<DfgConst>();
        if (!idxp) return;
        // From a variable
        const DfgVarArray* varp = vtxp->fromp()->cast<DfgVarArray>();
        if (!varp) return;
        // Skip through intermediate variables
        while (varp->srcp() && varp->srcp()->is<DfgVarArray>()) {
            varp = varp->srcp()->as<DfgVarArray>();
        }
        // Find driver
        if (!varp->srcp()) return;
        const DfgSpliceArray* const splicep = varp->srcp()->cast<DfgSpliceArray>();
        if (!splicep) return;
        const DfgVertex* const driverp = splicep->driverAt(idxp->toSizeT());
        if (!driverp) return;
        const DfgUnitArray* const uap = driverp->cast<DfgUnitArray>();
        if (!uap) return;
        // Update mask
        MASK(vtxp) = MASK(uap->srcp());
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
        V3Number& m = MASK(vtxp);
        m.opSelInto(MASK(srcp), 0, sWidth);
        m.opSetRange(sWidth, vtxp->width() - sWidth, '0');
    }

    void visit(DfgNot* vtxp) override {  //
        MASK(vtxp) = MASK(vtxp->srcp());
    }

    void visit(DfgAnd* vtxp) override {  //
        MASK(vtxp).opOr(MASK(vtxp->lhsp()), MASK(vtxp->rhsp()));
    }
    void visit(DfgOr* vtxp) override {  //
        MASK(vtxp).opOr(MASK(vtxp->lhsp()), MASK(vtxp->rhsp()));
    }
    void visit(DfgXor* vtxp) override {  //
        MASK(vtxp).opOr(MASK(vtxp->lhsp()), MASK(vtxp->rhsp()));
    }

    void visit(DfgAdd* vtxp) override {
        V3Number& m = MASK(vtxp);
        m.opOr(MASK(vtxp->lhsp()), MASK(vtxp->rhsp()));
        floodTowardsMsb(m);
    }
    void visit(DfgSub* vtxp) override {  // Same as Add: 2's complement (a - b) == (a + ~b + 1)
        V3Number& m = MASK(vtxp);
        m.opOr(MASK(vtxp->lhsp()), MASK(vtxp->rhsp()));
        floodTowardsMsb(m);
    }

    void visit(DfgEq* vtxp) override {
        const bool independent = MASK(vtxp->lhsp()).isEqZero() && MASK(vtxp->rhsp()).isEqZero();
        MASK(vtxp).setBit(0, independent ? '0' : '1');
    }
    void visit(DfgNeq* vtxp) override {
        const bool independent = MASK(vtxp->lhsp()).isEqZero() && MASK(vtxp->rhsp()).isEqZero();
        MASK(vtxp).setBit(0, independent ? '0' : '1');
    }
    void visit(DfgLt* vtxp) override {
        const bool independent = MASK(vtxp->lhsp()).isEqZero() && MASK(vtxp->rhsp()).isEqZero();
        MASK(vtxp).setBit(0, independent ? '0' : '1');
    }
    void visit(DfgLte* vtxp) override {
        const bool independent = MASK(vtxp->lhsp()).isEqZero() && MASK(vtxp->rhsp()).isEqZero();
        MASK(vtxp).setBit(0, independent ? '0' : '1');
    }
    void visit(DfgGt* vtxp) override {
        const bool independent = MASK(vtxp->lhsp()).isEqZero() && MASK(vtxp->rhsp()).isEqZero();
        MASK(vtxp).setBit(0, independent ? '0' : '1');
    }
    void visit(DfgGte* vtxp) override {
        const bool independent = MASK(vtxp->lhsp()).isEqZero() && MASK(vtxp->rhsp()).isEqZero();
        MASK(vtxp).setBit(0, independent ? '0' : '1');
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
                m.setAllBits0();
            } else {
                m.opShiftR(MASK(lhsp), rConstp->num());
            }
            return;
        }

        // Otherwise, as the shift amount is non-negative, any bit at or below
        // the most significant dependent bit might be dependent
        V3Number& m = MASK(vtxp);
        m = MASK(lhsp);
        floodTowardsLsb(m);
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
                m.setAllBits0();
            } else {
                m.opShiftL(MASK(lhsp), rConstp->num());
            }
            return;
        }

        // Otherwise, as the shift amount is non-negative, any bit at or above
        // the least significant dependent bit might be dependent
        V3Number& m = MASK(vtxp);
        m = MASK(lhsp);
        floodTowardsMsb(m);
    }

    void visit(DfgCond* vtxp) override {
        if (!MASK(vtxp->condp()).isEqZero()) {
            MASK(vtxp).setAllBits1();
        } else {
            MASK(vtxp).opOr(MASK(vtxp->thenp()), MASK(vtxp->elsep()));
        }
    }

#undef MASK

    // CONSTRUCTOR
    IndependentBits(DfgGraph& dfg, const Vtx2Scc& vtx2Scc, DfgVertex& vertex)
        : m_vtx2Scc{vtx2Scc}
        , m_component{m_vtx2Scc.at(vertex)} {

#ifdef VL_DEBUG
        if (v3Global.opt.debugCheck()) {
            m_lineCoverageFile.open(  //
                v3Global.opt.makeDir() + "/" + v3Global.opt.prefix()
                    + "__V3DfgBreakCycles-IndependentBits-line-coverage.txt",  //
                std::ios_base::out | std::ios_base::app);
        }
#endif

        // Work list for the traversal
        std::deque<DfgVertex*> workList;

        // Enqueue every operation vertex in the analysed component
        for (DfgVertex& vtx : dfg.opVertices()) {
            if (m_vtx2Scc.at(vtx) == m_component) workList.emplace_back(&vtx);
        }

        // While there is an item on the worklist ...
        while (!workList.empty()) {
            // Grab next item
            DfgVertex* const currp = workList.front();
            workList.pop_front();

            if (currp->isArray()) {
                // For an unpacked array vertex, just enque it's sinks.
                // (There can be no loops through arrays directly)
                currp->foreachSink([&](DfgVertex& vtx) {
                    if (m_vtx2Scc.at(vtx) == m_component) workList.emplace_back(&vtx);
                    return false;
                });
                continue;
            }

            // Grab current mask of item
            const V3Number& maskCurr = mask(currp);
            // Remember current mask
            const V3Number prevMask = maskCurr;

            // Dispatch
            iterate(currp);

            // If mask changed, enqueue sinks
            if (!prevMask.isCaseEq(maskCurr)) {
                currp->foreachSink([&](DfgVertex& vtx) {
                    if (m_vtx2Scc.at(vtx) == m_component) workList.emplace_back(&vtx);
                    return false;
                });

                // Check the mask only ever contrects (no bit goes 0 -> 1)
                if (VL_UNLIKELY(v3Global.opt.debugCheck())) {
                    V3Number notPrev{prevMask};
                    notPrev.opNot(prevMask);
                    V3Number notPrevAndCurr{maskCurr};
                    notPrevAndCurr.opAnd(notPrev, maskCurr);
                    UASSERT_OBJ(notPrevAndCurr.isEqZero(), currp, "Mask should only contract");
                }
            }
        }
    }

public:
    // Given a Vertex that is part of an SCC denoted by vtxp->user<uint64_t>(),
    // compute which bits of this vertex have a value that is independent of
    // the current value of the Vertex itself (simple forward dataflow
    // analysis). Returns a bit mask where a set bit indicates that bit is
    // independent of the vertex itself (logic is not circular). The result is
    // a conservative estimate, so bits reported dependent might not actually
    // be, but all bits reported independent are known to be so.
    static V3Number apply(DfgGraph& dfg, const Vtx2Scc& vtx2Scc, DfgVertex& vtx) {
        IndependentBits independentBits{dfg, vtx2Scc, vtx};
        // The mask represents the dependent bits, so invert it
        V3Number result{vtx.fileline(), static_cast<int>(vtx.width()), 0};
        result.opNot(independentBits.mask(&vtx));
        return result;
    }
};

class FixUpSelDrivers final {
    DfgGraph& m_dfg;  // The graph being processed
    Vtx2Scc& m_vtx2Scc;  // The Vertex to SCC map
    size_t m_nImprovements = 0;  // Number of improvements mde

    void fixUpSelSinks(DfgVertex& vtx) {
        const uint64_t component = m_vtx2Scc[vtx];
        vtx.foreachSink([&](DfgVertex& sink) {
            // Ignore if sink is not part of same cycle
            if (m_vtx2Scc[sink] != component) return false;
            // Only handle Sel
            DfgSel* const selp = sink.cast<DfgSel>();
            if (!selp) return false;
            // Try to find the driver of the selected bits outside the cycle
            DfgVertex* const fixp
                = TraceDriver::apply(m_dfg, m_vtx2Scc, vtx, selp->lsb(), selp->width(), false);
            if (!fixp) return false;
            // Found an out-of-cycle driver. We can replace this sel with that.
            selp->replaceWith(fixp);
            selp->unlinkDelete(m_dfg);
            ++m_nImprovements;
            return false;
        });
    }

    void fixUpArraySelSinks(DfgVertex& vtx) {
        const uint64_t component = m_vtx2Scc[vtx];
        vtx.foreachSink([&](DfgVertex& sink) {
            // Ignore if sink is not part of same cycle
            if (m_vtx2Scc[sink] != component) return false;
            // Only handle ArraySels
            DfgArraySel* const asp = sink.cast<DfgArraySel>();
            if (!asp) return false;
            // First, try to fix up the whole word
            DfgVertex* const fixp
                = TraceDriver::apply(m_dfg, m_vtx2Scc, *asp, 0, asp->width(), false);
            if (fixp) {
                // Found an out-of-cycle driver for the whole ArraySel
                asp->replaceWith(fixp);
                asp->unlinkDelete(m_dfg);
                ++m_nImprovements;
                return false;
            }
            // Attempt to fix up piece-wise at Sels applied to the ArraySel
            fixUpSelSinks(*asp);
            // Remove if became unused
            if (!asp->hasSinks()) asp->unlinkDelete(m_dfg);
            return false;
        });
    }

    FixUpSelDrivers(DfgGraph& dfg, Vtx2Scc& vtx2Scc, DfgVertexVar& var)
        : m_dfg{dfg}
        , m_vtx2Scc{vtx2Scc} {
        UINFO(9, "FixUpSelDrivers of " << var.nodep()->name());
        if (var.isPacked()) {
            // For Packed variables, fix up all Sels applied to it
            fixUpSelSinks(var);
        } else if (var.isArray()) {
            // For Array variables, fix up each ArraySel applied to it
            fixUpArraySelSinks(var);
        }
        UINFO(9, "FixUpSelDrivers made " << m_nImprovements << " improvements");
    }

public:
    // Attempt to push Sel form Var through to the driving
    // expression of the selected bits. This can fix things like
    // 'a[1:0] = foo', 'a[2] = a[1]', which are somewhat common.
    // Returns the number of drivers fixed up.
    static size_t apply(DfgGraph& dfg, Vtx2Scc& vtx2Scc, DfgVertexVar& var) {
        return FixUpSelDrivers{dfg, vtx2Scc, var}.m_nImprovements;
    }
};

class FixUpIndependentRanges final {
    DfgGraph& m_dfg;  // The graph being processed
    Vtx2Scc& m_vtx2Scc;  // The Vertex to SCC map
    size_t m_nImprovements = 0;  // Number of improvements mde

    // Returns a bitmask set if that bit of 'vtx' is used (has a sink)
    static V3Number computeUsedBits(DfgVertex& vtx) {
        V3Number result{vtx.fileline(), static_cast<int>(vtx.width()), 0};
        vtx.foreachSink([&result](DfgVertex& sink) {
            // If used via a Sel, mark the selected bits used
            if (const DfgSel* const selp = sink.cast<DfgSel>()) {
                uint32_t lsb = selp->lsb();
                uint32_t msb = lsb + selp->width() - 1;
                for (uint32_t i = lsb; i <= msb; ++i) result.setBit(i, '1');
                return false;
            }
            // Used without a Sel, so all bits are used
            result.setAllBits1();
            return false;
        });
        return result;
    }

    static std::string debugStr(const DfgVertex& vtx) {
        if (const DfgArraySel* const aselp = vtx.cast<DfgArraySel>()) {
            const size_t i = aselp->bitp()->as<DfgConst>()->toSizeT();
            return debugStr(*aselp->fromp()) + "[" + std::to_string(i) + "]";
        }
        if (const DfgVertexVar* const varp = vtx.cast<DfgVertexVar>()) {
            return varp->nodep()->name();
        }
        vtx.v3fatalSrc("Unhandled node type");  // LCOV_EXCL_LINE
    }

    // Trace drivers of independent bits of 'vtxp' in the range '[hi:lo]'
    // append replacement terms to 'termps'. Returns number of successful
    // replacements.
    void gatherTerms(std::vector<DfgVertex*>& termps, DfgVertex& vtx, const V3Number& indpBits,
                     const uint32_t hi, const uint32_t lo) {
        // Iterate through consecutive dependent/non-dependet ranges within [hi:lo]
        bool isIndependent = indpBits.bitIs1(lo);
        uint32_t lsb = lo;
        for (uint32_t msb = lo; msb <= hi; ++msb) {
            const bool endRange = msb == hi || isIndependent != indpBits.bitIs1(msb + 1);
            if (!endRange) continue;
            const uint32_t width = msb - lsb + 1;
            DfgVertex* termp = nullptr;
            // If the range is not self-dependent, attempt to trace its driver
            if (isIndependent) {
                termp = TraceDriver::apply(m_dfg, m_vtx2Scc, vtx, lsb, width, true);
                if (termp) {
                    ++m_nImprovements;
                } else {
                    UINFO(5, "TraceDriver of independent range failed for "
                                 << debugStr(vtx) << "[" << msb << ":" << lsb << "]");
                }
            }
            // Fall back on using the part of the variable (if dependent, or trace failed)
            if (!termp) {
                DfgSel* const selp = new DfgSel{m_dfg, vtx.fileline(), DfgDataType::packed(width)};
                // Same component as 'vtxp', as reads 'vtxp' and will replace 'vtxp'
                m_vtx2Scc[selp] = m_vtx2Scc.at(vtx);
                // Do not connect selp->fromp yet, need to do afer replacing 'vtxp'
                selp->lsb(lsb);
                termp = selp;
            }
            // Record the term
            termps.emplace_back(termp);
            // Next iteration
            isIndependent = !isIndependent;
            lsb = msb + 1;
        }
    }

    void fixUpPacked(DfgVertex& vtx) {
        UASSERT_OBJ(vtx.isPacked(), &vtx, "Should be a packed type");

        // Figure out which bits of 'vtxp' are used
        const V3Number usedBits = computeUsedBits(vtx);
        UINFO(9, "Used        bits of '" << debugStr(vtx) << "' are "
                                         << usedBits.displayed(vtx.fileline(), "%b"));
        // Nothing to do if no bits are used
        if (usedBits.isEqZero()) return;

        // Figure out which bits of 'vtxp' are dependent of themselves
        const V3Number indpBits = IndependentBits::apply(m_dfg, m_vtx2Scc, vtx);
        UINFO(9, "Independent bits of '" << debugStr(vtx) << "' are "
                                         << indpBits.displayed(vtx.fileline(), "%b"));
        // Can't do anything if all bits are dependent
        if (indpBits.isEqZero()) return;

        {
            // Nothing to do if no used bits are independen (all used bits are dependent)
            V3Number usedAndIndependent{vtx.fileline(), static_cast<int>(vtx.width()), 0};
            usedAndIndependent.opAnd(usedBits, indpBits);
            if (usedAndIndependent.isEqZero()) return;
        }

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

        // If no imporovement was possible, delete the terms we just created
        if (!m_nImprovements) {
            for (DfgVertex* const tp : termps) VL_DO_DANGLING(tp->unlinkDelete(m_dfg), tp);
            termps.clear();
            return;
        }

        // We managed to imporove something, apply the replacement
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
        UINFO(9, "FixUpIndependentRanges of " << var.nodep()->name());

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
                // Remove if became unused
                if (!aselp->hasSinks()) aselp->unlinkDelete(m_dfg);
                return false;
            });
        }

        UINFO(9, "FixUpIndependentRanges made " << m_nImprovements << " improvements");
    }

    FixUpIndependentRanges(DfgGraph& dfg, Vtx2Scc& vtx2Scc, DfgVertexVar& var)
        : m_dfg{dfg}
        , m_vtx2Scc{vtx2Scc} {
        main(var);
    }

public:
    // Similar to FixUpSelDrivers, but first comptute which bits of the
    // variable are self dependent, and fix up those that are independent
    // but used.
    static size_t apply(DfgGraph& dfg, Vtx2Scc& vtx2Scc, DfgVertexVar& var) {
        return FixUpIndependentRanges{dfg, vtx2Scc, var}.m_nImprovements;
    }
};

std::pair<std::unique_ptr<DfgGraph>, bool>  //
V3DfgPasses::breakCycles(const DfgGraph& dfg, V3DfgContext& ctx) {
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

        // Attempt new improvements
        UINFO(9, "New iteration after " << nImprovements << " improvements");
        prevNImprovements = nImprovements;

        // Method 1: FixUpSelDrivers
        for (DfgVertexVar& vtx : res.varVertices()) {
            // If Variable is not part of a cycle, move on
            if (!vtx2Scc[vtx]) continue;

            const size_t nFixed = FixUpSelDrivers::apply(res, vtx2Scc, vtx);
            if (nFixed) {
                nImprovements += nFixed;
                ctx.m_breakCyclesContext.m_nImprovements += nFixed;
                dump(9, res, "FixUpSelDrivers");
            }
        }

        // If we managed to fix something, try again with the earlier methods
        if (nImprovements != prevNImprovements) continue;

        // Method 2. FixUpIndependentRanges
        for (DfgVertexVar& vtx : res.varVertices()) {
            // If Variable is not part of a cycle, move on
            if (!vtx2Scc[vtx]) continue;

            const size_t nFixed = FixUpIndependentRanges::apply(res, vtx2Scc, vtx);
            if (nFixed) {
                nImprovements += nFixed;
                ctx.m_breakCyclesContext.m_nImprovements += nFixed;
                dump(9, res, "FixUpIndependentRanges");
            }
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
