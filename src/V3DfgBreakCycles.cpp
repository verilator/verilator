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

#include <deque>
#include <fstream>
#include <limits>
#include <unordered_map>
#include <vector>

VL_DEFINE_DEBUG_FUNCTIONS;

// Similar algorithm used in ExtractCyclicComponents.
// This one sets DfgVertex::user(). See the static 'apply' method below.
class ColorStronglyConnectedComponents final {
    static constexpr uint32_t UNASSIGNED = std::numeric_limits<uint32_t>::max();

    // TYPES
    struct VertexState final {
        uint32_t component = UNASSIGNED;  // Result component number (0 means not in SCC)
        uint32_t index = UNASSIGNED;  // Used by Pearce's algorithm for detecting SCCs
        VertexState() = default;
        VertexState(uint32_t i, uint32_t n)
            : component{n}
            , index{i} {}
    };

    // STATE
    DfgGraph& m_dfg;  // The input graph
    uint32_t m_nonTrivialSCCs = 0;  // Number of non-trivial SCCs in the graph
    uint32_t m_index = 0;  // Visitation index counter
    std::vector<DfgVertex*> m_stack;  // The stack used by the algorithm

    // METHODS
    void visitColorSCCs(DfgVertex& vtx, VertexState& vtxState) {
        UDEBUGONLY(UASSERT_OBJ(vtxState.index == UNASSIGNED, &vtx, "Already visited vertex"););

        // Visiting vertex
        const size_t rootIndex = vtxState.index = ++m_index;

        // Visit children
        vtx.forEachSink([&](DfgVertex& child) {
            VertexState& childSatate = child.user<VertexState>();
            // If the child has not yet been visited, then continue traversal
            if (childSatate.index == UNASSIGNED) visitColorSCCs(child, childSatate);
            // If the child is not in an SCC
            if (childSatate.component == UNASSIGNED) {
                if (vtxState.index > childSatate.index) vtxState.index = childSatate.index;
            }
        });

        if (vtxState.index == rootIndex) {
            // This is the 'root' of an SCC

            // A trivial SCC contains only a single vertex
            const bool isTrivial = m_stack.empty()  //
                                   || m_stack.back()->getUser<VertexState>().index < rootIndex;
            // We also need a separate component for vertices that drive themselves (which can
            // happen for input like 'assign a = a'), as we want to extract them (they are cyclic).
            const bool drivesSelf = vtx.findSink<DfgVertex>([&vtx](const DfgVertex& sink) {  //
                return &vtx == &sink;
            });

            if (!isTrivial || drivesSelf) {
                // Allocate new component
                ++m_nonTrivialSCCs;
                vtxState.component = m_nonTrivialSCCs;
                while (!m_stack.empty()) {
                    VertexState& topState = m_stack.back()->getUser<VertexState>();
                    // Only higher nodes belong to the same SCC
                    if (topState.index < rootIndex) break;
                    m_stack.pop_back();
                    topState.component = m_nonTrivialSCCs;
                }
            } else {
                // Trivial SCC (and does not drive itself), so acyclic. Keep it in original graph.
                vtxState.component = 0;
            }
        } else {
            // Not the root of an SCC
            m_stack.push_back(&vtx);
        }
    }

    void colorSCCs() {
        // Implements Pearce's algorithm to color the strongly connected components. For reference
        // see "An Improved Algorithm for Finding the Strongly Connected Components of a Directed
        // Graph", David J.Pearce, 2005.

        // We know constant nodes have no input edges, so they cannot be part
        // of a non-trivial SCC. Mark them as such without any real traversals.
        for (DfgConst& vtx : m_dfg.constVertices()) vtx.setUser(VertexState{0, 0});

        // Start traversals through variables
        for (DfgVertexVar& vtx : m_dfg.varVertices()) {
            VertexState& vtxState = vtx.user<VertexState>();
            // If it has no input or no outputs, it cannot be part of a non-trivial SCC.
            if (vtx.arity() == 0 || !vtx.hasSinks()) {
                UDEBUGONLY(UASSERT_OBJ(vtxState.index == UNASSIGNED || vtxState.component == 0,
                                       &vtx, "Non circular variable must be in a trivial SCC"););
                vtxState.index = 0;
                vtxState.component = 0;
                continue;
            }
            // If not yet visited, start a traversal
            if (vtxState.index == UNASSIGNED) visitColorSCCs(vtx, vtxState);
        }

        // Start traversals through operations
        for (DfgVertex& vtx : m_dfg.opVertices()) {
            VertexState& vtxState = vtx.user<VertexState>();
            // If not yet visited, start a traversal
            if (vtxState.index == UNASSIGNED) visitColorSCCs(vtx, vtxState);
        }
    }

    ColorStronglyConnectedComponents(DfgGraph& dfg)
        : m_dfg{dfg} {
        UASSERT(dfg.size() < UNASSIGNED, "Graph too big " << dfg.name());
        // Yet another implementation of Pearce's algorithm.
        colorSCCs();
        // Re-assign user values
        m_dfg.forEachVertex([](DfgVertex& vtx) {
            const size_t component = vtx.getUser<VertexState>().component;
            vtx.setUser<uint32_t>(component);
        });
    }

public:
    // Sets DfgVertex::user<uint32_t>() for all vertext to:
    // - 0, if the vertex is not part of a non-trivial strongly connected component
    //   and is not part of a self-loop. That is: the Vertex is not part of any cycle.
    // - N, if the vertex is part of a non-trivial strongly conneced component or self-loop N.
    //   That is: each set of vertices that are reachable from each other will have the same
    //   non-zero value assigned.
    // Returns the number of non-trivial SCCs (distinct cycles)
    static uint32_t apply(DfgGraph& dfg) {
        return ColorStronglyConnectedComponents{dfg}.m_nonTrivialSCCs;
    }
};

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
                V3Hash hash{reinterpret_cast<uintptr_t>(item.m_vtxp)};
                hash += item.m_lsb;
                hash += item.m_msb;
                return hash.value();
            }
        };

        struct Equal final {
            bool operator()(const Visited& a, const Visited& b) const {
                return a.m_vtxp == b.m_vtxp && a.m_lsb == b.m_lsb && a.m_msb == b.m_lsb;
            }
        };
    };

    // STATE
    DfgGraph& m_dfg;  // The graph being processed
    // The strongly connected component we are trying to escape
    const uint32_t m_component;
    const bool m_aggressive;  // Trace aggressively, creating intermediate ops
    uint32_t m_lsb = 0;  // LSB to extract from the currently visited Vertex
    uint32_t m_msb = 0;  // MSB to extract from the currently visited Vertex
    // Result of tracing the currently visited Vertex. Use SET_RESULT below!
    DfgVertex* m_resp = nullptr;
    std::vector<DfgVertex*> m_newVtxps;  // New vertices created during the traversal

    std::vector<Visited> m_stack;  // Stack of currently visited vertices
    // Denotes if a 'Visited' entry appear in m_stack
    std::unordered_map<Visited, bool, Visited::Hash, Visited::Equal> m_visited;

    std::ofstream m_lineCoverageFile;  // Line coverage file, just for testing

    // METHODS

    // Create and return a new Vertex and add it to m_newVtxps. Fileline is
    // taken from 'refp', but 'refp' is otherwise not used. You should
    // always use this to create new vertices, so unused ones (if a trace
    // eventually fails) can be cleaned up at the end.
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
            DfgConst* const vtxp = new DfgConst{m_dfg, refp->fileline(), width};
            m_newVtxps.emplace_back(vtxp);
            return vtxp;
        } else {
            AstNodeDType* const dtypep = DfgVertex::dtypeForWidth(width);
            Vertex* const vtxp = new Vertex{m_dfg, refp->fileline(), dtypep};
            m_newVtxps.emplace_back(vtxp);
            return vtxp;
        }
    }

    // Continue tracing drivers of the given vertex, at the given LSB. Every
    // visitor should call this to continue the traversal, then immediately
    // return after the call. 'visit' methods should not call 'iterate', call
    // this method instead, which checks for cycles.
    DfgVertex* trace(DfgVertex* const vtxp, const uint32_t msb, const uint32_t lsb) {
        UASSERT_OBJ(!vtxp->is<DfgVarArray>(), vtxp, "Cannot trace array variables");
        UASSERT_OBJ(vtxp->width() > msb, vtxp, "Traced Vertex too narrow");

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

        if (vtxp->user<uint32_t>() != m_component) {
            // If the currently traced vertex is in a different component,
            // then we found what we were looking for.
            if (msb != vtxp->width() - 1 || lsb != 0) {
                // Apply a Sel to extract the relevant bits if only a part is needed
                DfgSel* const selp = make<DfgSel>(vtxp, msb - lsb + 1);
                selp->fromp(vtxp);
                selp->lsb(lsb);
                m_resp = selp;
            } else {
                // Otherwise just return the vertex
                m_resp = vtxp;
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
    Vertex* bitwiseBinary(Vertex* vtxp) {
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

    // Predicate to do determine if vtxp[$bits(vtxp)-1:idx] is known to be zero
    // Somewhat rudimentary but sufficient for current purposes.
    static bool knownToBeZeroAtAndAbove(const DfgVertex* vtxp, uint32_t idx) {
        if (const DfgConcat* const catp = vtxp->cast<DfgConcat>()) {
            DfgConst* const lConstp = catp->lhsp()->cast<DfgConst>();
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
            DfgConst* const rConstp = catp->rhsp()->cast<DfgConst>();
            return rConstp && idx < rConstp->width() && rConstp->isZero();
        }
        return false;
    }

    // Use this macro to set the result in 'visit' methods. This also emits
    // a line to m_lineCoverageFile for testing.
    // TODO: Use C++20 std::source_location instead of a macro
#define SET_RESULT(vtxp) \
    do { \
        m_resp = vtxp; \
        if (VL_UNLIKELY(m_lineCoverageFile.is_open())) m_lineCoverageFile << __LINE__ << '\n'; \
    } while (false)

    // VISITORS
    void visit(DfgVertex* vtxp) override {
        // Base case: cannot continue ...
        UINFO(9, "TraceDriver - Unhandled vertex type: " << vtxp->typeName());
    }

    void visit(DfgVarPacked* vtxp) override {
        // Proceed with the driver that wholly covers the searched bits
        const auto pair = vtxp->sourceEdges();
        for (size_t i = 0; i < pair.second; ++i) {
            DfgVertex* const srcp = pair.first[i].sourcep();
            const uint32_t lsb = vtxp->driverLsb(i);
            const uint32_t msb = lsb + srcp->width() - 1;
            // If it does not cover the searched bit range, move on
            if (m_lsb < lsb || msb < m_msb) continue;
            // Trace this driver
            SET_RESULT(trace(srcp, m_msb - lsb, m_lsb - lsb));
            return;
        }
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
        SET_RESULT(bitwiseBinary(vtxp));
    }
    void visit(DfgOr* vtxp) override {
        if (!m_aggressive) return;
        SET_RESULT(bitwiseBinary(vtxp));
    }
    void visit(DfgXor* vtxp) override {
        if (!m_aggressive) return;
        SET_RESULT(bitwiseBinary(vtxp));
    }

    void visit(DfgShiftR* vtxp) override {
        DfgVertex* const lhsp = vtxp->lhsp();
        if (DfgConst* const rConstp = vtxp->rhsp()->cast<DfgConst>()) {
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
        if (DfgConst* const rConstp = vtxp->rhsp()->cast<DfgConst>()) {
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

#undef SET_RESULT

    // CONSTRUCTOR
    TraceDriver(DfgGraph& dfg, uint32_t component, bool aggressive)
        : m_dfg{dfg}
        , m_component{component}
        , m_aggressive{aggressive} {
        if (v3Global.opt.debugCheck()) {
            m_lineCoverageFile.open(  //
                v3Global.opt.makeDir() + "/" + v3Global.opt.prefix()
                    + "__V3DfgBreakCycles-TraceDriver-line-coverage.txt",  //
                std::ios_base::out | std::ios_base::app);
        }
    }

public:
    // Given a Vertex that is part of an SCC denoted by vtxp->user<uint32_t>(),
    // return a vertex that is equivalent to 'vtxp[lsb +: width]', but is not
    // part of the same SCC. Returns nullptr if such a vertex cannot be
    // computed. This can add new vertices to the graph. The 'aggressive' flag
    // enables creating many intermediate operations. This should only be set
    // if it is reasonably certain the tracing will succeed, otherwise we can
    // waste a lot of compute.
    static DfgVertex* apply(DfgGraph& dfg, DfgVertex* vtxp, uint32_t lsb, uint32_t width,
                            bool aggressive) {
        TraceDriver traceDriver{dfg, vtxp->user<uint32_t>(), aggressive};
        // Find the out-of-component driver of the given vertex
        DfgVertex* const resultp = traceDriver.trace(vtxp, lsb + width - 1, lsb);
        // Delete unused newly created vertices (these can be created if a
        // partial trace succeded, but an eventual one falied). Because new
        // vertices should be created depth first, it is enough to do a single
        // reverse pass over the collectoin
        for (DfgVertex* const vtxp : vlstd::reverse_view(traceDriver.m_newVtxps)) {
            // Keep the actual result!
            if (vtxp == resultp) continue;
            // Keep used ones!
            if (vtxp->hasSinks()) continue;
            // Delete it
            VL_DO_DANGLING(vtxp->unlinkDelete(dfg), vtxp);
        }
        // Return the result
        return resultp;
    }
};

class IndependentBits final : public DfgVisitor {
    // STATE
    DfgVarPacked* const m_varp;  // The variable we are computing dependencies for
    std::deque<DfgVertex*> m_workList;  // Work list for traversal
    // Vertex to current bit mask map. The mask is set for the bits that **depend** on 'm_varp'.
    std::unordered_map<const DfgVertex*, V3Number> m_vtxp2Mask;

    std::ofstream m_lineCoverageFile;  // Line coverage file, just for testing

    // METHODS

    // Retrieve the mask for the given vertex (create it with value 0 if needed)
    V3Number& mask(const DfgVertex* vtxp) {
        return m_vtxp2Mask
            .emplace(std::piecewise_construct,  //
                     std::forward_as_tuple(vtxp),  //
                     std::forward_as_tuple(vtxp->fileline(), static_cast<int>(vtxp->width()), 0))
            .first->second;
    }

    // Use this macro to call 'mask' in 'visit' methods. This also emits
    // a line to m_lineCoverageFile for testing.
    // TODO: Use C++20 std::source_location instead of a macro
#define MASK(vtxp) \
    ([this](const DfgVertex* p) -> V3Number& { \
        if (VL_UNLIKELY(m_lineCoverageFile.is_open())) m_lineCoverageFile << __LINE__ << '\n'; \
        return mask(p); \
    }(vtxp))

    // VISITORS
    void visit(DfgVertex* vtxp) override {
        UINFO(9, "Unhandled vertex type " << vtxp->typeName());
        // Conservatively assume it depends on the variable...
        mask(vtxp).setAllBits1();  // intentionally not using MASK here
    }

    void visit(DfgVarPacked* vtxp) override {
        // The mask of the traced variable is known to be all ones
        if (vtxp == m_varp) return;

        // Combine the masks of all drivers
        V3Number& m = MASK(vtxp);
        vtxp->forEachSourceEdge([&](DfgEdge& edge, size_t i) {
            const DfgVertex* const srcp = edge.sourcep();
            m.opSelInto(MASK(srcp), vtxp->driverLsb(i), srcp->width());
        });
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
        MASK(vtxp).opSelInto(MASK(srcp), 0, srcp->width());
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

    void visit(DfgShiftR* vtxp) override {
        DfgVertex* const rhsp = vtxp->rhsp();
        DfgVertex* const lhsp = vtxp->lhsp();
        const uint32_t width = vtxp->width();

        // Constant shift can be computed precisely
        if (DfgConst* const rConstp = rhsp->cast<DfgConst>()) {
            const uint32_t shiftAmount = rConstp->toU32();
            if (shiftAmount >= width) return;
            V3Number shiftedMask{lhsp->fileline(), static_cast<int>(width), 0};
            shiftedMask.opShiftR(MASK(lhsp), rConstp->num());
            MASK(vtxp).opSelInto(shiftedMask, 0, width - shiftAmount);
            return;
        }

        // Otherwise, as the shift amount is non-negative, any bit at or below
        // the most significant dependent bit might be dependent
        const V3Number& lMask = MASK(lhsp);
        V3Number& vMask = MASK(vtxp);
        int idx = width - 1;
        while (idx >= 0 && lMask.bitIs0(idx)) --idx;
        while (idx >= 0) vMask.setBit(idx--, '1');
    }

    void visit(DfgShiftL* vtxp) override {
        DfgVertex* const rhsp = vtxp->rhsp();
        DfgVertex* const lhsp = vtxp->lhsp();
        const uint32_t width = vtxp->width();

        // Constant shift can be computed precisely
        if (DfgConst* const rConstp = rhsp->cast<DfgConst>()) {
            const uint32_t shiftAmount = rConstp->toU32();
            if (shiftAmount >= width) return;
            V3Number shiftedMask{lhsp->fileline(), static_cast<int>(width), 0};
            shiftedMask.opShiftL(MASK(lhsp), rConstp->num());
            MASK(vtxp).opSelInto(shiftedMask, shiftAmount, width - shiftAmount);
            return;
        }

        // Otherwise, as the shift amount is non-negative, any bit at or above
        // the least significant dependent bit might be dependent
        const V3Number& lMask = MASK(lhsp);
        V3Number& vMask = MASK(vtxp);
        int idx = 0;
        while (idx < width && lMask.bitIs0(idx)) ++idx;
        while (idx < width) vMask.setBit(idx++, '1');
    }

#undef MASK

    // CONSTRUCTOR
    IndependentBits(DfgVarPacked* varp)
        : m_varp{varp} {
        if (v3Global.opt.debugCheck()) {
            m_lineCoverageFile.open(  //
                v3Global.opt.makeDir() + "/" + v3Global.opt.prefix()
                    + "__V3DfgBreakCycles-IndependentBits-line-coverage.txt",  //
                std::ios_base::out | std::ios_base::app);
        }

        // The starting vertex depends on it's own value, duuhh...
        mask(varp).setAllBits1();
        // Enqueue all sinks
        varp->forEachSink([&](DfgVertex& vtx) { m_workList.emplace_back(&vtx); });

        // While there is an item on the worklist ..
        while (!m_workList.empty()) {
            // Grab next item
            DfgVertex* const currp = m_workList.front();
            m_workList.pop_front();

            // Grab current mask of item
            const V3Number& maskCurr = mask(currp);
            // Remember current mask
            const V3Number prevMask = maskCurr;

            // Dispatch
            iterate(currp);

            // If mask changed, enqueue sinks
            if (!prevMask.isCaseEq(maskCurr)) {
                currp->forEachSink([&](DfgVertex& vtx) { m_workList.emplace_back(&vtx); });

                // Check the mask only ever expands (no bit goes 1 -> 0)
                if (VL_UNLIKELY(v3Global.opt.debugCheck())) {
                    V3Number notCurr{maskCurr};
                    notCurr.opNot(maskCurr);
                    V3Number prevAndNotCurr{maskCurr};
                    prevAndNotCurr.opAnd(prevMask, notCurr);
                    UASSERT_OBJ(prevAndNotCurr.isEqZero(), currp, "Mask should only expand");
                }
            }
        }
    }

public:
    // Given a variable, compute which bits in this variable are independent of
    // the variable itself (simple forward dataflow analysis). Returns a bit
    // mask where a set bit indicates that bit is independent of the variable
    // itself (logic is not circular). The result is a conservative estimate,
    // so bits reported dependent might not actually be, but all bits reported
    // independent are known to be so.
    static V3Number apply(DfgVarPacked* varp) {
        IndependentBits independentBits{varp};
        // Combine the masks of all drivers of the variable
        V3Number result{varp->fileline(), static_cast<int>(varp->width()), 0};
        varp->forEachSourceEdge([&](DfgEdge& edge, size_t i) {
            const DfgVertex* const srcp = edge.sourcep();
            // The mask represents the dependent bits, so invert it
            V3Number inverseMask{srcp->fileline(), static_cast<int>(srcp->width()), 0};
            inverseMask.opNot(independentBits.mask(srcp));
            result.opSelInto(inverseMask, varp->driverLsb(i), srcp->width());
        });
        return result;
    }
};

class FixUpSelDrivers final {
public:
    // Attempt to push Sel form Var through to the driving
    // expression of the selected bits. This can fix things like
    // 'a[1:0] = foo', 'a[2] = a[1]', which are somewhat common.
    // Returns the number of drivers fixed up.
    static size_t apply(DfgGraph& dfg, DfgVarPacked* varp) {
        UINFO(9, "FixUpSelDrivers of " << varp->nodep()->name());
        const uint32_t component = varp->getUser<uint32_t>();
        size_t nImprovements = 0;
        varp->forEachSink([&](DfgVertex& sink) {
            // Ignore if sink is not part of cycle
            if (sink.getUser<uint32_t>() != component) return;
            // Only Handle Sels now
            DfgSel* const selp = sink.cast<DfgSel>();
            if (!selp) return;
            // Try to find of the driver of the selected bits outside the cycle
            DfgVertex* const fixp
                = TraceDriver::apply(dfg, varp, selp->lsb(), selp->width(), false);
            if (!fixp) return;
            // Found an out-of-cycle driver. We can replace this sel with that.
            selp->replaceWith(fixp);
            selp->unlinkDelete(dfg);
            ++nImprovements;
        });
        UINFO(9, "FixUpSelDrivers made " << nImprovements << " improvements");
        return nImprovements;
    }
};

class FixUpIndependentRanges final {
    // Returns a bitmask set if that bit of 'varp' is used (has a sink)
    static V3Number computeUsedBits(DfgVarPacked* varp) {
        V3Number result{varp->fileline(), static_cast<int>(varp->width()), 0};
        varp->forEachSink([&](DfgVertex& sink) {
            // If used via a Sel, mark the selected bits used
            if (DfgSel* const selp = sink.cast<DfgSel>()) {
                uint32_t lsb = selp->lsb();
                uint32_t msb = lsb + selp->width() - 1;
                for (uint32_t i = lsb; i <= msb; ++i) result.setBit(i, '1');
                return;
            }

            // Used without a Sel, so all bits are used
            result.setAllBits1();
        });
        return result;
    }

    // Trace drivers of independent bits of 'varp' in the range '[hi:lo]'
    // append replacement terms to 'termps'. Returns number of successful
    // replacements.
    static size_t gatherTerms(std::vector<DfgVertex*>& termps, DfgGraph& dfg,
                              DfgVarPacked* const varp, const V3Number& indpBits,
                              const uint32_t hi, const uint32_t lo) {
        size_t nImprovements = 0;
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
                termp = TraceDriver::apply(dfg, varp, lsb, width, true);
                if (termp) {
                    ++nImprovements;
                } else {
                    UINFO(5, "TraceDriver of independent range failed for "
                                 << varp->nodep()->name() << "[" << msb << ":" << lsb << "]");
                }
            }
            // Fall back on using the part of the variable (if dependent, or trace failed)
            if (!termp) {
                AstNodeDType* const dtypep = DfgVertex::dtypeForWidth(width);
                DfgSel* const selp = new DfgSel{dfg, varp->fileline(), dtypep};
                // Do not connect selp->fromp yet, need to do afer replacing 'varp'
                selp->lsb(lsb);
                termp = selp;
            }
            // Record the term
            termps.emplace_back(termp);
            // Next iteration
            isIndependent = !isIndependent;
            lsb = msb + 1;
        }
        return nImprovements;
    }

public:
    // Similar to FixUpSelDrivers, but first comptute which bits of the
    // variable are self dependent, and fix up those that are independent
    // but used.
    static size_t apply(DfgGraph& dfg, DfgVarPacked* varp) {
        UINFO(9, "FixUpIndependentRanges of " << varp->nodep()->name());
        size_t nImprovements = 0;

        // Figure out which bits of 'varp' are used
        const V3Number usedBits = computeUsedBits(varp);
        UINFO(9, "Used        bits of '" << varp->nodep()->name() << "' are "
                                         << usedBits.displayed(varp->nodep(), "%b"));
        // Nothing to do if no bits are used
        if (usedBits.isEqZero()) return 0;

        // Figure out which bits of 'varp' are dependent on themselves
        const V3Number indpBits = IndependentBits::apply(varp);
        UINFO(9, "Independent bits of '" << varp->nodep()->name() << "' are "
                                         << indpBits.displayed(varp->nodep(), "%b"));
        // Can't do anything if all bits are dependent
        if (indpBits.isEqZero()) return 0;

        {
            // Nothing to do if no used bits are independen (all used bits are dependent)
            V3Number usedAndIndependent{varp->fileline(), static_cast<int>(varp->width()), 0};
            usedAndIndependent.opAnd(usedBits, indpBits);
            if (usedAndIndependent.isEqZero()) return 0;
        }

        // We are computing the terms to concatenate and replace 'varp' with
        std::vector<DfgVertex*> termps;

        // Iterate through consecutive used/unused ranges
        FileLine* const flp = varp->fileline();
        const uint32_t width = varp->width();
        bool isUsed = usedBits.bitIs1(0);  // Is current range used
        uint32_t lsb = 0;  // LSB of current range
        for (uint32_t msb = 0; msb < width; ++msb) {
            const bool endRange = msb == width - 1 || isUsed != usedBits.bitIs1(msb + 1);
            if (!endRange) continue;
            if (isUsed) {
                // The range is used, compute the replacement terms
                nImprovements += gatherTerms(termps, dfg, varp, indpBits, msb, lsb);
            } else {
                // The range is not used, just use constant 0 as a placeholder
                termps.emplace_back(new DfgConst{dfg, flp, msb - lsb + 1});
            }
            // Next iteration
            isUsed = !isUsed;
            lsb = msb + 1;
        }

        // If we managed to imporove something, apply the replacement
        if (nImprovements) {
            // Concatenate all the terms to create the replacement
            DfgVertex* replacementp = termps.front();
            for (size_t i = 1; i < termps.size(); ++i) {
                DfgVertex* const termp = termps[i];
                const uint32_t catWidth = replacementp->width() + termp->width();
                AstNodeDType* const dtypep = DfgVertex::dtypeForWidth(catWidth);
                DfgConcat* const catp = new DfgConcat{dfg, flp, dtypep};
                catp->rhsp(replacementp);
                catp->lhsp(termp);
                replacementp = catp;
            }

            // Replace the variable
            varp->replaceWith(replacementp);
            // Connect the Sel nodes in the replacement
            for (DfgVertex* const termp : termps) {
                if (DfgSel* const selp = termp->cast<DfgSel>()) {
                    if (!selp->fromp()) selp->fromp(varp);
                }
            }
        }

        UINFO(9, "FixUpIndependentRanges made " << nImprovements << " improvements");
        return nImprovements;
    }
};

std::pair<std::unique_ptr<DfgGraph>, bool>
V3DfgPasses::breakCycles(const DfgGraph& dfg, V3DfgOptimizationContext& ctx) {
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
        // Color SCCs (populates DfgVertex::user<uint32_t>())
        const auto userDataInUse = res.userDataInUse();
        const uint32_t numNonTrivialSCCs = ColorStronglyConnectedComponents::apply(res);

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
            // Only handle DfgVarPacked at this point
            DfgVarPacked* const varp = vtx.cast<DfgVarPacked>();
            if (!varp) continue;
            // If Variable is not part of a cycle, move on
            const uint32_t component = varp->getUser<uint32_t>();
            if (!component) continue;

            const size_t nFixed = FixUpSelDrivers::apply(res, varp);
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
            // Only handle DfgVarPacked at this point
            DfgVarPacked* const varp = vtx.cast<DfgVarPacked>();
            if (!varp) continue;
            // If Variable is not part of a cycle, move on
            const uint32_t component = varp->getUser<uint32_t>();
            if (!component) continue;

            const size_t nFixed = FixUpIndependentRanges::apply(res, varp);
            if (nFixed) {
                nImprovements += nFixed;
                ctx.m_breakCyclesContext.m_nImprovements += nFixed;
                dump(9, res, "FixUpIndependentRanges");
            }
        }
    } while (nImprovements != prevNImprovements);

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
