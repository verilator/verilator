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

    // SATE
    DfgGraph& m_dfg;  // The graph being processed
    // The strongly connected component we are trying to escape
    const uint32_t m_component;
    uint32_t m_lsb = 0;  // LSB to extract from the currently visited Vertex
    uint32_t m_msb = 0;  // MSB to extract from the currently visited Vertex
    // Result of tracing the currently visited Vertex. Use SET_RESULT below!
    DfgVertex* m_resp = nullptr;
    std::vector<DfgVertex*> m_newVtxps;  // New vertices created during the traversal
    std::ofstream m_lineCoverageFile;  // Line coverage file, just for testing

    std::vector<Visited> m_stack;  // Stack of currently visited vertices
    // Denotes if a 'Visited' entry appear in m_stack
    std::unordered_map<Visited, bool, Visited::Hash, Visited::Equal> m_visited;

    // METHODS

    // Create and return a new Vertex and add it to m_newVtxps. You should
    // always use this to create new vertices, so unused ones (if a trace
    // eventually fails) can be cleaned up at the end.
    template <typename Vertex>
    Vertex* make(FileLine* flp, uint32_t width) {
        static_assert(std::is_base_of<DfgVertex, Vertex>::value  //
                          && !std::is_base_of<DfgVertexVar, Vertex>::value  //
                          && !std::is_same<DfgConst, DfgVertex>::value,
                      "Should only make operation vertices");
        AstNodeDType* const dtypep = DfgVertex::dtypeForWidth(width);
        Vertex* const vtxp = new Vertex{m_dfg, flp, dtypep};
        m_newVtxps.emplace_back(vtxp);
        return vtxp;
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
                DfgSel* const selp = make<DfgSel>(vtxp->fileline(), msb - lsb + 1);
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
        return m_resp;
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
        // The traced bit span both sides, attempt to trace both
        if (DfgVertex* const rp = trace(rhsp, rWidth - 1, m_lsb)) {
            if (DfgVertex* const lp = trace(lhsp, m_msb - rWidth, 0)) {
                DfgConcat* const resp = make<DfgConcat>(vtxp->fileline(), m_msb - m_lsb + 1);
                resp->rhsp(rp);
                resp->lhsp(lp);
                SET_RESULT(resp);
                return;
            }
        }
    }

    void visit(DfgExtend* vtxp) override {
        DfgVertex* const srcp = vtxp->srcp();
        if (srcp->width() > m_msb) {
            SET_RESULT(trace(srcp, m_msb, m_lsb));
            return;
        }
    }

    void visit(DfgSel* vtxp) override {
        const uint32_t lsb = vtxp->lsb();
        SET_RESULT(trace(vtxp->srcp(), m_msb + lsb, m_lsb + lsb));
        return;
    }

#undef SET_RESULT

    // CONSTRUCTOR
    TraceDriver(DfgGraph& dfg, uint32_t component)
        : m_dfg{dfg}
        , m_component{component} {
        if (v3Global.opt.debugCheck()) {
            m_lineCoverageFile.open(  //
                v3Global.opt.makeDir() + "/V3DfgBreakCycles-TraceDriver-line-coverage.txt",  //
                std::ios_base::out | std::ios_base::app);
        }
    }

public:
    // Given a Vertex that is part of an SCC denoted by vtxp->user<uint32_t>(),
    // return a vertex that is equivalent to 'vtxp[lsb +: width]', but is not
    // part of the same SCC. Returns nullptr if such a vertex cannot be
    // computed. This can add new vertices to the graph.
    static DfgVertex* apply(DfgGraph& dfg, DfgVertex* vtxp, uint32_t lsb, uint32_t width) {
        TraceDriver traceDriver{dfg, vtxp->user<uint32_t>()};
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

        // Method 1. Attempt to push Sel form Var through to the driving
        // expression of the selected bits. This can fix things like
        // 'a[1:0] = foo', 'a[2] = a[1]', which are somewhat common.
        for (DfgVertexVar& vtx : res.varVertices()) {
            // Only handle DfgVarPacked at this point
            DfgVarPacked* const varp = vtx.cast<DfgVarPacked>();
            if (!varp) continue;
            // If Variable is not part of a cycle, move on
            const uint32_t component = varp->getUser<uint32_t>();
            if (!component) continue;

            UINFO(9, "Attempting to TraceDriver " << varp->nodep()->name());

            varp->forEachSink([&](DfgVertex& sink) {
                // Ignore if sink is not part of cycle
                if (sink.getUser<uint32_t>() != component) return;
                // Only Handle Sels now
                DfgSel* const selp = sink.cast<DfgSel>();
                if (!selp) return;
                // Try to find of the driver of the selected bits outside the cycle
                DfgVertex* const fixp = TraceDriver::apply(res, varp, selp->lsb(), selp->width());
                if (!fixp) return;
                // Found an out-of-cycle driver. We can replace this sel with that.
                selp->replaceWith(fixp);
                selp->unlinkDelete(res);
                ++nImprovements;
                ++ctx.m_breakCyclesContext.m_nImprovements;
                dump(9, res, "TraceDriver");
            });
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
