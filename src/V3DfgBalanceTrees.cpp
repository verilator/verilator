// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Balance associative op trees in DfgGraphs
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2024 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
//
// - Convert concatenation trees into balanced form
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Dfg.h"
#include "V3DfgPasses.h"

VL_DEFINE_DEBUG_FUNCTIONS;

class DfgBalanceTrees final {
    // We keep the expressions, together with their offsets within a concatenation tree
    struct ConcatTerm final {
        DfgVertex* vtxp = nullptr;
        size_t offset = 0;

        ConcatTerm() = default;
        ConcatTerm(DfgVertex* vtxp, size_t offset)
            : vtxp{vtxp}
            , offset{offset} {}
    };

    DfgGraph& m_dfg;  // The graph being processed
    V3DfgBalanceTreesContext& m_ctx;  // The optimization context for stats

    // Is the given vertex the root of a tree (of potentially size 1), of the given type?
    template <typename Vertex>
    static bool isRoot(const DfgVertex& vtx) {
        static_assert(std::is_base_of<DfgVertexBinary, Vertex>::value,
                      "'Vertex' must be a 'DfgVertexBinary'");
        if (!vtx.is<Vertex>()) return false;
        // Has a single sink, and that sink is not another vertex of the same type
        return vtx.hasSingleSink() && !vtx.findSink<Vertex>();
    }

    // Recursive implementation of 'gatherTerms' below.
    template <typename Vertex>
    static void gatherTermsImpl(DfgVertex* vtxp, std::vector<DfgVertex*>& terms) {
        // Base case: different type, or multiple sinks -> it's a term
        if (!vtxp->is<Vertex>() || vtxp->hasMultipleSinks()) {
            terms.emplace_back(vtxp);
            return;
        }
        // Recursive case: gather sub terms, right to right
        DfgVertexBinary* const binp = vtxp->as<Vertex>();
        gatherTermsImpl<Vertex>(binp->rhsp(), terms);
        gatherTermsImpl<Vertex>(binp->lhsp(), terms);
    }

    // Gather terms in the tree of given type, rooted at the given vertex.
    // Results are right to left, that is, index 0 in the returned vector
    // is the rightmost term, index size()-1 is the leftmost term.
    template <typename Vertex>
    static std::vector<DfgVertex*> gatherTerms(Vertex& root) {
        static_assert(std::is_base_of<DfgVertexBinary, Vertex>::value,
                      "'Vertex' must be a 'DfgVertexBinary'");
        std::vector<DfgVertex*> terms;
        gatherTermsImpl<Vertex>(root.rhsp(), terms);
        gatherTermsImpl<Vertex>(root.lhsp(), terms);
        return terms;
    }

    // Construct a balanced concatenation from the given terms,
    // between indices begin (inclusive), and end (exclusive).
    // Note term[end].offset must be valid. term[end].vtxp is
    // never referenced.
    DfgVertex* constructConcat(const std::vector<ConcatTerm>& terms, const size_t begin,
                               const size_t end) {
        UASSERT(end < terms.size(), "Invalid end");
        UASSERT(begin < end, "Invalid range");
        // Base case: just return the term
        if (end == begin + 1) return terms[begin].vtxp;

        // Recursive case:
        // Compute the mid-point, trying to create roughly equal width intermediates
        const size_t width = terms[end].offset - terms[begin].offset;
        const size_t midOffset = width / 2 + terms[begin].offset;
        const auto beginIt = terms.begin() + begin;
        const auto endIt = terms.begin() + end;
        const auto midIt = std::lower_bound(beginIt + 1, endIt - 1, midOffset,  //
                                            [&](const ConcatTerm& term, size_t value) {  //
                                                return term.offset < value;
                                            });
        const size_t mid = begin + std::distance(beginIt, midIt);
        UASSERT(begin < mid && mid < end, "Must make some progress");
        // Construct the subtrees
        DfgVertex* const rhsp = constructConcat(terms, begin, mid);
        DfgVertex* const lhsp = constructConcat(terms, mid, end);
        // Construct new node
        AstNodeDType* const dtypep = DfgVertex::dtypeForWidth(lhsp->width() + rhsp->width());
        DfgConcat* const newp = new DfgConcat{m_dfg, lhsp->fileline(), dtypep};
        newp->rhsp(rhsp);
        newp->lhsp(lhsp);
        return newp;
    }

    // Delete unused tree rooted at the given vertex
    void deleteTree(DfgVertexBinary* const vtxp) {
        UASSERT_OBJ(!vtxp->hasSinks(), vtxp, "Trying to remove used vertex");
        DfgVertexBinary* const lhsp = vtxp->lhsp()->cast<DfgVertexBinary>();
        DfgVertexBinary* const rhsp = vtxp->rhsp()->cast<DfgVertexBinary>();
        VL_DO_DANGLING(vtxp->unlinkDelete(m_dfg), vtxp);
        if (lhsp && !lhsp->hasSinks()) deleteTree(lhsp);
        if (rhsp && !rhsp->hasSinks()) deleteTree(rhsp);
    }

    void balanceConcat(DfgConcat* const rootp) {
        // Gather all input vertices of the tree
        const std::vector<DfgVertex*> vtxps = gatherTerms<DfgConcat>(*rootp);
        // Don't bother with trivial trees
        if (vtxps.size() <= 3) return;

        // Construct the terms Vector that we are going to do processing on
        std::vector<ConcatTerm> terms(vtxps.size() + 1);
        // These are redundant (constructor does the same), but here they are for clarity
        terms[0].offset = 0;
        terms[vtxps.size()].vtxp = nullptr;
        for (size_t i = 0; i < vtxps.size(); ++i) {
            terms[i].vtxp = vtxps[i];
            terms[i + 1].offset = terms[i].offset + vtxps[i]->width();
        }

        // Round 1: try to create terms ending on VL_EDATASIZE boundaries.
        // This ensures we pack bits within a VL_EDATASIZE first is possible,
        // and then hopefully we can just assemble VL_EDATASIZE words afterward.
        std::vector<ConcatTerm> terms2;
        {
            terms2.reserve(terms.size());

            size_t begin = 0;  // Start of current range considered
            size_t end = 0;  // End of current range considered
            size_t offset = 0;  // Offset of current range considered

            // Create a term from the current range
            const auto makeTerm = [&]() {
                DfgVertex* const vtxp = constructConcat(terms, begin, end);
                terms2.emplace_back(vtxp, offset);
                offset += vtxp->width();
                begin = end;
            };

            // Create all terms ending on a boundary.
            while (++end < terms.size() - 1) {
                if (terms[end].offset % VL_EDATASIZE == 0) makeTerm();
            }
            // Final term. Loop condition above ensures this always exists,
            // and might or might not be on a boundary.
            makeTerm();
            // Sentinel term
            terms2.emplace_back(nullptr, offset);
            // should have ended up with the same number of bits at least...
            UASSERT(terms2.back().offset == terms.back().offset, "Inconsitent terms");
        }

        // Round 2: Combine the partial terms
        rootp->replaceWith(constructConcat(terms2, 0, terms2.size() - 1));
        VL_DO_DANGLING(deleteTree(rootp), rootp);

        ++m_ctx.m_balancedConcats;
    }

    DfgBalanceTrees(DfgGraph& dfg, V3DfgBalanceTreesContext& ctx)
        : m_dfg{dfg}
        , m_ctx{ctx} {
        // Find all roots
        std::vector<DfgConcat*> rootps;
        for (DfgVertex& vtx : dfg.opVertices()) {
            if (isRoot<DfgConcat>(vtx)) rootps.emplace_back(vtx.as<DfgConcat>());
        }
        // Balance them
        for (DfgConcat* const rootp : rootps) balanceConcat(rootp);
    }

public:
    static void apply(DfgGraph& dfg, V3DfgBalanceTreesContext& ctx) { DfgBalanceTrees{dfg, ctx}; }
};

void V3DfgPasses::balanceTrees(DfgGraph& dfg, V3DfgBalanceTreesContext& ctx) {
    DfgBalanceTrees::apply(dfg, ctx);
}
