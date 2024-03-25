// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: DAG Path Checking
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

#ifndef VERILATOR_V3GRAPHPATHCHECKER_H_
#define VERILATOR_V3GRAPHPATHCHECKER_H_

#include "V3Error.h"
#include "V3Graph.h"
#include "V3GraphAlg.h"
#include "V3ThreadSafety.h"

//######################################################################

/// Implement pathExistsFrom() with some caching to prune the search.
/// Far more aggressive caching/pruning is possible; for now the use cases
/// don't rely so heavily on this class that it's necessary.
///
/// The graph (or at least, the subset the algorithm sees through
/// edgeFuncp) must not change during the lifetime of the checker.
class GraphPathChecker final : GraphAlg<V3Graph> {
    // Count "generations" which increases on operations that scan through
    // the graph. Each node is marked with the last generation that scanned
    // it, to enable asserting there are no cycles, and to avoid recursing
    // through the same node twice while searching for a path.
    uint64_t m_generation = 0;

public:
    // CONSTRUCTORS
    explicit GraphPathChecker(V3Graph* graphp, V3EdgeFuncP edgeFuncp
                                               = V3GraphEdge::followAlwaysTrue) VL_MT_DISABLED;
    ~GraphPathChecker() VL_MT_DISABLED;

    // METHODS
    bool pathExistsFrom(const V3GraphVertex* fromp, const V3GraphVertex* top) VL_MT_DISABLED;

    // If have edges A->B, B->C, and A->C then A->C is considered a
    // "transitive" edge (implied by A->B and B->C) and it could be safely
    // removed. Detect such an edge.
    bool isTransitiveEdge(const V3GraphEdge* edgep) VL_MT_DISABLED;

private:
    bool pathExistsInternal(const V3GraphVertex* ap, const V3GraphVertex* bp,
                            unsigned* costp = nullptr) VL_MT_DISABLED;
    template <GraphWay::en T_Way>
    void initHalfCriticalPaths(bool checkOnly) VL_MT_DISABLED;
    void incGeneration() { ++m_generation; }

    VL_UNCOPYABLE(GraphPathChecker);
};

#endif  // Guard
