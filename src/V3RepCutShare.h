// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Share immutable values inside RepCut phases
//
// Code available from: https://verilator.org
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026-2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//*************************************************************************

#ifndef VERILATOR_V3REPCUTSHARE_H_
#define VERILATOR_V3REPCUTSHARE_H_

#include "V3RepCutGraph.h"

namespace V3RepCut {

// A lowering view, never a mutation of the graph or partition membership. Values
// may share only an earlier definition with identical type and execution region.
// Exports retain storage identity; inputs are valid opaque scalar phase values.
struct SharedPhase final {
    std::vector<size_t> m_representatives;  // Canonical graph node for each original node ID
    std::vector<size_t> m_sequence;  // Dependency-ordered canonical nodes retained in the phase
    size_t m_shared = 0;  // Equivalent nodes folded into existing representatives
    size_t m_pruned = 0;  // Nodes removed because no retained sink needs them

    static SharedPhase make(const Graph& graph, const std::vector<size_t>& sequence,
                            const std::set<size_t>& inputs, const std::set<size_t>& exports,
                            std::vector<size_t>* representativesp = nullptr);
    static void selfTest();
};

}  // namespace V3RepCut
#endif  // Guard
