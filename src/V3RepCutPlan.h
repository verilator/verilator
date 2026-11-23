// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Import and order RepCut partition memberships
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026-2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#ifndef VERILATOR_V3REPCUTPLAN_H_
#define VERILATOR_V3REPCUTPLAN_H_

#include "V3RepCutGraph.h"

#include <iosfwd>

namespace V3RepCut {

struct Partition final {
    // Each sequence includes its sources and lists operands before their users.
    // These are independent evaluation phases with separate private temporaries.
    std::vector<size_t> m_next;
    std::vector<size_t> m_output;  // Ordered output-reference dependencies for this partition
};

class Plan final {
public:
    Ownership m_ownership;  // Publication owners and ordered memory-write sinks
    std::vector<Partition> m_partitions;  // Execution order for each simulation partition

    // Read RepCut's CSV format: one partition per line, optional trailing comma.
    // Blank lines preserve empty partitions. Revalidate against this graph;
    // input file ordering is never treated as an execution order.
    static bool read(const Graph& graph, std::istream& input, Plan& result, std::string& error);
    // Invoke the external partitioner only for nontrivial automatic plans.
    // Validate generated memberships before constructing the executable plan.
    static bool partition(const Graph& graph, const std::string& base, Plan& result,
                          std::string& error);
    void dump(const Graph& graph, const std::string& base) const;
    static void selfTest();

private:
    void order(const Graph& graph, std::vector<std::vector<size_t>>& partitions);
};

}  // namespace V3RepCut
#endif  // Guard
