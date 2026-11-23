// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Test RepCut graph dependencies and partition ownership
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
//
// Construct small graphs to check dependency closure, exclusive sink ownership,
// publication ordering, and rejection of malformed partition memberships.
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3RepCutGraph.h"

#include <initializer_list>
#include <sstream>

VL_DEFINE_DEBUG_FUNCTIONS;

namespace V3RepCut {
namespace {

// Resolve IDs after pruning, which may renumber the surviving vertices.
std::vector<size_t> membership(std::initializer_list<const Vertex*> vertices) {
    std::vector<size_t> ids;
    for (const Vertex* const vertexp : vertices) ids.push_back(vertexp->m_id);
    return ids;
}

void selfTestControl() {
    Graph graph;
    graph.m_storage = {{"next", 8, false, 0}, {"output", 8, false, 0}};
    graph.m_domains = {{"clock"}};
    Vertex* const unusedp = graph.make(Op::CONSTANT, 1, false);
    const size_t unusedRegion = graph.makeRegion(NO_ID, unusedp, true);
    Vertex* const predicatep = graph.make(Op::INPUT, 1, false);
    Vertex* const datap = graph.make(Op::INPUT, 8, false);
    Vertex* const nestedp = graph.make(Op::REDOR, 1, false, {datap});
    const size_t taken = graph.makeRegion(NO_ID, predicatep, true);
    const size_t untaken = graph.makeRegion(NO_ID, predicatep, false);
    graph.setRegion(nestedp, taken);
    const size_t inner = graph.makeRegion(taken, nestedp, false);
    Vertex* const addp = graph.make(Op::ADD, 8, false, {datap, datap});
    graph.setRegion(addp, inner);
    // The same predecessor may be both data and control; preserve both edges.
    Vertex* const xorp = graph.make(Op::XOR, 8, false, {datap, predicatep});
    graph.setRegion(xorp, untaken);
    Vertex* const nextp = graph.make(Op::NEXT, 8, false, {addp});
    nextp->m_storage = 0;
    nextp->m_domain = 0;
    Vertex* const outputp = graph.make(Op::OUTPUT, 8, false, {xorp});
    outputp->m_storage = 1;
    graph.setRegion(graph.make(Op::NOT, 8, false, {datap}), unusedRegion);
    graph.removeUnused();
    UASSERT(graph.m_vertexps.size() == 7 && graph.m_regions.size() == 3,
            "RepCut pruning must retain control ancestors and remove dead regions");
    UASSERT(addp->m_inputps == (std::vector<Vertex*>{datap, datap}) && addp->inEdges().size() == 3
                && xorp->inEdges().size() == 3,
            "Control dependencies changed data operands");
    UASSERT(nestedp->m_region == 0 && addp->m_region == 2 && graph.m_regions[2].m_parent == 0,
            "Pruning lost nested region identities");
    Ownership ownership;
    std::string error;
    const std::vector<std::vector<size_t>> parts{
        membership({predicatep, datap, nestedp, addp, nextp}),
        membership({predicatep, datap, xorp, outputp})};
    UASSERT(graph.ownership(parts, ownership, error), error);
    UASSERT(!graph.ownership({membership({predicatep, datap, addp, nextp}),
                              membership({predicatep, datap, nestedp, xorp, outputp})},
                             ownership, error)
                && error == "Control dependency outside partition"
                && ownership.m_sinkOwners.empty(),
            "RepCut accepted a missing control-only ancestor");
    const std::vector<size_t> topo = graph.topologicalOrder();
    std::vector<size_t> rank(topo.size());
    UASSERT(topo.size() == graph.m_vertexps.size(),
            "Repeated dependencies broke topological order");
    for (size_t i = 0; i < topo.size(); ++i) rank[topo[i]] = i;
    for (const Vertex* const vp : graph.m_vertexps) {
        vp->foreachPredecessor([&](const Vertex& input, DependencyKind) {
            UASSERT(rank[input.m_id] < rank[vp->m_id], "Control predecessor ordered after use");
            return false;
        });
    }
    // Literal IDs here independently check the stable diagnostic export format.
    std::ostringstream regions;
    std::ostringstream controls;
    graph.dumpControl(regions, controls);
    UASSERT(regions.str() == "id\tparent\tpredicate\ttaken\n0\t\t0\t1\n1\t\t0\t0\n2\t0\t2\t0\n"
                && controls.str()
                       == "node\tregion\tpredicate\ttaken\n2\t0\t0\t1\n3\t2\t2\t0\n4\t1\t0\t0\n",
            "Control export lost branch polarity or remapped identities");
    graph.removeUnused();
    std::ostringstream prunedRegions;
    std::ostringstream prunedControls;
    graph.dumpControl(prunedRegions, prunedControls);
    UASSERT(prunedRegions.str() == regions.str() && prunedControls.str() == controls.str(),
            "Repeated pruning changed control metadata");
    // A predicate depending on its controlled computation creates a mixed cycle.
    graph.addInput(nestedp, addp);
    UASSERT(!graph.ownership(parts, ownership, error) && error == "Graph is incomplete or cyclic",
            "RepCut accepted a data/control dependency cycle");
}

void selfTestOwnership() {
    static constexpr size_t MEMORY_STORAGE = 1;
    static constexpr size_t SCALAR_STORAGE = 2;
    static constexpr size_t CLOCK_DOMAIN = 0;
    static constexpr size_t EARLY_PRIORITY = 2;
    static constexpr size_t LATE_PRIORITY = 9;

    Graph graph;
    // Deliberately indistinguishable labels prove ownership uses identities.
    graph.m_storage = {{"same", 1, false, 0}, {"same", 8, false, 3}, {"same", 8, false, 0}};
    graph.m_domains = {{"same"}};
    Vertex* const oldp = graph.make(Op::OLDMEM, 8, false);
    oldp->m_storage = MEMORY_STORAGE;
    Vertex* const onep = graph.make(Op::CONSTANT, 1, false);
    onep->m_words = {1};
    // Creation order differs from source priority. Candidates belong to different
    // workers, while publication must apply early then late at a single owner.
    Vertex* const latep = graph.make(Op::MEMWRITE, 8, false, {oldp, onep, onep, onep});
    latep->m_storage = MEMORY_STORAGE;
    latep->m_domain = CLOCK_DOMAIN;
    latep->m_priority = LATE_PRIORITY;
    Vertex* const earlyp = graph.make(Op::MEMWRITE, 8, false, {oldp, onep, onep, onep});
    earlyp->m_storage = MEMORY_STORAGE;
    earlyp->m_domain = CLOCK_DOMAIN;
    earlyp->m_priority = EARLY_PRIORITY;
    Vertex* const nextp = graph.make(Op::NEXT, 8, false, {onep});
    nextp->m_storage = SCALAR_STORAGE;
    nextp->m_domain = CLOCK_DOMAIN;
    Vertex* const outputp = graph.make(Op::OUTPUT, 8, false, {onep});
    outputp->m_storage = SCALAR_STORAGE;
    const std::vector<std::vector<size_t>> parts{membership({oldp, onep, latep, nextp}),
                                                 membership({oldp, onep, earlyp, outputp})};
    Ownership plan;
    std::string error;
    UASSERT(graph.ownership(parts, plan, error), error);
    UASSERT(plan.m_stateOwners[oldp->m_storage] == 0 && plan.m_stateOwners[nextp->m_storage] == 0
                && plan.m_outputOwners[outputp->m_storage] == 1
                && plan.m_sinkOwners[earlyp->m_id] == 1,
            "Incorrect RepCut phase ownership");
    UASSERT(plan.m_memoryWrites[oldp->m_storage] == membership({earlyp, latep}),
            "Memory publication order");
    const auto checkBad
        = [&](const std::vector<std::vector<size_t>>& invalid, const std::string& expected) {
              UASSERT(!graph.ownership(invalid, plan, error), "Invalid membership accepted");
              UASSERT(error == expected, error);
              UASSERT(plan.m_sinkOwners.empty() && plan.m_stateOwners.empty()
                          && plan.m_outputOwners.empty() && plan.m_memoryWrites.empty(),
                      "Failed ownership retained stale plan");
          };
    checkBad({}, "No partitions");
    std::vector<std::vector<size_t>> unknown = parts;
    unknown.back().push_back(graph.m_vertexps.size());
    checkBad(unknown, "Unknown node in membership");
    checkBad(
        {membership({oldp, onep, latep, nextp}), membership({oldp, onep, earlyp, outputp, onep})},
        "Duplicate node within partition");
    checkBad(
        {membership({oldp, onep, latep, nextp}), membership({oldp, onep, earlyp, outputp, latep})},
        "Replicated sink");
    checkBad({membership({oldp, onep, latep, nextp}), membership({onep, earlyp, outputp})},
             "Operand outside partition");
    checkBad({membership({oldp, onep, latep, nextp}), membership({oldp, onep, outputp})},
             "Uncovered node");
    // Publication metadata must identify an unambiguous destination and write order.
    latep->m_priority = EARLY_PRIORITY;
    checkBad(parts, "Ambiguous memory write priority");
    latep->m_priority = LATE_PRIORITY;
    nextp->m_storage = NO_ID;
    checkBad(parts, "Missing sink storage");
    nextp->m_storage = SCALAR_STORAGE;
    nextp->m_domain = NO_ID;
    checkBad(parts, "Missing sink domain");
    nextp->m_domain = CLOCK_DOMAIN;
    outputp->m_kind = Op::NEXT;
    outputp->m_domain = CLOCK_DOMAIN;
    checkBad(parts, "Multiple next-state sinks for storage");
    outputp->m_kind = Op::OUTPUT;
    outputp->m_domain = NO_ID;
    nextp->m_kind = Op::OUTPUT;
    checkBad(parts, "Multiple output sinks for storage");
    nextp->m_kind = Op::NEXT;
    latep->m_priority = NO_ID;
    checkBad(parts, "Missing memory write priority");
    latep->m_priority = LATE_PRIORITY;
    oldp->m_storage = SCALAR_STORAGE;
    checkBad(parts, "Memory write has mismatched old-memory source");
    oldp->m_storage = MEMORY_STORAGE;
    // Both incomplete extraction and actual cycles must reject ownership.
    graph.m_report.m_failures = 1;
    checkBad(parts, "Graph is incomplete or cyclic");
    graph.m_report.m_failures = 0;
    UASSERT(graph.ownership(parts, plan, error), error);
    // A real graph cycle must also reject ownership even without a coverage error.
    graph.addInput(onep, onep);
    checkBad(parts, "Graph is incomplete or cyclic");
}

}  // namespace

void Graph::selfTest() {
    selfTestControl();
    selfTestOwnership();
}

}  // namespace V3RepCut
