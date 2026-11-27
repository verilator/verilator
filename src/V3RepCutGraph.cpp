// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Represent and validate RepCut dependency graphs
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
// Own normalized operations independently of AST lifetime. Retain ordered operands
// and structured storage/domain identities through pruning and partition planning.
// Membership validation separates candidate evaluation from exclusive publication;
// it adds no scheduling edges, SCC merging, or runtime tasks.
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3RepCutGraph.h"

#include "V3File.h"
#include "V3Stats.h"

#include <algorithm>
#include <cstdio>
#include <fstream>
#include <memory>

VL_DEFINE_DEBUG_FUNCTIONS;

const char* V3RepCut::ascii(Op op) {
    switch (op) {
    case Op::ADD: return "ADD";
    case Op::AND: return "AND";
    case Op::BRANCH: return "BRANCH";
    case Op::CALL_CAPTURE: return "CALLBACK";
    case Op::CONCAT: return "CONCAT";
    case Op::COND: return "COND";
    case Op::CONSTANT: return "CONST";
    case Op::CONTEXT: return "CONTEXT";
    case Op::COUNTONES: return "COUNTONES";
    case Op::DIV: return "DIV";
    case Op::DIVS: return "DIVS";
    case Op::EFFECT: return "EFFECT";
    case Op::EQ: return "EQ";
    case Op::EXTEND: return "EXTEND";
    case Op::EXTENDS: return "EXTENDS";
    case Op::EXTERNAL: return "EXTERNAL";
    case Op::GT: return "GT";
    case Op::GTE: return "GTE";
    case Op::GTES: return "GTES";
    case Op::GTS: return "GTS";
    case Op::INIT: return "INIT";
    case Op::INPUT: return "INPUT";
    case Op::JOIN: return "JOIN";
    case Op::LOGAND: return "LOGAND";
    case Op::LOGNOT: return "LOGNOT";
    case Op::LOGOR: return "LOGOR";
    case Op::LT: return "LT";
    case Op::LTE: return "LTE";
    case Op::LTES: return "LTES";
    case Op::LTS: return "LTS";
    case Op::MEMREAD: return "MEMREAD";
    case Op::MEMWRITE: return "MEMWRITE";
    case Op::MODDIV: return "MODDIV";
    case Op::MODDIVS: return "MODDIVS";
    case Op::MUL: return "MUL";
    case Op::MULS: return "MULS";
    case Op::NEGATE: return "NEGATE";
    case Op::NEQ: return "NEQ";
    case Op::NEXT: return "NEXT";
    case Op::NOT: return "NOT";
    case Op::OLD: return "OLD";
    case Op::OLDMEM: return "OLDMEM";
    case Op::OR: return "OR";
    case Op::OUTPUT: return "OUTPUT";
    case Op::PENDING_MEMWRITE: return "PENDING_MEMWRITE";
    case Op::REDAND: return "REDAND";
    case Op::REDOR: return "REDOR";
    case Op::REDXOR: return "REDXOR";
    case Op::REPLICATE: return "REPLICATE";
    case Op::SEL: return "SEL";
    case Op::SHIFTL: return "SHIFTL";
    case Op::SHIFTR: return "SHIFTR";
    case Op::SHIFTRS: return "SHIFTRS";
    case Op::SUB: return "SUB";
    case Op::VAR: return "VAR";
    case Op::XOR: return "XOR";
    }
    v3fatalSrc("Invalid RepCut operation");
    return "";
}

V3RepCut::Vertex::Vertex(V3Graph* graphp, size_t id, Op kind, int width, bool sign,
                         const std::string& label)
    : V3GraphVertex{graphp}
    , m_id{id}
    , m_kind{kind}
    , m_width{width}
    , m_signed{sign}
    , m_label{label} {}

bool V3RepCut::Vertex::isSink() const {
    return m_kind == Op::NEXT || m_kind == Op::OUTPUT || m_kind == Op::MEMWRITE
           || m_kind == Op::EFFECT || m_kind == Op::CALL_CAPTURE;
}
bool V3RepCut::Vertex::zeroCost() const {
    return m_kind == Op::VAR || m_kind == Op::OLD || m_kind == Op::INPUT || m_kind == Op::CONSTANT
           || m_kind == Op::OLDMEM || m_kind == Op::INIT || m_kind == Op::EXTERNAL;
}

V3RepCut::Vertex* V3RepCut::Graph::make(Op kind, int width, bool sign,
                                        const std::vector<Vertex*>& inputs,
                                        const std::string& label) {
    Vertex* const vp = new Vertex{&m_graph, m_vertexps.size(), kind, width, sign, label};
    m_vertexps.push_back(vp);
    for (Vertex* const ip : inputs) {
        if (!ip) continue;  // The normalizer already marked this graph incomplete.
        addInput(vp, ip);
    }
    return vp;
}

void V3RepCut::Graph::addInput(Vertex* vertexp, Vertex* inputp) {
    UASSERT_OBJ(m_vertexps.at(vertexp->m_id) == vertexp && m_vertexps.at(inputp->m_id) == inputp,
                vertexp, "RepCut data dependency crosses graphs");
    vertexp->m_inputps.push_back(inputp);
    new Dependency{&m_graph, inputp, vertexp, DependencyKind::DATA};
}

size_t V3RepCut::Graph::makeRegion(size_t parent, Vertex* predicatep, bool taken) {
    UASSERT_OBJ(parent == NO_ID || parent < m_regions.size(), predicatep,
                "RepCut region parent must already exist");
    UASSERT_OBJ(m_vertexps.at(predicatep->m_id) == predicatep && predicatep->m_region == parent,
                predicatep, "RepCut predicate must execute in its parent region");
    UASSERT_OBJ(predicatep->m_width == 1 && !predicatep->isSink(), predicatep,
                "RepCut region requires a Boolean computation");
    predicatep->m_isRegionPredicate = true;
    m_regions.push_back({parent, predicatep, taken});
    return m_regions.size() - 1;
}

void V3RepCut::Graph::setRegion(Vertex* vertexp, size_t region) {
    UASSERT_OBJ(m_vertexps.at(vertexp->m_id) == vertexp && vertexp->m_region == NO_ID
                    && !vertexp->m_isRegionPredicate,
                vertexp, "RepCut execution region must be assigned once");
    const Region& control = m_regions.at(region);
    vertexp->m_region = region;
    new Dependency{&m_graph, control.m_predicatep, vertexp, DependencyKind::CONTROL};
}

// Overwritten assignments can leave unused operations. They must not become
// artificial sinks in the partitioning problem.
void V3RepCut::Graph::removeUnused() {
    std::vector<bool> live(m_vertexps.size(), false);
    std::vector<Vertex*> pending;
    for (Vertex* const vp : m_vertexps) {
        if (vp->isSink()) { pending.push_back(vp); }
    }
    while (!pending.empty()) {
        Vertex* const vp = pending.back();
        pending.pop_back();
        if (live[vp->m_id]) continue;
        live[vp->m_id] = true;
        vp->foreachPredecessor([&](const Vertex& input, DependencyKind) {
            pending.push_back(m_vertexps[input.m_id]);
            return false;
        });
    }
    // Drop empty regions before deleting their predicates. Parent regions precede
    // children, so reverse propagation retains ancestry without repeated walks.
    std::vector<bool> liveRegions(m_regions.size(), false);
    for (const Vertex* const vp : m_vertexps) {
        if (live[vp->m_id] && vp->m_region != NO_ID) liveRegions[vp->m_region] = true;
    }
    for (size_t i = m_regions.size(); i > 0; --i) {
        const size_t parent = m_regions[i - 1].m_parent;
        if (liveRegions[i - 1] && parent != NO_ID) liveRegions[parent] = true;
    }
    std::vector<size_t> regionIds(m_regions.size(), NO_ID);
    std::vector<Region> regions;
    for (size_t i = 0; i < m_regions.size(); ++i) {
        if (!liveRegions[i]) continue;
        const Region& region = m_regions[i];
        UASSERT(live[region.m_predicatep->m_id], "Live RepCut region lost its predicate");
        regionIds[i] = regions.size();
        regions.push_back({region.m_parent == NO_ID ? NO_ID : regionIds[region.m_parent],
                           region.m_predicatep, region.m_taken});
    }
    m_regions = std::move(regions);
    std::vector<Vertex*> retained;
    for (Vertex* const vp : m_vertexps) {
        if (live[vp->m_id]) {
            if (vp->m_region != NO_ID) vp->m_region = regionIds[vp->m_region];
            vp->m_id = retained.size();
            retained.push_back(vp);
        } else {
            VL_DO_DANGLING(vp->unlinkDelete(&m_graph), vp);
        }
    }
    m_vertexps = std::move(retained);
}

std::vector<size_t> V3RepCut::Graph::topologicalOrder() const {
    std::vector<size_t> indegree(m_vertexps.size(), 0);
    std::vector<Vertex*> ready;
    for (Vertex* const vp : m_vertexps) {
        indegree[vp->m_id] = vp->inEdges().size();
        if (!indegree[vp->m_id]) ready.push_back(vp);
    }
    for (size_t i = 0; i < ready.size(); ++i) {
        for (const V3GraphEdge& edge : ready[i]->outEdges()) {
            Vertex* const vp = static_cast<Vertex*>(edge.top());
            if (!--indegree[vp->m_id]) ready.push_back(vp);
        }
    }
    std::vector<size_t> result;
    result.reserve(ready.size());
    for (const Vertex* const vp : ready) result.push_back(vp->m_id);
    return result;
}

size_t V3RepCut::Graph::cyclicNodes() const {
    // Includes descendants blocked by a cycle, not only the cycle itself.
    return m_vertexps.size() - topologicalOrder().size();
}

void V3RepCut::Graph::nativeCycleBoundaries() {
    std::vector<bool> blocked(m_vertexps.size(), true);
    for (const size_t id : topologicalOrder()) blocked[id] = false;
    // Verilator converges the original combinational procedures. Cut reads of
    // their stored results at variables; never merge an SCC or guess a fixed
    // number of iterations inside the RepCut kernel. Descendants of a cycle
    // are conservatively treated as boundaries as well.
    for (Vertex* const vp : m_vertexps) {
        if (!blocked[vp->m_id] || vp->m_kind != Op::VAR) continue;
        UASSERT(vp->m_storage != NO_ID && vp->m_region == NO_ID,
                "Native cycle boundary requires unconditional storage");
        while (V3GraphEdge* const edgep = vp->inEdges().frontp()) edgep->unlinkDelete();
        vp->m_inputps.clear();
        vp->m_kind = Op::EXTERNAL;
        ++m_report.m_nativeCycleBoundaries;
    }
}

void V3RepCut::Graph::dumpControl(std::ostream& regions, std::ostream& controls) const {
    regions << "id\tparent\tpredicate\ttaken\n";
    for (size_t i = 0; i < m_regions.size(); ++i) {
        const Region& region = m_regions[i];
        regions << i << '\t';
        if (region.m_parent != NO_ID) regions << region.m_parent;
        regions << '\t' << region.m_predicatep->m_id << '\t' << region.m_taken << '\n';
    }
    controls << "node\tregion\tpredicate\ttaken\n";
    for (const Vertex* const vp : m_vertexps) {
        if (vp->m_region == NO_ID) continue;
        const Region& region = m_regions[vp->m_region];
        controls << vp->m_id << '\t' << vp->m_region << '\t' << region.m_predicatep->m_id << '\t'
                 << region.m_taken << '\n';
    }
}

void V3RepCut::Graph::dump(const std::string& base) const {
    // Validate every complete normalized graph independently of partitioner
    // availability. Multi-partition error paths are exercised by selfTest().
    if (!m_report.m_failures) {
        std::vector<std::vector<size_t>> partitions(1);
        for (const Vertex* const vp : m_vertexps) partitions[0].push_back(vp->m_id);
        Ownership plan;
        std::string error;
        UASSERT(ownership(partitions, plan, error), error);
    }
    size_t edges = 0;
    size_t controlEdges = 0;
    for (const Vertex* const vp : m_vertexps) {
        edges += vp->inEdges().size();
        if (vp->m_region != NO_ID) ++controlEdges;
    }
    if (v3Global.opt.repcutDumpGraph()
        || (v3Global.opt.repcut() && !v3Global.opt.repcutPartitioner().empty())) {
        // Remove a stale complete graph when a later invocation is incomplete.
        std::remove((base + ".graph").c_str());
        std::remove((base + ".partial").c_str());
        const std::unique_ptr<std::ofstream> graphp{
            V3File::new_ofstream(base + (m_report.m_failures ? ".partial" : ".graph"))};
        if (graphp->fail()) v3fatal("Cannot write RepCut early graph files: " << base);
        *graphp << edges << ' ' << m_vertexps.size() << '\n';
        for (const Vertex* const vp : m_vertexps) {
            // Unit costs only for operations and sinks; wires/sources have zero cost.
            *graphp << 'n' << vp->m_id << ' ' << (vp->zeroCost() ? 0 : 1);
            for (const V3GraphEdge& edge : vp->outEdges()) {
                *graphp << ' ' << static_cast<Vertex*>(edge.top())->m_id;
            }
            *graphp << '\n';
        }
        graphp->close();
        if (graphp->fail()) v3fatal("Cannot write RepCut early graph files: " << base);
    }
    V3Stats::addStat("RepCut native, cycle boundaries", m_report.m_nativeCycleBoundaries);
    for (const auto& pair : m_report.m_nativeRetained)
        V3Stats::addStat("RepCut native, retained " + pair.first, pair.second);
    V3Stats::addStat("RepCut early, nodes", m_vertexps.size());
    V3Stats::addStat("RepCut early, edges", edges);
    V3Stats::addStat("RepCut early, control edges", controlEdges);
    V3Stats::addStat("RepCut early, regions", m_regions.size());
    V3Stats::addStat("RepCut early, supported procedures", m_report.m_supported);
    V3Stats::addStat("RepCut early, unsupported occurrences", m_report.m_failures);
    V3Stats::addStat("RepCut early, state variables", m_report.m_stateVariables);
    V3Stats::addStat("RepCut early, memories with writes", m_report.m_writtenMemories);
    if (v3Global.opt.repcutDumpGraph()) dumpDiagnostics(base);
}

void V3RepCut::Graph::dumpDiagnostics(const std::string& base) const {
    const std::unique_ptr<std::ofstream> nodesp{V3File::new_ofstream(base + ".nodes.tsv")};
    const std::unique_ptr<std::ofstream> reportp{V3File::new_ofstream(base + ".report.txt")};
    const std::unique_ptr<std::ofstream> clocksp{V3File::new_ofstream(base + ".clocks.tsv")};
    const std::unique_ptr<std::ofstream> memoriesp{V3File::new_ofstream(base + ".memories.tsv")};
    const std::unique_ptr<std::ofstream> storagep{V3File::new_ofstream(base + ".storage.tsv")};
    const std::unique_ptr<std::ofstream> domainsp{V3File::new_ofstream(base + ".domains.tsv")};
    const std::unique_ptr<std::ofstream> bindingsp{V3File::new_ofstream(base + ".bindings.tsv")};
    const std::unique_ptr<std::ofstream> regionsp{V3File::new_ofstream(base + ".regions.tsv")};
    const std::unique_ptr<std::ofstream> controlsp{V3File::new_ofstream(base + ".controls.tsv")};
    if (nodesp->fail() || reportp->fail() || clocksp->fail() || memoriesp->fail()
        || storagep->fail() || domainsp->fail() || bindingsp->fail() || regionsp->fail()
        || controlsp->fail()) {
        v3fatal("Cannot write RepCut early graph files: " << base);
    }
    dumpControl(*regionsp, *controlsp);
    *storagep << "id\tlabel\twidth\tsigned\telements\n";
    for (size_t i = 0; i < m_storage.size(); ++i) {
        const Storage& storage = m_storage[i];
        *storagep << i << '\t' << storage.m_label << '\t' << storage.m_width << '\t'
                  << storage.m_signed << '\t' << storage.m_elements << '\n';
    }
    *domainsp << "id\tclock_storage\tposedge\tlabel\n";
    for (size_t i = 0; i < m_domains.size(); ++i) {
        const Domain& domain = m_domains[i];
        *domainsp << i << '\t';
        *domainsp << '\t';
        *domainsp << '\t' << domain.m_label << '\n';
    }
    *bindingsp << "id\tstorage\tdomain\tpriority\twords\taux\n";
    for (const Vertex* const vp : m_vertexps) {
        *bindingsp << vp->m_id << '\t';
        if (vp->m_storage != NO_ID) *bindingsp << vp->m_storage;
        *bindingsp << '\t';
        if (vp->m_domain != NO_ID) *bindingsp << vp->m_domain;
        *bindingsp << '\t';
        if (vp->m_priority != NO_ID) *bindingsp << vp->m_priority;
        *bindingsp << '\t';
        for (size_t i = 0; i < vp->m_words.size(); ++i) {
            if (i) *bindingsp << ',';
            *bindingsp << vp->m_words[i];
        }
        *bindingsp << '\t';
        if (vp->m_aux != NO_ID) *bindingsp << vp->m_aux;
        *bindingsp << '\n';
    }
    *nodesp << "id\tkind\twidth\tsigned\tlabel\tinputs\n";
    for (const Vertex* const vp : m_vertexps) {
        *nodesp << vp->m_id << '\t' << ascii(vp->m_kind) << '\t' << vp->m_width << '\t'
                << vp->m_signed << '\t' << vp->m_label << '\t';
        for (size_t i = 0; i < vp->m_inputps.size(); ++i) {
            if (i) *nodesp << ',';
            *nodesp << vp->m_inputps[i]->m_id;
        }
        *nodesp << '\n';
    }
    *reportp
        << "Native scheduler kernel graph; retained procedures execute outside kernels\n"
        << "OUTPUT nodes describe pre-edge observations; post-update settling is not modeled\n"
        << "complete " << (m_report.m_failures ? 0 : 1) << "\nprocedures " << m_report.m_procedures
        << "\nsupported_procedures " << m_report.m_supported << "\nstate_variables "
        << m_report.m_stateVariables << "\nraw_domains " << 0 << "\ndomains " << m_domains.size()
        << "\ninitial_values " << m_report.m_initialValues << "\nmemories_with_writes "
        << m_report.m_writtenMemories << "\ncycle_blocked_nodes " << m_report.m_blocked << '\n';
    *reportp << "native_threads " << v3Global.opt.threads() << '\n';
    *reportp << "native_cycle_boundaries " << m_report.m_nativeCycleBoundaries << '\n';
    for (const auto& pair : m_report.m_nativeRetained)
        *reportp << "native_retained " << pair.first << ": " << pair.second << '\n';
    *clocksp << "raw\tcanonical\n";
    *memoriesp << "memory\telements\telement_width\n";
    for (const auto& pair : m_report.m_memories) {
        *memoriesp << pair.first << '\t' << pair.second.first << '\t' << pair.second.second
                   << '\n';
    }
    for (const auto& pair : m_report.m_unsupported)
        *reportp << pair.first << ": " << pair.second << '\n';
    for (const auto& pair : m_report.m_writeTargets)
        *reportp << "unsupported_write_target " << pair.first << ": " << pair.second << '\n';
}

bool V3RepCut::Graph::ownership(const std::vector<std::vector<size_t>>& partitions,
                                Ownership& result, std::string& error) const {
    result = Ownership{};
    error.clear();
    const auto reject = [&error](const std::string& reason) {
        error = reason;
        return false;
    };
    if (m_report.m_failures || cyclicNodes()) { return reject("Graph is incomplete or cyclic"); }
    if (partitions.empty()) return reject("No partitions");
    Ownership plan;
    plan.m_sinkOwners.resize(m_vertexps.size(), NO_ID);
    plan.m_stateOwners.resize(m_storage.size(), NO_ID);
    plan.m_outputOwners.resize(m_storage.size(), NO_ID);
    plan.m_memoryWrites.resize(m_storage.size());
    std::vector<bool> covered(m_vertexps.size(), false);
    // Generation tags make validation linear in memberships and replicated edges,
    // without allocating a nodes-by-partitions matrix or clearing it per partition.
    std::vector<size_t> member(m_vertexps.size(), NO_ID);
    for (size_t part = 0; part < partitions.size(); ++part) {
        for (const size_t id : partitions[part]) {
            if (id >= m_vertexps.size()) return reject("Unknown node in membership");
            if (member[id] == part) return reject("Duplicate node within partition");
            member[id] = part;
            covered[id] = true;
            if (m_vertexps[id]->isSink()) {
                if (plan.m_sinkOwners[id] != NO_ID) return reject("Replicated sink");
                plan.m_sinkOwners[id] = part;
            }
        }
        for (const size_t id : partitions[part]) {
            const bool missing = m_vertexps[id]->foreachPredecessor([&](const Vertex& input,
                                                                        DependencyKind kind) {
                if (member[input.m_id] == part) return false;
                error = kind == DependencyKind::CONTROL ? "Control dependency outside partition"
                                                        : "Operand outside partition";
                return true;
            });
            if (missing) { return false; }
        }
    }
    for (const Vertex* const vp : m_vertexps) {
        if (!covered[vp->m_id]) return reject("Uncovered node");
        if (!vp->isSink()) continue;
        if (vp->m_kind == Op::EFFECT || vp->m_kind == Op::CALL_CAPTURE) {
            if (vp->m_domain >= m_domains.size()) return reject("Missing sink domain");
            continue;
        }
        if (vp->m_storage >= m_storage.size()) return reject("Missing sink storage");
        const Storage& storage = m_storage[vp->m_storage];
        const size_t owner = plan.m_sinkOwners[vp->m_id];
        size_t& stateOwner = plan.m_stateOwners[vp->m_storage];
        if (vp->m_kind == Op::OUTPUT) {
            size_t& outputOwner = plan.m_outputOwners[vp->m_storage];
            if (outputOwner != NO_ID) return reject("Multiple output sinks for storage");
            outputOwner = owner;
            // A state/output alias intentionally has separate phase owners.
            continue;
        }
        if (vp->m_domain >= m_domains.size()) return reject("Missing sink domain");
        if (vp->m_kind == Op::NEXT) {
            if (storage.m_elements) return reject("Scalar next-state sink targets memory");
            if (stateOwner != NO_ID) return reject("Multiple next-state sinks for storage");
            stateOwner = owner;
        } else {
            if (!storage.m_elements) return reject("Memory write targets scalar storage");
            if (vp->m_priority == NO_ID) return reject("Missing memory write priority");
            if ((vp->m_inputps.size() != 4 && vp->m_inputps.size() != 5)
                || vp->m_inputps[0]->m_kind != Op::OLDMEM
                || vp->m_inputps[0]->m_storage != vp->m_storage) {
                return reject("Memory write has mismatched old-memory source");
            }
            stateOwner = stateOwner == NO_ID ? owner : std::min(stateOwner, owner);
            plan.m_memoryWrites[vp->m_storage].push_back(vp->m_id);
        }
    }
    for (std::vector<size_t>& writes : plan.m_memoryWrites) {
        std::sort(writes.begin(), writes.end(), [this](size_t a, size_t b) {
            return m_vertexps[a]->m_priority < m_vertexps[b]->m_priority;
        });
        for (size_t i = 1; i < writes.size(); ++i) {
            if (m_vertexps[writes[i - 1]]->m_priority == m_vertexps[writes[i]]->m_priority) {
                return reject("Ambiguous memory write priority");
            }
        }
    }
    result = std::move(plan);
    return true;
}
