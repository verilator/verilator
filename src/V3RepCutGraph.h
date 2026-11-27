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

#ifndef VERILATOR_V3REPCUTGRAPH_H_
#define VERILATOR_V3REPCUTGRAPH_H_

#include "V3Graph.h"

#include <iosfwd>
#include <limits>
#include <map>
#include <set>
#include <string>
#include <vector>

namespace V3RepCut {

// These IDs belong to one normalized graph, never to an AST address or a label.
static constexpr size_t NO_ID = std::numeric_limits<size_t>::max();

enum class Op : uint8_t {
    ADD,
    AND,
    BRANCH,  // Boolean decision evaluated in its containing region
    CALL_CAPTURE,  // Independent input capture for a native foreign procedure
    CONCAT,
    COND,
    CONSTANT,
    CONTEXT,  // Read of simulation context; never cached across evaluations
    COUNTONES,
    DIV,
    DIVS,
    EFFECT,  // Captured arguments for one ordered caller-side operation
    EQ,
    EXTEND,
    EXTENDS,
    EXTERNAL,  // Value maintained by native scheduling outside the kernel
    GT,
    GTE,
    GTES,
    GTS,
    INIT,
    INPUT,
    JOIN,  // Procedural value merge; selects one arm without demanding the other
    LOGAND,
    LOGNOT,
    LOGOR,
    LT,
    LTE,
    LTES,
    LTS,
    MEMREAD,
    MEMWRITE,  // Old memory, enable, address, value, optional partial-write bit offset
    MODDIV,
    MODDIVS,
    MUL,
    MULS,
    NEGATE,
    NEQ,
    NEXT,
    NOT,
    OLD,
    OLDMEM,
    OR,
    OUTPUT,
    PENDING_MEMWRITE,
    REDAND,
    REDOR,
    REDXOR,
    REPLICATE,
    SEL,
    SHIFTL,
    SHIFTR,
    SHIFTRS,
    SUB,
    VAR,
    XOR,
};
const char* ascii(Op op);

struct Storage final {
    std::string m_label;  // Protected diagnostic label; not a binding key
    int m_width = 0;  // Packed element width in bits
    bool m_signed = false;  // Stored values use signed interpretation
    size_t m_elements = 0;  // Zero for scalars
};
struct Domain final {
    std::string m_label;  // Diagnostic label for the sensitivity domain
};

enum class DependencyKind : uint8_t { CONTROL, DATA };

class Dependency final : public V3GraphEdge {
    VL_RTTI_IMPL(Dependency, V3GraphEdge)
    const DependencyKind m_kind;  // Whether this edge carries data or a control prerequisite

public:
    Dependency(V3Graph* graphp, V3GraphVertex* fromp, V3GraphVertex* top, DependencyKind kind)
        : V3GraphEdge{graphp, fromp, top, 1}
        , m_kind{kind} {}
    DependencyKind kind() const { return m_kind; }
    V3GraphEdge* clone(V3Graph* graphp, V3GraphVertex* fromp, V3GraphVertex* top) const override {
        return new Dependency{graphp, fromp, top, m_kind};
    }
};

class Vertex final : public V3GraphVertex {
public:
    size_t m_id;  // Stable index in the graph vertex table
    Op m_kind;  // Operation represented by this vertex
    const int m_width;  // Width of the result in bits
    const bool m_signed;  // Result uses signed interpretation
    const std::string m_label;  // Diagnostic source label, not an AST binding
    std::vector<Vertex*> m_inputps;  // Operand order, including repeated operands
    size_t m_region = NO_ID;  // Execution region; NO_ID means unconditional
    bool m_isRegionPredicate = false;  // Region creation fixes the predicate's execution region
    std::vector<uint32_t> m_words;  // Constant value, least significant word first
    size_t m_storage = NO_ID;  // Source storage or publication destination
    size_t m_domain = NO_ID;  // NEXT/MEMWRITE edge domain
    size_t m_priority = NO_ID;  // MEMWRITE source order within its writing procedure
    size_t m_aux = NO_ID;  // Synchronous emitter binding for context/effect templates

    Vertex(V3Graph* graphp, size_t id, Op kind, int width, bool sign, const std::string& label);
    bool isSink() const;
    bool zeroCost() const;
    // Visit ALL dependencies, independently of arithmetic operand order. Stop
    // and return true when the callback does; repeated edges are visited too.
    template <typename T_Func>
    bool foreachPredecessor(const T_Func& func) const {
        for (const V3GraphEdge& edge : inEdges()) {
            if (func(*static_cast<const Vertex*>(edge.fromp()), edge.as<Dependency>()->kind())) {
                return true;
            }
        }
        return false;
    }
};

// Regions preserve branch structure without coarsening operations. The predicate
// executes in the parent region, so its own control edge carries outer guards
// into every dependent cone. Predicate pointers belong only to this owned graph.
struct Region final {
    size_t m_parent;
    Vertex* m_predicatep;  // Predicate controlling entry to the region
    bool m_taken;  // Predicate polarity required to enter the region
};

struct Report final {
    size_t m_procedures = 0;  // Number of procedures considered for extraction
    size_t m_supported = 0;  // Procedures accepted by source analysis
    size_t m_failures = 0;  // Failures preventing a complete partitionable graph
    size_t m_initialValues = 0;  // Storage objects with extracted initial values
    size_t m_stateVariables = 0;  // State variables referenced by extracted kernels
    size_t m_writtenMemories = 0;  // Memories with extracted write ports
    size_t m_blocked = 0;  // Procedures retained under native scheduling
    size_t m_nativeCycleBoundaries = 0;  // Native feedback boundaries outside the kernel graph
    std::map<std::string, size_t> m_nativeRetained;
    std::map<std::string, size_t> m_unsupported;
    std::map<std::string, size_t> m_writeTargets;
    // Includes unsupported/unretained memories to preserve diagnostic coverage.
    std::map<std::string, std::pair<size_t, int>> m_memories;
};

// Membership permits replicated pure operations, but every sink has exactly one
// evaluation owner. All writes to one memory share a publication owner so source
// priority survives replicated evaluation. These assignments describe placement,
// not synchronization: the emitter and native scheduler must still order old-state
// reads, candidate capture and publication. Native OUTPUT sinks are references
// for planning; the ordinary scheduler retains their combinational settling.
struct Ownership final {
    std::vector<size_t> m_sinkOwners;  // Node ID -> partition, NO_ID for non-sinks
    std::vector<size_t> m_stateOwners;  // Storage ID -> publication partition
    std::vector<size_t> m_outputOwners;  // Storage ID -> output publication partition
    std::vector<std::vector<size_t>> m_memoryWrites;  // Storage ID -> ordered sink IDs
};

// Owned, AST-independent snapshot. Normalization and emission share separate
// live AST bindings at one pass boundary; Graph and Plan never retain them.
// Diagnostic labels must never be parsed to rebind ASTs. Incomplete graphs remain
// inspectable but cannot be partitioned. Retained native procedures are explicit
// graph boundaries and do not by themselves make the kernel graph incomplete.
class Graph final {
    void dumpDiagnostics(const std::string& base) const;

public:
    V3Graph m_graph;  // Owned operation and dependency graph
    std::vector<Vertex*> m_vertexps;  // Vertices indexed by stable node ID
    std::vector<Storage> m_storage;  // Storage descriptions indexed by storage ID
    std::vector<Domain> m_domains;  // Sensitivity domains indexed by domain ID
    std::vector<Region> m_regions;  // Nested control regions indexed by region ID
    Report m_report;  // Extraction counts and retained-procedure diagnostics

    Vertex* make(Op kind, int width, bool sign, const std::vector<Vertex*>& inputs = {},
                 const std::string& label = "");
    void addInput(Vertex* vertexp, Vertex* inputp);
    size_t makeRegion(size_t parent, Vertex* predicatep, bool taken);
    void setRegion(Vertex* vertexp, size_t region);
    void removeUnused();
    void nativeCycleBoundaries();
    std::vector<size_t> topologicalOrder() const;
    size_t cyclicNodes() const;
    void dump(const std::string& base) const;
    void dumpControl(std::ostream& regions, std::ostream& controls) const;
    // Reject malformed/incomplete membership; leave result empty on any failure.
    bool ownership(const std::vector<std::vector<size_t>>& partitions, Ownership& result,
                   std::string& error) const;
    static void selfTest();
};

}  // namespace V3RepCut
#endif  // Guard
