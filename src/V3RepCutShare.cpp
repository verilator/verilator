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

// Intern exact typed expressions after partitioning, independently in each
// evaluation phase. The first definition in the same execution region dominates
// later uses whenever that region executes: graph values and its predicates are
// immutable. No operation is speculated, and no guard is removed or combined.
// Memory operations and their local dependents are excluded. Cache inputs are
// opaque values whose validity the caller proves; cache exports and publication
// sinks keep their identities. Recompute the closure through remapped data and
// unchanged control edges before constructing any mutable AST temporaries.
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3RepCutShare.h"

#include <numeric>
#include <tuple>
#include <unordered_map>

VL_DEFINE_DEBUG_FUNCTIONS;

namespace V3RepCut {
namespace {

// Full keys, rather than hash equality, prove equivalence. Operand order, result
// signedness, constant words and source storage are all semantically significant.
using Key = std::tuple<Op, int, bool, size_t, size_t, std::vector<uint32_t>, std::vector<size_t>>;

bool pure(const Vertex& vertex) {
    switch (vertex.m_kind) {
    case Op::ADD:
    case Op::AND:
    case Op::BRANCH:
    case Op::CONCAT:
    case Op::COND:
    case Op::CONSTANT:
    case Op::COUNTONES:
    case Op::DIV:
    case Op::DIVS:
    case Op::EQ:
    case Op::EXTEND:
    case Op::EXTENDS:
    case Op::EXTERNAL:
    case Op::GT:
    case Op::GTE:
    case Op::GTES:
    case Op::GTS:
    case Op::INIT:
    case Op::INPUT:
    case Op::JOIN:
    case Op::LOGAND:
    case Op::LOGNOT:
    case Op::LOGOR:
    case Op::LT:
    case Op::LTE:
    case Op::LTES:
    case Op::LTS:
    case Op::MODDIV:
    case Op::MODDIVS:
    case Op::MUL:
    case Op::MULS:
    case Op::NEGATE:
    case Op::NEQ:
    case Op::NOT:
    case Op::OLD:
    case Op::OR:
    case Op::REDAND:
    case Op::REDOR:
    case Op::REDXOR:
    case Op::REPLICATE:
    case Op::SEL:
    case Op::SHIFTL:
    case Op::SHIFTR:
    case Op::SHIFTRS:
    case Op::SUB:
    case Op::VAR:
    case Op::XOR: return true;
    default: return false;
    }
}

}  // namespace

SharedPhase SharedPhase::make(const Graph& graph, const std::vector<size_t>& sequence,
                              const std::set<size_t>& inputs, const std::set<size_t>& exports,
                              std::vector<size_t>* representativesp) {
    const size_t n = graph.m_vertexps.size();
    SharedPhase result;
    std::vector<size_t>& representatives
        = representativesp ? *representativesp : result.m_representatives;
    if (representatives.size() != n) representatives.resize(n);
    if (!representativesp) std::iota(representatives.begin(), representatives.end(), size_t{0});
    // Native event domains can contain small cones in a large model. Reuse the
    // dense representative lookup, but initialize only this phase's members.
    // Sparse flags avoid a full-design scan for every domain/partition pair.
    static constexpr uint8_t ELIGIBLE = 1;
    static constexpr uint8_t AVAILABLE = 2;
    static constexpr uint8_t NEEDED = 4;
    std::unordered_map<size_t, uint8_t> flags;
    flags.reserve(sequence.size() + inputs.size());
    for (const size_t id : sequence) representatives[id] = id;
    for (const size_t id : inputs) {
        representatives[id] = id;
        flags[id] = ELIGIBLE | AVAILABLE;
    }
    std::map<Key, size_t> expressions;
    for (const size_t id : sequence) {
        const Vertex& vertex = *graph.m_vertexps[id];
        bool safe = pure(vertex);
        vertex.foreachPredecessor([&](const Vertex& pred, DependencyKind) {
            const uint8_t state = flags[pred.m_id];
            UASSERT(state & AVAILABLE, "RepCut sharing input is unavailable");
            safe &= (state & ELIGIBLE) != 0;
            return false;
        });
        flags[id] = AVAILABLE | (safe ? ELIGIBLE : 0)
                    | (vertex.isSink() || exports.count(id) ? NEEDED : 0);
        // Predicates have control consumers not counted by expression inlining.
        // Keeping their identity also leaves the region tree entirely unchanged.
        if (!safe || vertex.m_isRegionPredicate || exports.count(id)) continue;
        std::vector<size_t> operands;
        for (const Vertex* const inputp : vertex.m_inputps)
            operands.push_back(representatives[inputp->m_id]);
        if (vertex.m_kind == Op::VAR) {
            const Vertex& input = *graph.m_vertexps[operands[0]];
            if (vertex.m_width == input.m_width && vertex.m_signed == input.m_signed
                && vertex.m_region == input.m_region) {
                representatives[id] = input.m_id;
                continue;
            }
        }
        const Key key{vertex.m_kind,    vertex.m_width, vertex.m_signed,    vertex.m_region,
                      vertex.m_storage, vertex.m_words, std::move(operands)};
        const auto found = expressions.emplace(key, id);
        representatives[id] = found.first->second;
        if (!found.second && !vertex.zeroCost()) ++result.m_shared;
    }
    // Representatives always precede their replacements. One reverse traversal
    // suffices, including dependencies of JOIN arms and nested region predicates.
    for (auto it = sequence.rbegin(); it != sequence.rend(); ++it) {
        const size_t id = *it;
        if (!(flags[id] & NEEDED)) continue;
        UASSERT(representatives[id] == id, "RepCut retained a replaced value");
        graph.m_vertexps[id]->foreachPredecessor([&](const Vertex& pred, DependencyKind) {
            flags[representatives[pred.m_id]] |= NEEDED;
            return false;
        });
    }
    for (const size_t id : sequence) {
        if (flags[id] & NEEDED)
            result.m_sequence.push_back(id);
        else if (!graph.m_vertexps[id]->zeroCost())
            ++result.m_pruned;
    }
    return result;
}

void SharedPhase::selfTest() {
    Graph graph;
    Vertex* const a = graph.make(Op::INPUT, 65, false);
    a->m_storage = 0;
    Vertex* const b = graph.make(Op::INPUT, 65, false);
    b->m_storage = 1;
    Vertex* const sum = graph.make(Op::ADD, 65, false, {a, b});
    Vertex* const alias = graph.make(Op::VAR, 65, false, {a});
    Vertex* const duplicate = graph.make(Op::ADD, 65, false, {alias, b});
    Vertex* const signedSum = graph.make(Op::ADD, 65, true, {a, b});
    Vertex* const reversed = graph.make(Op::SUB, 65, false, {b, a});
    Vertex* const difference = graph.make(Op::SUB, 65, false, {a, b});
    Vertex* const narrow = graph.make(Op::ADD, 63, false, {a, b});
    Vertex* const predicate = graph.make(Op::BRANCH, 1, false, {a});
    const size_t region = graph.makeRegion(NO_ID, predicate, true);
    const size_t opposite = graph.makeRegion(NO_ID, predicate, false);
    Vertex* const guarded = graph.make(Op::ADD, 65, false, {a, b});
    graph.setRegion(guarded, region);
    Vertex* const guardedCopy = graph.make(Op::ADD, 65, false, {a, b});
    graph.setRegion(guardedCopy, region);
    Vertex* const otherArm = graph.make(Op::ADD, 65, false, {a, b});
    graph.setRegion(otherArm, opposite);
    Vertex* const memory = graph.make(Op::OLDMEM, 65, false);
    Vertex* const read = graph.make(Op::MEMREAD, 65, false, {memory, a});
    Vertex* const readCopy = graph.make(Op::MEMREAD, 65, false, {memory, a});
    Vertex* const memorySum = graph.make(Op::ADD, 65, false, {read, b});
    Vertex* const memorySumCopy = graph.make(Op::ADD, 65, false, {read, b});
    Vertex* const cached = graph.make(Op::ADD, 65, false, {a, b});
    Vertex* const out = graph.make(Op::OUTPUT, 65, false, {duplicate});
    const std::set<size_t> exports{cached->m_id, guardedCopy->m_id};
    const SharedPhase phase = make(graph, graph.topologicalOrder(), {}, exports);
    const auto rep = [&](const Vertex* vertexp) { return phase.m_representatives[vertexp->m_id]; };
    UASSERT(rep(duplicate) == rep(sum), "RepCut did not share equivalent expressions");
    UASSERT(rep(alias) == rep(a), "RepCut did not resolve a typed alias");
    UASSERT(rep(signedSum) != rep(sum) && rep(narrow) != rep(sum), "RepCut shared unlike types");
    UASSERT(rep(reversed) != rep(difference), "RepCut ignored operand order");
    UASSERT(rep(guarded) != rep(sum) && rep(otherArm) != rep(guarded),
            "RepCut shared across execution regions");
    UASSERT(rep(readCopy) != rep(read) && rep(memorySumCopy) != rep(memorySum),
            "RepCut shared memory-dependent computations");
    UASSERT(rep(cached) == cached->m_id && rep(guardedCopy) == guardedCopy->m_id,
            "RepCut lost an export binding");
    UASSERT(rep(out) == out->m_id, "RepCut lost a publication sink");
    UASSERT(phase.m_sequence.size() == 7, "RepCut failed to prune the remapped closure");
    // An absent value is opaque even if its original defining expression equals
    // a local value. No sharing may cross phases or partitions by that equation.
    const SharedPhase boundary
        = make(graph, {duplicate->m_id, out->m_id}, {alias->m_id, b->m_id}, {});
    UASSERT(boundary.m_representatives[duplicate->m_id] == duplicate->m_id,
            "RepCut shared with an unavailable phase definition");
    const SharedPhase unbound = make(graph, graph.topologicalOrder(), {}, {});
    UASSERT(unbound.m_representatives[guardedCopy->m_id]
                == unbound.m_representatives[guarded->m_id],
            "RepCut missed sharing within one execution region");
    UASSERT(unbound.m_sequence.size() == 4, "RepCut retained dead exported ancestors");
    // Reusing scratch across a full phase, a small boundary, and a full phase
    // must not retain substitutions or availability from the previous phase.
    std::vector<size_t> scratch;
    const SharedPhase reused = make(graph, graph.topologicalOrder(), {}, exports, &scratch);
    UASSERT(reused.m_sequence == phase.m_sequence && scratch == phase.m_representatives,
            "RepCut shared scratch changed the initial phase");
    const SharedPhase reusedBoundary
        = make(graph, {duplicate->m_id, out->m_id}, {alias->m_id, b->m_id}, {}, &scratch);
    UASSERT(reusedBoundary.m_sequence == boundary.m_sequence
                && scratch[duplicate->m_id] == duplicate->m_id,
            "RepCut shared scratch retained a previous phase substitution");
    const SharedPhase reusedUnbound = make(graph, graph.topologicalOrder(), {}, {}, &scratch);
    UASSERT(reusedUnbound.m_sequence == unbound.m_sequence && scratch == unbound.m_representatives,
            "RepCut shared scratch retained a previous phase boundary");
    UASSERT(duplicate->m_inputps[0] == alias && duplicate->m_inputps[1] == b,
            "RepCut sharing changed the immutable partitioning graph");

    // Storage kind and identity, upper constant words, and alias conversions
    // must remain distinct even when low bits or diagnostic labels coincide.
    Graph leaves;
    Vertex* const source = leaves.make(Op::INPUT, 65, false);
    source->m_storage = 0;
    Vertex* const sourceCopy = leaves.make(Op::INPUT, 65, false);
    sourceCopy->m_storage = 0;
    Vertex* const other = leaves.make(Op::INPUT, 65, false);
    other->m_storage = 1;
    Vertex* const old = leaves.make(Op::OLD, 65, false);
    old->m_storage = 0;
    Vertex* const literal = leaves.make(Op::CONSTANT, 65, false);
    literal->m_words = {1, 0, 0};
    Vertex* const literalCopy = leaves.make(Op::CONSTANT, 65, false);
    literalCopy->m_words = {1, 0, 0};
    Vertex* const upper = leaves.make(Op::CONSTANT, 65, false);
    upper->m_words = {1, 0, 1};
    Vertex* const converted = leaves.make(Op::VAR, 63, false, {source});
    Vertex* const signedAlias = leaves.make(Op::VAR, 65, true, {source});
    const SharedPhase values = make(leaves, leaves.topologicalOrder(), {}, {});
    const auto value
        = [&](const Vertex* vertexp) { return values.m_representatives[vertexp->m_id]; };
    UASSERT(value(source) == value(sourceCopy), "RepCut missed identical source reads");
    UASSERT(value(source) != value(other) && value(source) != value(old),
            "RepCut shared unlike source storage");
    UASSERT(value(literal) == value(literalCopy) && value(literal) != value(upper),
            "RepCut compared constant words incorrectly");
    UASSERT(value(source) != value(converted) && value(source) != value(signedAlias),
            "RepCut discarded an alias type conversion");
}

}  // namespace V3RepCut
