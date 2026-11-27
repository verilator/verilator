// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Source-backed native RepCut partition programs
//
// Code available from: https://verilator.org
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026-2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//*************************************************************************

#ifndef VERILATOR_V3REPCUTNATIVE_H_
#define VERILATOR_V3REPCUTNATIVE_H_

#include "V3RepCutEmit.h"

#include <array>
#include <functional>

class AstScope;

namespace V3RepCut {
using NativeValues = std::map<size_t, AstVarScope*>;
// Graph islands consume previously materialized source values and export named
// combinational values. These are immutable within one evaluation, not caches.
struct NativeGraphBoundary final {
    const NativeValues& m_inputs;
    const NativeValues& m_outputs;  // Bindings receiving values exported by the graph island
};
using NativeGraphLower = std::function<std::vector<AstNodeStmt*>(const std::vector<size_t>&,
                                                                 const NativeGraphBoundary&)>;
enum class NativeLowering : uint8_t { GRAPH, SOURCE, HYBRID };

// Source drivers shared within one partition. Groups are ordered so every
// dependency precedes its consumers. Each group keeps its exact domain union;
// its values are valid only during the current joined compute invocation.
struct NativeSharedGroup final {
    std::vector<size_t> m_domains;
    std::vector<AstNodeStmt*> m_statements;  // Source statements evaluated under the domain union
};
struct NativeSharedPartition final {
    NativeValues m_values;  // Shared values materialized in this partition
    std::vector<NativeSharedGroup> m_groups;  // Shared source groups in dependency order
};
std::vector<NativeSharedPartition> nativeSharedPrograms(const Graph& graph, const Plan& plan,
                                                        const Bindings& bindings,
                                                        size_t statementLimit);

// Inputs and services used during one synchronous source-lowering invocation.
// Every field is aggregate-initialized at the synchronous call site.
// cppcheck-suppress-begin uninitMemberVarNoCtor
struct NativeProgramContext final {
    AstScope& m_scope;  // Scope receiving generated temporaries
    const Graph& m_graph;  // Normalized operation graph
    const Bindings& m_bindings;  // Live AST bindings
    const std::vector<size_t>& m_sequence;  // Dependency-ordered partition program
    const std::string& m_tag;  // Prefix for generated temporaries
    uint32_t m_storageGroup;  // Partition ownership group
    size_t m_statementLimit;  // AST construction budget
    const NativeValues& m_captures;  // Previously captured native inputs
    AstVarScope* m_effectPendingp;  // Optional aggregate effect enable
    const NativeGraphLower& m_lowerGraph;  // Lower exceptional graph islands
    const NativeValues& m_sharedInputs;  // Values materialized by shared prefixes
};
// cppcheck-suppress-end uninitMemberVarNoCtor
// Lowering appends statements and fills sink-indexed publication bindings.
// GRAPH leaves these outputs untouched for the caller's graph fallback.
struct NativeProgramOutput final {
    std::vector<Candidates>& m_candidates;  // Publication operands indexed by sink ID
    std::vector<std::vector<AstVarScope*>>& m_effectArguments;  // Captured effect arguments
    std::vector<AstNodeStmt*>& m_statements;  // Appended partition statements
};
// Retain source procedures and lower exceptional cones as local graph islands.
NativeLowering nativeProgram(const NativeProgramContext& context, NativeProgramOutput& output);
}  // namespace V3RepCut

#endif  // Guard
