// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Emit RepCut kernels and state publication
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

#ifndef VERILATOR_V3REPCUTEMIT_H_
#define VERILATOR_V3REPCUTEMIT_H_

#include "V3RepCutPlan.h"

#include <array>
#include <map>

class AstNetlist;
class AstVarScope;
class AstNodeExpr;
class AstNodeStmt;
class AstNodeAssign;
class AstSenTree;
class AstAlways;
namespace V3RepCut {
// Publication bindings retain operand order for deterministic dependency emission.
// Scalar values/enables, memory operands, and effect enables have named accessors
// because the same compact storage serves different sink kinds.
class Candidates final {
    std::array<AstVarScope*, 4> m_slots{};  // Sink operands in their original binding order

public:
    AstVarScope*& scalarValuep() { return m_slots[0]; }
    AstVarScope* scalarValuep() const { return m_slots[0]; }
    AstVarScope*& scalarEnablep() { return m_slots[1]; }
    AstVarScope* scalarEnablep() const { return m_slots[1]; }
    AstVarScope*& memoryEnablep() { return m_slots[0]; }
    AstVarScope* memoryEnablep() const { return m_slots[0]; }
    AstVarScope*& memoryAddressp() { return m_slots[1]; }
    AstVarScope* memoryAddressp() const { return m_slots[1]; }
    AstVarScope*& memoryValuep() { return m_slots[2]; }
    AstVarScope* memoryValuep() const { return m_slots[2]; }
    AstVarScope*& memoryOffsetp() { return m_slots[3]; }
    AstVarScope* memoryOffsetp() const { return m_slots[3]; }
    AstVarScope*& effectEnablep() { return m_slots[0]; }
    AstVarScope* effectEnablep() const { return m_slots[0]; }
    // Memory operand order is enable, address, value, optional bit offset.
    AstVarScope*& memoryOperand(size_t operand) { return m_slots[operand]; }
    const std::array<AstVarScope*, 4>& slots() const { return m_slots; }
};
// Capture independent read-only inputs in partitions while retaining the
// original scheduled foreign body and its DPI ABI. Reentrant callbacks remain
// entirely under ordinary scheduling.
struct Callback final {
    const AstNodeStmt* m_statementsp;
    std::vector<const AstVarScope*> m_inputps;
    std::vector<std::pair<const AstVarScope*, bool>> m_outputs;  // Variable, NBA
};
// Bindings are valid only during synchronous normalization and lowering, before
// any later pass can delete or rewrite storage. Never retained in Graph or Plan.
struct Bindings final {
    std::vector<AstVarScope*> m_storageps;
    std::vector<const AstNodeExpr*> m_contextps;
    std::vector<const AstNodeStmt*> m_effectps;
    std::vector<Callback> m_callbacks;  // Retained callback bodies and their input/output bindings
    // Native callbacks retain their original process and event scheduling. Only
    // read-only scalar arguments and completely driven array elements are
    // computed and captured by the partitions.
    std::map<size_t, AstAlways*> m_nativeCallbackps;
    std::vector<const AstSenTree*> m_domainps;
    std::vector<AstAlways*> m_clockedps;  // Source clocked procedures indexed by procedure ID
    std::vector<const AstAlways*> m_retainedps;
    std::map<size_t, const AstNodeAssign*> m_combAssignments;
    std::map<const Vertex*, size_t> m_sinkProcedures;  // Index in m_clockedps
    std::map<const AstNodeAssign*, const Vertex*> m_memoryWrites;
    std::map<const AstNodeStmt*, const Vertex*> m_effects;
};
void emit(AstNetlist* netlistp, const Graph& graph, const Plan& plan, const Bindings& bindings);
}  // namespace V3RepCut
#endif  // Guard
