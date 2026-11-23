// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Structured partition-local RepCut programs
//
// Code available from: https://verilator.org
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026-2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//*************************************************************************
//
// Separate immutable evaluation values and guard regions from execution order.
// The AST expressions here are a typed bridge to Verilator's DFG, not scheduled
// functions. A guard region can contain many non-adjacent pieces of the input
// program. Optimize all its pure single-assignment equations together, retaining
// explicit joins, guards, memory reads and phase interfaces as graph boundaries.
// Then rebuild data/control dependences and schedule the optimized program.
// Physical state writes and compilation chunks are constructed by the caller
// only after this pass. This never synthesizes control flow into eager muxes.
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3RepCutProgram.h"

#include "V3DfgContext.h"
#include "V3DfgOptimizer.h"
#include "V3Graph.h"
#include "V3Stats.h"

#include <algorithm>
#include <functional>
#include <limits>
#include <map>
#include <set>
#include <tuple>

VL_DEFINE_DEBUG_FUNCTIONS;

namespace V3RepCut {
namespace {

struct Access final {
    std::set<AstVarScope*> m_reads;  // Variable bindings read by this statement
    std::set<AstVarScope*> m_writes;  // Variable bindings written by this statement
    bool m_pure = true;  // Every expression in the statement is pure
    bool m_memory = false;  // The statement accesses unpacked memory

    explicit Access(AstNode* nodep) {
        nodep->foreach([&](AstNode* childp) {
            if (const AstVarRef* const refp = VN_CAST(childp, VarRef)) {
                if (refp->access().isReadOrRW()) m_reads.insert(refp->varScopep());
                if (refp->access().isWriteOrRW()) m_writes.insert(refp->varScopep());
            }
            if (AstNodeExpr* const exprp = VN_CAST(childp, NodeExpr)) m_pure &= exprp->isPure();
            m_memory |= VN_IS(childp, ArraySel);
        });
    }
};

struct Guard final {
    size_t m_parent;  // Parent control-region index
    AstNodeExpr* m_conditionp;  // Condition governing this control region
    bool m_taken;  // Condition polarity selecting this region
    size_t m_depth;  // Nesting depth in the guard tree
};

struct Atom final {
    AstNodeStmt* m_statementp;  // Original indivisible statement
    size_t m_region;  // Guard region containing this statement
    Access m_access;  // Read, write and effect properties of the statement
    Atom(AstNodeStmt* stmtp, size_t region)
        : m_statementp{stmtp}
        , m_region{region}
        , m_access{stmtp} {}
};

class Operation final : public V3GraphVertex {
public:
    const size_t m_id;  // Stable operation index for deterministic scheduling
    const size_t m_region;  // Guard region required by the operation
    AstNodeStmt* const m_statementp;  // Null for a guard-dependency vertex
    size_t m_pending = 0;  // Predecessors still awaiting scheduling
    size_t m_priority;  // Earliest source definition order propagated to this operation
    Operation(V3Graph& graph, size_t id, size_t region, AstNodeStmt* stmtp)
        : V3GraphVertex{&graph}
        , m_id{id}
        , m_region{region}
        , m_statementp{stmtp}
        , m_priority{std::numeric_limits<size_t>::max()} {}
};

class Program final {
    AstScope& m_scope;  // Scope owning the reconstructed program
    const std::set<AstVarScope*>&
        m_preserve;  // Bindings that must remain observable outside the program
    const size_t m_expressionLimit;  // Maximum expression size for scoped optimization
    V3DfgContext& m_context;  // Shared partition-local DFG optimization context
    // Guard tree with the unconditional root at index zero
    std::vector<Guard> m_guards{{0, nullptr, true, 0}};
    std::map<std::tuple<size_t, AstVarScope*, bool>, size_t> m_guardIds;
    std::vector<Atom> m_atoms;  // Statements collected with their original guard regions
    std::map<AstVarScope*, size_t> m_definitionOrder;
    VNDeleter m_deleter;  // Deferred disposal of replaced source nodes

    // A join reads just one selected value. Keep it as an indivisible operation;
    // its guarded producers remain separate graph nodes, never eager operands.
    static bool isJoin(const AstIf* ifp) {
        const AstAssign* const thenp = VN_CAST(ifp->thensp(), Assign);
        const AstAssign* const elsep = VN_CAST(ifp->elsesp(), Assign);
        if (!thenp || !elsep || thenp->nextp() || elsep->nextp()) return false;
        const AstVarRef* const lhsThenp = VN_CAST(thenp->lhsp(), VarRef);
        const AstVarRef* const lhsElsep = VN_CAST(elsep->lhsp(), VarRef);
        return lhsThenp && lhsElsep && lhsThenp->varScopep() == lhsElsep->varScopep();
    }
    size_t region(size_t parent, AstNodeExpr* conditionp, bool taken) {
        // Normalized predicates are immutable scalar bindings. More general
        // conditions keep distinct regions, avoiding any speculative equivalence.
        const AstVarRef* const refp = VN_CAST(conditionp, VarRef);
        if (refp) {
            const auto found = m_guardIds.find({parent, refp->varScopep(), taken});
            if (found != m_guardIds.end()) return found->second;
        }
        const size_t id = m_guards.size();
        m_guards.push_back(
            {parent, conditionp->cloneTree(false), taken, m_guards[parent].m_depth + 1});
        m_deleter.pushDeletep(m_guards.back().m_conditionp);
        if (refp) m_guardIds.emplace(std::make_tuple(parent, refp->varScopep(), taken), id);
        return id;
    }
    void import(AstNodeStmt* stmtp, size_t parent) {
        AstIf* const ifp = VN_CAST(stmtp, If);
        if (!ifp || isJoin(ifp)) {
            m_atoms.emplace_back(stmtp, parent);
            return;
        }
        for (const bool taken : {true, false}) {
            if (!(taken ? ifp->thensp() : ifp->elsesp())) continue;
            const size_t child = region(parent, ifp->condp(), taken);
            // Unlinking each child advances the parent's branch head until it is empty.
            // cppcheck-suppress knownConditionTrueFalse
            while (AstNode* const bodyp = taken ? ifp->thensp() : ifp->elsesp()) {
                import(VN_AS(bodyp->unlinkFrBack(), NodeStmt), child);
            }
        }
        m_deleter.pushDeletep(ifp);
    }
    void optimize() {
        std::map<AstVarScope*, size_t> writers;
        for (const Atom& atom : m_atoms) {
            for (AstVarScope* const vscp : atom.m_access.m_writes) ++writers[vscp];
        }
        std::vector<bool> eligible(m_atoms.size(), false);
        std::set<AstVarScope*> boundary = m_preserve;
        for (size_t i = 1; i < m_guards.size(); ++i) {
            const Access access{m_guards[i].m_conditionp};
            boundary.insert(access.m_reads.begin(), access.m_reads.end());
        }
        std::map<AstVarScope*, std::set<size_t>> readers;
        for (size_t i = 0; i < m_atoms.size(); ++i) {
            const Atom& atom = m_atoms[i];
            eligible[i] = VN_IS(atom.m_statementp, Assign) && atom.m_access.m_pure
                          && !atom.m_access.m_memory && atom.m_access.m_writes.size() == 1;
            for (AstVarScope* const vscp : atom.m_access.m_writes)
                eligible[i] = eligible[i] && writers[vscp] == 1;
            for (AstVarScope* const vscp : atom.m_access.m_reads) {
                readers[vscp].insert(atom.m_region);
                if (!eligible[i]) boundary.insert(vscp);
                // Repeated writes are imperative candidate buffers. No equation
                // using them may be moved into a single-assignment region.
                if (writers[vscp] > 1) eligible[i] = false;
            }
            if (!eligible[i])
                boundary.insert(atom.m_access.m_reads.begin(), atom.m_access.m_reads.end());
        }
        std::vector<std::vector<AstNodeStmt*>> groups(m_guards.size());
        std::vector<Atom> opaque;
        for (size_t i = 0; i < m_atoms.size(); ++i) {
            if (eligible[i])
                groups[m_atoms[i].m_region].push_back(m_atoms[i].m_statementp);
            else
                opaque.emplace_back(m_atoms[i].m_statementp, m_atoms[i].m_region);
        }
        m_atoms.clear();
        for (size_t id = 0; id < groups.size(); ++id) {
            std::vector<AstNodeStmt*>& statements = groups[id];
            if (statements.empty()) continue;
            std::set<AstVarScope*> liveOuts;
            std::set<AstVarScope*> inputs;
            std::set<AstVarScope*> defined;
            for (AstNodeStmt* const stmtp : statements) {
                const Access access{stmtp};
                inputs.insert(access.m_reads.begin(), access.m_reads.end());
                for (AstVarScope* const vscp : access.m_writes) {
                    defined.insert(vscp);
                    const auto it = readers.find(vscp);
                    if (boundary.count(vscp)
                        || (it != readers.end()
                            && (it->second.size() > 1 || !it->second.count(id))))
                        liveOuts.insert(vscp);
                }
            }
            for (AstVarScope* const vscp : defined) inputs.erase(vscp);
            V3Stats::addStatSum("RepCut program, region input statements", statements.size());
            if (v3Global.opt.fDfg()) {
                const bool optimized = V3DfgOptimizer::optimizeBlock(
                    m_scope, statements, liveOuts, inputs, m_expressionLimit, m_context);
                V3Stats::addStatSum("RepCut program, optimized regions", optimized);
            }
            V3Stats::addStatSum("RepCut program, region output statements", statements.size());
            for (AstNodeStmt* const stmtp : statements) m_atoms.emplace_back(stmtp, id);
        }
        for (Atom& atom : opaque) m_atoms.emplace_back(atom.m_statementp, atom.m_region);
    }

    std::vector<Operation*> schedule(V3Graph& graph) {
        std::vector<Operation*> operations;
        std::map<AstVarScope*, std::vector<Operation*>> writers;
        std::vector<Operation*> guards(m_guards.size(), nullptr);
        for (size_t i = 1; i < m_guards.size(); ++i) {
            guards[i] = new Operation{graph, operations.size(), i, nullptr};
            operations.push_back(guards[i]);
        }
        for (const Atom& atom : m_atoms) {
            Operation* const opp
                = new Operation{graph, operations.size(), atom.m_region, atom.m_statementp};
            operations.push_back(opp);
            for (AstVarScope* const vscp : atom.m_access.m_writes) {
                writers[vscp].push_back(opp);
                const auto origin = m_definitionOrder.find(vscp);
                if (origin != m_definitionOrder.end())
                    opp->m_priority = std::min(opp->m_priority, origin->second);
            }
        }
        const auto depend = [&](Operation* top, const std::set<Operation*>& predecessors) {
            for (Operation* const fromp : predecessors) {
                UASSERT(fromp != top, "RepCut program value reads its own definition");
                new V3GraphEdge{&graph, fromp, top, 1};
                ++top->m_pending;
            }
        };
        for (Operation* const opp : operations) {
            std::set<Operation*> predecessors;
            const size_t parent
                = opp->m_statementp ? opp->m_region : m_guards[opp->m_region].m_parent;
            if (parent) predecessors.insert(guards[parent]);
            const Access access{opp->m_statementp ? static_cast<AstNode*>(opp->m_statementp)
                                                  : m_guards[opp->m_region].m_conditionp};
            for (AstVarScope* const vscp : access.m_reads) {
                const auto it = writers.find(vscp);
                if (it != writers.end()) predecessors.insert(it->second.begin(), it->second.end());
            }
            depend(opp, predecessors);
        }
        // Repeated candidate writes retain source order. They are never DFG
        // equations, and no reader of such a buffer moves into an optimized group.
        for (const auto& pair : writers) {
            for (size_t i = 1; i < pair.second.size(); ++i)
                depend(pair.second[i], {pair.second[i - 1]});
        }
        std::vector<Operation*> topological;
        for (Operation* const opp : operations) {
            if (!opp->m_pending) topological.push_back(opp);
        }
        for (size_t i = 0; i < topological.size(); ++i) {
            for (const V3GraphEdge& edge : topological[i]->outEdges()) {
                Operation* const nextp = static_cast<Operation*>(edge.top());
                UASSERT(nextp->m_pending, "RepCut program dependency underflow");
                if (!--nextp->m_pending) topological.push_back(nextp);
            }
        }
        UASSERT(topological.size() == operations.size(),
                "RepCut program contains a dependence cycle");
        // Preserve sink-cone locality after DFG creates or removes values. New
        // expressions inherit the earliest original consumer's priority. Region
        // membership constrains optimization, but is never an execution batch.
        for (auto it = topological.rbegin(); it != topological.rend(); ++it) {
            Operation* const opp = *it;
            for (const V3GraphEdge& edge : opp->inEdges()) {
                Operation* const predp = static_cast<Operation*>(edge.fromp());
                predp->m_priority = std::min(predp->m_priority, opp->m_priority);
                ++opp->m_pending;
            }
        }
        std::set<std::pair<size_t, size_t>> pending;
        for (Operation* const opp : operations) {
            if (!opp->m_pending) pending.emplace(opp->m_priority, opp->m_id);
        }
        std::vector<Operation*> ordered;
        while (!pending.empty()) {
            Operation* const opp = operations[pending.begin()->second];
            pending.erase(pending.begin());
            if (opp->m_statementp) ordered.push_back(opp);
            for (V3GraphEdge& edge : opp->outEdges()) {
                Operation* const nextp = static_cast<Operation*>(edge.top());
                if (!--nextp->m_pending) pending.emplace(nextp->m_priority, nextp->m_id);
            }
        }
        return ordered;
    }
    void emit(std::vector<AstNodeStmt*>& statements) {
        V3Graph graph;
        const std::vector<Operation*> ordered = schedule(graph);
        struct Frame final {
            size_t m_region;  // Guard region represented by this emission frame
            AstIf* m_ifp;  // Conditional receiving statements in this frame
        };
        std::vector<Frame> frames{{0, nullptr}};
        const auto append = [&](AstNodeStmt* stmtp) {
            const Frame& frame = frames.back();
            if (!frame.m_ifp)
                statements.push_back(stmtp);
            else if (m_guards[frame.m_region].m_taken)
                frame.m_ifp->addThensp(stmtp);
            else
                frame.m_ifp->addElsesp(stmtp);
        };
        for (Operation* const opp : ordered) {
            size_t target = opp->m_region;
            std::vector<size_t> path;
            while (frames.back().m_region != target) {
                if (m_guards[frames.back().m_region].m_depth >= m_guards[target].m_depth) {
                    frames.pop_back();
                } else {
                    path.push_back(target);
                    target = m_guards[target].m_parent;
                }
            }
            for (auto it = path.rbegin(); it != path.rend(); ++it) {
                AstNodeExpr* const condp = m_guards[*it].m_conditionp->cloneTree(false);
                AstIf* const ifp = new AstIf{condp->fileline(), condp, nullptr};
                append(ifp);
                frames.push_back({*it, ifp});
                V3Stats::addStatSum("RepCut program, emitted guards", 1);
            }
            append(opp->m_statementp);
        }
    }

public:
    Program(AstScope& scope, std::vector<AstNodeStmt*>& statements,
            const std::set<AstVarScope*>& preserve, size_t expressionLimit, V3DfgContext& context)
        : m_scope{scope}
        , m_preserve{preserve}
        , m_expressionLimit{expressionLimit}
        , m_context{context} {
        for (AstNodeStmt* const stmtp : statements) import(stmtp, 0);
        statements.clear();
        for (size_t i = 0; i < m_atoms.size(); ++i) {
            for (AstVarScope* const vscp : m_atoms[i].m_access.m_writes)
                m_definitionOrder.emplace(vscp, i);
        }
        V3Stats::addStatSum("RepCut program, programs", 1);
        V3Stats::addStatSum("RepCut program, guard regions", m_guards.size() - 1);
        optimize();
        emit(statements);
    }
};

}  // namespace

void optimizeProgram(AstScope& scope, std::vector<AstNodeStmt*>& statements,
                     const std::set<AstVarScope*>& preserve, size_t expressionLimit,
                     V3DfgContext& context) {
    Program{scope, statements, preserve, expressionLimit, context};
}

void selfTestProgram(AstScope& scope) {
    FileLine* const flp = scope.fileline();
    size_t counter = 0;
    const auto variable = [&](int width) {
        AstVarScope* const vscp = v3Global.rootp()->topScopep()->createTemp(
            "__Vrepcut_program_test" + cvtToStr(counter++),
            scope.findBitDType(width, width, VSigning::UNSIGNED));
        vscp->varp()->isInternal(true);
        return vscp;
    };
    const auto read = [&](AstVarScope* vscp) { return new AstVarRef{flp, vscp, VAccess::READ}; };
    const auto assign = [&](AstVarScope* vscp, AstNodeExpr* exprp) {
        return new AstAssign{flp, new AstVarRef{flp, vscp, VAccess::WRITE}, exprp};
    };
    AstVarScope* const ap = variable(7);
    AstVarScope* const bp = variable(7);
    AstVarScope* const gp = variable(1);
    AstVarScope* const xp = variable(7);
    AstVarScope* const yp = variable(7);
    AstVarScope* const rp = variable(7);
    AstVarScope* const sp = variable(7);
    AstVarScope* const zp = variable(7);
    const auto sum = [&]() { return new AstAdd{flp, read(ap), read(bp)}; };
    const auto join = [&](AstVarScope* dstp, AstVarScope* srcp) {
        return new AstIf{flp, read(gp), assign(dstp, read(srcp)), assign(dstp, read(bp))};
    };
    V3DfgContext context{"__VrepcutSelfTestProgram"};
    const auto check = [&](std::vector<AstNodeStmt*> statements, size_t adds) {
        optimizeProgram(scope, statements, {rp, sp}, 64, context);
        size_t count = 0;
        for (AstNodeStmt* const stmtp : statements)
            stmtp->foreach([&](const AstAdd*) { ++count; });
        if (v3Global.opt.fDfg())
            UASSERT(count == adds, "RepCut program did not optimize the complete guard region");
        // Execute both paths, with varied inputs and no default value for a
        // temporary. An inactive or forward read is an immediate test failure.
        for (uint32_t sample = 0; sample < 128; ++sample) {
            std::map<AstVarScope*, uint32_t> values{
                {ap, sample}, {bp, (sample * 13) & 127}, {gp, sample & 1}};
            std::function<uint32_t(const AstNodeExpr*)> value;
            value = [&](const AstNodeExpr* exprp) -> uint32_t {
                if (const AstVarRef* const refp = VN_CAST(exprp, VarRef)) {
                    const auto it = values.find(refp->varScopep());
                    UASSERT(it != values.end(), "RepCut program read an unavailable value");
                    return it->second;
                }
                if (const AstAdd* const addp = VN_CAST(exprp, Add))
                    return (value(addp->lhsp()) + value(addp->rhsp())) & 127;
                if (const AstConst* const constp = VN_CAST(exprp, Const)) return constp->toUInt();
                v3fatalSrc("Unexpected expression in RepCut program test");
                return 0;
            };
            std::function<void(const AstNode*)> execute;
            execute = [&](const AstNode* stmtp) {
                for (; stmtp; stmtp = stmtp->nextp()) {
                    if (const AstIf* const ifp = VN_CAST(stmtp, If)) {
                        execute(value(ifp->condp()) ? ifp->thensp() : ifp->elsesp());
                    } else {
                        const AstAssign* const assignp = VN_AS(stmtp, Assign);
                        values[VN_AS(assignp->lhsp(), VarRef)->varScopep()]
                            = value(assignp->rhsp());
                    }
                }
            };
            for (const AstNodeStmt* const stmtp : statements) execute(stmtp);
            const uint32_t expected = sample & 1 ? (values[ap] + values[bp]) & 127 : values[bp];
            UASSERT(values.at(rp) == expected && values.at(sp) == expected,
                    "RepCut program changed a guarded result");
        }
        VNDeleter deleter;
        for (AstNodeStmt* const stmtp : statements) deleter.pushDeletep(stmtp);
    };
    // Same-guard definitions separated by an observation of the first result
    // share within the complete program. A basic-block-only DFG cannot do this.
    check({new AstIf{flp, read(gp), assign(xp, sum())}, join(rp, xp),
           new AstIf{flp, read(gp), assign(yp, sum())}, join(sp, yp)},
          1);
    // The same guard must be revisitable: x -> unguarded join -> guarded z is a
    // legal DAG, although collapsing the guard into one atomic task makes a cycle.
    check({new AstIf{flp, read(gp), assign(xp, sum())}, join(rp, xp),
           new AstIf{flp, read(gp), assign(zp, read(rp))}, join(sp, zp)},
          1);
}

}  // namespace V3RepCut
