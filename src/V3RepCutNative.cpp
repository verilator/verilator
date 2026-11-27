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
//
// The fine data/control graph selects each partition's dependency closure.
// Materialize the original optimized combinational drivers in that order, then
// slice original clocked bodies by owned state/memory sinks. Expressions and
// procedural control remain native AST. All evaluation writes private storage;
// ordinary native NBAs publish the candidates after the worker join. No graph
// vertices are merged and no source procedure becomes a partitioning unit.
// Unsupported source materialization is local: graph-lower exceptional driver
// cones first, export their private values, then retain other source drivers.
// Exceptional clocked procedures consume these immutable values through a
// second graph island. Source and graph effects only capture arguments here;
// their ordered replay and state publication still follow the worker join.
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3RepCutNative.h"

#include "V3Branch.h"
#include "V3DupFinder.h"
#include "V3File.h"
#include "V3InstrCount.h"
#include "V3RepCut.h"
#include "V3Stats.h"

#include <algorithm>
#include <fstream>
#include <memory>
#include <set>

VL_DEFINE_DEBUG_FUNCTIONS;

namespace V3RepCut {
namespace {

using Remap = std::map<const AstVarScope*, AstVarScope*>;
using EffectCapture = std::pair<AstVarScope*, std::vector<AstVarScope*>>;

void mergeWrites(std::set<const AstVarScope*>& target, std::set<const AstVarScope*>& source) {
    // Merge smaller sets into larger sets to avoid repeatedly copying large
    // nested results.
    if (target.size() < source.size()) target.swap(source);
    target.insert(source.begin(), source.end());
}

std::set<const AstVarScope*> definiteWrites(const AstNode* nodep) {
    std::set<const AstVarScope*> result;
    for (; nodep; nodep = nodep->nextp()) {
        if (const AstAssignDly* const assignp = VN_CAST(nodep, AssignDly)) {
            if (const AstVarRef* const refp = VN_CAST(assignp->lhsp(), VarRef))
                result.insert(refp->varScopep());
        } else if (const AstIf* const ifp = VN_CAST(nodep, If)) {
            std::set<const AstVarScope*> taken = definiteWrites(ifp->thensp());
            std::set<const AstVarScope*> untaken = definiteWrites(ifp->elsesp());
            if (taken.size() > untaken.size()) taken.swap(untaken);
            for (auto it = taken.begin(); it != taken.end();) {
                if (!untaken.count(*it))
                    it = taken.erase(it);
                else
                    ++it;
            }
            mergeWrites(result, taken);
        } else if (const AstBegin* const beginp = VN_CAST(nodep, Begin)) {
            std::set<const AstVarScope*> nested = definiteWrites(beginp->stmtsp());
            mergeWrites(result, nested);
        }
    }
    return result;
}

class SourceRewrite final : public VNVisitor {
    const Remap& m_remap;  // Original bindings mapped to private source temporaries
    const Remap& m_scalar;  // Scalar NBA destinations mapped to candidate value slots
    const std::map<const AstNodeAssign*, Candidates>& m_memory;
    const std::map<const AstNodeStmt*, EffectCapture>& m_effects;
    AstVarScope* const m_effectPendingp;  // Flag recording effects pending caller execution

    static AstVarRef* ref(AstVarScope* vscp, VAccess access = VAccess::READ) {
        return new AstVarRef{vscp->fileline(), vscp, access};
    }
    void visit(AstVarRef* nodep) override {
        const auto it = m_remap.find(nodep->varScopep());
        if (it == m_remap.end()) return;
        nodep->varScopep(it->second);
        nodep->varp(it->second->varp());
    }
    void visit(AstAssignDly* nodep) override {
        AstNodeStmt* replacementp = nullptr;
        if (const AstVarRef* const lhsp = VN_CAST(nodep->lhsp(), VarRef)) {
            const auto it = m_scalar.find(lhsp->varScopep());
            if (it != m_scalar.end()) {
                replacementp = new AstAssign{nodep->fileline(), ref(it->second, VAccess::WRITE),
                                             nodep->rhsp()->unlinkFrBack()};
            }
        } else {
            const auto it = m_memory.find(nodep);
            if (it != m_memory.end()) {
                const Candidates& candidate = it->second;
                const AstSel* const partialp = VN_CAST(nodep->lhsp(), Sel);
                const AstArraySel* const selectp
                    = VN_AS(partialp ? partialp->fromp() : nodep->lhsp(), ArraySel);
                const AstUnpackArrayDType* const dtypep
                    = VN_AS(selectp->fromp()->dtypep()->skipRefp(), UnpackArrayDType);
                AstBegin* const beginp = new AstBegin{nodep->fileline(), "", nullptr, false};
                beginp->addStmtsp(new AstAssign{nodep->fileline(),
                                                ref(candidate.memoryAddressp(), VAccess::WRITE),
                                                selectp->bitp()->unlinkFrBack()});
                AstNodeExpr* enabledp = new AstConst{nodep->fileline(), AstConst::BitTrue{}};
                if ((uint64_t{1} << candidate.memoryAddressp()->width())
                    > static_cast<uint64_t>(dtypep->elementsConst())) {
                    enabledp->deleteTree();
                    const V3Number bound{nodep, candidate.memoryAddressp()->width(),
                                         static_cast<uint32_t>(dtypep->elementsConst() - 1)};
                    enabledp = new AstLte{nodep->fileline(), ref(candidate.memoryAddressp()),
                                          new AstConst{nodep->fileline(), bound}};
                }
                beginp->addStmtsp(new AstAssign{
                    nodep->fileline(), ref(candidate.memoryEnablep(), VAccess::WRITE), enabledp});
                beginp->addStmtsp(new AstAssign{nodep->fileline(),
                                                ref(candidate.memoryValuep(), VAccess::WRITE),
                                                nodep->rhsp()->unlinkFrBack()});
                if (candidate.memoryOffsetp()) {
                    beginp->addStmtsp(new AstAssign{nodep->fileline(),
                                                    ref(candidate.memoryOffsetp(), VAccess::WRITE),
                                                    partialp->lsbp()->unlinkFrBack()});
                }
                replacementp = beginp;
            }
        }
        if (!replacementp) {
            pushDeletep(nodep->unlinkFrBack());
            return;
        }
        nodep->replaceWith(replacementp);
        pushDeletep(nodep);
        iterate(replacementp);
    }
    void visit(AstCoverInc* nodep) override { pushDeletep(nodep->unlinkFrBack()); }
    void effect(AstNodeStmt* nodep) {
        const auto it = m_effects.find(nodep);
        if (it == m_effects.end()) {
            pushDeletep(nodep->unlinkFrBack());
            return;
        }
        AstBegin* const beginp = new AstBegin{nodep->fileline(), "", nullptr, false};
        size_t index = 0;
        const auto capture = [&](AstNodeExpr* argp) {
            beginp->addStmtsp(new AstAssign{nodep->fileline(),
                                            ref(it->second.second.at(index++), VAccess::WRITE),
                                            argp->unlinkFrBack()});
        };
        if (const AstDisplay* const displayp = VN_CAST(nodep, Display)) {
            for (AstNodeExpr* argp = displayp->fmtp()->exprsp(); argp;) {
                AstNodeExpr* const nextp = VN_AS(argp->nextp(), NodeExpr);
                const AstConst* const cp = VN_CAST(argp, Const);
                if (!cp || !cp->num().isString()) capture(argp);
                argp = nextp;
            }
            if (AstNodeExpr* const filep = displayp->filep()) capture(filep);
        }
        UASSERT_OBJ(index == it->second.second.size(), nodep, "Effect capture argument mismatch");
        beginp->addStmtsp(new AstAssign{nodep->fileline(), ref(it->second.first, VAccess::WRITE),
                                        new AstConst{nodep->fileline(), AstConst::BitTrue{}}});
        if (m_effectPendingp) {
            beginp->addStmtsp(new AstAssign{nodep->fileline(),
                                            ref(m_effectPendingp, VAccess::WRITE),
                                            new AstConst{nodep->fileline(), AstConst::BitTrue{}}});
        }
        nodep->replaceWith(beginp);
        pushDeletep(nodep);
        iterate(beginp);
    }
    void visit(AstDisplay* nodep) override { effect(nodep); }
    void visit(AstStop* nodep) override { effect(nodep); }
    void visit(AstFinish* nodep) override { effect(nodep); }
    void visit(AstComment* nodep) override { pushDeletep(nodep->unlinkFrBack()); }
    void visit(AstBegin* nodep) override {
        iterateChildren(nodep);
        if (AstNode* const stmtsp = nodep->stmtsp()) {
            nodep->replaceWith(stmtsp->unlinkFrBackWithNext());
            pushDeletep(nodep);
        } else {
            pushDeletep(nodep->unlinkFrBack());
        }
    }
    void visit(AstIf* nodep) override {
        iterateChildren(nodep);
        if (!nodep->thensp() && !nodep->elsesp()) pushDeletep(nodep->unlinkFrBack());
    }
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    SourceRewrite(AstNode* nodep, const Remap& remap, const Remap& scalar,
                  const std::map<const AstNodeAssign*, Candidates>& memory,
                  const std::map<const AstNodeStmt*, EffectCapture>& effects,
                  AstVarScope* effectPendingp)
        : m_remap{remap}
        , m_scalar{scalar}
        , m_memory{memory}
        , m_effects{effects}
        , m_effectPendingp{effectPendingp} {
        iterate(nodep);
    }
};

class NativeProgram final {
    AstScope& m_scope;  // Scope owning generated bindings and statements
    const Graph& m_graph;  // Normalized operation graph for this design
    const Bindings& m_bindings;  // Live source AST bindings for the normalized graph
    const std::vector<size_t>& m_sequence;  // Nodes selected for this partition evaluation
    const std::string& m_tag;  // Prefix for generated partition-local names
    const uint32_t m_storageGroup;  // Ownership group assigned to private temporaries
    std::vector<Candidates>& m_candidates;  // Captured publication slots indexed by sink ID
    std::vector<std::vector<AstVarScope*>>&
        m_effectArguments;  // Captured effect argument storage indexed by sink ID
    std::vector<AstNodeStmt*>&
        m_statements;  // Generated statements for this native partition program
    AstVarScope* const m_effectPendingp;  // Flag recording effects pending caller execution
    const NativeGraphLower& m_lowerGraph;  // Callback used to lower exceptional graph islands
    const NativeValues& m_sharedInputs;  // Materialized inputs supplied by shared source drivers
    Remap m_remap;  // Original bindings mapped to private source temporaries
    Remap m_scalar;  // Scalar NBA destinations mapped to candidate value slots
    NativeValues m_values;  // Materialized variable bindings indexed by graph node ID
    std::set<size_t> m_graphDrivers;  // Values requiring graph lowering before source statements
    std::set<size_t> m_graphSinks;  // Sinks requiring graph lowering after source statements
    std::vector<size_t>
        m_driverSequence;  // Dependency-ordered graph nodes producing source inputs
    std::map<size_t, const AstAlways*> m_procedures;
    std::set<const Vertex*> m_sinks;
    std::set<const AstVarScope*> m_definiteWrites;
    // Scalar candidates may share a publication enable when their complete
    // sets of source write branches agree. Source pointers only live during
    // this lowering; no new cross-node AST references are introduced.
    using WriteSites = std::map<size_t, const AstAssignDly*>;
    std::map<const AstVarScope*, WriteSites> m_writeSites;
    std::map<const AstAssignDly*, std::vector<AstVarScope*>> m_writeMarkers;
    Remap m_scalarEnables;  // Scalar NBA destinations mapped to publication enable slots
    std::map<std::tuple<size_t, const AstNode*, bool>, size_t> m_writeBranches;
    size_t m_temporaries = 0;  // Number of private source temporaries created
    std::unique_ptr<std::ofstream> m_costReportp;  // Optional report of native statement costs

    void reportCost(const char* kindp, size_t id, AstNode* nodep) {
        if (!m_costReportp) return;
        size_t conditionals = 0;
        size_t selections = 0;
        nodep->foreach([&](const AstNode* childp) {
            conditionals += VN_IS(childp, If) || VN_IS(childp, Cond);
            selections += VN_IS(childp, ArraySel);
        });
        // Count this materialized source tree once, independently of its graph
        // closure. V3InstrCount chooses the longer conditional path; this is
        // an estimate before local optimization, not a hardware cycle count.
        *m_costReportp << kindp << '\t' << id << '\t' << nodep->nodeCount() << '\t'
                       << V3InstrCount::count(nodep, false) << '\t' << conditionals << '\t'
                       << selections << '\n';
    }

    AstVarScope* temp(AstNodeDType* dtypep) {
        AstVarScope* const vscp = v3Global.rootp()->topScopep()->createTemp(
            m_tag + "__source" + cvtToStr(m_temporaries++), dtypep);
        vscp->varp()->varType(VVarType::BLOCKTEMP);
        vscp->varp()->noReset(true);
        vscp->varp()->trace(false);
        vscp->varp()->isInternal(true);
        vscp->varp()->repcutStorageGroup(m_storageGroup);
        return vscp;
    }
    static AstVarRef* ref(AstVarScope* vscp, VAccess access = VAccess::READ) {
        return new AstVarRef{vscp->fileline(), vscp, access};
    }
    void reject(const char* reasonp, const AstNode* nodep) const {
        V3Stats::addStatSum(std::string{"RepCut native source, rejected "} + reasonp, 1);
        UINFO(3, m_tag << " source fallback: " << reasonp << ": " << nodep);
        if (debug() >= 9) {
            const std::unique_ptr<std::ofstream> reportp{
                V3File::new_ofstream(v3Global.opt.makeDir() + "/" + v3Global.opt.prefix() + m_tag
                                     + ".source-rejected.tree")};
            if (reportp->fail()) v3fatal("Cannot write RepCut source rejection report");
            *reportp << reasonp << '\n';
            nodep->dumpTree(*reportp, "", 8);
        }
    }
    std::vector<size_t> closure(const std::set<size_t>& roots, const NativeValues& inputs) const {
        std::set<size_t> included;
        std::vector<size_t> pending{roots.begin(), roots.end()};
        while (!pending.empty()) {
            const size_t id = pending.back();
            pending.pop_back();
            if (inputs.count(id) || !included.insert(id).second) continue;
            m_graph.m_vertexps[id]->foreachPredecessor(
                [&](const Vertex& predecessor, DependencyKind) {
                    pending.push_back(predecessor.m_id);
                    return false;
                });
        }
        // Retain the partition's topological order, including control edges.
        // There are at most two islands, so this scans the sequence at most twice.
        std::vector<size_t> result;
        result.reserve(included.size());
        for (const size_t id : m_sequence) {
            if (included.count(id)) result.push_back(id);
        }
        UASSERT_OBJ(result.size() == included.size(), &m_scope,
                    "Native graph island escaped partition closure");
        return result;
    }
    bool prepare(size_t limit) {
        size_t driverCount = 0;
        for (const size_t id : m_sequence) {
            const Vertex& vertex = *m_graph.m_vertexps[id];
            if (vertex.m_kind == Op::VAR) {
                ++driverCount;
                const auto it = m_bindings.m_combAssignments.find(vertex.m_storage);
                if (it == m_bindings.m_combAssignments.end()) {
                    reject("combinational source", m_bindings.m_storageps[vertex.m_storage]);
                    m_graphDrivers.insert(id);
                } else if (static_cast<size_t>(it->second->nodeCount()) > limit) {
                    reject("driver size", it->second);
                    m_graphDrivers.insert(id);
                }
            } else if (vertex.isSink()) {
                const auto it = m_bindings.m_sinkProcedures.find(&vertex);
                if (it == m_bindings.m_sinkProcedures.end())
                    reject("sink source", &m_scope);
                else
                    m_procedures.emplace(it->second, m_bindings.m_clockedps.at(it->second));
            }
        }
        for (auto it = m_procedures.begin(); it != m_procedures.end();) {
            const AstAlways* const alwaysp = it->second;
            const char* reasonp = nullptr;
            const AstNode* rejectedp = nullptr;
            alwaysp->foreach([&](const AstNode* nodep) {
                if (reasonp) return;
                // Slicing imperative local definitions needs separate liveness
                // analysis. Keep those procedures on the graph lowering path.
                if (VN_IS(nodep, Assign)) reasonp = "blocking assignment";
                if (const AstNodeAssign* const assignp = VN_CAST(nodep, NodeAssign))
                    if (static_cast<size_t>(assignp->nodeCount()) + 8 > limit)
                        reasonp = "assignment size";
                if (const AstIf* const ifp = VN_CAST(nodep, If))
                    if (static_cast<size_t>(ifp->condp()->nodeCount()) + 8 > limit)
                        reasonp = "condition size";
                if (const AstDisplay* const displayp = VN_CAST(nodep, Display)) {
                    for (const AstNodeExpr* argp = displayp->fmtp()->exprsp(); argp;
                         argp = VN_AS(argp->nextp(), NodeExpr))
                        if (static_cast<size_t>(argp->nodeCount()) + 8 > limit)
                            reasonp = "effect argument size";
                }
                if (reasonp) rejectedp = nodep;
            });
            if (reasonp) {
                reject(reasonp, rejectedp);
                V3Stats::addStatSum("RepCut native source, graph clocked procedures", 1);
                it = m_procedures.erase(it);
            } else {
                const std::set<const AstVarScope*> written = definiteWrites(alwaysp->stmtsp());
                m_definiteWrites.insert(written.begin(), written.end());
                ++it;
            }
        }
        for (const size_t id : m_sequence) {
            const Vertex& vertex = *m_graph.m_vertexps[id];
            if (!vertex.isSink()) continue;
            const auto it = m_bindings.m_sinkProcedures.find(&vertex);
            if (it != m_bindings.m_sinkProcedures.end() && m_procedures.count(it->second))
                m_sinks.insert(&vertex);
            else
                m_graphSinks.insert(id);
        }
        // Materialize bad combinational cones once, exporting every VAR they
        // contain. Eligible downstream drivers can then keep their source AST.
        if (!m_graphDrivers.empty()) {
            m_driverSequence = closure(m_graphDrivers, m_sharedInputs);
            for (const size_t id : m_driverSequence) {
                if (m_graph.m_vertexps[id]->m_kind == Op::VAR) m_graphDrivers.insert(id);
            }
        }
        return m_graphSinks.empty() || !m_procedures.empty()
               || driverCount > m_graphDrivers.size();
    }
    void drivers() {
        for (const size_t id : m_sequence) {
            const Vertex& vertex = *m_graph.m_vertexps[id];
            if (vertex.m_kind != Op::VAR) continue;
            AstVarScope* const sourcep = m_bindings.m_storageps[vertex.m_storage];
            const auto shared = m_sharedInputs.find(id);
            AstVarScope* const valuep
                = shared == m_sharedInputs.end() ? temp(sourcep->dtypep()) : shared->second;
            m_remap.emplace(sourcep, valuep);
            m_values.emplace(id, valuep);
        }
        if (!m_driverSequence.empty()) {
            NativeValues outputs;
            for (const size_t id : m_graphDrivers) outputs.emplace(id, m_values.at(id));
            const std::vector<AstNodeStmt*> graph
                = m_lowerGraph(m_driverSequence, NativeGraphBoundary{m_sharedInputs, outputs});
            m_statements.insert(m_statements.end(), graph.begin(), graph.end());
            V3Stats::addStatSum("RepCut native source, graph combinational drivers",
                                outputs.size());
        }
        for (const size_t id : m_sequence) {
            const Vertex& vertex = *m_graph.m_vertexps[id];
            if (vertex.m_kind != Op::VAR || m_graphDrivers.count(id) || m_sharedInputs.count(id))
                continue;
            AstNodeAssign* const clonep
                = const_cast<AstNodeAssign*>(m_bindings.m_combAssignments.at(vertex.m_storage))
                      ->cloneTree(false);
            SourceRewrite{clonep, m_remap, {}, {}, {}, nullptr};
            reportCost("driver", id, clonep);
            m_statements.push_back(clonep);
            V3Stats::addStatSum("RepCut native source, combinational drivers", 1);
        }
    }
    size_t writeBranch(size_t parent, AstNodeExpr* condp, bool taken, V3DupFinder& conditions) {
        const auto found = conditions.findDuplicate(condp);
        const AstNode* const keyp
            = (found == conditions.end() ? conditions.insert(condp) : found)->second;
        return m_writeBranches
            .emplace(std::make_tuple(parent, keyp, taken), m_writeBranches.size() + 1)
            .first->second;
    }
    bool collectWriteSites(const AstNode* nodep, size_t block, V3DupFinder& conditions) {
        for (; nodep; nodep = nodep->nextp()) {
            if (const AstAssignDly* const assignp = VN_CAST(nodep, AssignDly)) {
                if (const AstVarRef* const refp = VN_CAST(assignp->lhsp(), VarRef))
                    m_writeSites[refp->varScopep()].emplace(block, assignp);
            } else if (const AstIf* const ifp = VN_CAST(nodep, If)) {
                const size_t taken = writeBranch(block, ifp->condp(), true, conditions);
                const size_t untaken = writeBranch(block, ifp->condp(), false, conditions);
                if (!collectWriteSites(ifp->thensp(), taken, conditions)) return false;
                if (!collectWriteSites(ifp->elsesp(), untaken, conditions)) return false;
            } else if (const AstBegin* const beginp = VN_CAST(nodep, Begin)) {
                if (!collectWriteSites(beginp->stmtsp(), block, conditions)) return false;
            } else if (!VN_IS(nodep, Comment) && !VN_IS(nodep, CoverInc) && !VN_IS(nodep, Display)
                       && !VN_IS(nodep, Stop) && !VN_IS(nodep, Finish)) {
                // Do not infer write activity through an unhandled control
                // construct. The ordinary hold/publication path remains valid.
                V3Stats::addStatSum(std::string{"RepCut native source, ungrouped statement "}
                                        + nodep->typeName(),
                                    1);
                return false;
            }
        }
        return true;
    }
    void writeGroups() {
        // Eligibility excludes imperative assignments and impure expressions.
        // Within this partition/domain every source predicate observes the same
        // old state and precomputed inputs, even across split source procedures.
        // V3DupFinder verifies tree equality after hashing (and owns user4).
        V3DupFinder conditions;
        for (const auto& pair : m_procedures) {
            if (!collectWriteSites(pair.second->stmtsp(), 0, conditions)) return;
        }
        std::map<std::vector<size_t>, std::vector<const AstVarScope*>> groups;
        // Graph order makes group membership and marker placement deterministic.
        for (const size_t id : m_sequence) {
            const Vertex& vertex = *m_graph.m_vertexps[id];
            if (vertex.m_kind != Op::NEXT || !m_sinks.count(&vertex)) continue;
            const AstVarScope* const storagep = m_bindings.m_storageps[vertex.m_storage];
            if (m_definiteWrites.count(storagep)) continue;
            const auto it = m_writeSites.find(storagep);
            if (it == m_writeSites.end()) continue;
            std::vector<size_t> blocks;
            for (const auto& site : it->second) blocks.push_back(site.first);
            groups[blocks].push_back(storagep);
        }
        for (const auto& group : groups) {
            V3Stats::addStatSum("RepCut native source, scalar write paths", 1);
            // Amortize the flag's initialization and publication test across
            // multiple scalar destinations. Leave singleton groups unchanged.
            if (group.second.size() < 2) continue;
            AstVarScope* const enabledp = temp(m_scope.findBitDType(1, 1, VSigning::UNSIGNED));
            m_statements.push_back(
                new AstAssign{enabledp->fileline(), ref(enabledp, VAccess::WRITE),
                              new AstConst{enabledp->fileline(), AstConst::BitFalse{}}});
            for (const AstVarScope* const storagep : group.second)
                m_scalarEnables.emplace(storagep, enabledp);
            for (const auto& site : m_writeSites.at(group.second.front()))
                m_writeMarkers[site.second].push_back(enabledp);
            V3Stats::addStatSum("RepCut native source, scalar write groups", 1);
            V3Stats::addStatSum("RepCut native source, guarded scalar candidates",
                                group.second.size());
        }
    }
    void candidates() {
        for (const size_t id : m_sequence) {
            const Vertex& vertex = *m_graph.m_vertexps[id];
            if (!m_sinks.count(&vertex)) continue;
            Candidates& values = m_candidates[id];
            if (vertex.m_kind == Op::EFFECT) {
                values.effectEnablep() = temp(m_scope.findBitDType());
                m_statements.push_back(
                    new AstAssign{m_scope.fileline(), ref(values.effectEnablep(), VAccess::WRITE),
                                  new AstConst{m_scope.fileline(), AstConst::BitFalse{}}});
                for (const Vertex* const inputp : vertex.m_inputps) {
                    m_effectArguments[id].push_back(temp(m_scope.findBitDType(
                        inputp->m_width, inputp->m_width,
                        inputp->m_signed ? VSigning::SIGNED : VSigning::UNSIGNED)));
                }
                continue;
            }
            AstVarScope* const storagep = m_bindings.m_storageps[vertex.m_storage];
            if (vertex.m_kind == Op::NEXT) {
                values.scalarValuep() = temp(storagep->dtypep());
                m_scalar.emplace(storagep, values.scalarValuep());
                // Preserve an inactive NBA's hold value without changing any
                // state before all partitions finish their old-state reads.
                const auto enabled = m_scalarEnables.find(storagep);
                if (enabled != m_scalarEnables.end()) {
                    // Slot one is the optional scalar publication enable.
                    // Candidate values are read only when this group wrote.
                    values.scalarEnablep() = enabled->second;
                } else if (!m_definiteWrites.count(storagep)) {
                    m_statements.push_back(
                        new AstAssign{storagep->fileline(),
                                      ref(values.scalarValuep(), VAccess::WRITE), ref(storagep)});
                }
            } else {
                UASSERT(vertex.m_kind == Op::MEMWRITE, "Unexpected native source sink");
                for (size_t i = 0; i + 1 < vertex.m_inputps.size(); ++i) {
                    const Vertex& input = *vertex.m_inputps[i + 1];
                    if (i == 3 && input.m_kind == Op::CONSTANT) continue;
                    values.memoryOperand(i) = temp(m_scope.findBitDType(
                        input.m_width, input.m_width,
                        input.m_signed ? VSigning::SIGNED : VSigning::UNSIGNED));
                }
                m_statements.push_back(new AstAssign{
                    storagep->fileline(), ref(values.memoryEnablep(), VAccess::WRITE),
                    new AstConst{storagep->fileline(), AstConst::BitFalse{}}});
            }
        }
    }
    void clocked() {
        // Iterate source order, not pointer order. Different procedures cannot
        // communicate through their private blocking temporaries.
        for (const auto& pair : m_procedures) {
            const AstAlways* const sourcep = pair.second;
            AstAlways* const clonep = const_cast<AstAlways*>(sourcep)->cloneTree(false);
            // Capturing effects replaces $display/$stop/$finish with ordinary
            // assignments. Preserve the stock branch heuristic while its source
            // cues still exist, including branches with retained state updates.
            // Chunking keeps these If nodes even when it outlines their arms.
            V3Branch::branchSubtree(clonep);
            std::map<const AstNodeAssign*, Candidates> memory;
            std::map<const AstNodeStmt*, EffectCapture> effects;
            sourcep->foreach([&](const AstAssignDly* assignp) {
                const auto it = m_bindings.m_memoryWrites.find(assignp);
                if (it != m_bindings.m_memoryWrites.end() && m_sinks.count(it->second))
                    memory.emplace(assignp->clonep(), m_candidates[it->second->m_id]);
                const auto marker = m_writeMarkers.find(assignp);
                if (marker != m_writeMarkers.end()) {
                    for (AstVarScope* const enabledp : marker->second) {
                        assignp->clonep()->addNextHere(
                            new AstAssign{assignp->fileline(), ref(enabledp, VAccess::WRITE),
                                          new AstConst{assignp->fileline(), AstConst::BitTrue{}}});
                    }
                }
            });
            sourcep->foreach([&](const AstNodeStmt* stmtp) {
                const auto it = m_bindings.m_effects.find(stmtp);
                if (it != m_bindings.m_effects.end() && m_sinks.count(it->second)) {
                    const size_t id = it->second->m_id;
                    effects.emplace(
                        stmtp->clonep(),
                        EffectCapture{m_candidates[id].effectEnablep(), m_effectArguments[id]});
                }
            });
            SourceRewrite{clonep, m_remap, m_scalar, memory, effects, m_effectPendingp};
            reportCost("clocked", pair.first, clonep);
            while (AstNode* const stmtp = clonep->stmtsp())
                m_statements.push_back(VN_AS(stmtp->unlinkFrBack(), NodeStmt));
            clonep->deleteTree();
            V3Stats::addStatSum("RepCut native source, clocked procedures", 1);
        }
    }

public:
    NativeProgram(const NativeProgramContext& context, NativeProgramOutput& output)
        : m_scope{context.m_scope}
        , m_graph{context.m_graph}
        , m_bindings{context.m_bindings}
        , m_sequence{context.m_sequence}
        , m_tag{context.m_tag}
        , m_storageGroup{context.m_storageGroup}
        , m_candidates{output.m_candidates}
        , m_effectArguments{output.m_effectArguments}
        , m_statements{output.m_statements}
        , m_effectPendingp{context.m_effectPendingp}
        , m_lowerGraph{context.m_lowerGraph}
        , m_sharedInputs{context.m_sharedInputs} {}

    NativeLowering apply(size_t limit, const std::map<size_t, AstVarScope*>& captures) {
        if (!prepare(limit)) {
            V3Stats::addStatSum("RepCut native source, graph fallback programs", 1);
            return NativeLowering::GRAPH;
        }
        if (v3Global.opt.repcutDumpGraph()) {
            m_costReportp.reset(V3File::new_ofstream(v3Global.opt.makeDir() + "/"
                                                     + v3Global.opt.prefix() + m_tag
                                                     + ".source-costs.tsv"));
            if (m_costReportp->fail()) v3fatal("Cannot write RepCut source cost report");
            *m_costReportp << "kind\tid\tbody_nodes\tinstruction_estimate\tconditionals"
                              "\tarray_selects\n";
        }
        for (const auto& pair : captures)
            m_remap.emplace(m_bindings.m_storageps[pair.first], pair.second);
        if (m_effectPendingp) {
            m_statements.push_back(
                new AstAssign{m_scope.fileline(), ref(m_effectPendingp, VAccess::WRITE),
                              new AstConst{m_scope.fileline(), AstConst::BitFalse{}}});
        }
        drivers();
        if (!m_graphSinks.empty()) {
            const std::vector<size_t> sequence = closure(m_graphSinks, m_values);
            const std::vector<AstNodeStmt*> graph
                = m_lowerGraph(sequence, NativeGraphBoundary{m_values, {}});
            m_statements.insert(m_statements.end(), graph.begin(), graph.end());
            V3Stats::addStatSum("RepCut native source, graph clocked vertices", sequence.size());
        }
        writeGroups();
        candidates();
        clocked();
        V3Stats::addStatSum("RepCut native source, programs", 1);
        V3Stats::addStatSum("RepCut native source, temporaries", m_temporaries);
        if (!m_graphSinks.empty() || !m_graphDrivers.empty()) {
            V3Stats::addStatSum("RepCut native source, hybrid programs", 1);
            return NativeLowering::HYBRID;
        }
        return NativeLowering::SOURCE;
    }
};

// Share only complete native combinational assignments. The graph still owns
// partitioning and control dependencies; this is a lowering view after the cut.
// Every source input that has a graph driver must itself be shared in a superset
// of the consumer's domains. Thus each group is pure and can precede all domain
// bodies in the same fixed worker, without publishing state or capturing effects.
class NativeSharedPrograms final {
    struct DomainOrder final {
        bool operator()(const std::vector<size_t>& lhs, const std::vector<size_t>& rhs) const {
            return lhs.size() != rhs.size() ? lhs.size() > rhs.size() : lhs < rhs;
        }
    };
    using Membership = std::map<size_t, std::vector<size_t>>;
    using SharedCandidates = std::map<size_t, const AstNodeAssign*>;
    // Extraction adds guarded calls and private storage traffic. Require enough
    // shared work in a fixed partition to amortize that overhead. Keep a
    // worthwhile partition's eligible computations together: pruning individual
    // groups can undo reuse and change the layout of its larger native bodies.
    // Count one execution, not memberships; clocks need not coactivate.
    static constexpr uint64_t MIN_PARTITION_COST
        = 4ULL * (AstNode::INSTR_COUNT_CALL + AstNode::INSTR_COUNT_BRANCH);
    const Graph& m_graph;
    const Bindings& m_bindings;
    const size_t m_limit;
    std::map<const AstVarScope*, size_t> m_driverIds;
    std::vector<size_t> m_order;
    std::vector<size_t> m_visited;
    size_t m_generation = 0;

    Membership membership(const Partition& partition) {
        std::map<size_t, std::vector<size_t>> roots;
        for (const size_t id : partition.m_next) {
            const Vertex& vertex = *m_graph.m_vertexps[id];
            if (vertex.isSink()) roots[vertex.m_domain].push_back(id);
        }
        Membership result;
        for (const auto& domain : roots) {
            ++m_generation;
            std::vector<size_t> pending = domain.second;
            while (!pending.empty()) {
                const size_t id = pending.back();
                pending.pop_back();
                if (m_visited[id] == m_generation) continue;
                m_visited[id] = m_generation;
                const Vertex& vertex = *m_graph.m_vertexps[id];
                if (vertex.m_kind == Op::VAR) result[id].push_back(domain.first);
                vertex.foreachPredecessor([&](const Vertex& pred, DependencyKind) {
                    pending.push_back(pred.m_id);
                    return false;
                });
            }
        }
        return result;
    }
    SharedCandidates candidates(const Membership& members, uint64_t& cost) const {
        SharedCandidates result;
        for (const size_t id : m_order) {
            const auto member = members.find(id);
            if (member == members.end() || member->second.size() < 2) continue;
            const Vertex& vertex = *m_graph.m_vertexps[id];
            const auto source = m_bindings.m_combAssignments.find(vertex.m_storage);
            if (source == m_bindings.m_combAssignments.end() || vertex.m_region != NO_ID) continue;
            const AstNodeAssign* const assignp = source->second;
            const AstVarRef* const targetp = VN_CAST(assignp->lhsp(), VarRef);
            if (!targetp || targetp->varScopep() != m_bindings.m_storageps[vertex.m_storage]
                || static_cast<size_t>(assignp->nodeCount()) > m_limit)
                continue;
            if (assignp->rhsp()->exists([](AstNodeExpr* nodep) {
                    return !nodep->isPure() || VN_IS(nodep, CCall) || VN_IS(nodep, CMethodHard);
                }))
                continue;
            bool available = true;
            assignp->rhsp()->foreach([&](const AstVarRef* refp) {
                if (!refp->access().isReadOnly()) available = false;
                const auto driver = m_driverIds.find(refp->varScopep());
                if (driver == m_driverIds.end()) return;
                const auto input = members.find(driver->second);
                if (!result.count(driver->second) || input == members.end()
                    || !std::includes(input->second.begin(), input->second.end(),
                                      member->second.begin(), member->second.end()))
                    available = false;
            });
            if (!available) continue;
            result.emplace(id, assignp);
            cost += V3InstrCount::count(const_cast<AstNodeAssign*>(assignp), false);
        }
        return result;
    }
    NativeSharedPartition makePartition(const Partition& partition, size_t part) {
        NativeSharedPartition result;
        const Membership members = membership(partition);
        uint64_t cost = 0;
        const SharedCandidates available = candidates(members, cost);
        if (cost < MIN_PARTITION_COST) {
            V3Stats::addStatSum("RepCut shared domains, cheap drivers retained locally",
                                available.size());
            V3Stats::addStatSum("RepCut shared domains, partitions below cost floor",
                                !available.empty());
            return result;
        }
        V3Stats::addStatSum("RepCut shared domains, partitions above cost floor", 1);
        Remap remap;
        std::map<std::vector<size_t>, std::vector<AstNodeStmt*>, DomainOrder> groups;
        for (const size_t id : m_order) {
            const auto found = available.find(id);
            if (found == available.end()) continue;
            const AstNodeAssign* const assignp = found->second;
            const AstVarRef* const targetp = VN_AS(assignp->lhsp(), VarRef);
            const std::vector<size_t>& domains = members.at(id);
            AstVarScope* const valuep = v3Global.rootp()->topScopep()->createTemp(
                "__Vrepcut_shared_p" + cvtToStr(part) + "_v" + cvtToStr(id), targetp->dtypep());
            valuep->varp()->varType(VVarType::BLOCKTEMP);
            valuep->varp()->noReset(true);
            valuep->varp()->trace(false);
            valuep->varp()->isInternal(true);
            valuep->varp()->repcutStorageGroup(storageGroup(part, StorageRole::PRIVATE_EVAL));
            result.m_values.emplace(id, valuep);
            remap.emplace(targetp->varScopep(), valuep);
            AstNodeAssign* const clonep = const_cast<AstNodeAssign*>(assignp)->cloneTree(false);
            SourceRewrite{clonep, remap, {}, {}, {}, nullptr};
            groups[domains].push_back(clonep);
            V3Stats::addStatSum("RepCut shared domains, source drivers", 1);
            V3Stats::addStatSum("RepCut shared domains, extra driver memberships",
                                domains.size() - 1);
        }
        // A producer's domain set contains every consumer domain. Sorting by
        // decreasing cardinality orders distinct groups; native topological
        // order above orders assignments within each identical set.
        for (auto& group : groups)
            result.m_groups.push_back({group.first, std::move(group.second)});
        V3Stats::addStatSum("RepCut shared domains, groups", result.m_groups.size());
        return result;
    }

public:
    // Need () to select the size/value constructor, not a two-element list.
    NativeSharedPrograms(const Graph& graph, const Bindings& bindings, size_t limit)
        : m_graph{graph}
        , m_bindings{bindings}
        , m_limit{limit}
        , m_visited(graph.m_vertexps.size(), 0) {
        for (const size_t id : graph.topologicalOrder()) {
            const Vertex& vertex = *graph.m_vertexps[id];
            if (vertex.m_kind != Op::VAR) continue;
            m_order.push_back(id);
            m_driverIds.emplace(bindings.m_storageps[vertex.m_storage], id);
        }
    }
    std::vector<NativeSharedPartition> apply(const Plan& plan) {
        std::vector<NativeSharedPartition> result;
        for (size_t part = 0; part < plan.m_partitions.size(); ++part)
            result.push_back(makePartition(plan.m_partitions[part], part));
        return result;
    }
};

}  // namespace

std::vector<NativeSharedPartition> nativeSharedPrograms(const Graph& graph, const Plan& plan,
                                                        const Bindings& bindings,
                                                        size_t statementLimit) {
    return NativeSharedPrograms{graph, bindings, statementLimit}.apply(plan);
}

NativeLowering nativeProgram(const NativeProgramContext& context, NativeProgramOutput& output) {
    return NativeProgram{context, output}.apply(context.m_statementLimit, context.m_captures);
}

}  // namespace V3RepCut
