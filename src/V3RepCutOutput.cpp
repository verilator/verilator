// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Place terminal output words after local publication
//
// Code available from: https://verilator.org
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026-2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//*************************************************************************
// After wide lowering, collect every fast access to each primary output word.
// Move an ordered chain of unconditional assignments only when the output has
// no other readers, every source is private state published by one certified
// worker, and the native clock conditions match. Cross-owner words and unknown
// access patterns stay on the caller. Bounded helpers finish before the existing
// worker completion; no new dispatch, synchronization or state copy is needed.
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3RepCut.h"
#include "V3Stats.h"

#include <map>
#include <set>
#include <vector>

VL_DEFINE_DEBUG_FUNCTIONS;

namespace {
using Word = std::pair<AstVar*, int>;

bool outputWord(const AstWordSel* nodep, Word& word) {
    AstVarRef* const refp = VN_CAST(nodep->fromp(), VarRef);
    const AstConst* const indexp = VN_CAST(nodep->bitp(), Const);
    if (!refp || !indexp || indexp->num().isFourState() || refp->classOrPackagep()
        || !(refp->selfPointer() == VSelfPointerText{VSelfPointerText::This()}))
        return false;
    AstVar* const varp = refp->varp();
    if (!varp->isPrimaryIO() || varp->direction() != VDirection::OUTPUT || !varp->isWide()
        || !varp->dtypep()->skipRefp()->isIntegralOrPacked() || varp->isSc()
        || varp->isSigUserRdPublic() || varp->isSigUserRWPublic())
        return false;
    const int index = indexp->toSInt();
    if (index < 0 || index >= varp->widthWords()) return false;
    word = {varp, index};
    return true;
}

struct Access final {
    AstVarRef* m_refp;  // Variable reference describing this access
    AstCFunc* m_funcp;  // Generated function containing the access
    AstAssign* m_assignp;  // Assignment containing the access, if any
    AstWordSel* m_wordp;  // Word selection enclosing the variable reference, if any
};
struct Function final {
    AstNodeModule* m_modp = nullptr;  // Module declaring this generated function
    size_t m_calls = 0;  // Number of call sites referencing the function
};

class AccessIndex final : public VNVisitor {
    AstNodeModule* m_modp = nullptr;  // Module currently being indexed
    AstCFunc* m_funcp = nullptr;  // Generated function currently being indexed
    AstAssign* m_assignp = nullptr;  // Assignment currently being indexed
    AstWordSel* m_wordp = nullptr;  // Word selection enclosing the current variable access

    void visit(AstNodeModule* nodep) override {
        VL_RESTORER(m_modp);
        m_modp = nodep;
        iterateChildren(nodep);
    }
    void visit(AstCFunc* nodep) override {
        VL_RESTORER(m_funcp);
        m_funcp = nodep;
        m_functions[nodep].m_modp = m_modp;
        if (nodep->slow()) {
            nodep->foreach([&](AstNodeCCall* callp) { ++m_functions[callp->funcp()].m_calls; });
            return;
        }
        if (nodep->repcutLocalPublish()) ++m_workers;
        for (AstNode* stmtp = nodep->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
            if (AstAssign* const assignp = VN_CAST(stmtp, Assign))
                m_topAssignments.insert(assignp);
        }
        iterateChildren(nodep);
    }
    void visit(AstAssign* nodep) override {
        VL_RESTORER(m_assignp);
        m_assignp = nodep;
        iterateChildren(nodep);
    }
    void visit(AstWordSel* nodep) override {
        {
            VL_RESTORER(m_wordp);
            m_wordp = nodep;
            iterate(nodep->fromp());
        }
        iterate(nodep->bitp());
    }
    void visit(AstVarRef* nodep) override {
        if (m_funcp) m_accesses[nodep->varp()].push_back({nodep, m_funcp, m_assignp, m_wordp});
    }
    void visit(AstNodeCCall* nodep) override {
        ++m_functions[nodep->funcp()].m_calls;
        // These operands describe scheduling dependencies, not physical accesses.
        if (!nodep->funcp()->repcutDependencyArgs()) iterateChildren(nodep);
    }
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    std::map<AstVar*, std::vector<Access>> m_accesses;
    std::map<AstCFunc*, Function> m_functions;
    std::set<AstAssign*> m_topAssignments;  // Assignments directly in non-slow function bodies
    size_t m_workers = 0;  // Number of closed worker wrappers with local publication
    explicit AccessIndex(AstNetlist* netlistp) { iterate(netlistp); }
};

// Each clause means at least one bit in this immutable word mask is set.
// A conjunction of positive clauses handles native union/domain guards without
// depending on generated names. Unknown conditions are deliberately rejected.
struct Clause final {
    AstVar* m_varp;
    int m_word;  // Word index in the trigger vector
    uint64_t m_mask;  // Trigger bits whose disjunction satisfies this clause
};
using Guard = std::vector<Clause>;

bool clause(AstNodeExpr* nodep, Clause& result) {
    if (const AstNeq* const nep = VN_CAST(nodep, Neq)) {
        const AstConst* const zerop = VN_CAST(nep->lhsp(), Const);
        if (!zerop || !zerop->isZero()) return false;
        nodep = nep->rhsp();
    }
    const AstAnd* const andp = VN_CAST(nodep, And);
    if (!andp) return false;
    const AstConst* const maskp = VN_CAST(andp->lhsp(), Const);
    const AstArraySel* const selp = VN_CAST(andp->rhsp(), ArraySel);
    if (!maskp || maskp->width() > 64 || maskp->num().isFourState() || !selp) return false;
    const AstVarRef* const refp = VN_CAST(selp->fromp(), VarRef);
    const AstConst* const indexp = VN_CAST(selp->bitp(), Const);
    if (!refp || refp->classOrPackagep() || !indexp || indexp->num().isFourState()
        || !(refp->selfPointer() == VSelfPointerText{VSelfPointerText::This()}))
        return false;
    result = {refp->varp(), indexp->toSInt(), maskp->toUQuad()};
    return result.m_mask != 0;
}

bool implies(const Guard& lhs, const Guard& rhs) {
    // Guard depth is capped at 16, bounding this conservative clause comparison.
    for (const Clause& b : rhs) {
        bool found = false;
        for (const Clause& a : lhs) {
            if (a.m_varp == b.m_varp && a.m_word == b.m_word && !(a.m_mask & ~b.m_mask)) {
                found = true;
                break;
            }
        }
        if (!found) return false;
    }
    return true;
}

struct Context final {
    Guard m_guard;  // Conjunction of trigger clauses guarding this context
    AstExecGraph* m_graphp = nullptr;  // Execution graph active in this context
    AstCFunc* m_localp = nullptr;  // Closed local-publication function active in this context
    size_t m_order = 0;  // Relative execution order of this call context
    bool m_valid = true;  // Control and call context remains unambiguous for motion
};

class Schedule final {
    const AccessIndex& m_index;  // Indexed variable accesses and generated call sites
    std::map<AstCFunc*, std::vector<AstCFunc*>> m_children;
    std::vector<AstCFunc*> m_repeated;  // Functions reached through multiple call contexts
    size_t m_order = 0;  // Next execution-order index assigned during traversal

    void function(AstCFunc* funcp, Context context) {
        const auto found = m_contexts.emplace(funcp, context);
        if (!found.second) {
            found.first->second.m_valid = false;
            m_repeated.push_back(funcp);
            return;
        }
        Context& stored = found.first->second;
        stored.m_order = ++m_order;
        if (funcp->repcutLocalPublish()) stored.m_localp = funcp;
        // Batched kernels retain unreachable original ExecGraphs until late
        // lowering. Count live worker invocations from NBA traversal instead of
        // rejecting their task functions for those dormant call sites.
        if ((!stored.m_graphp && m_index.m_functions.at(funcp).m_calls != 1) || funcp->slow())
            stored.m_valid = false;
        statements(funcp->stmtsp(), stored, funcp);
    }
    void statements(AstNode* nodep, const Context& context, AstCFunc* parentp) {
        for (; nodep; nodep = nodep->nextp()) {
            if (const AstIf* const ifp = VN_CAST(nodep, If)) {
                Context branch = context;
                Clause condition;
                if (branch.m_guard.size() == 16 || !clause(ifp->condp(), condition))
                    branch.m_valid = false;
                else
                    branch.m_guard.push_back(condition);
                statements(ifp->thensp(), branch, parentp);
                if (ifp->elsesp()) {
                    branch.m_valid = false;
                    statements(ifp->elsesp(), branch, parentp);
                }
            } else if (AstExecGraph* const graphp = VN_CAST(nodep, ExecGraph)) {
                Context worker = context;
                if (worker.m_graphp) worker.m_valid = false;
                worker.m_graphp = graphp;
                statements(graphp->callsp(), worker, parentp);
            } else if (const AstStmtExpr* const stmtp = VN_CAST(nodep, StmtExpr)) {
                if (const AstCCall* const callp = VN_CAST(stmtp->exprp(), CCall)) {
                    Context callee = context;
                    if (!(callp->selfPointer() == VSelfPointerText{VSelfPointerText::This()}))
                        callee.m_valid = false;
                    if (callp->argsp() && !callp->funcp()->repcutDependencyArgs())
                        callee.m_valid = false;
                    m_children[parentp].push_back(callp->funcp());
                    function(callp->funcp(), callee);
                }
            }
        }
    }

public:
    std::map<AstCFunc*, Context> m_contexts;
    Schedule(AstCFunc* rootp, const AccessIndex& index)
        : m_index{index} {
        function(rootp, {});
        std::set<AstCFunc*> invalid;
        while (!m_repeated.empty()) {
            AstCFunc* const funcp = m_repeated.back();
            m_repeated.pop_back();
            if (!invalid.insert(funcp).second) continue;
            m_contexts.at(funcp).m_valid = false;
            const auto it = m_children.find(funcp);
            if (it != m_children.end())
                m_repeated.insert(m_repeated.end(), it->second.begin(), it->second.end());
        }
    }
};

class Sources final : public VNVisitorConst {
    const Word& m_target;  // Output word whose self-reference is permitted
    const std::map<AstVar*, AstCFunc*>& m_owners;

    void visit(AstWordSel* nodep) override {
        Word word;
        if (outputWord(nodep, word)) {
            if (word != m_target) m_safe = false;
            return;
        }
        iterateChildrenConst(nodep);
    }
    void visit(AstVarRef* nodep) override {
        const auto found = m_owners.find(nodep->varp());
        if (nodep->classOrPackagep() || !nodep->access().isReadOnly() || found == m_owners.end()
            || !(nodep->selfPointer() == VSelfPointerText{VSelfPointerText::This()})) {
            m_safe = false;
            return;
        }
        if (m_ownerp && m_ownerp != found->second) m_safe = false;
        m_ownerp = found->second;
    }
    void visit(AstNodeExpr* nodep) override {
        if (!nodep->isPure() || VN_IS(nodep, CExpr) || VN_IS(nodep, NodeCCall)
            || VN_IS(nodep, CMethodHard))
            m_safe = false;
        iterateChildrenConst(nodep);
    }
    void visit(AstNode* nodep) override {
        m_safe = false;
        iterateChildrenConst(nodep);
    }

public:
    AstCFunc* m_ownerp = nullptr;  // Single worker owning every candidate source
    bool m_safe = true;  // All source reads are pure and belong to one owner
    Sources(const Word& target, const std::map<AstVar*, AstCFunc*>& owners)
        : m_target{target}
        , m_owners{owners} {}
    void inspect(AstNodeExpr* nodep) { iterateConst(nodep); }
};

class OutputPlacement final {
    struct Group final {
        Word m_word;  // Output word considered for worker publication
        AstCFunc* m_funcp = nullptr;  // Native function containing the grouped assignments
        std::vector<AstAssign*> m_assignments;  // Ordered assignments to this output word
        bool m_safe = true;  // Group satisfies the requirements for publication motion
    };
    AstNetlist* const m_netlistp;
    AccessIndex m_index;
    Schedule m_schedule;
    std::map<AstVar*, AstCFunc*> m_owners;
    std::set<AstVar*> m_nbaWrites;
    std::map<Word, Group> m_groups;
    const size_t m_limit
        = std::max(32, v3Global.opt.outputSplitCFuncs() ? v3Global.opt.outputSplitCFuncs()
                                                        : V3Options::REPCUT_DEFAULT_CFUNCS);
    size_t m_functions = 0;
    size_t m_words = 0;
    size_t m_assignments = 0;

    void owners() {
        for (const auto& entry : m_index.m_accesses) {
            AstVar* const varp = entry.first;
            const uint32_t group = varp->repcutStorageGroup();
            AstCFunc* ownerp = nullptr;
            bool safe = group
                        && (group - 1) % V3RepCut::STORAGE_ROLES
                               == static_cast<uint32_t>(V3RepCut::StorageRole::DIRECT_STATE);
            for (const Access& access : entry.second) {
                if (!access.m_refp->access().isWriteOrRW()) continue;
                const auto it = m_schedule.m_contexts.find(access.m_funcp);
                if (it != m_schedule.m_contexts.end()) m_nbaWrites.insert(varp);
                if (it == m_schedule.m_contexts.end() || !it->second.m_valid
                    || !it->second.m_localp
                    || !(access.m_refp->selfPointer()
                         == VSelfPointerText{VSelfPointerText::This()})) {
                    safe = false;
                    continue;
                }
                if (ownerp && ownerp != it->second.m_localp) safe = false;
                ownerp = it->second.m_localp;
            }
            if (safe && ownerp) m_owners.emplace(varp, ownerp);
        }
    }
    void groups() {
        for (const auto& entry : m_index.m_accesses) {
            const AstVar* const varp = entry.first;
            if (!varp->isPrimaryIO() || varp->direction() != VDirection::OUTPUT || !varp->isWide())
                continue;
            bool terminal = true;
            std::map<Word, Group> words;
            for (const Access& access : entry.second) {
                Word word;
                Word target;
                const AstWordSel* const lhsp
                    = access.m_assignp ? VN_CAST(access.m_assignp->lhsp(), WordSel) : nullptr;
                if (!access.m_wordp || !outputWord(access.m_wordp, word) || !lhsp
                    || !outputWord(lhsp, target) || target != word) {
                    terminal = false;
                    break;
                }
                Group& group = words[word];
                group.m_word = word;
                if (group.m_funcp && group.m_funcp != access.m_funcp) group.m_safe = false;
                group.m_funcp = access.m_funcp;
                if (!m_index.m_topAssignments.count(access.m_assignp)) group.m_safe = false;
                if (access.m_refp->access().isWriteOnly())
                    group.m_assignments.push_back(access.m_assignp);
                else if (!access.m_refp->access().isReadOnly())
                    group.m_safe = false;
            }
            if (terminal) m_groups.insert(words.begin(), words.end());
        }
    }
    bool sameClock(const Context& output, const Context& worker) const {
        if (!output.m_valid || !worker.m_valid || output.m_graphp || !worker.m_graphp
            || output.m_order <= worker.m_order || output.m_guard.empty()
            || !implies(output.m_guard, worker.m_guard)
            || !implies(worker.m_guard, output.m_guard))
            return false;
        for (const Clause& condition : output.m_guard) {
            if (m_nbaWrites.count(condition.m_varp)) return false;
        }
        for (const Clause& condition : worker.m_guard) {
            if (m_nbaWrites.count(condition.m_varp)) return false;
        }
        return true;
    }
    AstCFunc* owner(const Group& group) const {
        if (!group.m_safe || group.m_assignments.empty()) return nullptr;
        const auto output = m_schedule.m_contexts.find(group.m_funcp);
        if (output == m_schedule.m_contexts.end()) return nullptr;
        Sources sources{group.m_word, m_owners};
        for (const AstAssign* const assignp : group.m_assignments) {
            if (static_cast<size_t>(assignp->nodeCount()) > m_limit) return nullptr;
            sources.inspect(assignp->rhsp());
        }
        if (!sources.m_safe || !sources.m_ownerp) return nullptr;
        const Context& worker = m_schedule.m_contexts.at(sources.m_ownerp);
        if (!sameClock(output->second, worker)
            || m_index.m_functions.at(group.m_funcp).m_modp
                   != m_index.m_functions.at(sources.m_ownerp).m_modp)
            return nullptr;
        return sources.m_ownerp;
    }
    static AstNodeStmt* call(AstCFunc* funcp) {
        AstCCall* const callp = new AstCCall{funcp->fileline(), funcp};
        callp->dtypeSetVoid();
        callp->selfPointer(VSelfPointerText{VSelfPointerText::This()});
        return callp->makeStmt();
    }
    // The access index uses mutable AST pointers as keys, including for read-only lookup.
    // cppcheck-suppress constParameterPointer
    AstCFunc* function(AstCFunc* ownerp, const std::vector<AstNodeStmt*>& statements) {
        AstCFunc* const funcp
            = new AstCFunc{ownerp->fileline(), "__Vrepcut_output_words" + cvtToStr(m_functions++),
                           ownerp->scopep()};
        funcp->isLoose(true);
        funcp->isStatic(false);
        funcp->isConst(false);
        funcp->dontCombine(true);
        funcp->noInline(true);
        funcp->isRepCut(true);
        for (AstNodeStmt* const stmtp : statements) funcp->addStmtsp(stmtp);
        m_index.m_functions.at(ownerp).m_modp->addStmtsp(funcp);
        return funcp;
    }
    AstCFunc* chunks(AstCFunc* ownerp, const std::vector<AstNodeStmt*>& statements) {
        std::vector<AstNodeStmt*> chunk;
        std::vector<AstNodeStmt*> calls;
        size_t size = 0;
        for (AstNodeStmt* const stmtp : statements) {
            const size_t nodes = stmtp->nodeCount();
            if (size + nodes > m_limit) {
                calls.push_back(call(function(ownerp, chunk)));
                chunk.clear();
                size = 0;
            }
            chunk.push_back(stmtp);
            size += nodes;
        }
        if (calls.empty()) return function(ownerp, chunk);
        if (!chunk.empty()) calls.push_back(call(function(ownerp, chunk)));
        return chunks(ownerp, calls);
    }
    void move() {
        std::map<AstAssign*, AstCFunc*> selected;
        for (const auto& entry : m_groups) {
            const Group& group = entry.second;
            AstCFunc* const ownerp = owner(group);
            if (!ownerp) continue;
            ++m_words;
            for (AstAssign* const assignp : group.m_assignments) selected.emplace(assignp, ownerp);
        }
        // Iterate actual AST order, never pointer-map order, for reproducible
        // helpers and exact ordering of partial assignments to the same word.
        std::map<AstCFunc*, std::vector<AstNodeStmt*>> bodies;
        std::vector<AstCFunc*> orderedOwners;
        m_netlistp->foreach([&](AstAssign* assignp) {
            const auto it = selected.find(assignp);
            if (it == selected.end()) return;
            const auto dest = bodies.emplace(it->second, std::vector<AstNodeStmt*>{});
            if (dest.second) orderedOwners.push_back(it->second);
            dest.first->second.push_back(assignp);
        });
        for (AstCFunc* const ownerp : orderedOwners) {
            for (AstNodeStmt* const stmtp : bodies.at(ownerp)) {
                stmtp->unlinkFrBack();
                ++m_assignments;
            }
            ownerp->addStmtsp(call(chunks(ownerp, bodies.at(ownerp))));
        }
    }

public:
    explicit OutputPlacement(AstNetlist* netlistp)
        : m_netlistp{netlistp}
        , m_index{netlistp}
        , m_schedule{netlistp->evalFuncp(VEval::NBA), m_index} {
        if (m_index.m_workers) {
            owners();
            groups();
            move();
        }
        V3Stats::addStat("RepCut native output, moved words", m_words);
        V3Stats::addStat("RepCut native output, moved assignments", m_assignments);
        V3Stats::addStat("RepCut native output, bounded functions", m_functions);
        V3Stats::addStat("RepCut native output, certified workers", m_index.m_workers);
        V3Stats::addStat("RepCut native output, private sources", m_owners.size());
        V3Stats::addStat("RepCut native output, terminal words", m_groups.size());
    }
};
}  // namespace

void V3RepCut::placeNativeOutputWords(AstNetlist* netlistp) {
    if (!netlistp->evalFuncp(VEval::NBA)) return;
    bool workers = false;
    bool wideOutputs = false;
    // Avoid indexing expanded bodies for designs without an eligible worker or
    // wide primary output. Functions and fields have already been descoped.
    for (const AstNodeModule* modp = netlistp->modulesp(); modp;
         modp = VN_AS(modp->nextp(), NodeModule)) {
        for (AstNode* nodep = modp->stmtsp(); nodep; nodep = nodep->nextp()) {
            if (const AstCFunc* const funcp = VN_CAST(nodep, CFunc))
                workers |= funcp->repcutLocalPublish();
            if (const AstVar* const varp = VN_CAST(nodep, Var))
                wideOutputs |= varp->isPrimaryIO() && varp->direction() == VDirection::OUTPUT
                               && varp->isWide();
        }
    }
    if (!workers || !wideOutputs) {
        V3Stats::addStat("RepCut native output, moved words", 0);
        V3Stats::addStat("RepCut native output, moved assignments", 0);
        V3Stats::addStat("RepCut native output, bounded functions", 0);
        V3Stats::addStat("RepCut native output, certified workers", 0);
        V3Stats::addStat("RepCut native output, private sources", 0);
        V3Stats::addStat("RepCut native output, terminal words", 0);
        return;
    }
    OutputPlacement{netlistp};
    V3Global::dumpCheckGlobalTree("repcut_output", 0, dumpTreeEitherLevel() >= 3);
}
