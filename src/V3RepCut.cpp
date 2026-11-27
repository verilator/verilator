// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Extract state-aware RepCut dependency graphs
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
// Extraction follows DFG/Gate optimization and precedes NBA lowering. Convert packed pure
// expressions to individual operation vertices and procedural if/else to
// guarded regions and JOIN values. Blocking combinational assignments use a
// local value environment; clocked NBAs update a separate next-state environment.
// Later reads still see old state. Missing clocked assignments retain old state. Connect wires
// across procedures after conversion, but never connect next state to old state.
//
// This is deliberately not a runtime scheduler or a complete simulation IR.
// Report unsupported constructs and cycles without dropping dependency edges
// or merging nodes. Only a complete acyclic graph gets the .graph suffix
// accepted by the RepCut partitioner; other exports use .partial. Retain event
// scheduling, unsupported procedures, and combinational convergence in the
// original AST, with explicit storage boundaries in the kernel graph.
// Node weights are provisional unit operation costs, not timing predictions.
// Initialization and finalization remain outside this per-edge graph.
// Literal single-writer initial assignments become constant sources. V3Unknown
// X replacement temporaries become explicit INIT sources whose values must come
// from ordinary initialization. Outputs are inventoried even if startup-only.
// Memory reads use a shared old-memory source. Each supported NBA memory write
// is a separate sink with enable/address/data operands and source-order priority.
// Partial writes also retain their bit offset and width; no write feeds a read
// and no whole-memory next-state value is constructed. Preserve V3Unknown's
// logical bounds checks and safe physical memory indices.
//
// The graph and partition plan use graph-local node IDs. Bindings
// provide the temporary connection back to storage, expressions and procedures
// during this invocation. Export, validation and emission therefore finish at
// the same pass boundary, before later optimization can replace those AST nodes.
// Diagnostic names are never used to recover bindings. Unsupported native
// procedures stay scheduled by Verilator, and their results enter the graph at
// explicit storage boundaries; a complete kernel graph is not a claim that the
// entire design executes inside RepCut workers.
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3RepCut.h"

#include "V3RepCutEmit.h"
#include "V3RepCutGraph.h"
#include "V3RepCutPlan.h"
#include "V3Stats.h"
#include "V3String.h"

#include <algorithm>
#include <cstdio>
#include <map>
#include <memory>
#include <set>
#include <unordered_map>
#include <vector>

VL_DEFINE_DEBUG_FUNCTIONS;

namespace {

// V3Split may leave a comment in its own copy of a guarded process. Such a
// process does not read the guard at runtime and must not make a callback's
// otherwise private blocking variables appear externally observable.
bool emptyStatements(AstNode* nodep) {
    for (; nodep; nodep = nodep->nextp()) {
        if (VN_IS(nodep, Comment)) continue;
        if (const AstIf* const ifp = VN_CAST(nodep, If)) {
            if (!ifp->condp()->exists([](AstNode* childp) { return !childp->isPure(); })
                && emptyStatements(ifp->thensp()) && emptyStatements(ifp->elsesp()))
                continue;
        }
        if (const AstBegin* const beginp = VN_CAST(nodep, Begin)) {
            if (emptyStatements(beginp->stmtsp())) continue;
        }
        return false;
    }
    return true;
}

// Prove only unconditional, single-driver, one-bit copies to be clock aliases.
// Collect all writes before resolving any clock, including writes in other
// procedures and initialization. Gating, inversion, state, and alias cycles do
// not qualify. Also recognize literal assignments moved to initial blocks by
// V3Const, provided there is exactly one unconditional writer in the design.
// This is source normalization, not a scheduling transformation.
class RepCutSourceAnalysis final : public VNVisitorConst {
    using ElementDrivers = std::map<uint32_t, const AstNodeAssign*>;
    std::map<const AstVarScope*, ElementDrivers> m_elementDrivers;
    std::map<const AstVarScope*, size_t> m_writes;
    std::map<const AstVarScope*, const AstVarScope*> m_copies;
    std::map<const AstVarScope*, const AstVarScope*> m_roots;
    std::map<const AstVarScope*, const AstConst*> m_constants;
    std::set<const AstVarScope*> m_initialWrites;
    std::set<const AstVarScope*> m_recurringWrites;
    bool m_initial = false;  // Visiting an initial assignment rather than recurring logic
    const AstAlways* m_procedurep = nullptr;  // Current always procedure for access ownership
    std::map<const AstVarScope*, const AstAlways*> m_accessProcedures;
    std::set<const AstVarScope*> m_sharedAccess;
    std::map<const AstVarScope*, const AstAlways*> m_runtimeAccess;
    std::set<const AstVarScope*> m_sharedRuntimeAccess;
    std::map<const AstVarScope*, const AstAlways*> m_writingProcedures;
    std::set<const AstVarScope*> m_sharedWrites;
    const AstActive* m_activep = nullptr;  // Active region supplying the current sensitivity

    void visit(AstActive* nodep) override {
        VL_RESTORER(m_activep);
        m_activep = nodep;
        iterateAndNextConstNull(nodep->procsp());
    }
    void visit(AstAlways* nodep) override {
        if (emptyStatements(nodep->stmtsp())) return;
        VL_RESTORER(m_procedurep);
        m_procedurep = nodep;
        if (m_activep && m_activep->hasCombo()) {
            const AstNodeAssign* const ap = VN_CAST(nodep->stmtsp(), NodeAssign);
            if (ap && !ap->nextp() && !ap->timingControlp()
                && (VN_IS(ap, Assign) || VN_IS(ap, AssignW))) {
                const AstVarRef* const lp = VN_CAST(ap->lhsp(), VarRef);
                const AstVarRef* const rp = VN_CAST(ap->rhsp(), VarRef);
                if (lp && rp && lp->width() == 1 && rp->width() == 1) {
                    m_copies.emplace(lp->varScopep(), rp->varScopep());
                }
                if (const AstArraySel* const selp = VN_CAST(ap->lhsp(), ArraySel)) {
                    const AstVarRef* const refp = VN_CAST(selp->fromp(), VarRef);
                    const AstConst* const indexp = VN_CAST(selp->bitp(), Const);
                    if (refp && indexp && indexp->width() <= 32 && !indexp->num().isFourState())
                        m_elementDrivers[refp->varScopep()].emplace(indexp->toUInt(), ap);
                }
            }
        }
        iterateChildrenConst(nodep);
    }
    void visit(AstVarRef* nodep) override {
        if (!m_initial) {
            const auto access = m_runtimeAccess.emplace(nodep->varScopep(), m_procedurep);
            if (!access.second && access.first->second != m_procedurep)
                m_sharedRuntimeAccess.insert(nodep->varScopep());
        }
        const auto access = m_accessProcedures.emplace(nodep->varScopep(), m_procedurep);
        if (!access.second && access.first->second != m_procedurep)
            m_sharedAccess.insert(nodep->varScopep());
        if (nodep->access().isWriteOrRW()) {
            ++m_writes[nodep->varScopep()];
            (m_initial ? m_initialWrites : m_recurringWrites).insert(nodep->varScopep());
            if (!m_initial) {
                const auto writer = m_writingProcedures.emplace(nodep->varScopep(), m_procedurep);
                if (!writer.second && writer.first->second != m_procedurep)
                    m_sharedWrites.insert(nodep->varScopep());
            }
        }
    }
    void visit(AstInitial* nodep) override {
        VL_RESTORER(m_initial);
        m_initial = true;
        const AstAssign* const ap = VN_CAST(nodep->stmtsp(), Assign);
        if (ap && !ap->nextp() && !ap->timingControlp()) {
            const AstVarRef* const refp = VN_CAST(ap->lhsp(), VarRef);
            const AstConst* const valuep = VN_CAST(ap->rhsp(), Const);
            if (refp && valuep) m_constants.emplace(refp->varScopep(), valuep);
        }
        iterateChildrenConst(nodep);
    }
    void visit(AstInitialStatic* nodep) override {
        VL_RESTORER(m_initial);
        m_initial = true;
        iterateChildrenConst(nodep);
    }
    void visit(AstNode* nodep) override { iterateChildrenConst(nodep); }

public:
    explicit RepCutSourceAnalysis(AstNetlist* netlistp) { iterateConst(netlistp); }

    bool initializedOnly(const AstVarScope* vscp) const {
        // Declaration initializers include constant lookup arrays introduced by
        // V3Table. Never accept a rejected recurring writer as a ROM.
        return !m_recurringWrites.count(vscp)
               && (m_initialWrites.count(vscp) || vscp->varp()->valuep());
    }

    bool localTemporary(const AstVarScope* vscp, const AstAlways* procedurep) const {
        const auto access = m_accessProcedures.find(vscp);
        return vscp->varp()->varType() == VVarType::BLOCKTEMP && !m_sharedAccess.count(vscp)
               && access != m_accessProcedures.end() && access->second == procedurep;
    }

    bool soleWriter(const AstVarScope* vscp, const AstAlways* procedurep) const {
        const auto writer = m_writingProcedures.find(vscp);
        return !m_sharedWrites.count(vscp) && writer != m_writingProcedures.end()
               && writer->second == procedurep;
    }

    bool privateTo(const AstVarScope* vscp, const AstAlways* procedurep) const {
        const auto access = m_accessProcedures.find(vscp);
        return !vscp->varp()->isPrimaryIO() && !m_sharedAccess.count(vscp)
               && access != m_accessProcedures.end() && access->second == procedurep;
    }

    bool privateAtRuntime(const AstVarScope* vscp, const AstAlways* procedurep) const {
        const auto access = m_runtimeAccess.find(vscp);
        return !vscp->varp()->isPrimaryIO() && !vscp->varp()->isSigUserRdPublic()
               && !vscp->varp()->isSigUserRWPublic() && !m_sharedRuntimeAccess.count(vscp)
               && access != m_runtimeAccess.end() && access->second == procedurep;
    }

    const ElementDrivers* elementDrivers(const AstVarScope* vscp) const {
        const AstUnpackArrayDType* const dtypep
            = VN_CAST(vscp->dtypep()->skipRefp(), UnpackArrayDType);
        if (!dtypep || !dtypep->subDTypep()->skipRefp()->isIntegralOrPacked()
            || vscp->varp()->isSigUserRWPublic())
            return nullptr;
        const auto found = m_elementDrivers.find(vscp);
        const auto writes = m_writes.find(vscp);
        if (found == m_elementDrivers.end() || writes == m_writes.end()
            || found->second.size() != static_cast<size_t>(dtypep->elementsConst())
            || writes->second != found->second.size()
            || found->second.rbegin()->first >= static_cast<uint32_t>(dtypep->elementsConst()))
            return nullptr;
        // Every physical element has one unconditional continuous driver; an
        // initialization, whole-array write or second writer invalidates this.
        return &found->second;
    }

    const AstConst* constantValue(const AstVarScope* vscp) const {
        const auto written = m_writes.find(vscp);
        const auto value = m_constants.find(vscp);
        return written != m_writes.end() && written->second == 1 && value != m_constants.end()
                   ? value->second
                   : nullptr;
    }

    const AstVarScope* resolve(const AstVarScope* vscp) {
        std::vector<const AstVarScope*> path;
        std::set<const AstVarScope*> visited;
        const AstVarScope* rootp = nullptr;
        for (const AstVarScope* currentp = vscp; currentp;) {
            const auto cached = m_roots.find(currentp);
            if (cached != m_roots.end()) {
                rootp = cached->second;
                break;
            }
            if (!visited.insert(currentp).second) break;
            path.push_back(currentp);
            const AstVar* const varp = currentp->varp();
            const auto written = m_writes.find(currentp);
            if (varp->isPrimaryIO() && varp->direction().isInput() && varp->width() == 1
                && written == m_writes.end()) {
                rootp = currentp;
                break;
            }
            // Match the native optimizer's externally observable boundaries.
            // A public alias can be changed independently through VPI/DPI.
            if (varp->isSigPublic() || varp->isSigUserRWPublic() || varp->isSc()
                || varp->sensIfacep() || varp->isVirtIface())
                break;
            if (written == m_writes.end() || written->second != 1) break;
            const auto copy = m_copies.find(currentp);
            if (copy == m_copies.end()) break;
            currentp = copy->second;
        }
        // Cache both proven roots and failures, including cycles. No node merging.
        for (const AstVarScope* const memberp : path) m_roots.emplace(memberp, rootp);
        return rootp;
    }
};

using Op = V3RepCut::Op;
using RepCutVertex = V3RepCut::Vertex;

static const std::map<std::string, Op> s_unary{
    {"COUNTONES", Op::COUNTONES}, {"EXTEND", Op::EXTEND}, {"EXTENDS", Op::EXTENDS},
    {"LOGNOT", Op::LOGNOT},       {"NEGATE", Op::NEGATE}, {"NOT", Op::NOT},
    {"REDAND", Op::REDAND},       {"REDOR", Op::REDOR},   {"REDXOR", Op::REDXOR}};
static const std::map<std::string, Op> s_binary{{"ADD", Op::ADD},
                                                {"AND", Op::AND},
                                                {"CONCAT", Op::CONCAT},
                                                {"DIV", Op::DIV},
                                                {"DIVS", Op::DIVS},
                                                {"EQ", Op::EQ},
                                                {"GT", Op::GT},
                                                {"GTE", Op::GTE},
                                                {"GTES", Op::GTES},
                                                {"GTS", Op::GTS},
                                                {"LOGAND", Op::LOGAND},
                                                {"LOGOR", Op::LOGOR},
                                                {"LT", Op::LT},
                                                {"LTE", Op::LTE},
                                                {"LTES", Op::LTES},
                                                {"LTS", Op::LTS},
                                                {"MODDIV", Op::MODDIV},
                                                {"MODDIVS", Op::MODDIVS},
                                                {"MUL", Op::MUL},
                                                {"MULS", Op::MULS},
                                                {"NEQ", Op::NEQ},
                                                {"OR", Op::OR},
                                                {"REPLICATE", Op::REPLICATE},
                                                {"SHIFTL", Op::SHIFTL},
                                                {"SHIFTR", Op::SHIFTR},
                                                {"SHIFTRS", Op::SHIFTRS},
                                                {"SUB", Op::SUB},
                                                {"XOR", Op::XOR}};

// Retain the ordered imperative program around foreign calls, including
// private arrays and partial writes. Only read-only inputs can be lifted into
// partitions; callbacks requiring scheduler reentry remain entirely native.
class RepCutCallbackCheck final : public VNVisitorConst {
    std::set<const AstVarScope*> m_seen;
    std::map<const AstVarScope*, bool> m_written;
    V3RepCut::Callback& m_binding;  // Callback input captures being validated
    bool m_valid = true;  // Callback remains safe for input capture

    void write(const AstNodeExpr* nodep, bool nba) {
        while (true) {
            if (const AstSel* const selp = VN_CAST(nodep, Sel))
                nodep = selp->fromp();
            else if (const AstArraySel* const selp = VN_CAST(nodep, ArraySel))
                nodep = selp->fromp();
            else
                break;
        }
        const AstVarRef* const refp = VN_CAST(nodep, VarRef);
        if (!refp) {
            m_valid = false;
            return;
        }
        const auto inserted = m_written.emplace(refp->varScopep(), nba);
        if (inserted.second) m_binding.m_outputs.emplace_back(refp->varScopep(), nba);
        if (inserted.first->second != nba) m_valid = false;
    }
    void visit(AstVarRef* nodep) override {
        if (m_seen.insert(nodep->varScopep()).second)
            m_binding.m_inputps.push_back(nodep->varScopep());
    }
    void visit(AstNodeAssign* nodep) override {
        if ((!VN_IS(nodep, Assign) && !VN_IS(nodep, AssignDly)) || nodep->timingControlp())
            m_valid = false;
        write(nodep->lhsp(), VN_IS(nodep, AssignDly));
        iterateChildrenConst(nodep);
    }
    void visit(AstStmtExpr* nodep) override {
        const AstCCall* const callp = VN_CAST(nodep->exprp(), CCall);
        if (!callp || !callp->funcp()->dpiImportWrapper() || callp->funcp()->dpiContext()) {
            m_valid = false;
            return;
        }
        for (const AstNodeExpr* argp = callp->argsp(); argp;
             argp = VN_AS(argp->nextp(), NodeExpr)) {
            if (const AstVarRef* const refp = VN_CAST(argp, VarRef)) {
                if (refp->access().isWriteOrRW()) write(argp, false);
            }
        }
        iterateAndNextConstNull(callp->argsp());
    }
    void visit(AstComment*) override {}
    void visit(AstNode* nodep) override {
        if (AstNodeExpr* const exprp = VN_CAST(nodep, NodeExpr)) {
            // Formatting and time/context reads are allowed in this ordered
            // program, but nested calls or arbitrary foreign text are not.
            if (!exprp->isPure() && !VN_IS(exprp, Time) && !VN_IS(exprp, SFormatF))
                m_valid = false;
            if (const AstCExpr* const cp = VN_CAST(exprp, CExpr)) {
                if (!cp->isGateOptimizable() || cp->exists([](const AstNode* childp) {
                        return !VN_IS(childp, CExpr) && !VN_IS(childp, Text);
                    }))
                    m_valid = false;
            }
        } else if (!VN_IS(nodep, If) && !VN_IS(nodep, Begin) && !VN_IS(nodep, Display)
                   && !VN_IS(nodep, Stop) && !VN_IS(nodep, Finish) && !VN_IS(nodep, Text)) {
            m_valid = false;
        }
        iterateChildrenConst(nodep);
    }

public:
    RepCutCallbackCheck(const AstAlways* procedurep, V3RepCut::Callback& binding)
        : m_binding{binding} {
        iterateAndNextConstNull(procedurep->stmtsp());
    }
    bool valid() const { return m_valid; }
};

class RepCutVisitor final : public VNVisitorConst {
    // Deterministic output when branch merging visits variables from both arms.
    struct VarLess final {
        bool operator()(const AstVarScope* ap, const AstVarScope* bp) const {
            return ap->name() < bp->name();
        }
    };
    using Values = std::map<const AstVarScope*, RepCutVertex*, VarLess>;
    struct MemoryWrite final {
        const AstVarScope* m_memoryp;  // Native memory receiving this write
        RepCutVertex* m_portp;  // Graph sink for the memory write port
        const AstNodeAssign* m_assignp;  // Original assignment defining write priority
    };

    RepCutSourceAnalysis m_sourceAnalysis;
    const bool m_assertionActions;  // Native concurrent assertion/cover action processes
    V3RepCut::Graph& m_result;
    V3RepCut::Bindings* const m_bindingsp;
    std::map<const AstVarScope*, size_t> m_storageIds;
    std::map<const AstSenTree*, size_t> m_nativeDomains;
    VNDeleter m_nativeDomainDeleter;  // Own comparison-only sensitivity snapshots
    std::unordered_map<VNRef<AstSenTree>, size_t> m_nativeDomainKeys;
    size_t m_domainId = V3RepCut::NO_ID;
    Values m_varps;
    Values m_blockingValues;  // Procedure-local temporaries, distinct from deferred NBA values
    const AstAlways* m_procedurep = nullptr;
    size_t m_contexts = 0;
    size_t m_effects = 0;
    size_t m_callbacks = 0;
    Values m_drivers;
    std::set<const AstVarScope*, VarLess> m_state;
    std::map<const AstVarScope*, size_t, VarLess> m_memorySizes;
    std::map<const AstVarScope*, const AstAlways*> m_memoryOwners;
    std::vector<MemoryWrite> m_pendingWrites;
    const AstActive* m_activep = nullptr;
    bool m_clocked = false;
    RepCutVertex* m_guardp = nullptr;
    size_t m_region = V3RepCut::NO_ID;
    std::string m_domain;

    size_t nativeDomain(const AstSenTree* senp) {
        const auto cached = m_nativeDomains.find(senp);
        if (cached != m_nativeDomains.end()) return cached->second;
        // Compare complete event expressions, not per-scope tree identities.
        // Normalize only proven unconditional aliases to primary inputs; gated,
        // generated, opposite-edge, and differently guarded events stay distinct.
        // These private snapshots never rewrite native event scheduling.
        AstSenTree* const keyp = const_cast<AstSenTree*>(senp)->cloneTree(false);
        m_nativeDomainDeleter.pushDeletep(keyp);
        if (v3Global.opt.fGate()) {
            keyp->foreach([&](AstVarRef* refp) {
                if (const AstVarScope* const rootp = m_sourceAnalysis.resolve(refp->varScopep())) {
                    refp->varScopep(const_cast<AstVarScope*>(rootp));
                    refp->varp(rootp->varp());
                }
            });
        }
        const auto entry = m_nativeDomainKeys.emplace(*keyp, m_result.m_domains.size());
        const size_t id = entry.first->second;
        m_nativeDomains.emplace(senp, id);
        if (entry.second) {
            m_result.m_domains.push_back({"native:" + cvtToStr(id)});
            if (m_bindingsp) m_bindingsp->m_domainps.push_back(senp);
        }
        return id;
    }

    void unsupported(const std::string& reason) {
        ++m_result.m_report.m_unsupported[reason];
        ++m_result.m_report.m_failures;
    }

    RepCutVertex* make(Op kind, int width, bool sign,
                       const std::vector<RepCutVertex*>& inputs = {},
                       const std::string& label = "") {
        RepCutVertex* const vp = m_result.make(kind, width, sign, inputs, label);
        // Global storage references and literals retain unconditional availability.
        // A branch use must not move the definition of a shared value into it.
        if (m_region != V3RepCut::NO_ID && kind != Op::VAR && kind != Op::CONSTANT) {
            m_result.setRegion(vp, m_region);
        }
        return vp;
    }
    RepCutVertex* make(Op kind, const AstNode* nodep,
                       const std::vector<RepCutVertex*>& inputs = {},
                       const std::string& label = "") {
        return make(kind, nodep->width(), nodep->isSigned(), inputs, label);
    }
    RepCutVertex* constant(int width, bool sign, uint32_t word, const std::string& label) {
        RepCutVertex* const vp = make(Op::CONSTANT, width, sign, {}, label);
        vp->m_words.resize(VL_WORDS_I(width), 0);
        vp->m_words[0] = word;
        return vp;
    }
    size_t storage(const AstVarScope* vscp) {
        const auto it = m_storageIds.find(vscp);
        if (it != m_storageIds.end()) return it->second;
        const size_t id = m_result.m_storage.size();
        m_storageIds.emplace(vscp, id);
        if (m_bindingsp) m_bindingsp->m_storageps.push_back(const_cast<AstVarScope*>(vscp));
        m_result.m_storage.push_back(
            {scopedName(vscp), vscp->varp()->width(), vscp->varp()->isSigned(), 0});
        return id;
    }

    // Protect identifier components separately; a scope label is not an identifier.
    static std::string scopedName(const AstVarScope* vscp) {
        return vscp->scopep()->nameProtect() + "->" + vscp->varp()->nameProtect();
    }

    RepCutVertex* variable(const AstVarScope* vscp) {
        const auto it = m_varps.find(vscp);
        if (it != m_varps.end()) return it->second;
        RepCutVertex* const vp = make(Op::VAR, vscp->varp(), {}, scopedName(vscp));
        vp->m_storage = storage(vscp);
        m_varps.emplace(vscp, vp);
        return vp;
    }

    bool packed(const AstNode* nodep) {
        const AstNodeDType* const dtypep = nodep->dtypep()->skipRefp();
        if (dtypep->isIntegralOrPacked()) return true;
        unsupported("non-basic packed value");
        return false;
    }

    // Eligibility is checked before creating any graph nodes. Procedures that
    // need native language/event semantics remain intact, and their values are
    // explicit scheduler-maintained inputs to adjacent RepCut kernels.
    static bool nativeMemory(const AstArraySel* nodep) {
        const AstVarRef* const refp = VN_CAST(nodep->fromp(), VarRef);
        // An array of SystemC ports requires element-wise kernel reads, not
        // the whole-value capture used for ordinary packed SystemC inputs.
        if (!refp || refp->varp()->isSc() || nodep->bitp()->width() > 32) return false;
        const AstUnpackArrayDType* const dtypep
            = VN_CAST(refp->dtypep()->skipRefp(), UnpackArrayDType);
        return dtypep && dtypep->subDTypep()->skipRefp()->isIntegralOrPacked();
    }

    bool nativeExpression(const AstNodeExpr* rootp) const {
        std::vector<const AstNodeExpr*> pending{rootp};
        while (!pending.empty()) {
            const AstNodeExpr* const nodep = pending.back();
            pending.pop_back();
            if (!nodep->dtypep()->skipRefp()->isIntegralOrPacked()) return false;
            if (m_clocked && VN_IS(nodep, Time)) continue;
            if (const AstCExpr* const cp = VN_CAST(nodep, CExpr)) {
                if (!m_clocked || !cp->isGateOptimizable()
                    || cp->exists([](const AstNode* childp) {
                           return !VN_IS(childp, CExpr) && !VN_IS(childp, Text);
                       }))
                    return false;
            } else if (VN_IS(nodep, VarRef)) {
                continue;
            } else if (const AstConst* const cp = VN_CAST(nodep, Const)) {
                if (cp->num().isFourState()) return false;
            } else if (const AstArraySel* const sp = VN_CAST(nodep, ArraySel)) {
                if (!nativeMemory(sp)) return false;
                pending.push_back(sp->bitp());
            } else if (const AstCond* const cp = VN_CAST(nodep, Cond)) {
                pending.insert(pending.end(), {cp->elsep(), cp->thenp(), cp->condp()});
            } else if (const AstSel* const sp = VN_CAST(nodep, Sel)) {
                pending.insert(pending.end(), {sp->lsbp(), sp->fromp()});
            } else if (const AstNodeUniop* const up = VN_CAST(nodep, NodeUniop)) {
                if (!s_unary.count(nodep->typeName())) return false;
                pending.push_back(up->lhsp());
            } else if (const AstNodeBiop* const bp = VN_CAST(nodep, NodeBiop)) {
                if (!s_binary.count(nodep->typeName())) return false;
                pending.insert(pending.end(), {bp->rhsp(), bp->lhsp()});
            } else {
                return false;
            }
        }
        return true;
    }

    std::string nativeStatements(const AstNode* nodep) const {
        for (; nodep; nodep = nodep->nextp()) {
            if (VN_IS(nodep, Comment) || VN_IS(nodep, CoverInc)) continue;
            if (const AstNodeAssign* const ap = VN_CAST(nodep, NodeAssign)) {
                const AstVarRef* const refp = VN_CAST(ap->lhsp(), VarRef);
                const bool local
                    = m_clocked && refp
                      && m_sourceAnalysis.localTemporary(refp->varScopep(), m_procedurep);
                if (ap->timingControlp()
                    || (m_clocked ? !VN_IS(ap, AssignDly) && !(local && VN_IS(ap, Assign))
                                  : !VN_IS(ap, Assign) && !VN_IS(ap, AssignW)))
                    return "assignment scheduling";
                if (const AstArraySel* const sp = VN_CAST(ap->lhsp(), ArraySel)) {
                    if (!m_clocked || !nativeMemory(sp) || !nativeExpression(sp->bitp()))
                        return "memory write shape";
                } else if (const AstSel* const sp = VN_CAST(ap->lhsp(), Sel)) {
                    const AstArraySel* const arrayp = VN_CAST(sp->fromp(), ArraySel);
                    if (!m_clocked || !arrayp || !nativeMemory(arrayp)
                        || !nativeExpression(arrayp->bitp()) || !nativeExpression(sp->lsbp()))
                        return "write target type or shape";
                } else if (!refp || !nativeExpression(refp)) {
                    return "write target type or shape";
                }
                if (!nativeExpression(ap->rhsp())) return "expression or value type";
            } else if (const AstIf* const ip = VN_CAST(nodep, If)) {
                if (!nativeExpression(ip->condp())) return "condition expression";
                const std::string taken = nativeStatements(ip->thensp());
                if (!taken.empty()) return taken;
                const std::string untaken = nativeStatements(ip->elsesp());
                if (!untaken.empty()) return untaken;
            } else if (const AstBegin* const bp = VN_CAST(nodep, Begin)) {
                const std::string body = nativeStatements(bp->stmtsp());
                if (!body.empty()) return body;
            } else if (m_clocked && VN_IS(nodep, Display)) {
                const AstDisplay* const displayp = VN_AS(nodep, Display);
                if (displayp->displayType() == VDisplayType::DT_MONITOR
                    || displayp->displayType() == VDisplayType::DT_STROBE)
                    return "postponed effect";
                for (const AstNodeExpr* argp = displayp->fmtp()->exprsp(); argp;
                     argp = VN_AS(argp->nextp(), NodeExpr)) {
                    const AstConst* const cp = VN_CAST(argp, Const);
                    if ((!cp || !cp->num().isString()) && !nativeExpression(argp))
                        return "effect argument";
                }
                if (displayp->filep() && !nativeExpression(displayp->filep()))
                    return "effect file descriptor";
            } else if (m_clocked && (VN_IS(nodep, Stop) || VN_IS(nodep, Finish))) {
                // Capture activation in the partition; execute the effect once
                // on the caller, before publishing any next-state candidates.
            } else {
                return std::string{"statement "} + nodep->typeName();
            }
        }
        return "";
    }

    // V3Unknown has already inserted the language-level read/write bounds checks.
    // Retain safe physical indices independently of later expression lowering.
    const AstVarScope* memory(const AstArraySel* nodep) {
        const AstVarRef* const refp = VN_CAST(nodep->fromp(), VarRef);
        if (!refp) {
            unsupported("memory shape or index");
            return nullptr;
        }
        const AstUnpackArrayDType* const dtypep
            = VN_CAST(refp->dtypep()->skipRefp(), UnpackArrayDType);
        if (!dtypep || !dtypep->subDTypep()->skipRefp()->isIntegralOrPacked()) {
            unsupported("memory shape or index");
            return nullptr;
        }
        const AstNodeExpr* const indexp = nodep->bitp();
        if (indexp->width() > 32) {
            unsupported("memory shape or index");
            return nullptr;
        }
        m_memorySizes.emplace(refp->varScopep(), dtypep->elementsConst());
        m_result.m_storage[storage(refp->varScopep())].m_elements = dtypep->elementsConst();
        return refp->varScopep();
    }

    // Return null if every index bit pattern is valid. Otherwise return a
    // one-bit predicate using the normalized unsigned array-storage index.
    RepCutVertex* memoryBound(const AstVarScope* memoryp, RepCutVertex* indexp) {
        const size_t elements = m_memorySizes.at(memoryp);
        if ((uint64_t{1} << indexp->m_width) <= elements) return nullptr;
        RepCutVertex* const boundp
            = constant(indexp->m_width, false, elements - 1,
                       cvtToStr(indexp->m_width) + "'d" + cvtToStr(elements - 1));
        return make(Op::LTE, 1, false, {indexp, boundp});
    }

    struct ExpressionFrame final {
        const AstNodeExpr* m_nodep;  // Expression being lowered
        size_t m_region;  // Region containing this expression
        std::vector<const AstNodeExpr*> m_childps;  // Operands in source order
        std::vector<RepCutVertex*> m_inputs;  // Lowered graph operands
        Op m_kind = Op::CONSTANT;  // Operation to emit after lowering operands
        size_t m_taken = V3RepCut::NO_ID;  // Conditional's taken region
        size_t m_untaken = V3RepCut::NO_ID;  // Conditional's untaken region
        size_t m_next = 0;  // Next operand to lower
        bool m_started = false;  // Leaf classification has completed
        ExpressionFrame(const AstNodeExpr* nodep, size_t region)
            : m_nodep{nodep}
            , m_region{region} {}
    };

    RepCutVertex* startExpression(ExpressionFrame& frame, const Values& values) {
        const AstNodeExpr* const nodep = frame.m_nodep;
        if (!packed(nodep)) return nullptr;
        const AstCExpr* const contextp = VN_CAST(nodep, CExpr);
        if (m_clocked
            && (VN_IS(nodep, Time)
                || (contextp && contextp->isGateOptimizable()
                    && !contextp->exists([](const AstNode* childp) {
                           return !VN_IS(childp, CExpr) && !VN_IS(childp, Text);
                       })))) {
            RepCutVertex* const vp = make(Op::CONTEXT, nodep, {});
            vp->m_aux = m_contexts++;
            if (m_bindingsp) m_bindingsp->m_contextps.push_back(nodep);
            return vp;
        }
        if (const AstArraySel* const sp = VN_CAST(nodep, ArraySel)) {
            const AstVarScope* const memoryp = memory(sp);
            if (!memoryp) return nullptr;
            frame.m_kind = Op::MEMREAD;
            frame.m_inputs.push_back(variable(memoryp));
            frame.m_childps = {sp->bitp()};
            return nullptr;
        }
        if (const AstVarRef* const refp = VN_CAST(nodep, VarRef)) {
            const auto it = values.find(refp->varScopep());
            return it == values.end() ? variable(refp->varScopep()) : it->second;
        }
        if (const AstConst* const cp = VN_CAST(nodep, Const)) {
            if (cp->num().isFourState()) {
                unsupported("four-state constant");
                return nullptr;
            }
            RepCutVertex* const vp = make(Op::CONSTANT, nodep, {}, cp->num().ascii());
            for (int i = 0; i < VL_WORDS_I(nodep->width()); ++i) {
                vp->m_words.push_back(cp->num().edataWord(i));
            }
            return vp;
        }
        // Explicit allowlist: node type and operands fully describe these operations.
        const std::string kind = nodep->typeName();
        if (const AstNodeUniop* const up = VN_CAST(nodep, NodeUniop)) {
            if (s_unary.count(kind)) {
                frame.m_kind = s_unary.at(kind);
                frame.m_childps = {up->lhsp()};
                return nullptr;
            }
        }
        if (const AstNodeBiop* const bp = VN_CAST(nodep, NodeBiop)) {
            if (s_binary.count(kind)) {
                frame.m_kind = s_binary.at(kind);
                frame.m_childps = {bp->lhsp(), bp->rhsp()};
                return nullptr;
            }
        }
        if (const AstCond* const cp = VN_CAST(nodep, Cond)) {
            frame.m_kind = Op::COND;
            frame.m_childps = {cp->condp(), cp->thenp(), cp->elsep()};
            return nullptr;
        }
        if (const AstSel* const sp = VN_CAST(nodep, Sel)) {
            frame.m_kind = Op::SEL;
            frame.m_childps = {sp->fromp(), sp->lsbp()};
            return nullptr;
        }
        unsupported("expression " + kind);
        return nullptr;
    }

    RepCutVertex* expression(const AstNodeExpr* nodep, const Values& values) {
        // Inlining can create tens of thousands of nested concatenations.
        // Use an explicit stack while preserving recursive operand/region order.
        VL_RESTORER(m_region);
        std::vector<ExpressionFrame> pending;
        pending.emplace_back(nodep, m_region);
        while (!pending.empty()) {
            ExpressionFrame& frame = pending.back();
            m_region = frame.m_region;
            RepCutVertex* resultp = nullptr;
            if (!frame.m_started) {
                frame.m_started = true;
                resultp = startExpression(frame, values);
            }
            if (frame.m_next < frame.m_childps.size()) {
                if (frame.m_kind == Op::COND && frame.m_next == 1) {
                    RepCutVertex* const branchp = make(Op::BRANCH, 1, false, frame.m_inputs);
                    frame.m_inputs[0] = branchp;
                    frame.m_taken = m_result.makeRegion(m_region, branchp, true);
                    frame.m_untaken = m_result.makeRegion(m_region, branchp, false);
                }
                const size_t region = frame.m_kind == Op::COND && frame.m_next
                                          ? (frame.m_next == 1 ? frame.m_taken : frame.m_untaken)
                                          : frame.m_region;
                const AstNodeExpr* const childp = frame.m_childps[frame.m_next++];
                pending.emplace_back(childp, region);
                continue;
            }
            if (!frame.m_childps.empty()) {
                if (frame.m_kind == Op::MEMREAD) {
                    const AstArraySel* const selectp = VN_AS(frame.m_nodep, ArraySel);
                    const AstVarScope* const memoryp
                        = VN_AS(selectp->fromp(), VarRef)->varScopep();
                    RepCutVertex*& indexp = frame.m_inputs[1];
                    if (indexp) {
                        if (RepCutVertex* const boundp = memoryBound(memoryp, indexp)) {
                            RepCutVertex* const zerop = constant(
                                indexp->m_width, false, 0, cvtToStr(indexp->m_width) + "'h0");
                            indexp
                                = make(Op::COND, indexp->m_width, false, {boundp, indexp, zerop});
                        }
                        resultp = make(frame.m_kind, frame.m_nodep, frame.m_inputs);
                    }
                } else {
                    resultp = make(frame.m_kind, frame.m_nodep, frame.m_inputs);
                }
            }
            pending.pop_back();
            if (pending.empty()) return resultp;
            pending.back().m_inputs.push_back(resultp);
        }
        v3fatalSrc("Missing RepCut expression result");
        return nullptr;
    }

    RepCutVertex* value(const Values& values, const AstVarScope* vscp) {
        const auto it = values.find(vscp);
        return it == values.end() ? variable(vscp) : it->second;
    }

    void memoryWrite(const AstNodeAssign* nodep, const AstArraySel* selectp,
                     const AstSel* partialp = nullptr) {
        if (!m_clocked) {
            unsupported("blocking memory write");
            return;
        }
        const AstVarScope* const memoryp = memory(selectp);
        if (!memoryp || !packed(selectp)) return;
        RepCutVertex* const oldp = variable(memoryp);
        RepCutVertex* const indexp = expression(selectp->bitp(), m_blockingValues);
        RepCutVertex* const datap = expression(nodep->rhsp(), m_blockingValues);
        RepCutVertex* enablep = m_guardp ? m_guardp : constant(1, false, 1, "1'h1");
        if (indexp) {
            if (RepCutVertex* const boundp = memoryBound(memoryp, indexp)) {
                enablep = make(Op::LOGAND, 1, false, {enablep, boundp});
            }
        }
        // Source priority is metadata, not an eval dependence. Publication must
        // make the last enabled write to a conflicting address win.
        const std::string label
            = scopedName(memoryp) + "@" + m_domain + "#" + cvtToStr(m_pendingWrites.size());
        // Capture only the selected value, never a read/modify/write of the old
        // element. Publication applies the slice to the current element so that
        // earlier enabled ports survive outside this port's selected bits.
        std::vector<RepCutVertex*> inputs{oldp, enablep, indexp, datap};
        if (partialp) {
            if (const AstConst* const offsetp = VN_CAST(partialp->lsbp(), Const)) {
                // Width optimization may leave a signed dtype on an unsigned
                // normalized index (e.g. seven-bit 94). Preserve the numeric
                // index instead of reinterpreting its top bit as a sign bit.
                inputs.push_back(constant(32, false, static_cast<uint32_t>(offsetp->toSInt()),
                                          offsetp->num().ascii()));
            } else {
                inputs.push_back(expression(partialp->lsbp(), m_blockingValues));
            }
        }
        RepCutVertex* const portp = make(Op::PENDING_MEMWRITE, nodep->lhsp(), inputs, label);
        portp->m_storage = storage(memoryp);
        portp->m_domain = m_domainId;
        portp->m_priority = m_pendingWrites.size();
        m_pendingWrites.push_back({memoryp, portp, nodep});
    }

    void mergeValues(Values& result, const Values& thenValues, const Values& elseValues,
                     RepCutVertex* condp) {
        std::set<const AstVarScope*, VarLess> written;
        for (const auto& pair : thenValues) written.insert(pair.first);
        for (const auto& pair : elseValues) written.insert(pair.first);
        for (const AstVarScope* const vscp : written) {
            RepCutVertex* const tp = value(thenValues, vscp);
            RepCutVertex* const ep = value(elseValues, vscp);
            result[vscp] = tp == ep ? tp : make(Op::JOIN, vscp->varp(), {condp, tp, ep});
        }
    }

    void branchStatement(const AstIf* nodep, Values& values) {
        VL_RESTORER(m_guardp);
        VL_RESTORER(m_region);
        const size_t parent = m_region;
        RepCutVertex* const parentGuardp = m_guardp;
        // A local Boolean decision preserves outer control ancestry even when
        // the tested value was defined outside this region. Reduction, rather
        // than truncation, implements truth testing for wider conditions.
        RepCutVertex* const condp
            = make(Op::BRANCH, 1, false,
                   {expression(nodep->condp(), m_clocked ? m_blockingValues : values)});
        const size_t taken = m_result.makeRegion(parent, condp, true);
        const size_t untaken = m_result.makeRegion(parent, condp, false);
        Values thenValues = values;
        Values elseValues = values;
        const Values beforeBlocking = m_blockingValues;
        m_guardp = parentGuardp ? make(Op::LOGAND, 1, false, {parentGuardp, condp}) : condp;
        m_region = taken;
        statements(nodep->thensp(), thenValues);
        const Values thenBlocking = m_blockingValues;
        m_blockingValues = beforeBlocking;
        m_region = parent;
        RepCutVertex* const notp = make(Op::LOGNOT, 1, false, {condp});
        m_guardp = parentGuardp ? make(Op::LOGAND, 1, false, {parentGuardp, notp}) : notp;
        m_region = untaken;
        statements(nodep->elsesp(), elseValues);
        m_region = parent;
        m_guardp = parentGuardp;
        mergeValues(values, thenValues, elseValues, condp);
        const Values elseBlocking = m_blockingValues;
        mergeValues(m_blockingValues, thenBlocking, elseBlocking, condp);
    }

    void effect(const AstNodeStmt* nodep, const Values& values) {
        std::vector<RepCutVertex*> args;
        if (const AstDisplay* const displayp = VN_CAST(nodep, Display)) {
            for (const AstNodeExpr* argp = displayp->fmtp()->exprsp(); argp;
                 argp = VN_AS(argp->nextp(), NodeExpr)) {
                if (const AstConst* const cp = VN_CAST(argp, Const)) {
                    if (cp->num().isString()) continue;
                }
                args.push_back(expression(argp, values));
            }
            if (displayp->filep()) args.push_back(expression(displayp->filep(), values));
        }
        RepCutVertex* const vp = make(Op::EFFECT, 1, false, args);
        vp->m_domain = m_domainId;
        vp->m_aux = m_effects++;
        if (m_bindingsp) {
            m_bindingsp->m_effectps.push_back(nodep);
            m_bindingsp->m_effects.emplace(nodep, vp);
            m_bindingsp->m_sinkProcedures.emplace(vp, m_bindingsp->m_clockedps.size());
        }
    }

    bool nativeCallback(AstAlways* nodep) {
        if (!m_clocked || !nodep->exists([](const AstCCall*) { return true; })) return false;
        V3RepCut::Callback binding{nodep->stmtsp(), {}, {}};
        if (!RepCutCallbackCheck{nodep, binding}.valid()) return false;
        std::set<const AstVarScope*> written;
        for (const auto& output : binding.m_outputs) {
            written.insert(output.first);
            // A combined capture dispatch must not move a read ahead of a
            // blocking write in another process. NBA destinations remain under
            // ordinary native scheduling and retain its old-state ordering.
            if (!output.second && !m_sourceAnalysis.privateAtRuntime(output.first, nodep))
                return false;
        }
        std::vector<const AstVarScope*> captures;
        for (const AstVarScope* const vscp : binding.m_inputps) {
            if (written.count(vscp)) continue;
            if (vscp->dtypep()->skipRefp()->isIntegralOrPacked()) {
                captures.push_back(vscp);
            } else if (const auto* const driversp = m_sourceAnalysis.elementDrivers(vscp)) {
                if (std::all_of(driversp->begin(), driversp->end(), [&](const auto& item) {
                        return nativeExpression(item.second->rhsp());
                    }))
                    captures.push_back(vscp);
            }
        }
        if (captures.empty()) return false;
        binding.m_inputps = std::move(captures);
        std::vector<RepCutVertex*> inputs;
        for (const AstVarScope* const vscp : binding.m_inputps) {
            if (const auto* const driversp = m_sourceAnalysis.elementDrivers(vscp)) {
                for (const auto& item : *driversp)
                    inputs.push_back(expression(item.second->rhsp(), {}));
                V3Stats::addStatSum("RepCut native, callback array elements", driversp->size());
            } else {
                inputs.push_back(variable(vscp));
            }
        }
        // The foreign consumer runs after the join, so its inputs need not
        // share an owner. Keep each scalar/element as an independent sink;
        // bundling a wide interface would coarsen the partitioning problem.
        const size_t callbackId = m_callbacks++;
        const size_t domain = nativeDomain(m_activep->sentreep());
        for (size_t i = 0; i < inputs.size(); ++i) {
            RepCutVertex* const capturep = make(Op::CALL_CAPTURE, 1, false, {inputs[i]});
            capturep->m_domain = domain;
            capturep->m_aux = callbackId;
            capturep->m_priority = i;
        }
        if (m_bindingsp) {
            m_bindingsp->m_nativeCallbackps.emplace(callbackId, nodep);
            m_bindingsp->m_callbacks.push_back(std::move(binding));
        }
        ++m_result.m_report.m_supported;
        V3Stats::addStatSum("RepCut native, callback input captures", inputs.size());
        V3Stats::addStatSum("RepCut native, callback procedures", 1);
        return true;
    }

    void statements(const AstNode* nodep, Values& values) {
        for (; nodep; nodep = nodep->nextp()) {
            if (VN_IS(nodep, Comment)) continue;
            // Native coverage instrumentation is preserved in a separate copy
            // of this procedure's control flow. Never replicate its increments.
            if (VN_IS(nodep, CoverInc)) continue;
            if (const AstNodeAssign* const ap = VN_CAST(nodep, NodeAssign)) {
                const AstVarRef* const localp = VN_CAST(ap->lhsp(), VarRef);
                if (m_clocked && VN_IS(ap, Assign) && !ap->timingControlp() && localp
                    && m_sourceAnalysis.localTemporary(localp->varScopep(), m_procedurep)) {
                    if (packed(localp))
                        m_blockingValues[localp->varScopep()]
                            = expression(ap->rhsp(), m_blockingValues);
                    continue;
                }
                if ((m_clocked && !VN_IS(ap, AssignDly))
                    || (!m_clocked && !VN_IS(ap, Assign) && !VN_IS(ap, AssignW))
                    || ap->timingControlp()) {
                    unsupported("assignment scheduling");
                    continue;
                }
                if (const AstArraySel* const sp = VN_CAST(ap->lhsp(), ArraySel)) {
                    memoryWrite(ap, sp);
                    continue;
                }
                if (const AstSel* const sp = VN_CAST(ap->lhsp(), Sel)) {
                    if (const AstArraySel* const arrayp = VN_CAST(sp->fromp(), ArraySel)) {
                        memoryWrite(ap, arrayp, sp);
                        continue;
                    }
                }
                const AstVarRef* const refp = VN_CAST(ap->lhsp(), VarRef);
                if (!refp) {
                    ++m_result.m_report.m_writeTargets[ap->lhsp()->typeName()];
                    unsupported("partial or memory write");
                    continue;
                }
                if (!packed(refp)) continue;
                // NBA RHS reads never see earlier NBA updates in this procedure.
                RepCutVertex* const rhsp
                    = expression(ap->rhsp(), m_clocked ? m_blockingValues : values);
                values[refp->varScopep()] = rhsp;
            } else if (const AstIf* const ip = VN_CAST(nodep, If)) {
                branchStatement(ip, values);
            } else if (const AstBegin* const bp = VN_CAST(nodep, Begin)) {
                statements(bp->stmtsp(), values);
            } else if (m_clocked
                       && (VN_IS(nodep, Display) || VN_IS(nodep, Stop) || VN_IS(nodep, Finish))) {
                effect(VN_AS(nodep, NodeStmt), m_blockingValues);
            } else {
                unsupported("statement " + std::string{nodep->typeName()});
            }
        }
    }

    void visit(AstActive* nodep) override {
        VL_RESTORER(m_activep);
        m_activep = nodep;
        iterateAndNextConstNull(nodep->procsp());
    }

    void visit(AstAlways* nodep) override {
        if (emptyStatements(nodep->stmtsp())) return;
        VL_RESTORER(m_clocked);
        VL_RESTORER_CLEAR(m_blockingValues);
        VL_RESTORER(m_procedurep);
        m_blockingValues.clear();
        m_procedurep = nodep;
        VL_RESTORER(m_guardp);
        VL_RESTORER(m_region);
        VL_RESTORER_CLEAR(m_pendingWrites);
        VL_RESTORER_COPY(m_domain);
        VL_RESTORER(m_domainId);
        m_guardp = nullptr;
        m_region = V3RepCut::NO_ID;
        m_pendingWrites.clear();
        ++m_result.m_report.m_procedures;
        const size_t failures = m_result.m_report.m_failures;
        UASSERT_OBJ(m_activep, nodep, "RepCut export requires active classification");
        m_clocked = m_activep->hasClocked();
        std::string reason;
        // A concrete interface member may alias reads or writes through a
        // virtual interface. Those aliases are not represented by VarRef edges
        // in the kernel graph. Keep their original procedures so native NBA
        // lowering preserves old-value reads and conditional publication.
        if (m_clocked && m_assertionActions && nodep->exists([](const AstNode* stmtp) {
                return VN_IS(stmtp, Stop) || VN_IS(stmtp, Finish);
            })) {
            // Delaying a terminal effect until a capture join can let a native
            // assertion action run on an edge that should stop simulation.
            reason = "terminal effect before assertion actions";
        } else if (nodep->exists([](const AstVarRef* refp) {
                       return refp->varp()->sensIfacep() != nullptr;
                   })) {
            reason = "virtual interface storage";
        } else {
            if (nativeCallback(nodep)) return;
            reason = nativeStatements(nodep->stmtsp());
        }
        if (!m_clocked && !m_activep->hasCombo()) reason = "activation semantics";
        if (reason.empty() && nodep->exists([&](const AstVarRef* refp) {
                return refp->access().isWriteOrRW()
                       && !m_sourceAnalysis.soleWriter(refp->varScopep(), nodep);
            }))
            reason = "multiple writing procedures";
        if (!reason.empty()) {
            ++m_result.m_report.m_nativeRetained[reason];
            if (m_bindingsp) m_bindingsp->m_retainedps.push_back(nodep);
            UINFO(3, "RepCut retained procedure: " << reason << " " << nodep);
            if (debug() >= 9) nodep->dumpTree(std::cout);
            return;
        }
        m_domain.clear();
        m_domainId = V3RepCut::NO_ID;
        if (m_clocked) {
            m_domainId = nativeDomain(m_activep->sentreep());
            m_domain = "native:" + cvtToStr(m_domainId);
        }
        Values values;
        statements(nodep->stmtsp(), values);
        if (m_result.m_report.m_failures != failures) return;
        for (const MemoryWrite& write : m_pendingWrites) {
            const auto it = m_memoryOwners.find(write.m_memoryp);
            if (it != m_memoryOwners.end() && it->second != nodep) {
                unsupported("multiple processes write memory");
            }
        }
        if (m_result.m_report.m_failures != failures) return;
        for (const MemoryWrite& write : m_pendingWrites) {
            m_memoryOwners.emplace(write.m_memoryp, nodep);
            write.m_portp->m_kind = Op::MEMWRITE;
            if (m_bindingsp) {
                m_bindingsp->m_sinkProcedures.emplace(write.m_portp,
                                                      m_bindingsp->m_clockedps.size());
                m_bindingsp->m_memoryWrites.emplace(write.m_assignp, write.m_portp);
            }
        }
        for (const auto& pair : values) {
            const AstVarScope* const vscp = pair.first;
            variable(vscp);
            if (!m_drivers.emplace(vscp, pair.second).second)
                unsupported("multiple processes write variable");
            if (m_clocked) {
                m_state.insert(vscp);
                RepCutVertex* const nextp = make(Op::NEXT, vscp->varp(), {pair.second},
                                                 scopedName(vscp) + "@" + m_domain);
                nextp->m_storage = storage(vscp);
                nextp->m_domain = m_domainId;
                if (m_bindingsp)
                    m_bindingsp->m_sinkProcedures.emplace(nextp, m_bindingsp->m_clockedps.size());
            }
        }
        if (m_bindingsp && !m_clocked) {
            const AstNodeAssign* assignp = nullptr;
            for (const AstNode* stmtp = nodep->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
                if (VN_IS(stmtp, Comment)) continue;
                if (assignp || !VN_IS(stmtp, NodeAssign)) {
                    assignp = nullptr;
                    break;
                }
                assignp = VN_AS(stmtp, NodeAssign);
            }
            if (assignp) {
                if (const AstVarRef* const refp = VN_CAST(assignp->lhsp(), VarRef))
                    m_bindingsp->m_combAssignments.emplace(storage(refp->varScopep()), assignp);
            }
        }
        if (m_result.m_report.m_failures == failures) ++m_result.m_report.m_supported;
        if (m_clocked && m_bindingsp) m_bindingsp->m_clockedps.push_back(nodep);
    }

    void visit(AstInitial*) override {}  // Startup is outside the per-edge function.
    void visit(AstFinal*) override {}  // Finalization is outside the per-edge function.
    void visit(AstVarScope* nodep) override {
        // Include outputs even if their only reference is in excluded startup
        // logic. Otherwise a missing output could silently disappear from coverage.
        if (nodep->varp()->isPrimaryIO() && !nodep->varp()->isNonOutput()
            && nodep->dtypep()->skipRefp()->isIntegralOrPacked())
            variable(nodep);
        iterateChildrenConst(nodep);
    }
    void visit(AstNode* nodep) override { iterateChildrenConst(nodep); }

    void connectVariables() {
        for (const auto& pair : m_varps) {
            const AstVarScope* const vscp = pair.first;
            RepCutVertex* const vp = pair.second;
            if (vscp->varp()->isPrimaryIO() && !vscp->varp()->isNonOutput()) {
                RepCutVertex* const outputp
                    = make(Op::OUTPUT, vscp->varp(), {vp}, scopedName(vscp));
                outputp->m_storage = storage(vscp);
            }
            if (m_memorySizes.count(vscp)) {
                vp->m_kind = Op::OLDMEM;
                continue;
            }
            if (m_state.count(vscp)) {
                vp->m_kind = Op::OLD;
                continue;
            }
            if (vscp->varp()->isSigUserRWPublic()) {
                // Public deposits/forces can change storage independently of its
                // HDL driver. Read the value maintained by native scheduling.
                vp->m_kind = Op::EXTERNAL;
                continue;
            }
            const auto it = m_drivers.find(vscp);
            RepCutVertex* driverp = it == m_drivers.end() ? nullptr : it->second;
            if (!driverp) {
                if (const AstConst* const cp = m_sourceAnalysis.constantValue(vscp)) {
                    driverp = expression(cp, {});
                }
            }
            if (driverp) {
                m_result.addInput(vp, driverp);
            } else if (vscp->varp()->isPrimaryIO() && vscp->varp()->isNonOutput()) {
                vp->m_kind = Op::INPUT;
            } else if (vscp->varp()->isXTemp() || m_sourceAnalysis.initializedOnly(vscp)) {
                // V3Unknown's XTEMP stores an X replacement chosen during model
                // initialization. The same boundary represents other values
                // written only during initialization. Retain an explicit input to the
                // per-edge function; do not replace it with a constant or resample it.
                vp->m_kind = Op::INIT;
                ++m_result.m_report.m_initialValues;
            } else {
                vp->m_kind = Op::EXTERNAL;
            }
        }
    }

public:
    RepCutVisitor(AstNetlist* netlistp, V3RepCut::Graph& result,
                  V3RepCut::Bindings* bindingsp = nullptr)
        : m_sourceAnalysis{netlistp}
        , m_assertionActions{v3Global.hasConcurrentAssertions()}
        , m_result{result}
        , m_bindingsp{bindingsp} {
        iterateConst(netlistp);
        connectVariables();
        m_result.nativeCycleBoundaries();
        // Drop AST-to-vertex lookups before pruning can delete unused vertices.
        m_varps.clear();
        m_drivers.clear();
        m_result.removeUnused();
        m_result.m_report.m_blocked = m_result.cyclicNodes();
        if (m_result.m_report.m_blocked)
            unsupported("combinational cycle or incomplete assignment");
        m_result.m_report.m_stateVariables = m_state.size();
        m_result.m_report.m_writtenMemories = m_memoryOwners.size();
        V3Stats::addStat("RepCut native, source sensitivities", m_nativeDomains.size());
        V3Stats::addStat("RepCut native, coalesced sensitivities",
                         m_nativeDomains.size() - m_nativeDomainKeys.size());
        for (const auto& pair : m_memorySizes) {
            m_result.m_report.m_memories.emplace(
                scopedName(pair.first), std::make_pair(pair.second, pair.first->varp()->width()));
        }
    }
};

}  // namespace

void V3RepCut::partitionAll(AstNetlist* netlistp) {
    if (v3Global.opt.repcut()) {
        for (AstNodeModule* modp = netlistp->modulesp(); modp;
             modp = VN_AS(modp->nextp(), NodeModule)) {
            if (!modp->threadsGroup()) continue;
            // Explicit grouping and worker placement are native scheduler
            // constraints. Keep them intact until RepCut can represent them.
            v3Global.opt.repcut(false);
            V3Stats::addStat("RepCut, threads_group fallback", 1);
            break;
        }
    }
    if (!v3Global.opt.repcut() && !v3Global.opt.repcutDumpGraph()) return;

    // Lower synchronously while these bindings still refer to the normalized AST.
    Bindings bindings;
    const std::unique_ptr<Graph> graphp{new Graph};
    RepCutVisitor{netlistp, *graphp, v3Global.opt.repcut() ? &bindings : nullptr};
    const std::string base
        = v3Global.opt.makeDir() + "/" + v3Global.opt.prefix() + "__repcut_early";
    Plan plan;
    std::string error;
    // Never leave a previous accepted plan alongside a failed or export-only run.
    std::remove((base + ".chunks.tsv").c_str());
    std::remove((base + ".cuts.tsv").c_str());
    std::remove((base + ".plan.tsv").c_str());
    std::remove((base + ".owners.tsv").c_str());
    graphp->dump(base);
    if (v3Global.opt.repcut()) Plan::partition(*graphp, base, plan, error);
    if (!error.empty()) {
        v3error("Cannot partition RepCut graph: " << error << ".");
        V3Error::abortIfErrors();
    }
    if (!plan.m_partitions.empty()) {
        plan.dump(*graphp, base);
        if (v3Global.opt.repcut()) emit(netlistp, *graphp, plan, bindings);
    }
}
