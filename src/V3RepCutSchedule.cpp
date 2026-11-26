// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Batch independent RepCut kernels using native triggers
//
// Code available from: https://verilator.org
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026-2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//*************************************************************************
// Combine RepCut domains after the scheduler has assigned trigger indices to
// their sensitivities. Each domain currently carries its own AstExecGraph,
// which becomes its own thread schedule: systems with ~20 clocked sensitivities
// then pay ~20 dispatch/join barriers per evaluation. One combined graph with a
// task per fixed worker removes those barriers while preserving each domain's
// original trigger guard.
//
// The combined graph uses the region trigger vector directly, so a task's run
// mask is the union of the domain triggers it contains. Statements that
// surrounded the original dispatch (input captures, callbacks, effects and
// publication) move into the combined dispatch under the same per-domain guard.
// Pure shared prefixes run once per worker under the union of their consumers'
// triggers, in the dependency order assigned when the prefixes were extracted.
// With one thread the same guarded compute body uses ordinary serial calls.
// Captures still precede all compute; callbacks and publication retain their
// dependency-visible positions after compute. No value is cached across calls.
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3ExecGraph.h"
#include "V3RepCut.h"
#include "V3Sched.h"
#include "V3Stats.h"

#include <map>
#include <set>
#include <unordered_set>
#include <utility>
#include <vector>

VL_DEFINE_DEBUG_FUNCTIONS;

namespace V3RepCut {
namespace {
class NativeBatch final {
    struct Kernel final {
        AstCCall* m_callp;  // Call to the domain evaluate function
        AstSenTree* m_senp;  // Original domain sensitivity
        std::set<uint32_t> m_triggers;  // Region trigger indices of the domain
        AstCFunc* m_dispatchp;  // Serial calls or parallel graph for this domain
        AstExecGraph* m_graphp;  // Parallel domain graph, null for serial execution
        std::vector<AstNodeProcedure*> m_publicationps;  // Publication sharing this sensitivity
    };
    struct Shared final {
        AstCFunc* m_funcp = nullptr;  // Pure helper shared by the consuming trigger domains
        std::set<uint32_t> m_triggers;  // Union of this helper's consumer triggers
    };
    AstNetlist* const m_netlistp;
    AstVarScope* const m_trigVscp;
    const bool m_serial = v3Global.opt.threads() == 1;
    VNDeleter m_deleter;
    size_t m_ordinal = 0;

    std::vector<AstCFunc*> takeShared(AstCFunc* rootp) {
        std::vector<AstCFunc*> pending{rootp};
        std::unordered_set<AstCFunc*> visited;
        // The emitter numbers helpers in dependency order, independent of AST addresses.
        std::map<uint32_t, AstCFunc*> helpers;
        while (!pending.empty()) {
            AstCFunc* const funcp = pending.back();
            pending.pop_back();
            if (!visited.insert(funcp).second) continue;
            std::vector<AstStmtExpr*> remove;
            funcp->foreach([&](AstCCall* callp) {
                AstCFunc* const targetp = callp->funcp();
                if (targetp->repcutSharedOrder()) {
                    UASSERT_OBJ(!callp->argsp(), callp, "Shared native helper has arguments");
                    helpers.emplace(targetp->repcutSharedOrder(), targetp);
                    remove.push_back(VN_AS(callp->backp(), StmtExpr));
                } else if (targetp->isRepCut()) {
                    pending.push_back(targetp);
                }
            });
            for (AstStmtExpr* const stmtp : remove) {
                m_deleter.pushDeletep(stmtp->unlinkFrBack());
            }
            V3Stats::addStatSum("RepCut shared domains, removed helper calls", remove.size());
        }
        std::vector<AstCFunc*> result;
        for (const auto& helper : helpers) result.push_back(helper.second);
        return result;
    }
    static AstNodeStmt* call(AstCFunc* funcp) {
        AstCCall* const callp = new AstCCall{funcp->fileline(), funcp};
        callp->dtypeSetVoid();
        return callp->makeStmt();
    }
    AstNodeExpr* trigger(const Kernel& kernel) const {
        UASSERT_OBJ(!kernel.m_triggers.empty(), kernel.m_callp,
                    "RepCut batch domain has no trigger");
        return new AstTriggered{
            m_netlistp->fileline(), m_trigVscp,
            std::vector<uint32_t>{kernel.m_triggers.begin(), kernel.m_triggers.end()}};
    }
    static AstCFunc* dispatchFunc(AstCFunc* evalp) {
        AstCFunc* dispatchp = nullptr;
        for (AstNode* nodep = evalp->stmtsp(); nodep; nodep = nodep->nextp()) {
            AstStmtExpr* const stmtp = VN_CAST(nodep, StmtExpr);
            if (!stmtp) continue;
            AstCCall* const callp = VN_CAST(stmtp->exprp(), CCall);
            if (!callp || dispatchp) return nullptr;  // Only a single closed dispatch
            dispatchp = callp->funcp();
        }
        return dispatchp;
    }
    static AstExecGraph* findGraph(AstCFunc* dispatchp) {
        // The ExecGraph lives in the dispatch callee, not inline in the evaluate function.
        AstExecGraph* graphp = nullptr;
        for (AstNode* nodep = dispatchp->stmtsp(); nodep; nodep = nodep->nextp()) {
            if (AstExecGraph* const candidatep = VN_CAST(nodep, ExecGraph)) {
                if (graphp) return nullptr;
                graphp = candidatep;
            }
        }
        return graphp;
    }
    static AstNodeStmt* clonedBody(AstExecGraph* graphp, AstCCall* taskCallp, uint32_t& thread) {
        // Each domain MTask body is AstIf{AstTriggered(oldGraphTrig,{0}), <call>}.
        AstCFunc* const taskp = taskCallp->funcp();
        AstIf* const bodyp = VN_CAST(taskp->stmtsp(), If);
        if (!bodyp || bodyp->nextp() || !VN_IS(bodyp->condp(), Triggered)) return nullptr;
        AstNodeStmt* const stmtp = bodyp->thensp();
        if (!stmtp || stmtp->nextp()) return nullptr;
        for (V3GraphVertex& vertex : graphp->depGraphp()->vertices()) {
            ExecMTask* const mtaskp = vertex.as<ExecMTask>();
            if (mtaskp->funcp() != taskp) continue;
            if (!mtaskp->hasFixedThread()) return nullptr;
            thread = static_cast<uint32_t>(mtaskp->fixedThread());
            return stmtp->cloneTree(true);
        }
        return nullptr;
    }
    static void dependency(AstCCall* callp, AstVarScope* vscp, bool output) {
        FileLine* const flp = callp->fileline();
        AstVar* const argp = new AstVar{flp, VVarType::BLOCKTEMP, "__Vcompletion", vscp->dtypep()};
        argp->funcLocal(true);
        argp->direction(output ? VDirection::OUTPUT : VDirection::CONSTREF);
        argp->isConst(!output);
        callp->funcp()->addArgsp(argp);
        callp->addArgsp(new AstVarRef{flp, vscp, output ? VAccess::WRITE : VAccess::READ});
    }
    void collectShared(AstCFunc* rootp, const Kernel& kernel, std::map<uint32_t, Shared>& shared) {
        for (AstCFunc* const funcp : takeShared(rootp)) {
            Shared& prefix = shared[funcp->repcutSharedOrder()];
            UASSERT_OBJ(!prefix.m_funcp || prefix.m_funcp == funcp, funcp,
                        "Shared helper order collision");
            prefix.m_funcp = funcp;
            prefix.m_triggers.insert(kernel.m_triggers.begin(), kernel.m_triggers.end());
        }
    }
    AstNodeStmt* computeBody(AstScope* scopep, const std::string& tag,
                             const std::vector<Kernel>& kernels) {
        FileLine* const flp = scopep->fileline();
        AstExecGraph* const graphp = m_serial ? nullptr : new AstExecGraph{flp, tag, m_trigVscp};
        std::map<uint32_t, std::vector<AstNodeStmt*>> workers;
        std::map<uint32_t, std::map<uint32_t, Shared>> shared;
        for (const Kernel& kernel : kernels) {
            if (m_serial) {
                collectShared(kernel.m_dispatchp, kernel, shared[0]);
                workers[0].push_back(new AstIf{flp, trigger(kernel), call(kernel.m_dispatchp)});
                continue;
            }
            for (AstCCall* const taskCallp : kernel.m_graphp->callspList()) {
                uint32_t thread = 0;
                AstNodeStmt* const bodyp = clonedBody(kernel.m_graphp, taskCallp, thread);
                UASSERT_OBJ(bodyp, taskCallp, "Unrecognized RepCut MTask body");
                collectShared(taskCallp->funcp(), kernel, shared[thread]);
                workers[thread].push_back(new AstIf{flp, trigger(kernel), bodyp});
            }
        }
        for (const auto& worker : workers) {
            AstNodeStmt* bodyp = nullptr;
            for (const auto& prefix : shared[worker.first]) {
                const Shared& helper = prefix.second;
                AstTriggered* const guardp = new AstTriggered{
                    flp, m_trigVscp,
                    std::vector<uint32_t>{helper.m_triggers.begin(), helper.m_triggers.end()}};
                bodyp = AstNode::addNextNull(bodyp, new AstIf{flp, guardp, call(helper.m_funcp)});
                V3Stats::addStatSum("RepCut shared domains, factored helpers", 1);
            }
            for (AstNodeStmt* const stmtp : worker.second)
                bodyp = AstNode::addNextNull(bodyp, stmtp);
            // Serial calls retain the same trigger union and helper order,
            // without introducing a task graph or a worker synchronization.
            if (m_serial) return bodyp;
            ExecMTask* const taskp = new ExecMTask{graphp, scopep, bodyp};
            taskp->funcp()->isRepCut(true);
            taskp->fixedThread(static_cast<int>(worker.first));
            taskp->cost(1);
            taskp->priority(1);
            AstCCall* const callp = new AstCCall{flp, taskp->funcp()};
            callp->dtypeSetVoid();
            graphp->addCallsp(callp);
        }

        return graphp;
    }
    void combine(V3Sched::ProcessList& logic, AstScope* scopep,
                 const std::vector<Kernel>& kernels) {
        FileLine* const flp = scopep->fileline();
        const std::string tag = "__Vrepcut_batch" + cvtToStr(m_ordinal++);

        // Union sensitivity, one trigger entry for the combined dispatch.
        AstSenTree* const senp = new AstSenTree{flp, nullptr};
        for (const Kernel& kernel : kernels)
            senp->addSensesp(kernel.m_senp->sensesp()->cloneTree(true));
        // The scheduler releases global sensitivity trees after ordering all regions.
        m_netlistp->topScopep()->addSenTreesp(senp);

        AstNodeStmt* const computep = computeBody(scopep, tag, kernels);

        // Publication procedures stay in their original post region. Order them
        // after the combined dispatch with a completion dependency, as the
        // v5.050 batching pass did.
        AstVarScope* const completep
            = v3Global.rootp()->topScopep()->createTemp(tag + "_complete", 1);
        completep->varp()->noReset(true);
        completep->varp()->trace(false);
        completep->varp()->isInternal(true);

        AstCFunc* const batchp = new AstCFunc{flp, tag, scopep};
        batchp->isLoose(true);
        batchp->isStatic(false);
        batchp->isConst(false);
        batchp->dontCombine(true);
        batchp->noInline(true);
        batchp->isRepCut(true);
        batchp->repcutBatchRoot(true);
        batchp->repcutDependencyArgs(true);
        AstCCall* const batchCallp = new AstCCall{flp, batchp};
        batchCallp->dtypeSetVoid();
        dependency(batchCallp, completep, true);

        // Worker entry points are opaque to lifetime optimization. Preserve
        // the original calls' dependency operands so old-state reads remain
        // visible after the per-domain calls are removed.
        size_t argument = 0;
        for (const Kernel& kernel : kernels) {
            for (AstNode* argp = kernel.m_callp->funcp()->argsp(); argp; argp = argp->nextp()) {
                AstVar* const clonep = VN_AS(argp->cloneTree(false), Var);
                clonep->name("__Vdependency" + cvtToStr(argument++));
                batchp->addArgsp(clonep);
            }
            if (kernel.m_callp->argsp())
                batchCallp->addArgsp(kernel.m_callp->argsp()->cloneTree(true));
        }

        scopep->addBlocksp(batchp);

        // Replace each domain dispatch with its guarded pre/tail statements
        // around the single combined graph.
        std::vector<AstNodeStmt*> tails;
        size_t publication = 0;
        for (const Kernel& kernel : kernels) {
            AstStmtExpr* const callStmtp = VN_CAST(kernel.m_callp->backp(), StmtExpr);
            UASSERT_OBJ(callStmtp, kernel.m_callp, "RepCut dispatch call not in a statement");
            AstNodeProcedure* const procp = VN_CAST(callStmtp->backp(), NodeProcedure);
            UASSERT_OBJ(procp, callStmtp, "RepCut dispatch call not in a procedure");

            AstNodeStmt* prep = nullptr;
            for (AstNode* nodep = procp->stmtsp(); nodep && nodep != callStmtp;) {
                AstNode* const nextp = nodep->nextp();
                prep = AstNode::addNextNull(prep, VN_AS(nodep->unlinkFrBack(), NodeStmt));
                nodep = nextp;
            }
            AstNode* const tailp = callStmtp->nextp();
            if (tailp) tailp->unlinkFrBackWithNext();
            VL_DO_DANGLING(callStmtp->unlinkFrBack()->deleteTree(), callStmtp);
            if (prep) batchp->addStmtsp(new AstIf{flp, trigger(kernel), prep});
            if (tailp) tails.push_back(new AstIf{flp, trigger(kernel), VN_AS(tailp, NodeStmt)});
            for (AstNodeProcedure* const otherp : kernel.m_publicationps) {
                AstCFunc* const markerp
                    = new AstCFunc{flp, tag + "_pubdep" + cvtToStr(publication++), scopep};
                markerp->isLoose(true);
                markerp->dontCombine(true);
                markerp->isRepCut(true);
                markerp->repcutDependencyArgs(true);
                AstCCall* const markerCallp = new AstCCall{flp, markerp};
                markerCallp->dtypeSetVoid();
                dependency(markerCallp, completep, false);
                scopep->addBlocksp(markerp);
                otherp->addStmtsp(markerCallp->makeStmt());
            }

            // Only the graph is a schedule. Leave the now-unused dispatch,
            // evaluate and MTask functions for the dead-code pass; other
            // references may still exist while scheduling is in flight.
            if (kernel.m_graphp) {
                if (kernel.m_graphp->backp()) kernel.m_graphp->unlinkFrBack();
                VL_DO_DANGLING(kernel.m_graphp->deleteTree(), kernel.m_graphp);
            }
        }

        batchp->addStmtsp(computep);
        for (AstNodeStmt* const tailp : tails) batchp->addStmtsp(tailp);
        AstAlways* const alwaysp
            = new AstAlways{flp, VAlwaysKwd::ALWAYS, nullptr, batchCallp->makeStmt()};
        logic.add({scopep, senp, alwaysp, {}});
        V3Stats::addStatSum("RepCut native batch, domains", kernels.size());
        V3Stats::addStatSum("RepCut native batch, dispatches", 1);
        if (m_serial) V3Stats::addStatSum("RepCut native batch, serial dispatches", 1);
    }

public:
    NativeBatch(AstNetlist* netlistp, const std::vector<V3Sched::ProcessList*>& logic,
                AstVarScope* trigVscp)
        : m_netlistp{netlistp}
        , m_trigVscp{trigVscp} {
        for (V3Sched::ProcessList* const lbsp : logic) {
            std::map<AstScope*, std::vector<Kernel>> kernels;
            std::map<std::pair<AstScope*, AstSenTree*>, std::vector<AstNodeProcedure*>>
                publications;
            for (const V3Sched::Process& process : *lbsp) {
                if (VN_IS(process.m_procp, AlwaysPost)) {
                    publications[{process.m_scopep, process.m_senTreep}].push_back(
                        process.m_procp);
                }
            }
            for (const V3Sched::Process& entry : *lbsp) {
                std::vector<Kernel> found;
                entry.m_procp->foreach([&](AstCCall* callp) {
                    if (!callp->funcp()->repcutNativeBatch()) return;
                    AstCFunc* const dispatchp = dispatchFunc(callp->funcp());
                    if (!dispatchp) return;
                    AstExecGraph* const graphp = m_serial ? nullptr : findGraph(dispatchp);
                    if (!m_serial && !graphp) return;
                    found.push_back({callp, entry.m_senTreep, lbsp->triggers(entry.m_senTreep),
                                     dispatchp, graphp,
                                     publications[{entry.m_scopep, entry.m_senTreep}]});
                });
                if (found.size() == 1) kernels[entry.m_scopep].push_back(found.front());
            }
            for (const auto& group : kernels) {
                if (group.second.size() > 1) combine(*lbsp, group.first, group.second);
            }
            // Drop emptied dispatches; the caller rebuilds trigger indices for retained processes.
            V3Sched::ProcessList retained;
            for (V3Sched::Process& process : *lbsp) {
                if (process.m_procp->stmtsp()) {
                    retained.add(std::move(process));
                } else {
                    m_deleter.pushDeletep(process.m_procp);
                }
            }
            *lbsp = std::move(retained);
        }
    }
};
}  // namespace

void batchNativeKernels(AstNetlist* netlistp, const std::vector<V3Sched::ProcessList*>& logic,
                        AstVarScope* trigVscp) {
    NativeBatch{netlistp, logic, trigVscp};
}
}  // namespace V3RepCut
