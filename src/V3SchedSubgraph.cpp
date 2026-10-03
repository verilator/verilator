// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Experimental subgraph scheduling helpers
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2003-2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
//
// Build a local scheduling plan from admitted boundaries. Child logic is
// removed before parent partitioning, ordered with the existing scheduler,
// and exposed as evaluation and publication operations. Receiver state is
// independent even when evaluation bodies are shared. Rejected boundaries
// restore receiver procedures for ordinary parent scheduling.
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3SchedSubgraph.h"

#include "V3SchedSubgraphInternal.h"
#include "V3Stats.h"
#include "V3SubgraphBoundary.h"

#include <map>
#include <set>
#include <unordered_map>
#include <unordered_set>

VL_DEFINE_DEBUG_FUNCTIONS;

namespace V3Sched {

namespace {

bool isLocalCombinationalStatement(const AstScope* boundaryScopep, AstNode* stmtp) {
    std::vector<AstNodeAssign*> assignments;
    if (!localCombinationalAssignments(stmtp, assignments)) return false;
    for (const AstNodeAssign* const assp : assignments) {
        const AstVarRef* const lhsp = V3SubgraphBoundary::writtenCombinationalVarRef(assp->lhsp());
        if (!lhsp || !isUnderScope(lhsp->varScopep()->scopep(), boundaryScopep)
            || lhsp->varp()->subgraphCaptured() || lhsp->varp()->subgraphPublished()) {
            return false;
        }
    }
    return true;
}

void splitBoundaryCombinationalLogic(AstNetlist* netlistp) {
    std::vector<std::pair<AstScope*, AstActive*>> actives;
    netlistp->foreach([&](AstScope* scopep) {
        AstScope* const boundaryScopep = findBoundaryScope(scopep);
        if (!boundaryScopep) return;
        scopep->foreach([&](AstActive* activep) {
            if (activep->sentreep()->hasCombo()) actives.emplace_back(scopep, activep);
        });
    });
    for (const auto& pair : actives) {
        AstScope* const scopep = pair.first;
        AstActive* const activep = pair.second;
        AstScope* const boundaryScopep = findBoundaryScope(scopep);
        if (!activep->stmtsp() || !activep->stmtsp()->nextp()) continue;
        std::vector<AstNode*> boundaryStatements;
        for (AstNode* stmtp = activep->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
            if (isPublishStatement(stmtp) || isBoundaryInputStatement(boundaryScopep, stmtp)
                || isLocalCombinationalStatement(boundaryScopep, stmtp)) {
                boundaryStatements.push_back(stmtp);
            }
        }
        for (AstNode* const stmtp : boundaryStatements) {
            AstActive* const separatep
                = new AstActive{stmtp->fileline(), "subgraph-boundary", activep->sentreep()};
            separatep->addStmtsp(stmtp->unlinkFrBack());
            scopep->addBlocksp(separatep);
        }
        if (!activep->stmtsp()) activep->unlinkFrBack()->deleteTree();
    }
}

SubgraphReceivers prepareSharedReceiverState(AstNetlist* netlistp) {
    SubgraphReceivers receivers;
    netlistp->foreach([&](AstScope* scopep) {
        if (AstScope* const implementationp = scopep->subgraphImplementationScopep()) {
            receivers[implementationp].push_back(scopep);
        }
    });
    uint64_t lateVarScopes = 0;
    for (const auto& entry : receivers) {
        AstScope* const implementationp = entry.first;
        for (AstScope* const receiverp : entry.second) {
            UASSERT_OBJ(receiverp->modp() == implementationp->modp(), receiverp,
                        "Subgraph receiver has a different specialization");
            std::unordered_set<const AstVar*> receiverVars;
            for (AstVarScope* vscp = receiverp->varsp(); vscp;
                 vscp = VN_AS(vscp->nextp(), VarScope)) {
                receiverVars.insert(vscp->varp());
            }
            for (AstVarScope* vscp = implementationp->varsp(); vscp;
                 vscp = VN_AS(vscp->nextp(), VarScope)) {
                if (!receiverVars.insert(vscp->varp()).second) continue;
                AstVarScope* const newp
                    = new AstVarScope{vscp->fileline(), receiverp, vscp->varp()};
                receiverp->addVarsp(newp);
                ++lateVarScopes;
            }
        }
    }
    V3Stats::addStat("Scheduling, Subgraph receiver late VarScopes", lateVarScopes);
    V3Stats::addStat("Scheduling, Subgraph receiver late VarScope bytes",
                     lateVarScopes * sizeof(AstVarScope));
    return receivers;
}

uint64_t materializeSharedReceiverLogic(const SubgraphReceivers& receivers,
                                        const std::unordered_set<AstScope*>& accepted) {
    uint64_t materialized = 0;
    for (const auto& entry : receivers) {
        AstScope* const implementationp = entry.first;
        const bool sharedClocked = accepted.count(implementationp);
        for (AstScope* const receiverp : entry.second) {
            std::unordered_map<const AstVar*, AstVarScope*> receiverVars;
            for (AstVarScope* vscp = receiverp->varsp(); vscp;
                 vscp = VN_AS(vscp->nextp(), VarScope)) {
                receiverVars.emplace(vscp->varp(), vscp);
            }
            for (AstNode* blockp = implementationp->blocksp(); blockp; blockp = blockp->nextp()) {
                AstActive* const activep = VN_CAST(blockp, Active);
                if (!activep || isPublishActive(activep)
                    || (activep->sentreep()->hasCombo()
                        && isBoundaryInputActive(implementationp, activep))) {
                    continue;
                }
                if (sharedClocked
                    && (activep->sentreep()->hasClocked() || activep->sentreep()->hasCombo())) {
                    continue;
                }
                AstActive* const clonep = activep->cloneTree(false);
                clonep->foreach([&](AstNodeVarRef* refp) {
                    AstVarScope* const vscp = refp->varScopep();
                    if (vscp->scopep() != implementationp) return;
                    const auto it = receiverVars.find(vscp->varp());
                    UASSERT_OBJ(it != receiverVars.end(), refp,
                                "Shared subgraph state missing from receiver scope");
                    refp->varScopep(it->second);
                });
                receiverp->addBlocksp(clonep);
                ++materialized;
            }
            if (!sharedClocked) receiverp->subgraphImplementationScopep(nullptr);
        }
    }
    V3Stats::addStat("Scheduling, Subgraph receiver actives", materialized);
    return materialized;
}

}  // namespace

struct SubgraphPlan::Impl final {
    struct Group final {
        AstScope* m_scopep = nullptr;  // Selected scheduling boundary
        AstVarScope* m_clockp = nullptr;  // Single rising-edge clock of this boundary
        std::vector<SubgraphCandidate::OutputBinding>
            m_outputs;  // Boundary output publication bindings
        std::unordered_set<const AstVar*>
            m_outputCombVars;  // Combinational variables needed to compute outputs
        std::vector<AstVarScope*> m_exposedOutputs;  // Internal values read outside the boundary
        AstSenTree* m_senTreep = nullptr;  // Clock sensitivity after trigger remapping
        LogicByScope m_clocked;  // Clocked procedures owned by this boundary
        LogicByScope m_comb;  // Combinational procedures owned by this boundary
        LogicByScope m_hybrid;  // Hybrid logic extracted during cycle breaking
        LogicRegions m_regions;  // Locally partitioned evaluation regions
        LogicReplicas m_replicas;  // Local logic replicated into evaluation regions
        std::vector<Use> m_uses;  // Variable effects of the representative boundary
        std::vector<AstScope*> m_receivers;  // Instances using the representative body
        std::vector<std::vector<Use>>
            m_receiverUses;  // Variable effects remapped to each receiver
    };

    AstSenTree* m_comboSenTreep = nullptr;  // Cached sensitivity for publication ordering
    std::vector<Group> m_groups;  // Admitted boundaries in deterministic scheduling order
    std::map<AstScope*, size_t> m_accepted;  // Group index for each admitted scope
};

SubgraphPlan::SubgraphPlan(AstNetlist* netlistp, const V3SubgraphBoundary& subgraphBoundary)
    : m_impl{new Impl} {
    if (!v3Global.opt.subgraphSchedule()) return;
    const SubgraphReceivers sharedReceivers = prepareSharedReceiverState(netlistp);
    splitBoundaryCombinationalLogic(netlistp);

    std::vector<SubgraphCandidate> candidates
        = analyzeSubgraphs(netlistp, subgraphBoundary, sharedReceivers);

    uint64_t rejected = 0;
    uint64_t clocked = 0;
    uint64_t combinational = 0;
    uint64_t acceptedInstances = 0;
    std::unordered_set<AstScope*> acceptedScopes;
    for (SubgraphCandidate& candidate : candidates) {
        if (!candidate.m_rejection.empty()) {
            ++rejected;
            FileLine* const flp = candidate.m_rejectionFilelinep
                                      ? candidate.m_rejectionFilelinep
                                      : candidate.m_scopep->modp()->fileline();
            const auto warnFallback = [&](AstScope* const scopep) {
                flp->v3warn(SUBGRAPHFALLBACK, "Subgraph " << scopep->prettyNameQ()
                                                          << " fell back to parent scheduling: "
                                                          << candidate.m_rejection);
            };
            warnFallback(candidate.m_scopep);
            const auto receivers = sharedReceivers.find(candidate.m_scopep);
            if (receivers != sharedReceivers.end()) {
                for (AstScope* const receiverp : receivers->second) warnFallback(receiverp);
            }
            UINFO(4, "Subgraph early scheduling fallback for " << candidate.m_scopep->name()
                                                               << ": " << candidate.m_rejection);
            continue;
        }
        const size_t groupIndex = m_impl->m_groups.size();
        // Scope may omit an unconnected output in the representative or another
        // receiver. The shared post function needs a state slot in every receiver.
        for (SubgraphCandidate::OutputBinding& output : candidate.m_outputs) {
            const auto ensurePublished = [&](AstScope* scopep) {
                if (AstVarScope* const vscp = findVarScope(scopep, output.m_publishedVarp)) {
                    return vscp;
                }
                AstVarScope* const vscp = new AstVarScope{output.m_publishedVarp->fileline(),
                                                          scopep, output.m_publishedVarp};
                scopep->addVarsp(vscp);
                return vscp;
            };
            output.m_publishedp = ensurePublished(candidate.m_scopep);
            output.m_publishedVarp->subgraphSharedState(true);
            const auto receivers = sharedReceivers.find(candidate.m_scopep);
            if (receivers != sharedReceivers.end()) {
                for (AstScope* const receiverp : receivers->second) ensurePublished(receiverp);
            }
        }
        m_impl->m_groups.emplace_back();
        Impl::Group& group = m_impl->m_groups[groupIndex];
        group.m_scopep = candidate.m_scopep;
        group.m_clockp = candidate.m_clockp;
        group.m_outputs = std::move(candidate.m_outputs);
        group.m_outputCombVars = std::move(candidate.m_outputCombVars);
        group.m_exposedOutputs = std::move(candidate.m_exposedOutputs);
        m_impl->m_accepted.emplace(candidate.m_scopep, groupIndex);
        acceptedScopes.insert(candidate.m_scopep);
        const auto receivers = sharedReceivers.find(candidate.m_scopep);
        if (receivers != sharedReceivers.end()) group.m_receivers = receivers->second;
        acceptedInstances += 1 + group.m_receivers.size();
        clocked += candidate.m_clocked.size();
        combinational += candidate.m_comb.size();
    }
    materializeSharedReceiverLogic(sharedReceivers, acceptedScopes);
    V3Stats::addStat("Scheduling, Subgraph early candidates", candidates.size());
    V3Stats::addStat("Scheduling, Subgraph early groups", acceptedInstances);
    V3Stats::addStat("Scheduling, Subgraph early fallbacks", rejected);
    V3Stats::addStat("Scheduling, Subgraph early clocked actives", clocked);
    V3Stats::addStat("Scheduling, Subgraph early combinational actives", combinational);
}

SubgraphPlan::~SubgraphPlan() = default;

bool SubgraphPlan::extract(AstScope* scopep, AstActive* activep) {
    if (isPublishActive(activep)) return false;
    AstScope* const boundaryScopep = findBoundaryScope(scopep);
    if (boundaryScopep && isBoundaryInputActive(boundaryScopep, activep)) return false;
    const auto it = m_impl->m_accepted.find(boundaryScopep);
    if (it == m_impl->m_accepted.end()) return false;
    Impl::Group& group = m_impl->m_groups[it->second];
    AstSenTree* const senTreep = activep->sentreep();
    if (senTreep->hasClocked()) {
        if (!group.m_senTreep) group.m_senTreep = senTreep;
        group.m_clocked.emplace_back(scopep, activep);
    } else if (senTreep->hasCombo()) {
        group.m_comb.emplace_back(scopep, activep);
    } else {
        return false;
    }
    return true;
}

bool SubgraphPlan::isAccepted(const AstScope* scopep) const {
    return m_impl->m_accepted.count(const_cast<AstScope*>(scopep));
}

bool SubgraphPlan::isOutputCombinational(const AstScope* scopep, const AstVar* varp) const {
    const auto it = m_impl->m_accepted.find(const_cast<AstScope*>(scopep));
    UASSERT_OBJ(it != m_impl->m_accepted.end(), scopep, "Missing early subgraph output cone");
    return m_impl->m_groups[it->second].m_outputCombVars.count(varp);
}

AstVarScope* SubgraphPlan::clockPort(const AstScope* scopep) const {
    const auto it = m_impl->m_accepted.find(const_cast<AstScope*>(scopep));
    UASSERT_OBJ(it != m_impl->m_accepted.end(), scopep, "Missing early subgraph clock");
    return m_impl->m_groups[it->second].m_clockp;
}

void SubgraphPlan::foreachPublished(const AstScope* scopep,
                                    const std::function<void(AstVarScope*)>& callback) const {
    const auto it = m_impl->m_accepted.find(const_cast<AstScope*>(scopep));
    UASSERT_OBJ(it != m_impl->m_accepted.end(), scopep, "Missing early subgraph outputs");
    for (const SubgraphCandidate::OutputBinding& output : m_impl->m_groups[it->second].m_outputs) {
        callback(output.m_publishedp);
    }
    for (AstVarScope* const vscp : m_impl->m_groups[it->second].m_exposedOutputs) callback(vscp);
}

void SubgraphPlan::appendPublications(AstNetlist* netlistp, const AstScope* scopep,
                                      LogicByScope& comb) const {
    const auto it = m_impl->m_accepted.find(const_cast<AstScope*>(scopep));
    UASSERT_OBJ(it != m_impl->m_accepted.end(), scopep, "Missing early subgraph outputs");
    // Look up the shared sensitivity once rather than once per local group.
    if (!m_impl->m_comboSenTreep) {
        for (AstSenTree* sentreep = netlistp->topScopep()->senTreesp(); sentreep;
             sentreep = VN_AS(sentreep->nextp(), SenTree)) {
            if (sentreep->hasCombo()) {
                m_impl->m_comboSenTreep = sentreep;
                break;
            }
        }
    }
    UASSERT_OBJ(m_impl->m_comboSenTreep, netlistp, "Missing combinational sensitivity");
    for (const SubgraphCandidate::OutputBinding& output : m_impl->m_groups[it->second].m_outputs) {
        FileLine* const flp = output.m_publishedp->fileline();
        AstAssignW* const assp
            = new AstAssignW{flp, new AstVarRef{flp, output.m_publishedp, VAccess::WRITE},
                             output.m_exprp->cloneTree(false)};
        comb.add(m_impl->m_groups[it->second].m_scopep, m_impl->m_comboSenTreep,
                 new AstAlways{assp});
    }
}

void SubgraphPlan::appendSettleLogic(AstNetlist* netlistp, LogicByScope& comb,
                                     const CovergroupRefBindings& cgRefBindings,
                                     V3Order::BoundaryUses& boundaryUses,
                                     std::vector<AstActive*>& temporaryActives) const {
    if (m_impl->m_groups.empty()) return;
    AstSenTree* comboSenTreep = nullptr;
    for (AstSenTree* sentreep = netlistp->topScopep()->senTreesp(); sentreep;
         sentreep = VN_AS(sentreep->nextp(), SenTree)) {
        if (sentreep->hasCombo()) {
            comboSenTreep = sentreep;
            break;
        }
    }
    UASSERT_OBJ(comboSenTreep, netlistp, "Missing combinational sensitivity");
    FileLine* const triggerFlp = netlistp->fileline();
    AstSenTree* const localTriggerp = new AstSenTree{
        triggerFlp,
        new AstSenItem{triggerFlp, VEdgeType::ET_TRUE,
                       new AstVarRef{triggerFlp, netlistp->stlFirstIterationp(), VAccess::READ}}};
    netlistp->topScopep()->addSenTreesp(localTriggerp);
    uint64_t wrappers = 0;
    for (const Impl::Group& group : m_impl->m_groups) {
        const auto isOutputCone = [&](AstActive* const activep) {
            std::vector<AstNodeAssign*> assignments;
            UASSERT_OBJ(localCombinationalAssignments(activep->stmtsp(), assignments), activep,
                        "Accepted child combinational procedure changed shape");
            for (const AstNodeAssign* const assp : assignments) {
                const AstVarRef* const lhsp
                    = V3SubgraphBoundary::writtenCombinationalVarRef(assp->lhsp());
                UASSERT_OBJ(lhsp, assp, "Accepted child combinational writer changed");
                if (group.m_outputCombVars.count(lhsp->varp())) return true;
            }
            return false;
        };
        LogicByScope outputComb;
        for (const auto& pair : group.m_comb) {
            if (isOutputCone(pair.second)) {
                outputComb.emplace_back(pair.first, pair.second->cloneTree(false));
            }
        }
        appendPublications(netlistp, group.m_scopep, outputComb);
        AstCFunc* const orderedp
            = outputComb.empty()
                  ? nullptr
                  : V3Order::order(
                        netlistp, {&outputComb}, {}, cgRefBindings,
                        "subgraph_settle_" + cvtToStr(wrappers), false, true,
                        [localTriggerp](const AstVarScope*, std::vector<AstSenTree*>& out) {
                            out.push_back(localTriggerp);
                        },
                        group.m_scopep);
        FileLine* const flp = group.m_scopep->fileline();
        AstCFunc* const funcp
            = new AstCFunc{flp, "_eval_subgraph_settle_" + cvtToStr(wrappers), group.m_scopep};
        funcp->isLoose(true);
        funcp->isConst(false);
        funcp->declPrivate(true);
        funcp->slow(true);
        funcp->subgraphWrapper(true);
        funcp->subgraphShareable(true);
        group.m_scopep->addBlocksp(funcp);
        util::newArgument(funcp, netlistp->findBitDType(), "__VfirstIteration", VDirection::INPUT);
        if (orderedp) {
            orderedp->subgraphShareable(true);
            AstCCall* const callp = new AstCCall{flp, orderedp};
            callp->dtypeSetVoid();
            funcp->addStmtsp(callp->makeStmt());
        }
        V3Order::BoundaryContract contract;
        foreachPublished(group.m_scopep,
                         [&](AstVarScope* vscp) { contract.m_ports.push_back(vscp); });
        UASSERT_OBJ(boundaryUses.emplace(funcp, std::move(contract)).second, funcp,
                    "Duplicate settle boundary contract");
        const auto appendCall = [&](AstScope* scopep) {
            AstActive* const activep = new AstActive{flp, "subgraph-settle", comboSenTreep};
            AstCCall* const callp = new AstCCall{flp, funcp};
            callp->dtypeSetVoid();
            callp->addArgsp(new AstVarRef{flp, netlistp->stlFirstIterationp(), VAccess::READ});
            if (scopep != group.m_scopep) callp->subgraphReceiverScopep(scopep);
            activep->addStmtsp(new AstAlways{flp, VAlwaysKwd::ALWAYS, nullptr, callp->makeStmt()});
            comb.emplace_back(scopep, activep);
            temporaryActives.push_back(activep);
            ++wrappers;
        };
        appendCall(group.m_scopep);
        for (AstScope* const receiverp : group.m_receivers) { appendCall(receiverp); }
    }
    V3Stats::addStat("Scheduling, Subgraph settle wrappers", wrappers);
}

bool SubgraphPlan::hasAccepted() const { return !m_impl->m_groups.empty(); }

AstCFunc* SubgraphPlan::appendIcoLogic(AstNetlist* netlistp, AstCFunc* icoFuncp,
                                       AstSenTree* triggerp,
                                       const CovergroupRefBindings& cgRefBindings) const {
    if (m_impl->m_groups.empty()) return icoFuncp;
    if (!icoFuncp) {
        AstScope* const scopep = netlistp->topScopep()->scopep();
        icoFuncp = new AstCFunc{scopep->fileline(), "_eval_ico_subgraphs", scopep};
        icoFuncp->isLoose(true);
        icoFuncp->isConst(false);
        icoFuncp->declPrivate(true);
        scopep->addBlocksp(icoFuncp);
    }
    unsigned index = 0;
    for (const Impl::Group& group : m_impl->m_groups) {
        LogicByScope childComb;
        for (const auto& pair : group.m_comb) {
            childComb.emplace_back(pair.first, pair.second->cloneTree(false));
        }
        if (childComb.empty()) continue;
        AstCFunc* const orderedp = V3Order::order(
            netlistp, {&childComb}, {}, cgRefBindings, "subgraph_ico_" + cvtToStr(index), false,
            false,
            [triggerp](const AstVarScope*, std::vector<AstSenTree*>& out) {
                out.push_back(triggerp);
            },
            group.m_scopep);
        UASSERT_OBJ(orderedp, group.m_scopep, "Missing child combinational schedule");
        FileLine* const flp = group.m_scopep->fileline();
        AstCFunc* const wrapperp
            = new AstCFunc{flp, "_eval_subgraph_ico_" + cvtToStr(index++), group.m_scopep};
        wrapperp->isLoose(true);
        wrapperp->isConst(false);
        wrapperp->declPrivate(true);
        wrapperp->subgraphWrapper(true);
        wrapperp->subgraphShareable(true);
        orderedp->subgraphShareable(true);
        group.m_scopep->addBlocksp(wrapperp);
        AstCCall* const localCallp = new AstCCall{flp, orderedp};
        localCallp->dtypeSetVoid();
        wrapperp->addStmtsp(localCallp->makeStmt());
        const auto appendCall = [&](AstScope* receiverp) {
            AstCCall* const callp = new AstCCall{flp, wrapperp};
            callp->dtypeSetVoid();
            if (receiverp != group.m_scopep) callp->subgraphReceiverScopep(receiverp);
            icoFuncp->addStmtsp(callp->makeStmt());
        };
        appendCall(group.m_scopep);
        for (AstScope* const receiverp : group.m_receivers) appendCall(receiverp);
    }
    return icoFuncp;
}

void SubgraphPlan::movePublications(LogicByScope& comb, LogicByScope& hybrid) {
    const auto remove = [&](LogicByScope& lbs) {
        const auto newEnd = std::remove_if(lbs.begin(), lbs.end(), [&](const auto& pair) {
            if (!isPublishActive(pair.second)) return false;
            AstScope* const boundaryScopep = findBoundaryScope(pair.first);
            if (!boundaryScopep) return false;
            AstScope* const implementationp = boundaryScopep->subgraphImplementationScopep()
                                                  ? boundaryScopep->subgraphImplementationScopep()
                                                  : boundaryScopep;
            if (!m_impl->m_accepted.count(implementationp)) return false;
            pair.second->unlinkFrBack()->deleteTree();
            return true;
        });
        lbs.erase(newEnd, lbs.end());
    };
    remove(comb);
    remove(hybrid);
}

void SubgraphPlan::partitionAndReplicate() {
    for (Impl::Group& group : m_impl->m_groups) {
        LogicByScope emptyComb;
        group.m_regions = V3Sched::partition(group.m_clocked, emptyComb, group.m_hybrid);
        UASSERT_OBJ(group.m_regions.m_pre.empty() && group.m_regions.m_act.empty(), group.m_scopep,
                    "Early subgraph unexpectedly requires the Active region");
        group.m_replicas = replicateLogic(group.m_regions);
        UASSERT_OBJ(group.m_replicas.m_ico.empty() && group.m_replicas.m_act.empty()
                        && group.m_replicas.m_obs.empty() && group.m_replicas.m_react.empty(),
                    group.m_scopep, "Early subgraph unexpectedly requires a non-NBA replica");
        for (const SubgraphCandidate::OutputBinding& output : group.m_outputs) {
            group.m_uses.emplace_back(Use{output.m_publishedp, false, true});
        }
        for (AstVarScope* const vscp : group.m_exposedOutputs) {
            group.m_uses.emplace_back(Use{vscp, false, true});
        }
        for (AstScope* const receiverp : group.m_receivers) {
            std::unordered_map<const AstVar*, AstVarScope*> receiverVars;
            for (AstVarScope* vscp = receiverp->varsp(); vscp;
                 vscp = VN_AS(vscp->nextp(), VarScope)) {
                receiverVars.emplace(vscp->varp(), vscp);
            }
            std::vector<Use> uses;
            uses.reserve(group.m_uses.size());
            for (const Use& use : group.m_uses) {
                AstVarScope* vscp = use.m_vscp;
                if (vscp->scopep() == group.m_scopep) {
                    const auto it = receiverVars.find(vscp->varp());
                    UASSERT_OBJ(it != receiverVars.end(), receiverp,
                                "Shared subgraph state missing from receiver scope");
                    vscp = it->second;
                }
                uses.emplace_back(Use{vscp, use.m_read, use.m_write});
            }
            group.m_receiverUses.emplace_back(std::move(uses));
        }
    }
    uint64_t portWrites = 0;
    for (const Impl::Group& group : m_impl->m_groups) portWrites += group.m_uses.size();
    V3Stats::addStat("Scheduling, Subgraph boundary output ports", portWrites);
}

void SubgraphPlan::foreachBoundary(
    const std::function<void(AstScope*, AstSenTree*, const std::vector<Use>&)>& callback) const {
    for (const Impl::Group& group : m_impl->m_groups) {
        UASSERT_OBJ(group.m_senTreep, group.m_scopep, "Missing subgraph clocked sensitivity");
        callback(group.m_scopep, group.m_senTreep, group.m_uses);
        for (size_t i = 0; i < group.m_receivers.size(); ++i) {
            callback(group.m_receivers[i], group.m_senTreep, group.m_receiverUses[i]);
        }
    }
}

void SubgraphPlan::materializeNba(
    const std::unordered_map<const AstSenTree*, AstSenTree*>& senTreeMap,
    const std::vector<LogicByScope*>& parentLogic) {
    LogicByScope* const defaultOwnerp = parentLogic.front();
    for (Impl::Group& group : m_impl->m_groups) {
        const auto append = [&](LogicByScope& lbs) {
            for (const auto& pair : lbs) {
                AstActive* const activep = pair.second;
                if (!activep->sentreep()->hasCombo()) {
                    activep->sentreep(senTreeMap.at(activep->sentreep()));
                }
                defaultOwnerp->emplace_back(pair);
            }
            lbs.clear();
        };
        append(group.m_regions.m_nba);
        append(group.m_replicas.m_nba);
        append(group.m_comb);
    }
}

void SubgraphPlan::clearOutputExpressions() {
    // Publication generation has finished. These detached expressions must be
    // deleted before the global AST reachability check runs.
    for (Impl::Group& group : m_impl->m_groups) {
        for (SubgraphCandidate::OutputBinding& output : group.m_outputs) {
            output.m_exprp.reset();
        }
    }
}

void SubgraphPlan::foreachUse(const std::function<void(const Use&)>& callback) const {
    for (const Impl::Group& group : m_impl->m_groups) {
        for (const Use& use : group.m_uses) callback(use);
        for (const std::vector<Use>& uses : group.m_receiverUses) {
            for (const Use& use : uses) callback(use);
        }
    }
}

}  // namespace V3Sched
