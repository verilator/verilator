// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Subgraph NBA evaluation and publication
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
// Lower admitted child NBA transactions into locally ordered evaluation
// and publication functions. Bind compatible bodies to per-instance state,
// preserve old-input acquisition, and expose phase/port contracts to Order.
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

struct SubgraphGroup final {
    struct Capture final {
        AstVarScope* m_sourcep = nullptr;  // External value sampled on the clock edge
        AstVarScope* m_savedp = nullptr;  // Per-instance storage holding the sampled value
    };
    AstScope* m_boundaryScopep = nullptr;  // Scope of this local NBA schedule
    AstSenTree* m_senTreep = nullptr;  // Clock sensitivity after trigger remapping
    FileLine* m_filelinep = nullptr;  // Source location for generated operations
    LogicByScope* m_ownerp = nullptr;  // Parent logic list receiving generated operations
    LogicByScope m_preLogic;  // Next-state evaluation procedures
    LogicByScope m_postLogic;  // State commit and publication procedures
    LogicByScope m_combLogic;  // Local combinational procedures run after commit
    std::vector<Capture> m_captures;  // External values sampled before next-state evaluation
};

struct CaptureVars final {
    std::map<AstNodeModule*, std::map<AstVar*, std::vector<AstVar*>>>
        m_slots;  // Capture slots reusable across instances of a specialization
    std::map<AstNodeModule*, size_t> m_nextNameIndex;  // Next capture identifier per module
};

SubgraphGroup& findOrCreateGroup(std::vector<SubgraphGroup>& groups,
                                 std::map<AstScope*, size_t>& groupIndex, LogicByScope* ownerp,
                                 AstScope* boundaryScopep, FileLine* filelinep) {
    const auto inserted = groupIndex.emplace(boundaryScopep, groups.size());
    if (!inserted.second) return groups[inserted.first->second];
    groups.emplace_back();
    SubgraphGroup& group = groups.back();
    group.m_boundaryScopep = boundaryScopep;
    group.m_filelinep = filelinep;
    group.m_ownerp = ownerp;
    return group;
}

void addSubgraphLogic(SubgraphGroup& group, AstScope* scopep, AstActive* activep) {
    AstSenTree* const senTreep = activep->sentreep();
    if (!group.m_senTreep) group.m_senTreep = senTreep;

    for (AstNode *nodep = activep->stmtsp(), *nextp; nodep; nodep = nextp) {
        nextp = nodep->nextp();
        nodep->unlinkFrBack();
        LogicByScope& phaseLogic = VN_IS(nodep, AlwaysPost) ? group.m_postLogic : group.m_preLogic;
        phaseLogic.add(scopep, senTreep, nodep);
    }
    if (activep->backp()) activep->unlinkFrBack();
    activep->deleteTree();
}

void captureSubgraphInputs(SubgraphGroup& group, CaptureVars& savedVars) {
    AstScope* const boundaryScopep = group.m_boundaryScopep;
    std::map<AstVarScope*, AstVarScope*> savedScopes;
    std::map<AstVar*, size_t> sourceOccurrences;
    const auto rewrite = [&](LogicByScope& lbs) {
        lbs.foreachLogic([&](AstNode* nodep) {
            nodep->foreach([&](AstNodeVarRef* refp) {
                AstVarScope* const sourcep = refp->varScopep();
                const bool portInput
                    = sourcep->scopep() == boundaryScopep && sourcep->varp()->isNonOutput();
                const bool external = !isUnderScope(sourcep->scopep(), boundaryScopep);
                if (!refp->access().isReadOnly() || (!portInput && !external)) { return; }
                const auto inserted = savedScopes.emplace(sourcep, nullptr);
                if (inserted.second) {
                    AstVar* const sourceVarp = sourcep->varp();
                    AstNodeModule* const modp = boundaryScopep->modp();
                    const size_t occurrence = sourceOccurrences[sourceVarp]++;
                    std::vector<AstVar*>& slots = savedVars.m_slots[modp][sourceVarp];
                    if (slots.size() <= occurrence) slots.resize(occurrence + 1);
                    AstVar*& savedVarp = slots[occurrence];
                    if (!savedVarp) {
                        const string name
                            = "__VsubgraphCapture__" + cvtToStr(savedVars.m_nextNameIndex[modp]++);
                        savedVarp = new AstVar{sourcep->fileline(), VVarType::BLOCKTEMP, name,
                                               sourcep->dtypep()};
                        savedVarp->subgraphCaptured(true);
                        modp->addStmtsp(savedVarp);
                    }
                    UASSERT_OBJ(savedVarp->width() == sourcep->width(), sourcep,
                                "Capture slot has inconsistent widths across instances");
                    AstVarScope* const savedp
                        = new AstVarScope{sourcep->fileline(), boundaryScopep, savedVarp};
                    boundaryScopep->addVarsp(savedp);
                    inserted.first->second = savedp;
                    group.m_captures.push_back({sourcep, savedp});
                }
                AstVarScope* const savedp = inserted.first->second;
                refp->varScopep(savedp);
                refp->varp(savedp->varp());
            });
        });
    };
    // NBA right-hand sides are evaluated in the pre phase. Post-phase reads must
    // retain their normal commit-time semantics rather than being silently
    // sampled early.
    rewrite(group.m_preLogic);

    for (const SubgraphGroup::Capture& capture : group.m_captures) {
        FileLine* const flp = capture.m_sourcep->fileline();
        AstActive* const activep = new AstActive{flp, "subgraph-capture", group.m_senTreep};
        activep->addStmtsp(
            new AstAlways{flp, VAlwaysKwd::ALWAYS, nullptr,
                          new AstAssign{flp, new AstVarRef{flp, capture.m_savedp, VAccess::WRITE},
                                        new AstVarRef{flp, capture.m_sourcep, VAccess::READ}}});
        group.m_ownerp->emplace_back(boundaryScopep, activep);
    }
}

}  // namespace

static bool sameReceiverLogic(const LogicByScope& representative, const LogicByScope& candidate,
                              AstScope* representativeScopep, AstScope* candidateScopep) {
    if (representative.size() != candidate.size()) return false;
    std::map<const AstVar*, AstVarScope*> representativeVars;
    for (AstVarScope* vscp = representativeScopep->varsp(); vscp;
         vscp = VN_AS(vscp->nextp(), VarScope)) {
        representativeVars.emplace(vscp->varp(), vscp);
    }
    for (size_t i = 0; i < representative.size(); ++i) {
        const auto& source = representative[i];
        const auto& target = candidate[i];
        if (source.first != representativeScopep || target.first != candidateScopep
            || !source.second->sentreep()->sameTree(target.second->sentreep())) {
            return false;
        }
        AstNode* const sourcep = source.second->stmtsp();
        AstNode* const targetp = target.second->stmtsp();
        if (!sourcep || !targetp) {
            if (sourcep != targetp) return false;
            continue;
        }
        AstNode* const clonedp = targetp->cloneTree(true);
        bool compatible = true;
        clonedp->foreachAndNext([&](AstNode* nodep) {
            if (VN_IS(nodep, NodeCCall) || VN_IS(nodep, NodeFTaskRef) || VN_IS(nodep, ScopeName)
                || VN_IS(nodep, VarXRef) || VN_IS(nodep, CExpr) || VN_IS(nodep, CExprUser)
                || VN_IS(nodep, CStmt) || VN_IS(nodep, CStmtUser)) {
                compatible = false;
            }
            if (AstVarRef* const refp = VN_CAST(nodep, VarRef)) {
                if (refp->varScopep()->scopep() != candidateScopep) return;
                const auto it = representativeVars.find(refp->varp());
                if (it == representativeVars.end()) {
                    compatible = false;
                } else {
                    refp->varScopep(it->second);
                }
            }
        });
        if (compatible) compatible = sourcep->sameTree(clonedp);
        clonedp->deleteTree();
        if (!compatible) return false;
    }
    return true;
}

static bool sameReceiverGroup(const SubgraphGroup& representative,
                              const SubgraphGroup& candidate) {
    if (representative.m_boundaryScopep->modp() != candidate.m_boundaryScopep->modp()
        || !representative.m_senTreep || !candidate.m_senTreep
        || !representative.m_senTreep->sameTree(candidate.m_senTreep)) {
        return false;
    }
    return sameReceiverLogic(representative.m_preLogic, candidate.m_preLogic,
                             representative.m_boundaryScopep, candidate.m_boundaryScopep)
           && sameReceiverLogic(representative.m_postLogic, candidate.m_postLogic,
                                representative.m_boundaryScopep, candidate.m_boundaryScopep)
           && sameReceiverLogic(representative.m_combLogic, candidate.m_combLogic,
                                representative.m_boundaryScopep, candidate.m_boundaryScopep);
}

static void deleteCombinationalLogic(SubgraphGroup& group) {
    LogicByScope& logic = group.m_combLogic;
    for (const auto& pair : logic) {
        if (pair.second->backp()) pair.second->unlinkFrBack();
        pair.second->deleteTree();
    }
    group.m_combLogic.clear();
}

namespace {

// Order admitted NBA transactions and bind their shared bodies to receivers.
// Parent logic owns input acquisition; explicit contracts expose only ports
// and evaluation/publication phases to the parent Order graph.
class SubgraphNbaBuilder final {
    AstNetlist* const m_netlistp;  // Netlist receiving generated functions
    const V3Order::TrigToSenMap& m_trigToSen;  // Original sensitivities for each trigger
    const CovergroupRefBindings& m_cgRefBindings;  // Covergroup reference bindings for local Order
    const bool m_slow;  // Generate cold evaluation functions
    const V3Order::ExternalDomainsProvider&
        m_externalDomains;  // Parent provider for external trigger domains
    const SubgraphPlan& m_plan;  // Admitted local scheduling plan
    V3Order::BoundaryUses& m_boundaryUses;  // Parent-visible contracts for generated functions
    V3Order::FreshReads m_freshReads;  // Edge captures that must precede local evaluation
    std::vector<SubgraphGroup> m_groups;  // Admitted boundaries in deterministic scheduling order
    SubgraphReceivers m_sharedReceivers;  // Receiver scopes indexed by their representative
    std::map<AstNodeModule*, unsigned>
        m_groupsByModule;  // Number of local groups per specialization
    std::vector<size_t> m_representative;  // Representative group index for each local group
    std::vector<std::array<AstCFunc*, 2>>
        m_orderedFunctions;  // Ordered evaluation and publication functions per group
    std::vector<bool>
        m_sharedRepresentative;  // Groups whose functions need receiver-relative state
    CaptureVars m_savedVars;  // Capture storage allocated during lowering
    uint64_t m_orderedLogic = 0;  // Number of locally ordered procedures
    uint64_t m_orderedNextState = 0;  // Number of locally ordered next-state procedures
    uint64_t m_shareableFunctions = 0;  // Number of generated receiver-relative functions
    uint64_t m_sharedOrderSkips = 0;  // Repeated Order calls avoided through sharing
    uint64_t m_directReceivers = 0;  // Receiver calls emitted without forwarding functions

    void collectGroups(const std::vector<LogicByScope*>& logic) {
        std::map<AstScope*, size_t> groupByScope;
        for (LogicByScope* const lbsp : logic) {
            LogicByScope parentLogic;
            parentLogic.reserve(lbsp->size());
            for (const auto& pair : *lbsp) {
                AstScope* const scopep = pair.first;
                AstActive* const activep = pair.second;
                AstScope* const boundaryScopep = findBoundaryScope(scopep);
                // Region partitioning remaps sensitivities, so recognize port logic by
                // its statement instead of the original combinational sensitivity.
                if (!boundaryScopep || !m_plan.isAccepted(boundaryScopep)
                    || isBoundaryInputStatement(boundaryScopep, activep->stmtsp())
                    || isPublishStatement(activep->stmtsp())) {
                    parentLogic.emplace_back(pair);
                    continue;
                }
                SubgraphGroup& group = findOrCreateGroup(m_groups, groupByScope, lbsp,
                                                         boundaryScopep, activep->fileline());
                if (activep->sentreep()->hasCombo()) {
                    group.m_combLogic.emplace_back(scopep, activep);
                } else {
                    addSubgraphLogic(group, scopep, activep);
                }
            }
            *lbsp = std::move(parentLogic);
        }
    }

    void chooseRepresentatives() {
        m_netlistp->foreach([&](AstScope* scopep) {
            if (AstScope* const implementationp = scopep->subgraphImplementationScopep()) {
                m_sharedReceivers[implementationp].push_back(scopep);
            }
        });
        for (const SubgraphGroup& group : m_groups)
            ++m_groupsByModule[group.m_boundaryScopep->modp()];
        for (const auto& entry : m_sharedReceivers) {
            m_groupsByModule[entry.first->modp()] += entry.second.size();
        }
        m_representative.resize(m_groups.size());
        m_orderedFunctions.resize(m_groups.size());
        std::map<AstNodeModule*, size_t> firstByModule;
        for (size_t i = 0; i < m_groups.size(); ++i) {
            m_representative[i] = i;
            AstNodeModule* const modp = m_groups[i].m_boundaryScopep->modp();
            if (m_groupsByModule[modp] < 2) continue;
            const auto inserted = firstByModule.emplace(modp, i);
            if (!inserted.second
                && sameReceiverGroup(m_groups[inserted.first->second], m_groups[i])) {
                m_representative[i] = inserted.first->second;
            }
        }
        m_sharedRepresentative.assign(m_groups.size(), false);
        for (size_t i = 0; i < m_groups.size(); ++i) {
            if (m_representative[i] != i) m_sharedRepresentative[m_representative[i]] = true;
            if (m_sharedReceivers.count(m_groups[i].m_boundaryScopep))
                m_sharedRepresentative[i] = true;
        }
    }

    void orderPhase(SubgraphGroup& group, size_t groupIndex, bool post) {
        LogicByScope& phaseLogic = post ? group.m_postLogic : group.m_preLogic;
        const string phase = post ? "post" : "pre";

        if (phaseLogic.empty()) return;
        AstSenTree* const phaseSenTreep = phaseLogic.front().second->sentreep();
        std::unordered_set<const AstVarScope*> combinationalReads;
        for (const auto& pair : group.m_combLogic) {
            pair.second->foreach([&](const AstNodeVarRef* refp) {
                if (refp->access().isReadOrRW()) { combinationalReads.insert(refp->varScopep()); }
            });
        }
        const V3Order::ExternalDomainsProvider localDomains
            = [&](const AstVarScope* vscp, std::vector<AstSenTree*>& out) {
                  m_externalDomains(vscp, out);
                  if (combinationalReads.count(vscp)) out.push_back(phaseSenTreep);
              };
        V3Order::BoundaryContract contract;
        std::unordered_set<AstVarScope*> seenPorts;
        const auto addPort = [&](AstVarScope* vscp) {
            if (seenPorts.insert(vscp).second) contract.m_ports.push_back(vscp);
        };
        contract.m_operation = post ? V3Order::BoundaryContract::Operation::PUBLISH
                                    : V3Order::BoundaryContract::Operation::CLOCK_EVAL;
        contract.m_clockp = m_plan.clockPort(group.m_boundaryScopep);
        if (post) { m_plan.foreachPublished(group.m_boundaryScopep, addPort); }
        if (!post) {
            for (const auto& pair : group.m_combLogic) {
                pair.second->foreach([&](AstNodeVarRef* refp) {
                    AstVarScope* const vscp = refp->varScopep();
                    if (refp->access().isReadOrRW() && vscp->scopep() == group.m_boundaryScopep
                        && vscp->varp()->isInput()) {
                        addPort(vscp);
                    }
                });
            }
        }
        const bool mayShare
            = m_groupsByModule[group.m_boundaryScopep->modp()] > 1
              && std::all_of(phaseLogic.begin(), phaseLogic.end(), [&](const auto& pair) {
                     return pair.first == group.m_boundaryScopep;
                 });
        std::unordered_set<AstCFunc*> oldFunctions;
        if (mayShare) {
            for (AstNode* blockp = group.m_boundaryScopep->blocksp(); blockp;
                 blockp = blockp->nextp()) {
                if (AstCFunc* const cfuncp = VN_CAST(blockp, CFunc)) {
                    oldFunctions.insert(cfuncp);
                }
            }
        }
        AstCFunc* funcp = nullptr;
        if (m_representative[groupIndex] != groupIndex) {
            funcp = m_orderedFunctions[m_representative[groupIndex]][post];
            UASSERT_OBJ(funcp, group.m_boundaryScopep,
                        "Shared subgraph has no representative function");
            for (const auto& pair : phaseLogic) pair.second->deleteTree();
            phaseLogic.clear();
            if (!post) {
                for (const auto& pair : group.m_combLogic) {
                    if (pair.second->backp()) pair.second->unlinkFrBack();
                    pair.second->deleteTree();
                }
                group.m_combLogic.clear();
            }
            ++m_sharedOrderSkips;
        } else {
            const string tag = "nba_subgraph_" + phase + "_" + cvtToStr(groupIndex);
            funcp = V3Order::order(m_netlistp, {&phaseLogic}, m_trigToSen, m_cgRefBindings, tag,
                                   false, m_slow, localDomains, group.m_boundaryScopep);
            if (!funcp) return;
            if (post) {
                LogicByScope postComb;
                for (const auto& pair : group.m_combLogic) {
                    std::vector<AstNodeAssign*> assignments;
                    UASSERT_OBJ(localCombinationalAssignments(pair.second->stmtsp(), assignments),
                                pair.second, "Accepted child combinational procedure changed");
                    bool outputCone = false;
                    for (const AstNodeAssign* const assp : assignments) {
                        const AstVarRef* const lhsp
                            = V3SubgraphBoundary::writtenCombinationalVarRef(assp->lhsp());
                        UASSERT_OBJ(lhsp, assp, "Accepted child combinational writer changed");
                        if (m_plan.isOutputCombinational(group.m_boundaryScopep, lhsp->varp())) {
                            outputCone = true;
                        }
                    }
                    if (!outputCone) continue;
                    postComb.emplace_back(pair.first, pair.second->cloneTree(false));
                }
                // Order publication with output expressions so values derived from
                // a published port are refreshed after that port.
                m_plan.appendPublications(m_netlistp, group.m_boundaryScopep, postComb);
                if (!postComb.empty()) {
                    AstCFunc* const combinationalp = V3Order::order(
                        m_netlistp, {&postComb}, m_trigToSen, m_cgRefBindings,
                        "nba_subgraph_comb_post_" + cvtToStr(groupIndex), false, m_slow,
                        [phaseSenTreep](const AstVarScope*, std::vector<AstSenTree*>& out) {
                            out.push_back(phaseSenTreep);
                        },
                        group.m_boundaryScopep);
                    UASSERT_OBJ(combinationalp, group.m_boundaryScopep,
                                "Missing scheduled subgraph output cone");
                    AstCCall* const callp = new AstCCall{group.m_filelinep, combinationalp};
                    callp->dtypeSetVoid();
                    funcp->addStmtsp(callp->makeStmt());
                }
            }
            funcp->subgraphWrapper(true);
            if (m_sharedRepresentative[groupIndex]) {
                funcp->subgraphShareable(true);
                ++m_shareableFunctions;
            }
            util::splitCheck(funcp);
            m_orderedFunctions[groupIndex][post] = funcp;
            UASSERT_OBJ(m_boundaryUses.emplace(funcp, std::move(contract)).second, funcp,
                        "Duplicate subgraph boundary contract");
        }
        if (mayShare && m_representative[groupIndex] == groupIndex) {
            for (AstNode* blockp = group.m_boundaryScopep->blocksp(); blockp;
                 blockp = blockp->nextp()) {
                AstCFunc* const cfuncp = VN_CAST(blockp, CFunc);
                if (!cfuncp || oldFunctions.count(cfuncp)) continue;
                bool hasInstanceContext = false;
                cfuncp->foreach([&](AstNode* nodep) {
                    if (VN_IS(nodep, NodeCCall) || VN_IS(nodep, NodeFTaskRef)
                        || VN_IS(nodep, CExpr) || VN_IS(nodep, CExprUser) || VN_IS(nodep, CStmt)
                        || VN_IS(nodep, CStmtUser) || VN_IS(nodep, ScopeName)
                        || VN_IS(nodep, VarXRef)) {
                        hasInstanceContext = true;
                    }
                });
                if (hasInstanceContext) continue;
                cfuncp->dontCombine(false);
                cfuncp->subgraphShareable(true);
                ++m_shareableFunctions;
            }
        }

        AstActive* const wrapperp = new AstActive{group.m_filelinep, "subgraph", group.m_senTreep};
        AstCCall* const callp = new AstCCall{group.m_filelinep, funcp};
        callp->dtypeSetVoid();
        if (m_representative[groupIndex] != groupIndex) {
            callp->subgraphReceiverScopep(group.m_boundaryScopep);
        }
        if (post) {
            AstAlwaysPost* const postp = new AstAlwaysPost{group.m_filelinep};
            postp->addStmtsp(callp->makeStmt());
            wrapperp->addStmtsp(postp);
        } else {
            wrapperp->addStmtsp(callp->makeStmt());
        }
        group.m_ownerp->emplace_back(group.m_boundaryScopep, wrapperp);
    }

    void orderGroup(SubgraphGroup& group, size_t groupIndex) {

        m_orderedLogic += group.m_preLogic.size() + group.m_postLogic.size();
        m_orderedNextState += group.m_combLogic.size();
        UASSERT_OBJ(group.m_senTreep, group.m_boundaryScopep,
                    "Subgraph NBA logic has no clocked sensitivity");
        captureSubgraphInputs(group, m_savedVars);
        for (const SubgraphGroup::Capture& capture : group.m_captures) {
            m_freshReads[group.m_boundaryScopep].push_back(capture.m_savedp);
        }
        // Inst may have acquired a connected input before Scope shared the child
        // procedure. Those slots are also fresh on this edge, for every receiver.
        const auto addCapturedPorts = [&](AstScope* scopep) {
            for (AstVarScope* vscp = scopep->varsp(); vscp;
                 vscp = VN_AS(vscp->nextp(), VarScope)) {
                if (!vscp->varp()->subgraphCaptured()) continue;
                std::vector<AstVarScope*>& reads = m_freshReads[scopep];
                if (std::find(reads.begin(), reads.end(), vscp) == reads.end()) {
                    reads.push_back(vscp);
                }
            }
        };
        addCapturedPorts(group.m_boundaryScopep);
        const auto receivers = m_sharedReceivers.find(group.m_boundaryScopep);
        if (receivers != m_sharedReceivers.end()) {
            for (AstScope* const receiverp : receivers->second) addCapturedPorts(receiverp);
        }

        orderPhase(group, groupIndex, false);
        orderPhase(group, groupIndex, true);
        deleteCombinationalLogic(group);
    }

    void appendReceiverCalls() {
        for (size_t i = 0; i < m_groups.size(); ++i) {
            const SubgraphGroup& group = m_groups[i];
            const auto receivers = m_sharedReceivers.find(group.m_boundaryScopep);
            if (receivers == m_sharedReceivers.end()) continue;
            for (AstScope* const receiverp : receivers->second) {
                for (bool post : {false, true}) {
                    AstCFunc* const funcp = m_orderedFunctions[m_representative[i]][post];
                    if (!funcp) continue;
                    AstActive* const activep
                        = new AstActive{group.m_filelinep, "subgraph", group.m_senTreep};
                    AstCCall* const callp = new AstCCall{group.m_filelinep, funcp};
                    callp->dtypeSetVoid();
                    callp->subgraphReceiverScopep(receiverp);
                    if (post) {
                        AstAlwaysPost* const postp = new AstAlwaysPost{group.m_filelinep};
                        postp->addStmtsp(callp->makeStmt());
                        activep->addStmtsp(postp);
                    } else {
                        activep->addStmtsp(callp->makeStmt());
                    }
                    group.m_ownerp->emplace_back(receiverp, activep);
                    ++m_sharedOrderSkips;
                }
                receiverp->subgraphImplementationScopep(nullptr);
                ++m_directReceivers;
            }
        }
    }

    void recordStats() const {
        V3Stats::addStat("Scheduling, Subgraph NBA groups", m_groups.size() + m_directReceivers);
        V3Stats::addStat("Scheduling, Subgraph NBA internal actives", m_orderedLogic);
        V3Stats::addStat("Scheduling, Subgraph local next-state actives", m_orderedNextState);
        V3Stats::addStat("Scheduling, Subgraph shareable CFuncs", m_shareableFunctions);
        V3Stats::addStat("Scheduling, Subgraph shared Order skips", m_sharedOrderSkips);
        uint64_t contractUses = 0;
        for (const auto& entry : m_boundaryUses) { contractUses += entry.second.m_ports.size(); }
        V3Stats::addStat("Scheduling, Subgraph boundary contract uses", contractUses);
        uint64_t capturedInputs = 0;
        for (const auto& pair : m_freshReads) capturedInputs += pair.second.size();
        V3Stats::addStat("Scheduling, Subgraph captured inputs", capturedInputs);
    }

public:
    SubgraphNbaBuilder(AstNetlist* netlistp, const std::vector<LogicByScope*>& logic,
                       const V3Order::TrigToSenMap& trigToSen,
                       const CovergroupRefBindings& cgRefBindings, bool slow,
                       const V3Order::ExternalDomainsProvider& externalDomains,
                       const SubgraphPlan& plan, V3Order::BoundaryUses& boundaryUses)
        : m_netlistp{netlistp}
        , m_trigToSen{trigToSen}
        , m_cgRefBindings{cgRefBindings}
        , m_slow{slow}
        , m_externalDomains{externalDomains}
        , m_plan{plan}
        , m_boundaryUses{boundaryUses} {
        collectGroups(logic);
        chooseRepresentatives();
        for (size_t i = 0; i < m_groups.size(); ++i) orderGroup(m_groups[i], i);
        appendReceiverCalls();
        recordStats();
    }

    V3Order::FreshReads takeFreshReads() { return std::move(m_freshReads); }
};

}  // namespace

V3Order::FreshReads lowerSubgraphNbaLogic(AstNetlist* netlistp,
                                          const std::vector<LogicByScope*>& logic,
                                          const V3Order::TrigToSenMap& trigToSen,
                                          const CovergroupRefBindings& cgRefBindings, bool slow,
                                          const V3Order::ExternalDomainsProvider& externalDomains,
                                          const SubgraphPlan& plan,
                                          V3Order::BoundaryUses& boundaryUses) {
    if (!v3Global.opt.subgraphSchedule()) return {};
    return SubgraphNbaBuilder{netlistp, logic,           trigToSen, cgRefBindings,
                              slow,     externalDomains, plan,      boundaryUses}
        .takeFreshReads();
}

}  // namespace V3Sched
