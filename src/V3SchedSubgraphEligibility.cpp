// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Subgraph scheduling eligibility
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
// Check local scheduling eligibility before removing child logic from the
// parent. Admission follows transformed clock, write, call, output, and
// derived-clock dependencies. A rejection records its first RTL cause and
// leaves the original logic available to the ordinary scheduler.
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3SchedSubgraph.h"
#include "V3SchedSubgraphInternal.h"
#include "V3Stats.h"
#include "V3SubgraphBoundary.h"

#include <algorithm>
#include <map>
#include <set>
#include <unordered_map>
#include <unordered_set>

VL_DEFINE_DEBUG_FUNCTIONS;

namespace V3Sched {

bool isUnderScope(const AstScope* scopep, const AstScope* basep) {
    for (const AstScope* scanp = scopep; scanp; scanp = scanp->aboveScopep()) {
        if (scanp == basep) return true;
    }
    return false;
}

AstScope* findBoundaryScope(AstScope* scopep) {
    for (AstScope* scanp = scopep; scanp; scanp = scanp->aboveScopep()) {
        if (scanp->modp()->subgraphBoundary()) return scanp;
    }
    return nullptr;
}

AstVarScope* findVarScope(AstScope* scopep, const AstVar* varp) {
    for (AstVarScope* vscp = scopep->varsp(); vscp; vscp = VN_AS(vscp->nextp(), VarScope)) {
        if (vscp->varp() == varp) return vscp;
    }
    return nullptr;
}

bool isPublishStatement(const AstNode* stmtp) {
    const AstAlways* const alwaysp = VN_CAST(stmtp, Always);
    if (!alwaysp) return false;
    const AstAssignW* const assp = VN_CAST(alwaysp->stmtsp(), AssignW);
    if (!assp || assp->nextp()) return false;
    const AstVarRef* const lhsp = VN_CAST(assp->lhsp(), VarRef);
    return lhsp && lhsp->varp()->subgraphPublished();
}

bool isPublishActive(const AstActive* activep) {
    return activep->sentreep()->hasCombo() && activep->stmtsp() && !activep->stmtsp()->nextp()
           && isPublishStatement(activep->stmtsp());
}

// Port connections execute in the parent schedule even when Inst places them in
// the child scope. Their writes establish the input values observed by the
// local scheduler.
bool isBoundaryInputStatement(const AstScope* boundaryScopep, const AstNode* stmtp) {
    const AstAlways* const alwaysp = VN_CAST(stmtp, Always);
    if (!alwaysp) return false;
    const AstAssignW* const assp = VN_CAST(alwaysp->stmtsp(), AssignW);
    if (!assp || assp->nextp()) return false;
    const AstVarRef* const lhsp = VN_CAST(assp->lhsp(), VarRef);
    if (!lhsp || lhsp->varScopep()->scopep() != boundaryScopep || !lhsp->varp()->isNonOutput()
        || !lhsp->varp()->subgraphPortId()) {
        return false;
    }
    bool externalInputs = true;
    assp->rhsp()->foreach([&](const AstNodeVarRef* refp) {
        if (isUnderScope(refp->varScopep()->scopep(), boundaryScopep)) externalInputs = false;
    });
    return externalInputs;
}

bool isBoundaryInputActive(const AstScope* boundaryScopep, const AstActive* activep) {
    return activep->sentreep()->hasCombo() && activep->stmtsp() && !activep->stmtsp()->nextp()
           && isBoundaryInputStatement(boundaryScopep, activep->stmtsp());
}

// Keep the statements of one combinational procedure together. Order handles
// their dependencies on other procedures.
static AstNode* collectLocalAssignments(AstNode* stmtsp,
                                        std::vector<AstNodeAssign*>& assignments) {
    for (AstNode* nodep = stmtsp; nodep; nodep = nodep->nextp()) {
        if (VN_IS(nodep, Comment)) continue;
        if (AstNodeAssign* const assp = VN_CAST(nodep, NodeAssign)) {
            assignments.push_back(assp);
        } else if (AstIf* const ifp = VN_CAST(nodep, If)) {
            if (collectLocalAssignments(ifp->thensp(), assignments)) { return ifp; }
            if (collectLocalAssignments(ifp->elsesp(), assignments)) { return ifp; }
        } else if (AstBegin* const beginp = VN_CAST(nodep, Begin)) {
            if (AstNode* const problem = collectLocalAssignments(beginp->stmtsp(), assignments)) {
                return problem;
            }
        } else if (AstStmtExpr* const exprp = VN_CAST(nodep, StmtExpr)) {
            if (!VN_IS(exprp->exprp(), CCall)) return nodep;
        } else {
            return nodep;
        }
    }
    return nullptr;
}

bool localCombinationalAssignments(AstNode* stmtp, std::vector<AstNodeAssign*>& assignments,
                                   AstNode** problemp) {
    AstAlways* const alwaysp = VN_CAST(stmtp, Always);
    if (!alwaysp) {
        if (problemp) *problemp = stmtp;
        return false;
    }
    AstNode* const problem = collectLocalAssignments(alwaysp->stmtsp(), assignments);
    if (problemp) *problemp = problem ? problem : assignments.empty() ? alwaysp : nullptr;
    return !problem && !assignments.empty();
}

void SubgraphCandidate::ExprDeleter::operator()(AstNodeExpr* const exprp) const {
    if (exprp) exprp->deleteTree();
}

namespace {

// Reject read-before-write cycles within a child combinational procedure.
AstNode* checkDefiniteLocalWrites(AstNode* stmtsp,
                                  const std::unordered_set<AstVarScope*>& localWriters,
                                  std::unordered_set<AstVarScope*>& assigned) {
    for (AstNode* nodep = stmtsp; nodep; nodep = nodep->nextp()) {
        if (AstNodeAssign* const assp = VN_CAST(nodep, NodeAssign)) {
            AstNode* problem = nullptr;
            assp->rhsp()->foreach([&](AstNodeVarRef* refp) {
                if (!problem && refp->access().isReadOrRW()
                    && localWriters.count(refp->varScopep())
                    && !assigned.count(refp->varScopep())) {
                    problem = refp;
                }
            });
            if (problem) return assp->rhsp();
            if (const AstVarRef* const lhsp
                = V3SubgraphBoundary::writtenCombinationalVarRef(assp->lhsp())) {
                assigned.insert(lhsp->varScopep());
            }
        } else if (AstIf* const ifp = VN_CAST(nodep, If)) {
            if (!ifp->condp()->isPure()) return ifp->condp();
            AstNode* problem = nullptr;
            ifp->condp()->foreach([&](AstNodeVarRef* refp) {
                if (!problem && refp->access().isReadOrRW()
                    && localWriters.count(refp->varScopep())
                    && !assigned.count(refp->varScopep())) {
                    problem = refp;
                }
            });
            if (problem) return problem;
            std::unordered_set<AstVarScope*> thenAssigned = assigned;
            std::unordered_set<AstVarScope*> elseAssigned = assigned;
            if (AstNode* const errorp
                = checkDefiniteLocalWrites(ifp->thensp(), localWriters, thenAssigned)) {
                return errorp;
            }
            if (AstNode* const errorp
                = checkDefiniteLocalWrites(ifp->elsesp(), localWriters, elseAssigned)) {
                return errorp;
            }
            for (AstVarScope* const vscp : thenAssigned) {
                if (elseAssigned.count(vscp)) assigned.insert(vscp);
            }
        } else if (AstBegin* const beginp = VN_CAST(nodep, Begin)) {
            if (AstNode* const errorp
                = checkDefiniteLocalWrites(beginp->stmtsp(), localWriters, assigned)) {
                return errorp;
            }
        }
    }
    return nullptr;
}

void reject(SubgraphCandidate& candidate, const char* reason, FileLine* filelinep) {
    if (!candidate.m_rejection.empty()) return;
    candidate.m_rejection = reason;
    candidate.m_rejectionFilelinep = filelinep;
}

// A call can remain in the shared body if it depends only on its arguments and
// automatic function locals. Receiver-specific state must be explicit in the
// caller so input capture and the boundary contract can account for it.
bool isDpiImport(const AstCFunc* funcp) {
    return funcp->dpiImportPrototype() || funcp->dpiImportWrapper();
}

bool isStatelessCallee(AstCFunc* funcp, std::unordered_map<const AstCFunc*, bool>& calleeSafety) {
    const auto inserted = calleeSafety.emplace(funcp, false);
    if (!inserted.second) return inserted.first->second;
    if (isDpiImport(funcp)) {
        inserted.first->second = true;
        return true;
    }
    if (funcp->dpiExportImpl() || funcp->recursive() || funcp->needProcess()
        || funcp->isCoroutine()) {
        return false;
    }
    bool valid = true;
    funcp->foreach([&](AstNode* nodep) {
        if (AstStmtExpr* const exprp = VN_CAST(nodep, StmtExpr)) {
            if (AstCCall* const callp = VN_CAST(exprp->exprp(), CCall)) {
                if (isDpiImport(callp->funcp())) return;
            }
        }
        if (AstCCall* const callp = VN_CAST(nodep, CCall)) {
            if (isDpiImport(callp->funcp())) return;
        }
        if (!nodep->isPure() || nodep->isTimingControl() || VN_IS(nodep, NodeCCall)
            || VN_IS(nodep, NodeFTaskRef) || VN_IS(nodep, ScopeName) || VN_IS(nodep, VarXRef)
            || VN_IS(nodep, CExpr) || VN_IS(nodep, CExprUser) || VN_IS(nodep, CStmt)
            || VN_IS(nodep, CStmtUser)) {
            valid = false;
        }
        if (const AstNodeVarRef* const refp = VN_CAST(nodep, NodeVarRef)) {
            if (!refp->varp()->isFuncLocal() || !refp->varp()->lifetime().isAutomatic()) {
                valid = false;
            }
        }
    });
    inserted.first->second = valid;
    return valid;
}

bool isLocalPureCall(AstCCall* callp, AstScope* boundaryScopep,
                     std::unordered_map<const AstCFunc*, bool>& calleeSafety) {
    if (!isStatelessCallee(callp->funcp(), calleeSafety)) return false;
    bool valid = true;
    if (callp->argsp()) {
        callp->argsp()->foreachAndNext([&](AstNode* nodep) {
            if (!nodep->isPure()) valid = false;
            if (const AstNodeVarRef* const refp = VN_CAST(nodep, NodeVarRef)) {
                if (!refp->access().isReadOnly()
                    && !(refp->access().isWriteOnly() && refp->varp()->isTemp()
                         && isUnderScope(refp->varScopep()->scopep(), boundaryScopep))) {
                    valid = false;
                }
            }
        });
    }
    return valid;
}

AstNode*
findUnsupportedCallOrSuspendable(AstActive* activep, AstScope* boundaryScopep,
                                 std::unordered_map<const AstCFunc*, bool>& calleeSafety) {
    AstNode* unsupportedp = nullptr;
    activep->foreach([&](AstCCall* callp) {
        if (!unsupportedp && !isLocalPureCall(callp, boundaryScopep, calleeSafety)) {
            unsupportedp = callp;
        }
    });
    activep->foreach([&](AstNodeProcedure* procp) {
        if (!unsupportedp && procp->isSuspendable()) unsupportedp = procp;
    });
    return unsupportedp;
}

template <typename Func>
void foreachCombinationalRead(AstActive* activep, Func&& func) {
    VN_AS(activep->stmtsp(), Always)->stmtsp()->foreachAndNext([&](AstNodeVarRef* refp) {
        if (refp->access().isReadOrRW()) func(refp);
    });
}

using CombinationalWriters = std::map<AstVarScope*, std::vector<size_t>>;

template <typename Logic>
std::vector<size_t> orderNextState(const Logic& logic, const CombinationalWriters& writers,
                                   size_t* cycleIndexp = nullptr) {
    std::vector<std::vector<size_t>> successors(logic.size());
    std::vector<size_t> indegree(logic.size(), 0);
    for (size_t i = 0; i < logic.size(); ++i) {
        std::unordered_set<size_t> predecessors;
        foreachCombinationalRead(logic[i].second, [&](AstNodeVarRef* refp) {
            const auto writer = writers.find(refp->varScopep());
            if (writer == writers.end()) return;
            for (const size_t index : writer->second) {
                if (index != i) predecessors.insert(index);
            }
        });
        for (const size_t index : predecessors) {
            successors[index].push_back(i);
            ++indegree[i];
        }
    }
    std::set<size_t> ready;
    for (size_t i = 0; i < indegree.size(); ++i) {
        if (!indegree[i]) ready.insert(i);
    }
    std::vector<size_t> ordered;
    ordered.reserve(logic.size());
    while (!ready.empty()) {
        const size_t index = *ready.begin();
        ready.erase(ready.begin());
        ordered.push_back(index);
        for (const size_t next : successors[index]) {
            if (!--indegree[next]) ready.insert(next);
        }
    }
    if (cycleIndexp && ordered.size() != logic.size()) {
        size_t index = 0;
        while (!indegree[index]) ++index;
        std::unordered_set<size_t> visited;
        while (visited.insert(index).second) {
            size_t predecessor = index;
            foreachCombinationalRead(logic[index].second, [&](AstNodeVarRef* refp) {
                const auto writer = writers.find(refp->varScopep());
                if (writer == writers.end()) return;
                for (const size_t candidate : writer->second) {
                    if (candidate != index && indegree[candidate]) predecessor = candidate;
                }
            });
            index = predecessor;
        }
        *cycleIndexp = index;
    }
    return ordered;
}

using OutputSources = std::unordered_set<AstVarScope*>;
using OutputDependencies = std::map<AstVarScope*, OutputSources>;

void collectOutputReads(AstNode* rootp, OutputSources& sources) {
    rootp->foreach([&](AstNodeVarRef* refp) {
        if (refp->access().isReadOrRW()) sources.insert(refp->varScopep());
    });
}

// Index each assignment separately so an unrelated next-state expression in the
// same procedure cannot make an FF-derived output appear to depend on a
// boundary input.
void collectOutputDependencies(AstNode* stmtsp, OutputDependencies& dependencies,
                               const OutputSources& controls) {
    for (AstNode* nodep = stmtsp; nodep; nodep = nodep->nextp()) {
        if (AstNodeAssign* const assp = VN_CAST(nodep, NodeAssign)) {
            OutputSources sources = controls;
            collectOutputReads(assp->lhsp(), sources);
            collectOutputReads(assp->rhsp(), sources);
            assp->lhsp()->foreach([&](AstNodeVarRef* refp) {
                if (!refp->access().isWriteOrRW()) return;
                OutputSources& targetSources = dependencies[refp->varScopep()];
                targetSources.insert(sources.begin(), sources.end());
            });
        } else if (AstIf* const ifp = VN_CAST(nodep, If)) {
            OutputSources branchControls = controls;
            collectOutputReads(ifp->condp(), branchControls);
            collectOutputDependencies(ifp->thensp(), dependencies, branchControls);
            collectOutputDependencies(ifp->elsesp(), dependencies, branchControls);
        } else if (AstNodeProcedure* const procp = VN_CAST(nodep, NodeProcedure)) {
            collectOutputDependencies(procp->stmtsp(), dependencies, controls);
        } else if (AstBegin* const beginp = VN_CAST(nodep, Begin)) {
            collectOutputDependencies(beginp->stmtsp(), dependencies, controls);
        } else if (AstStmtExpr* const exprp = VN_CAST(nodep, StmtExpr)) {
            // Lowered function calls can write a return temporary through an
            // argument.
            OutputSources sources = controls;
            collectOutputReads(exprp->exprp(), sources);
            exprp->exprp()->foreach([&](AstNodeVarRef* refp) {
                if (!refp->access().isWriteOrRW()) return;
                OutputSources& targetSources = dependencies[refp->varScopep()];
                targetSources.insert(sources.begin(), sources.end());
            });
        }
    }
}

// Reject identified feedthrough paths. Unknown local sources are admitted for
// the MVP, rather than requiring a complete proof that every output leaf is FF
// state.
bool collectOutputCone(AstVarScope* vscp, const SubgraphCandidate& candidate,
                       const OutputDependencies& dependencies,
                       const std::unordered_set<AstVarScope*>& clockedWrites,
                       OutputSources& visited, OutputSources& outputComb) {
    if (!isUnderScope(vscp->scopep(), candidate.m_scopep) || vscp->varp()->subgraphCaptured()
        || (vscp->scopep() == candidate.m_scopep && vscp->varp()->isNonOutput()
            && vscp->varp()->subgraphPortId())) {
        return false;
    }
    // Clocked writes terminate the combinational path, including lowered FF
    // temporaries.
    if (clockedWrites.count(vscp) || !visited.insert(vscp).second) return true;
    const auto it = dependencies.find(vscp);
    if (it == dependencies.end()) return true;
    outputComb.insert(vscp);
    for (AstVarScope* const sourcep : it->second) {
        if (!collectOutputCone(sourcep, candidate, dependencies, clockedWrites, visited,
                               outputComb)) {
            return false;
        }
    }
    return true;
}

AstVarScope* posedgeClock(AstActive* activep) {
    AstSenItem* const itemp = activep->sentreep()->sensesp();
    if (!itemp || itemp->nextp() || itemp->condp() || itemp->edgeType() != VEdgeType::ET_POSEDGE) {
        return nullptr;
    }
    AstNodeVarRef* const refp = itemp->varrefp();
    return refp ? refp->varScopep() : nullptr;
}

AstNodeVarRef* writesExternalValue(AstActive* activep, AstScope* boundaryScopep) {
    AstNodeVarRef* externalp = nullptr;
    activep->foreach([&](AstNodeVarRef* refp) {
        if (!externalp && refp->access().isWriteOrRW()
            && !isUnderScope(refp->varScopep()->scopep(), boundaryScopep)) {
            externalp = refp;
        }
    });
    return externalp;
}

class SubgraphEligibility final {
    const V3SubgraphBoundary& m_boundary;  // Boundary metadata captured before scheduling
    const SubgraphReceivers& m_receivers;  // Instances using the representative body
    std::vector<SubgraphCandidate> m_candidates;  // Selected scopes under eligibility analysis
    std::map<AstScope*, size_t> m_candidateIndex;  // Candidate index for each selected scope
    LogicByScope m_allClocked;  // Clocked logic used to detect external dependencies
    LogicByScope m_allComb;  // Combinational logic used to detect external dependencies
    std::unordered_map<const AstCFunc*, bool>
        m_calleeSafety;  // Cached eligibility of transformed callees

    std::map<AstScope*, std::map<AstVarScope*, FileLine*>>
        m_exposedReads;  // Boundary values read by logic outside their owning scope

    void gather(AstNetlist* netlistp) {
        netlistp->foreach([&](AstScope* scopep) {
            scopep->foreach([&](AstActive* activep) {
                AstSenTree* const senTreep = activep->sentreep();
                const bool clocked = senTreep->hasClocked();
                const bool comb = senTreep->hasCombo();
                if (clocked) m_allClocked.emplace_back(scopep, activep);
                if (comb) m_allComb.emplace_back(scopep, activep);
                AstScope* const boundaryScopep = findBoundaryScope(scopep);
                if (!boundaryScopep || (!clocked && !comb)) return;
                if (comb
                    && (isPublishActive(activep)
                        || isBoundaryInputActive(boundaryScopep, activep))) {
                    return;
                }
                const auto inserted
                    = m_candidateIndex.emplace(boundaryScopep, m_candidates.size());
                if (inserted.second) {
                    m_candidates.emplace_back();
                    m_candidates.back().m_scopep = boundaryScopep;
                }
                SubgraphCandidate& candidate = m_candidates[inserted.first->second];
                if (clocked && !VN_IS(activep->stmtsp(), AlwaysObserved)
                    && !VN_IS(activep->stmtsp(), AlwaysReactive)) {
                    candidate.m_clocked.emplace_back(scopep, activep);
                } else if (comb && !VN_IS(activep->stmtsp(), AlwaysPostponed)) {
                    candidate.m_comb.emplace_back(scopep, activep);
                } else {
                    reject(candidate, "unsupported region",
                           activep->stmtsp() ? activep->stmtsp()->fileline()
                                             : activep->fileline());
                }
            });
        });
    }

    void gatherExposedReads() {
        const auto collect = [&](const LogicByScope& logic) {
            for (const auto& pair : logic) {
                pair.second->stmtsp()->foreachAndNext([&](AstNodeVarRef* refp) {
                    if (!refp->access().isReadOrRW()) return;
                    AstVarScope* vscp = refp->varScopep();
                    AstScope* scopep = findBoundaryScope(vscp->scopep());
                    if (!scopep || isUnderScope(pair.first, scopep)
                        || vscp->varp()->subgraphPublished())
                        return;
                    if (AstScope* const implementationp = scopep->subgraphImplementationScopep()) {
                        vscp = findVarScope(implementationp, vscp->varp());
                        UASSERT_OBJ(vscp, refp, "Missing representative boundary value");
                        scopep = implementationp;
                    }
                    m_exposedReads[scopep].emplace(vscp, refp->fileline());
                });
            }
        };
        collect(m_allComb);
        collect(m_allClocked);
    }

    void bindOutputs() {
        // Keep the publication expression in the representative scope. It can be an
        // FF reference or a pure expression of FF-derived local combinational
        // values.
        for (const auto& pair : m_allComb) {
            AstScope* const boundaryScopep = findBoundaryScope(pair.first);
            if (!boundaryScopep || !isPublishActive(pair.second)) continue;
            AstScope* const implementationp = boundaryScopep->subgraphImplementationScopep()
                                                  ? boundaryScopep->subgraphImplementationScopep()
                                                  : boundaryScopep;
            const auto it = m_candidateIndex.find(implementationp);
            if (it == m_candidateIndex.end()) continue;
            SubgraphCandidate& candidate = m_candidates[it->second];
            const AstAssignW* const assp
                = VN_AS(VN_AS(pair.second->stmtsp(), Always)->stmtsp(), AssignW);
            const AstVarRef* const lhsp = VN_AS(assp->lhsp(), VarRef);
            AstNodeExpr* const exprp = assp->rhsp()->cloneTree(false);
            SubgraphCandidate::ExprDeleter deleteExpr;
            std::unique_ptr<AstNodeExpr, SubgraphCandidate::ExprDeleter> expression{exprp,
                                                                                    deleteExpr};
            bool mapped = true;
            exprp->foreach([&](AstNodeVarRef* refp) {
                if (!isUnderScope(refp->varScopep()->scopep(), boundaryScopep)) {
                    mapped = false;
                    return;
                }
                // Unshared boundaries keep their references, including descendant FF
                // state.
                if (implementationp == boundaryScopep) return;
                AstVarScope* const representativep = findVarScope(implementationp, refp->varp());
                if (!representativep) {
                    mapped = false;
                    return;
                }
                refp->varScopep(representativep);
            });
            if (!mapped) reject(candidate, "output is not FF state", assp->rhsp()->fileline());
            const uint32_t portId = lhsp->varp()->subgraphPortId();
            bool found = false;
            for (const SubgraphCandidate::OutputBinding& output : candidate.m_outputs) {
                if (output.m_portId != portId) continue;
                if (output.m_publishedVarp != lhsp->varp()
                    || !output.m_exprp->sameTree(expression.get())) {
                    reject(candidate, "output expression differs across receivers",
                           assp->rhsp()->fileline());
                }
                found = true;
            }
            if (!found) {
                candidate.m_outputs.push_back(
                    {portId, std::move(expression), lhsp->varp(), nullptr});
            }
        }
    }

    void checkCombinational(SubgraphCandidate& candidate) {
        // Track all writers of a value. Separate procedures can write disjoint
        // elements of the same variable, and the output cone needs each source.
        CombinationalWriters combWriters;
        for (size_t i = 0; i < candidate.m_comb.size(); ++i) {
            AstActive* const activep = candidate.m_comb[i].second;
            AstNode* shapeProblemp = nullptr;
            std::vector<AstNodeAssign*> assignments;
            const bool localShape
                = localCombinationalAssignments(activep->stmtsp(), assignments, &shapeProblemp);
            AstNode* const callp
                = findUnsupportedCallOrSuspendable(activep, candidate.m_scopep, m_calleeSafety);
            if (!localShape || callp) {
                AstNode* const problemp = callp           ? callp
                                          : shapeProblemp ? shapeProblemp
                                                          : activep->stmtsp();
                reject(candidate, "unsupported child combinational logic", problemp->fileline());
            }
            std::unordered_set<const AstNodeVarRef*> lhsRefs;
            std::unordered_set<AstVarScope*> localWriters;
            for (AstNodeAssign* const assignmentp : assignments) {
                const AstVarRef* const lhsp
                    = V3SubgraphBoundary::writtenCombinationalVarRef(assignmentp->lhsp());
                if (!lhsp || !lhsp->access().isWriteOnly()
                    || !isUnderScope(lhsp->varScopep()->scopep(), candidate.m_scopep)
                    || lhsp->varp()->subgraphPublished() || lhsp->varp()->subgraphCaptured()
                    || assignmentp->isTimingControl()
                    || (!assignmentp->rhsp()->isPure()
                        && !(VN_IS(assignmentp->rhsp(), CCall)
                             && isStatelessCallee(VN_AS(assignmentp->rhsp(), CCall)->funcp(),
                                                  m_calleeSafety)))) {
                    reject(candidate, "unsupported child combinational logic",
                           assignmentp->fileline());
                    continue;
                }
                std::vector<size_t>& writers = combWriters[lhsp->varScopep()];
                if (writers.empty() || writers.back() != i) writers.push_back(i);
                lhsRefs.insert(lhsp);
                localWriters.insert(lhsp->varScopep());
            }
            if (localShape) {
                std::unordered_set<AstVarScope*> assigned;
                if (AstNode* const problemp = checkDefiniteLocalWrites(
                        VN_AS(activep->stmtsp(), Always)->stmtsp(), localWriters, assigned)) {
                    reject(candidate, "child combinational cycle", problemp->fileline());
                }
            }
            if (localShape) {
                VN_AS(activep->stmtsp(), Always)->stmtsp()->foreachAndNext([&](AstNode* nodep) {
                    if (const AstNodeVarRef* const refp = VN_CAST(nodep, NodeVarRef)) {
                        if (lhsRefs.count(refp)) return;
                        // External reads are captured before local FF evaluation.
                        // Output cones still require boundary-local FF state below.
                        if (!refp->access().isReadOnly()
                            && !(refp->access().isWriteOnly() && refp->varp()->isTemp()
                                 && isUnderScope(refp->varScopep()->scopep(),
                                                 candidate.m_scopep))) {
                            reject(candidate, "child combinational read outside boundary",
                                   refp->fileline());
                        }
                    } else if (VN_IS(nodep, NodeFTaskRef) || VN_IS(nodep, ScopeName)
                               || VN_IS(nodep, CExpr) || VN_IS(nodep, CExprUser)
                               || VN_IS(nodep, CStmt) || VN_IS(nodep, CStmtUser)) {
                        reject(candidate, "unsupported child combinational expression",
                               nodep->fileline());
                    }
                });
            }
        }
        if (!combWriters.empty() && candidate.m_rejection.empty()) {
            size_t cycleIndex = 0;
            if (orderNextState(candidate.m_comb, combWriters, &cycleIndex).size()
                != candidate.m_comb.size()) {
                std::vector<AstNodeAssign*> cycleAssignments;
                localCombinationalAssignments(candidate.m_comb[cycleIndex].second->stmtsp(),
                                              cycleAssignments);
                reject(candidate, "child combinational cycle",
                       cycleAssignments.back()->fileline());
            }
        }
    }

    void checkClock(SubgraphCandidate& candidate) {
        AstVarScope* clockVscp = nullptr;
        for (const auto& pair : candidate.m_clocked) {
            AstActive* const activep = pair.second;
            AstVarScope* const activeClockVscp = posedgeClock(activep);
            FileLine* const sensitivityFlp = activep->sentreep()->sensesp()->fileline();
            if (!activeClockVscp) {
                reject(candidate, "not a single posedge clock", sensitivityFlp);
            }
            if (!clockVscp) clockVscp = activeClockVscp;
            if (activeClockVscp != clockVscp) {
                reject(candidate, "multiple clocks", sensitivityFlp);
            }
            if (AstNode* const callp
                = findUnsupportedCallOrSuspendable(activep, candidate.m_scopep, m_calleeSafety)) {
                reject(candidate, "call or timing control", callp->fileline());
            }
            if (AstNodeVarRef* const externalp
                = writesExternalValue(activep, candidate.m_scopep)) {
                reject(candidate, "clocked write outside boundary", externalp->fileline());
            }
        }
        if (clockVscp) {
            candidate.m_clockp = clockVscp;
            if (isUnderScope(clockVscp->scopep(), candidate.m_scopep)) {
                const bool boundaryClockInput = clockVscp->scopep() == candidate.m_scopep
                                                && clockVscp->varp()->isNonOutput()
                                                && clockVscp->varp()->subgraphPortId();
                if (!boundaryClockInput) {
                    reject(candidate, "clock is inside boundary",
                           candidate.m_clocked.front().second->sentreep()->sensesp()->fileline());
                }
            }
            const auto checkClockWrite = [&](const auto& pairs) {
                for (const auto& pair : pairs) {
                    pair.second->foreach([&](AstNodeVarRef* refp) {
                        if (refp->varScopep() == clockVscp && refp->access().isWriteOrRW()) {
                            reject(candidate, "internally driven clock", refp->fileline());
                        }
                    });
                }
            };
            checkClockWrite(candidate.m_clocked);
            checkClockWrite(candidate.m_comb);
        }
    }

    void checkOutputs(SubgraphCandidate& candidate) {
        std::unordered_set<AstVarScope*> clockedWrites;
        for (const auto& pair : candidate.m_clocked) {
            pair.second->foreach([&](AstNodeVarRef* refp) {
                if (refp->access().isWriteOrRW()) clockedWrites.insert(refp->varScopep());
            });
        }
        if (candidate.m_rejection.empty()) {
            OutputDependencies dependencies;
            for (const auto& pair : candidate.m_comb) {
                collectOutputDependencies(VN_AS(pair.second->stmtsp(), Always)->stmtsp(),
                                          dependencies, {});
            }
            OutputSources visited;
            OutputSources outputComb;
            for (const SubgraphCandidate::OutputBinding& output : candidate.m_outputs) {
                bool valid = true;
                output.m_exprp->foreach([&](AstNodeVarRef* refp) {
                    if (valid
                        && !collectOutputCone(refp->varScopep(), candidate, dependencies,
                                              clockedWrites, visited, outputComb)) {
                        valid = false;
                    }
                });
                if (!valid) {
                    reject(candidate, "output is not FF state", output.m_exprp->fileline());
                    break;
                }
            }
            // DFG can move a parent expression into the child. Its result is a
            // boundary output too, even though it is not an RTL port.
            const auto exposed = m_exposedReads.find(candidate.m_scopep);
            if (exposed != m_exposedReads.end()) {
                for (const auto& entry : exposed->second) {
                    if (!collectOutputCone(entry.first, candidate, dependencies, clockedWrites,
                                           visited, outputComb)) {
                        reject(candidate, "output is not FF state", entry.second);
                        break;
                    }
                    candidate.m_exposedOutputs.push_back(entry.first);
                }
            }
            for (AstVarScope* const vscp : outputComb) {
                candidate.m_outputCombVars.insert(vscp->varp());
            }
        }
        if (FileLine* const flp = m_boundary.externalAccessFileline(candidate.m_scopep)) {
            reject(candidate, "external access to child state", flp);
        }
    }

    void checkCandidate(SubgraphCandidate& candidate) {
        if (v3Global.usesZeroDelay()) {
            reject(candidate, "zero-delay design", v3Global.zeroDelayFilelinep());
        }
        if (candidate.m_clocked.empty()) {
            AstActive* const activep
                = candidate.m_comb.empty() ? nullptr : candidate.m_comb.front().second;
            reject(candidate, "no clocked logic",
                   activep
                       ? (activep->stmtsp() ? activep->stmtsp()->fileline() : activep->fileline())
                       : candidate.m_scopep->modp()->fileline());
            return;
        }
        checkCombinational(candidate);
        checkClock(candidate);
        checkOutputs(candidate);
    }

    void checkDerivedClocks() {
        // A clock derived from child FF state requires Active-region scheduling.
        // Boundary inputs and unrelated assignments in the same procedure do not
        // create that dependency.
        OutputDependencies clockDependencies;
        for (const auto& pair : m_allComb) {
            collectOutputDependencies(pair.second->stmtsp(), clockDependencies, {});
        }
        OutputDependencies clockDependents;
        for (const auto& dependency : clockDependencies) {
            for (AstVarScope* const sourcep : dependency.second) {
                clockDependents[sourcep].insert(dependency.first);
            }
        }
        for (SubgraphCandidate& candidate : m_candidates) {
            if (!candidate.m_rejection.empty()) continue;
            OutputSources tainted;
            std::vector<AstVarScope*> pending;
            std::set<const AstVar*> stateVars;
            const auto seed = [&](AstVarScope* const vscp) {
                if (tainted.insert(vscp).second) pending.push_back(vscp);
            };
            for (const auto& pair : candidate.m_clocked) {
                pair.second->foreach([&](AstNodeVarRef* refp) {
                    const AstVar* const varp = refp->varp();
                    if (!refp->access().isWriteOrRW() || varp->isTemp() || varp->isInput()
                        || varp->subgraphCaptured()
                        || !isUnderScope(refp->varScopep()->scopep(), candidate.m_scopep)) {
                        return;
                    }
                    stateVars.insert(varp);
                    seed(refp->varScopep());
                });
            }
            // Receiver procedures have not been cloned; seed their corresponding FF
            // state.
            const auto receivers = m_receivers.find(candidate.m_scopep);
            if (receivers != m_receivers.end()) {
                for (AstScope* const receiverp : receivers->second) {
                    for (AstVarScope* vscp = receiverp->varsp(); vscp;
                         vscp = VN_AS(vscp->nextp(), VarScope)) {
                        if (stateVars.count(vscp->varp())) seed(vscp);
                    }
                }
            }
            for (size_t index = 0; index < pending.size(); ++index) {
                const auto it = clockDependents.find(pending[index]);
                if (it == clockDependents.end()) continue;
                for (AstVarScope* const targetp : it->second) seed(targetp);
            }

            for (const auto& pair : m_allClocked) {
                if (findBoundaryScope(pair.first) == candidate.m_scopep) continue;
                pair.second->sentreep()->foreach([&](AstNodeVarRef* refp) {
                    if (tainted.count(refp->varScopep())) {
                        reject(candidate, "boundary value used as clock", refp->fileline());
                    }
                });
            }
        }
    }

public:
    SubgraphEligibility(AstNetlist* netlistp, const V3SubgraphBoundary& boundary,
                        const SubgraphReceivers& receivers)
        : m_boundary{boundary}
        , m_receivers{receivers} {
        gather(netlistp);
        gatherExposedReads();
        bindOutputs();
        for (SubgraphCandidate& candidate : m_candidates) checkCandidate(candidate);
        checkDerivedClocks();
    }

    std::vector<SubgraphCandidate> takeCandidates() { return std::move(m_candidates); }
};

}  // namespace

std::vector<SubgraphCandidate> analyzeSubgraphs(AstNetlist* netlistp,
                                                const V3SubgraphBoundary& boundary,
                                                const SubgraphReceivers& receivers) {
    return SubgraphEligibility{netlistp, boundary, receivers}.takeCandidates();
}

}  // namespace V3Sched
