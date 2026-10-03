// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Receiver-independent subgraph procedure sharing
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

// Analyze module bodies and all elaborated connections once before Scope.
// Eligible bodies read explicit per-receiver captures, allowing Scope to keep
// a representative procedure instead of cloning it for every instance. Inst
// retains normal pin lowering and asks this helper to add edge captures after
// simplifying each connection.

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3SubgraphSharing.h"

#include "V3Stats.h"
#include "V3SubgraphBoundary.h"

#include <map>
#include <set>

VL_DEFINE_DEBUG_FUNCTIONS;

static bool shareableLocalFunction(const AstNodeFTask* ftaskp) {
    if (!ftaskp || !ftaskp->isFunction() || ftaskp->dpiImport() || ftaskp->dpiExport()
        || ftaskp->recursive() || ftaskp->needProcess()
        || !const_cast<AstNodeFTask*>(ftaskp)->isPure()) {
        return false;
    }
    bool local = true;
    ftaskp->foreach([&](const AstNode* nodep) {
        if (const AstNodeVarRef* const refp = VN_CAST(nodep, NodeVarRef)) {
            if (!refp->varp()->isFuncLocal() || !refp->varp()->lifetime().isAutomatic()) {
                local = false;
            }
        } else if (VN_IS(nodep, NodeFTaskRef) || VN_IS(nodep, ScopeName)
                   || VN_IS(nodep, VarXRef)) {
            local = false;
        }
    });
    return local;
}

static bool shareableCombinationalStatements(const AstNode* stmtsp) {
    for (const AstNode* nodep = stmtsp; nodep; nodep = nodep->nextp()) {
        if (const AstAssign* const assp = VN_CAST(nodep, Assign)) {
            const AstVarRef* const lhsp
                = V3SubgraphBoundary::writtenCombinationalVarRef(assp->lhsp());
            if (!lhsp || lhsp->varp()->isIO()) return false;
        } else if (const AstIf* const ifp = VN_CAST(nodep, If)) {
            if (!shareableCombinationalStatements(ifp->thensp())
                || !shareableCombinationalStatements(ifp->elsesp())) {
                return false;
            }
        } else if (const AstBegin* const beginp = VN_CAST(nodep, Begin)) {
            if (!shareableCombinationalStatements(beginp->stmtsp())) return false;
        } else if (!VN_IS(nodep, Comment)) {
            return false;
        }
    }
    return true;
}

bool V3SubgraphSharing::shareableModuleShape(const AstNodeModule* modp) {
    unsigned clocked = 0;
    std::set<const AstNodeFTask*> localFunctions;
    for (const AstNode* stmtp = modp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
        if (const AstNodeFTask* const ftaskp = VN_CAST(stmtp, NodeFTask)) {
            if (!shareableLocalFunction(ftaskp)) return false;
            localFunctions.insert(ftaskp);
        }
    }
    for (const AstNode* stmtp = modp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
        if (const AstVar* const varp = VN_CAST(stmtp, Var)) {
            if (varp->isInoutOrRef()) return false;
        }
        if (VN_IS(stmtp, Cell)) return false;
        if (VN_IS(stmtp, NodeFTask)) continue;
        if (const AstAlways* const alwaysp = VN_CAST(stmtp, Always)) {
            if (alwaysp->keyword() == VAlwaysKwd::ALWAYS_FF) {
                ++clocked;
            } else if (alwaysp->keyword() == VAlwaysKwd::ALWAYS_COMB) {
                if (!alwaysp->stmtsp() || !shareableCombinationalStatements(alwaysp->stmtsp())) {
                    return false;
                }
            } else {
                const AstAssignW* const assp = VN_CAST(alwaysp->stmtsp(), AssignW);
                const AstVarRef* const lhsp = assp ? VN_CAST(assp->lhsp(), VarRef) : nullptr;
                if (!assp || assp->nextp() || !lhsp
                    || (lhsp->varp()->isIO() && !lhsp->varp()->isWritable())) {
                    return false;
                }
            }
        } else if (const AstNodeProcedure* const procp = VN_CAST(stmtp, NodeProcedure)) {
            if ((!VN_IS(procp, InitialStatic) && !VN_IS(procp, Initial))
                || procp->isSuspendable()) {
                return false;
            }
        }
        bool instanceSpecific = false;
        stmtp->foreach([&](const AstNode* nodep) {
            if (VN_IS(nodep, ScopeName) || VN_IS(nodep, VarXRef)) {
                instanceSpecific = true;
            } else if (const AstNodeFTaskRef* const refp = VN_CAST(nodep, NodeFTaskRef)) {
                if (!localFunctions.count(refp->taskp())) instanceSpecific = true;
            }
        });
        if (instanceSpecific) return false;
    }
    return clocked >= 1;
}

struct V3SubgraphSharing::Impl final {
    struct SharedInput final {
        AstVar* m_clockp = nullptr;  // Single rising-edge clock selected for capture
        std::map<AstVar*, AstVar*>
            m_savedByPort;  // Per-instance input capture storage for each port
    };
    struct SharedInputAnalysis final {
        AstVar* m_clockp = nullptr;  // Single rising-edge clock selected for capture
        std::vector<AstAlways*> m_procedures;  // Clocked procedures rewritten to read captures
        std::map<uint32_t, AstVar*> m_inputPorts;  // Input ports read during next-state evaluation
        std::map<AstVar*, AstAlways*> m_stateWriters;  // Clocked writer for each state variable
        std::set<AstVar*> m_combWriters;  // Variables written by local combinational logic
        std::set<const AstVar*> m_ownedVars;  // Variables declared in this specialization
        std::set<const AstNodeFTask*>
            m_shareableFunctions;  // Pure local functions accepted for early sharing
        bool m_valid = true;  // All procedures satisfy the early sharing preconditions

        explicit SharedInputAnalysis(AstNodeModule* modp) {
            for (AstNode* stmtp = modp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
                if (const AstVar* const varp = VN_CAST(stmtp, Var)) m_ownedVars.insert(varp);
                if (const AstNodeFTask* const ftaskp = VN_CAST(stmtp, NodeFTask)) {
                    if (shareableLocalFunction(ftaskp)) { m_shareableFunctions.insert(ftaskp); }
                }
            }
        }

        void readExpression(AstNodeExpr* exprp, bool captureInputs = true) {
            if (!exprp->isPure()) m_valid = false;
            exprp->foreach([&](AstNode* nodep) {
                if (const AstNodeVarRef* const refp = VN_CAST(nodep, NodeVarRef)) {
                    const AstVarRef* const plainp = VN_CAST(refp, VarRef);
                    if (!plainp || !plainp->access().isReadOnly()
                        || !m_ownedVars.count(plainp->varp())) {
                        m_valid = false;
                    } else if (plainp->varp()->isInoutOrRef()) {
                        m_valid = false;
                    } else if (plainp->varp()->isInput()) {
                        if (!plainp->varp()->subgraphPortId()) {
                            m_valid = false;
                        } else if (captureInputs) {
                            m_inputPorts.emplace(plainp->varp()->subgraphPortId(), plainp->varp());
                        }
                    }
                } else if (const AstNodeFTaskRef* const refp = VN_CAST(nodep, NodeFTaskRef)) {
                    if (!m_shareableFunctions.count(refp->taskp())) m_valid = false;
                } else if (VN_IS(nodep, ScopeName) || VN_IS(nodep, CExpr) || VN_IS(nodep, CStmt)) {
                    m_valid = false;
                }
            });
        }

        void statements(AstNode* stmtsp, AstAlways* ownerp) {
            for (AstNode* stmtp = stmtsp; stmtp; stmtp = stmtp->nextp()) {
                if (AstAssignDly* const assp = VN_CAST(stmtp, AssignDly)) {
                    const AstVarRef* const lhsp = VN_CAST(assp->lhsp(), VarRef);
                    if (!lhsp || !lhsp->access().isWriteOrRW() || !m_ownedVars.count(lhsp->varp())
                        || (lhsp->varp()->isIO() && !lhsp->varp()->isWritable())
                        || lhsp->varp()->isInoutOrRef() || assp->timingControlp()) {
                        m_valid = false;
                        continue;
                    }
                    const auto inserted = m_stateWriters.emplace(lhsp->varp(), ownerp);
                    if (!inserted.second && inserted.first->second != ownerp) m_valid = false;
                    readExpression(assp->rhsp());
                } else if (AstIf* const ifp = VN_CAST(stmtp, If)) {
                    readExpression(ifp->condp());
                    statements(ifp->thensp(), ownerp);
                    statements(ifp->elsesp(), ownerp);
                } else if (AstBegin* const beginp = VN_CAST(stmtp, Begin)) {
                    statements(beginp->stmtsp(), ownerp);
                } else {
                    // Unknown statements may change externally visible state or timing.
                    m_valid = false;
                }
            }
        }

        void procedure(AstAlways* alwaysp) {
            if (alwaysp->keyword() != VAlwaysKwd::ALWAYS_FF || !alwaysp->sentreep()) {
                m_valid = false;
                return;
            }
            const AstSenItem* const itemp = alwaysp->sentreep()->sensesp();
            const AstNodeVarRef* const clockp = itemp ? itemp->varrefp() : nullptr;
            const AstVarRef* const plainp = VN_CAST(clockp, VarRef);
            if (!plainp || !plainp->access().isReadOnly() || !m_ownedVars.count(plainp->varp())
                || itemp->nextp() || itemp->condp() || itemp->edgeType() != VEdgeType::ET_POSEDGE
                || !plainp->varp()->isInput() || !plainp->varp()->subgraphPortId()
                || (m_clockp && m_clockp != plainp->varp())) {
                m_valid = false;
                return;
            }
            m_clockp = plainp->varp();
            m_procedures.push_back(alwaysp);
            statements(alwaysp->stmtsp(), alwaysp);
        }

        void combStatements(AstNode* stmtsp, std::set<AstVar*>& localWriters) {
            for (AstNode* nodep = stmtsp; nodep; nodep = nodep->nextp()) {
                if (const AstNodeAssign* const assp = VN_CAST(nodep, NodeAssign)) {
                    const AstVarRef* const lhsp
                        = V3SubgraphBoundary::writtenCombinationalVarRef(assp->lhsp());
                    if (!lhsp || !lhsp->access().isWriteOnly() || !m_ownedVars.count(lhsp->varp())
                        || lhsp->varp()->isIO() || assp->isTimingControl()) {
                        m_valid = false;
                        return;
                    }
                    assp->lhsp()->foreach([&](const AstNodeVarRef* refp) {
                        if (refp == lhsp) return;
                        if (!refp->access().isReadOnly() || !m_ownedVars.count(refp->varp())) {
                            m_valid = false;
                        }
                    });
                    localWriters.insert(lhsp->varp());
                    readExpression(assp->rhsp(), false);
                } else if (AstIf* const ifp = VN_CAST(nodep, If)) {
                    readExpression(ifp->condp(), false);
                    combStatements(ifp->thensp(), localWriters);
                    combStatements(ifp->elsesp(), localWriters);
                } else if (AstBegin* const beginp = VN_CAST(nodep, Begin)) {
                    combStatements(beginp->stmtsp(), localWriters);
                } else if (!VN_IS(nodep, Comment)) {
                    m_valid = false;
                    return;
                }
            }
        }

        void combProcedure(AstAlways* alwaysp) {
            std::set<AstVar*> localWriters;
            combStatements(alwaysp->stmtsp(), localWriters);
            if (localWriters.empty()) m_valid = false;
            for (AstVar* const varp : localWriters) { m_combWriters.insert(varp); }
        }
    };
    std::map<AstNodeModule*, std::vector<AstCell*>>
        m_cellsByModule;  // Elaborated cells grouped by specialization
    std::map<AstNodeModule*, uint64_t>
        m_instantiationsByModule;  // Number of instances including hierarchical multiplicity
    std::map<AstNodeModule*, SharedInput>
        m_sharedInputs;  // Prepared capture slots for each shareable specialization
    std::set<AstNodeModule*> m_sharedInputChecked;  // Specializations already analyzed for sharing
    uint64_t m_sharedCaptures = 0;  // Number of per-instance input capture assignments

    void countInstantiations(AstNodeModule* modp) {
        ++m_instantiationsByModule[modp];
        for (AstNode* stmtp = modp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
            if (const AstCell* const cellp = VN_CAST(stmtp, Cell)) {
                countInstantiations(cellp->modp());
            }
        }
    }

    void prepareSharedInput(AstNodeModule* modp) {
        // The pre-scope shared-procedure path currently requires serial Order.
        if (!v3Global.opt.subgraphSchedule() || v3Global.opt.threads() > 1
            || !m_sharedInputChecked.insert(modp).second) {
            return;
        }
        // The elaborated specialization and all its cell connections are available here.
        // Analyze it once even if no receiver can use the shared procedure.
        if (!modp->subgraphBoundary() || m_instantiationsByModule[modp] < 2
            || m_instantiationsByModule[modp] != m_cellsByModule[modp].size()
            || !V3SubgraphSharing::shareableModuleShape(modp)) {
            return;
        }
        SharedInputAnalysis analysis{modp};
        for (AstNode* stmtp = modp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
            AstAlways* const alwaysp = VN_CAST(stmtp, Always);
            if (alwaysp && alwaysp->keyword() == VAlwaysKwd::ALWAYS_FF) {
                analysis.procedure(alwaysp);
            } else if (alwaysp && alwaysp->keyword() == VAlwaysKwd::ALWAYS_COMB) {
                analysis.combProcedure(alwaysp);
            }
        }
        for (AstVar* const varp : analysis.m_combWriters) {
            if (analysis.m_stateWriters.count(varp)) analysis.m_valid = false;
        }
        if (!analysis.m_valid || analysis.m_stateWriters.empty()) return;
        // The body is rewritten once, so every instance needs all captured connections.
        const AstVar* clockActualp = nullptr;
        for (const AstCell* const cellp : m_cellsByModule[modp]) {
            const AstVar* cellClockActualp = nullptr;
            std::set<AstVar*> connectedInputs;
            for (const AstPin* pinp = cellp->pinsp(); pinp; pinp = VN_AS(pinp->nextp(), Pin)) {
                if (pinp->modVarp() == analysis.m_clockp) {
                    if (const AstVarRef* const refp = VN_CAST(pinp->exprp(), VarRef)) {
                        cellClockActualp = refp->varp();
                    }
                }
                if (analysis.m_inputPorts.count(pinp->modVarp()->subgraphPortId()) && pinp->exprp()
                    && pinp->exprp()->isPure()) {
                    connectedInputs.insert(pinp->modVarp());
                }
            }
            if (!cellClockActualp || connectedInputs.size() != analysis.m_inputPorts.size())
                return;
            if (clockActualp && clockActualp != cellClockActualp) return;
            clockActualp = cellClockActualp;
        }
        SharedInput shared;
        shared.m_clockp = analysis.m_clockp;
        for (const auto& entry : analysis.m_inputPorts) {
            AstVar* const portp = entry.second;
            AstVar* const savedp
                = new AstVar{portp->fileline(), VVarType::BLOCKTEMP,
                             "__VsubgraphInput__" + cvtToStr(entry.first), portp->dtypep()};
            savedp->noSubst(true);
            savedp->subgraphCaptured(true);
            modp->addStmtsp(savedp);
            shared.m_savedByPort.emplace(portp, savedp);
        }
        const auto inserted = m_sharedInputs.emplace(modp, std::move(shared));
        modp->subgraphSharedInput(true);
        for (AstAlways* const alwaysp : analysis.m_procedures) {
            alwaysp->stmtsp()->foreachAndNext([&](AstVarRef* refp) {
                if (!refp->access().isReadOnly()) return;
                const auto it = inserted.first->second.m_savedByPort.find(refp->varp());
                if (it != inserted.first->second.m_savedByPort.end()) refp->varp(it->second);
            });
        }
    }
};

V3SubgraphSharing::V3SubgraphSharing(AstNetlist* netlistp)
    : m_impl{new Impl} {
    if (!v3Global.opt.subgraphSchedule()) return;
    netlistp->foreach(
        [&](AstCell* cellp) { m_impl->m_cellsByModule[cellp->modp()].push_back(cellp); });
    if (AstNodeModule* const topModp = netlistp->topModulep()) {
        m_impl->countInstantiations(topModp);
    }
}

V3SubgraphSharing::~V3SubgraphSharing() {
    V3Stats::addStat("Inst, Subgraph shared input captures", m_impl->m_sharedCaptures);
}

AstNodeExpr* V3SubgraphSharing::clockExpression(AstCell* cellp) {
    m_impl->prepareSharedInput(cellp->modp());
    const auto it = m_impl->m_sharedInputs.find(cellp->modp());
    if (it == m_impl->m_sharedInputs.end()) return nullptr;
    for (AstPin* pinp = cellp->pinsp(); pinp; pinp = VN_AS(pinp->nextp(), Pin)) {
        if (pinp->modVarp() == it->second.m_clockp && pinp->exprp()) {
            return VN_AS(pinp->exprp()->cloneTree(false), NodeExpr);
        }
    }
    return nullptr;
}

void V3SubgraphSharing::captureInput(AstCell* cellp, AstVar* portp, AstNodeExpr* exprp,
                                     AstNodeExpr* clockp) {
    if (!clockp) return;
    const auto shared = m_impl->m_sharedInputs.find(cellp->modp());
    if (shared == m_impl->m_sharedInputs.end()) return;
    const auto saved = shared->second.m_savedByPort.find(portp);
    if (saved == shared->second.m_savedByPort.end()) return;
    FileLine* const flp = exprp->fileline();
    AstSenTree* const senp = new AstSenTree{
        flp, new AstSenItem{flp, VEdgeType::ET_POSEDGE, clockp->cloneTree(false)}};
    AstVarXRef* const lhsp = new AstVarXRef{flp, saved->second, cellp->name(), VAccess::WRITE};
    AstAlways* const capturep = new AstAlways{flp, VAlwaysKwd::ALWAYS, senp,
                                              new AstAssign{flp, lhsp, exprp->cloneTree(false)}};
    cellp->addNextHere(capturep);
    ++m_impl->m_sharedCaptures;
}
