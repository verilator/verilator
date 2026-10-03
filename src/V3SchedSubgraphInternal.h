// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Subgraph eligibility and internal scheduling
// interfaces
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
#ifndef VERILATOR_V3SCHEDSUBGRAPHINTERNAL_H_
#define VERILATOR_V3SCHEDSUBGRAPHINTERNAL_H_

#include "V3Sched.h"

#include <memory>

namespace V3Sched {

// Candidate logic and output expressions remain owned by the scheduling plan
// until admission. Rejected candidates leave their original logic in the AST.
struct SubgraphCandidate final {
    struct ExprDeleter final {
        void operator()(AstNodeExpr* exprp) const;
    };
    struct OutputBinding final {
        uint32_t m_portId = 0;  // Stable identity of the selected output port
        std::unique_ptr<AstNodeExpr, ExprDeleter>
            m_exprp;  // Owned expression used to publish the output
        AstVar* m_publishedVarp = nullptr;  // Publication storage shared by the specialization
        AstVarScope* m_publishedp = nullptr;  // Publication storage in this instance
    };
    AstScope* m_scopep = nullptr;  // Selected scheduling boundary
    AstVarScope* m_clockp = nullptr;  // Single rising-edge clock of this boundary
    std::vector<std::pair<AstScope*, AstActive*>>
        m_clocked;  // Clocked procedures owned by this boundary
    std::vector<std::pair<AstScope*, AstActive*>>
        m_comb;  // Combinational procedures owned by this boundary
    std::vector<OutputBinding> m_outputs;  // Boundary output publication bindings
    std::unordered_set<const AstVar*>
        m_outputCombVars;  // Combinational variables needed to compute outputs
    std::vector<AstVarScope*> m_exposedOutputs;  // Internal values read outside the boundary
    std::string m_rejection;  // First failed eligibility condition
    FileLine* m_rejectionFilelinep = nullptr;  // RTL location of the failed eligibility condition

    SubgraphCandidate() = default;
    VL_UNCOPYABLE(SubgraphCandidate);
    SubgraphCandidate(SubgraphCandidate&&) = default;
    SubgraphCandidate& operator=(SubgraphCandidate&&) = default;
};

using SubgraphReceivers = std::unordered_map<AstScope*, std::vector<AstScope*>>;

bool isUnderScope(const AstScope* scopep, const AstScope* basep);
AstScope* findBoundaryScope(AstScope* scopep);
AstVarScope* findVarScope(AstScope* scopep, const AstVar* varp);
bool isPublishStatement(const AstNode* stmtp);
bool isPublishActive(const AstActive* activep);
bool isBoundaryInputStatement(const AstScope* boundaryScopep, const AstNode* stmtp);
bool isBoundaryInputActive(const AstScope* boundaryScopep, const AstActive* activep);
bool localCombinationalAssignments(AstNode* stmtp, std::vector<AstNodeAssign*>& assignments,
                                   AstNode** problemp = nullptr);

std::vector<SubgraphCandidate> analyzeSubgraphs(AstNetlist* netlistp,
                                                const V3SubgraphBoundary& boundary,
                                                const SubgraphReceivers& receivers);

}  // namespace V3Sched

#endif  // Guard
