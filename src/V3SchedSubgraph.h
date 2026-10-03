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

#ifndef VERILATOR_V3SCHEDSUBGRAPH_H_
#define VERILATOR_V3SCHEDSUBGRAPH_H_

#include "config_build.h"
#include "verilatedos.h"

#include "V3Order.h"
#include "V3Sched.h"

#include <functional>
#include <memory>
#include <unordered_map>
#include <vector>

namespace V3Sched {

class SubgraphPlan final {
    struct Impl;
    const std::unique_ptr<Impl> m_impl;  // Scheduling state retained between pipeline stages

public:
    struct Use final {
        AstVarScope* m_vscp = nullptr;  // Variable affected by this boundary
        bool m_read = false;  // Boundary reads this variable
        bool m_write = false;  // Boundary writes this variable
    };

    SubgraphPlan(AstNetlist* netlistp, const V3SubgraphBoundary& subgraphBoundary);
    ~SubgraphPlan();
    VL_UNCOPYABLE(SubgraphPlan);

    bool extract(AstScope* scopep, AstActive* activep);
    bool isAccepted(const AstScope* scopep) const;
    bool hasAccepted() const;
    bool isOutputCombinational(const AstScope* scopep, const AstVar* varp) const;
    AstVarScope* clockPort(const AstScope* scopep) const;
    void foreachPublished(const AstScope* scopep,
                          const std::function<void(AstVarScope*)>& callback) const;
    void appendPublications(AstNetlist* netlistp, const AstScope* scopep,
                            LogicByScope& comb) const;
    void appendSettleLogic(AstNetlist* netlistp, LogicByScope& comb,
                           const CovergroupRefBindings& cgRefBindings,
                           V3Order::BoundaryUses& boundaryUses,
                           std::vector<AstActive*>& temporaryActives) const;
    AstCFunc* appendIcoLogic(AstNetlist* netlistp, AstCFunc* icoFuncp, AstSenTree* triggerp,
                             const CovergroupRefBindings& cgRefBindings) const;
    void movePublications(LogicByScope& comb, LogicByScope& hybrid);
    void partitionAndReplicate();
    void materializeNba(const std::unordered_map<const AstSenTree*, AstSenTree*>& senTreeMap,
                        const std::vector<LogicByScope*>& parentLogic);
    void clearOutputExpressions();
    void foreachUse(const std::function<void(const Use&)>& callback) const;
    void foreachBoundary(const std::function<void(AstScope*, AstSenTree*,
                                                  const std::vector<Use>&)>& callback) const;
};

V3Order::FreshReads lowerSubgraphNbaLogic(AstNetlist* netlistp,
                                          const std::vector<LogicByScope*>& logic,
                                          const V3Order::TrigToSenMap& trigToSen,
                                          const CovergroupRefBindings& cgRefBindings, bool slow,
                                          const V3Order::ExternalDomainsProvider& externalDomains,
                                          const SubgraphPlan& plan,
                                          V3Order::BoundaryUses& boundaryUses);

}  // namespace V3Sched

#endif  // Guard
