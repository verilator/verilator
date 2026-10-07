// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Block code ordering
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
//  Initial graph dependency builder for ordering
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3OrderGraph.h"
#include "V3OrderInternal.h"

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// ProcessDomains class

class V3OrderProcessDomains final {
    // STATE
    OrderGraph& m_graph;  // The ordering graph
    const string m_tag;  // Substring to add to generated names
    // This is a function provided by the invoker of the ordering that can provide additional
    // trigger indices that when set indicate the passed AstVarScope might have changed external
    // to the code being ordered, hence dependent logic needs to be evaluated.
    const V3Order::ExternalTriggersProvider m_externalTriggers;
    std::vector<OrderLogicVertex*> m_untriggeredps;  // Logic never triggered and can be deleted

    // METHODS

    // Compute the OrderDomain for combinational and hybrid logic vertices.
    void processDomains() {
        // The triggers of the current vertex
        std::set<uint32_t> triggers;

        // The graph is already in topological order, so can walk vertices once
        for (V3GraphVertex& it : m_graph.vertices()) {
            OrderEitherVertex* const vtxp = it.as<OrderEitherVertex>();
            // Sequential logic already has its domain set
            if (vtxp->domainp()) continue;

            // Reset state
            triggers.clear();

            OrderLogicVertex* const lvtxp = vtxp->cast<OrderLogicVertex>();

            // For logic vertices, start with the explicit hybrid sensitivities, if any
            if (const OrderDomain* const hybridp = lvtxp ? lvtxp->hybridp() : nullptr) {
                const std::set<uint32_t>& hybridTriggers = hybridp->triggers();
                triggers.insert(hybridTriggers.begin(), hybridTriggers.end());
            }

            // For each incoming edge, union the source vertex's domain into the current domain
            for (V3GraphEdge& edge : vtxp->inEdges()) {
                OrderEitherVertex* const fromVtxp = edge.fromp()->as<OrderEitherVertex>();
                // Cut edge
                if (!edge.weight()) continue;
                // some edges can be ignored as they only encode ordering constraints
                if (!fromVtxp->domainMatters()) continue;

                // Add driver's domains
                const OrderDomain* const fromDomainp = fromVtxp->domainp();
                const std::set<uint32_t>& fromTriggers = fromDomainp->triggers();
                triggers.insert(fromTriggers.begin(), fromTriggers.end());

                // Add in any external domains of variables
                if (OrderVarVertex* const varVtxp = fromVtxp->cast<OrderVarVertex>()) {
                    m_externalTriggers(varVtxp->vscp(), triggers);
                }
            }

            // Set the domain of the vertex
            const OrderDomain* const domainp = m_graph.domainp(triggers);
            vtxp->domainp(domainp);

            // If nothing triggers this vertex, we can delete the corresponding logic
            if (domainp->triggers().empty() && lvtxp) m_untriggeredps.push_back(lvtxp);
        }
    }

    // CONSTRUCTOR
    V3OrderProcessDomains(OrderGraph& graph, const string& tag,
                          const V3Order::ExternalTriggersProvider& externalTriggers)
        : m_graph{graph}
        , m_tag{tag}
        , m_externalTriggers{externalTriggers} {

        // Assign vertices to their sensitivity domains
        processDomains();
        if (dumpGraphLevel()) m_graph.dumpDotFilePrefixed(m_tag + "_orderg_domain");

        // Delete logic that is never triggered
        for (OrderLogicVertex* const lVtxp : m_untriggeredps) {
            UASSERT_OBJ(lVtxp->domainp()->triggers().empty(), lVtxp,
                        "Deleted logic should not be triggered");
            lVtxp->nodep()->unlinkFrBack()->deleteTree();
            lVtxp->unlinkDelete(&m_graph);
        }
    }

    ~V3OrderProcessDomains() = default;

public:
    // Order the logic
    static void apply(OrderGraph& graph, const string& tag,
                      const V3Order::ExternalTriggersProvider& externalTriggers) {
        V3OrderProcessDomains{graph, tag, externalTriggers};
    }
};

void V3Order::processDomains(OrderGraph& graph,  //
                             const std::string& tag,  //
                             const ExternalTriggersProvider& externalTriggers) {
    V3OrderProcessDomains::apply(graph, tag, externalTriggers);
}
