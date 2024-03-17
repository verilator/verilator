// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Block code ordering
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2024 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
//
//  OrderMoveGraph implementation and related
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3OrderMoveGraph.h"

#include "V3Graph.h"

VL_DEFINE_DEBUG_FUNCTIONS;

//======================================================================
// OrderMoveDomScope implementation

OrderMoveDomScope::DomScopeMap OrderMoveDomScope::s_dsMap;

//======================================================================
// OrderMoveVertex implementation

OrderMoveVertex::OrderMoveVertex(OrderMoveGraph& graph, OrderLogicVertex* lVtxp,
                                 const AstSenTree* domainp) VL_MT_DISABLED
    : V3GraphVertex{&graph},
      m_logicp{lVtxp},
      m_domScope{OrderMoveDomScope::getOrCreate(domainp, lVtxp ? lVtxp->scopep() : nullptr)} {
    UASSERT_OBJ(!lVtxp || lVtxp->domainp() == domainp, lVtxp, "Wrong domain for Move vertex");
}

//======================================================================
// OrderMoveGraphBuilder - for OrderMoveGraph::build

class OrderMoveGraphBuilder final {
    // NODE STATE
    // AstSenTree::user1p()     -> AstSenTree:  Original AstSenTree for trigger
    const VNUser1InUse m_user1InUse;

    // TYPES
    using DomainMap = std::map<const AstSenTree*, OrderMoveVertex*>;

    // MEMBERS
    OrderGraph& m_orderGraph;  // Input OrderGraph
    std::unique_ptr<OrderMoveGraph> m_moveGraphp{new OrderMoveGraph};  // Output OrderMoveGraph
    // Map from Trigger reference AstSenItem to the original AstSenTree
    const V3Order::TrigToSenMap& m_trigToSen;
    // Storage for domain -> OrderMoveVertex, maps held in OrderVarVertex::userp()
    std::deque<DomainMap> m_domainMaps;

    // CONSTRUCTORS
    OrderMoveGraphBuilder(OrderGraph& orderGraph, const V3Order::TrigToSenMap& trigToSen)
        : m_orderGraph{orderGraph}
        , m_trigToSen{trigToSen} {
        // How this works:
        //  - Create a OrderMoveVertex for each OrderLogicVertex.
        //  - Following each OrderLogicVertex, search forward in the context of its domain
        //    - If we encounter another OrderLogicVertex in non-exclusive domain, make the
        //      OrderMoveVertex->OrderMoveVertex edge.
        //    - If we encounter an OrderVarVertex, make a Vertex for the (OrderVarVertex, domain)
        //      pair and continue to search forward in the context of the same domain.  Unless we
        //      already created that pair, in which case, we've already done the forward search,
        //      so stop.

        // For each logic vertex, make a OrderMoveVertex, for each variable vertex, allocate
        // storage
        for (V3GraphVertex& vtx : m_orderGraph.vertices()) {
            if (OrderLogicVertex* const lvtxp = vtx.cast<OrderLogicVertex>()) {
                lvtxp->userp(new OrderMoveVertex{*m_moveGraphp, lvtxp, lvtxp->domainp()});
            } else {
                // This is an OrderVarVertex
                m_domainMaps.emplace_back();
                vtx.userp(&m_domainMaps.back());
            }
        }
        // Build edges between logic vertices
        for (V3GraphVertex& vtx : m_orderGraph.vertices()) {
            if (OrderLogicVertex* const lvtxp = vtx.cast<OrderLogicVertex>()) {
                iterateLogicVertex(lvtxp);
            }
        }
        m_moveGraphp->removeRedundantEdgesSum(&V3GraphEdge::followAlwaysTrue);
        m_moveGraphp->userClearVertices();
    }
    virtual ~OrderMoveGraphBuilder() = default;
    VL_UNCOPYABLE(OrderMoveGraphBuilder);
    VL_UNMOVABLE(OrderMoveGraphBuilder);

    // METHODS

    // Returns the AstSenItem that originally corresponds to this AstSenTree, or nullptr if no
    // original AstSenTree, or if the original AstSenTree had multiple AstSenItems.
    const AstSenItem* getOrigSenItem(AstSenTree* senTreep) {
        if (!senTreep->user1p()) {
            // Find the original simple AstSenTree, if any
            AstNode* const origp = [&]() -> AstSenItem* {
                // If more than one AstSenItems, then not a simple AstSenTree
                if (senTreep->sensesp()->nextp()) return nullptr;

                // Find the original AstSenTree
                auto it = m_trigToSen.find(senTreep->sensesp());
                if (it == m_trigToSen.end()) return nullptr;

                // If more than one AstSenItems on the original, then not a simple AstSenTree
                if (it->second->sensesp()->nextp()) return nullptr;

                // Else we found it.
                return it->second->sensesp();
            }();

            // We use the node itself as a sentinel to denote 'no original node'
            senTreep->user1p(origp ? origp : senTreep);
        }

        return senTreep->user1p() == senTreep ? nullptr : VN_AS(senTreep->user1p(), SenItem);
    }

    bool domainsExclusive(AstSenTree* fromp, AstSenTree* top) {
        // Return 'true' if we can prove that both 'from' and 'to' cannot both
        // be active on the same evaluation, or false if we can't prove this.
        //
        // This detects the case of 'always @(posedge clk)'
        // and 'always @(negedge clk)' being exclusive.
        //
        // Are there any other cases we need to handle? Maybe not,
        // because these are not exclusive:
        //   always @(posedge A or posedge B)
        //   always @(negedge A)
        //
        // ... unless you know more about A and B, which sounds hard.

        const AstSenItem* const fromSenItemp = getOrigSenItem(fromp);
        if (!fromSenItemp) return false;
        const AstSenItem* const toSenItemp = getOrigSenItem(top);
        if (!toSenItemp) return false;

        const AstNodeVarRef* const fromVarrefp = fromSenItemp->varrefp();
        if (!fromVarrefp) return false;
        const AstNodeVarRef* const toVarrefp = toSenItemp->varrefp();
        if (!toVarrefp) return false;

        // We know nothing about the relationship between different clocks here,
        // so only proceed if strictly the same clock.
        if (fromVarrefp->varScopep() != toVarrefp->varScopep()) return false;

        return fromSenItemp->edgeType().exclusiveEdge(toSenItemp->edgeType());
    }

    void addEdge(OrderMoveVertex* srcp, OrderMoveVertex* dstp) {
        new V3GraphEdge{m_moveGraphp.get(), srcp, dstp, 1};
    }

    void iterateLogicVertex(const OrderLogicVertex* lvtxp) {
        AstSenTree* const domainp = lvtxp->domainp();
        OrderMoveVertex* const lMoveVtxp = static_cast<OrderMoveVertex*>(lvtxp->userp());
        // Search forward from lvtxp, making new edges from lMoveVtxp forward
        for (const V3GraphEdge& edge : lvtxp->outEdges()) {
            if (edge.weight() == 0) continue;  // Was cut

            // OrderGraph is a bipartite graph, so we know it's an OrderVarVertex
            const OrderVarVertex* const vvtxp = static_cast<const OrderVarVertex*>(edge.top());

            // Look up OrderMoveVertex for this domain on this variable
            DomainMap& mapp = *static_cast<DomainMap*>(vvtxp->userp());
            const auto pair = mapp.emplace(domainp, nullptr);
            // Reference to the mapped OrderMoveVertex
            OrderMoveVertex*& vMoveVtxp = pair.first->second;

            // On first encounter, visit downstream logic dependent on this (var, domain)
            if (pair.second) vMoveVtxp = iterateVarVertex(vvtxp, domainp);

            // If no downstream dependents from this variable, then there is no need to add this
            // variable as a dependent.
            if (!vMoveVtxp) continue;

            // Add this (variable, domain) as dependent of the logic that writes it.
            addEdge(lMoveVtxp, vMoveVtxp);
        }
    }

    // Return the OrderMoveVertex for this (var, domain) pair, iff it has downstream dependencies,
    // otherwise return nullptr.
    OrderMoveVertex* iterateVarVertex(const OrderVarVertex* vvtxp, AstSenTree* domainp) {
        OrderMoveVertex* vMoveVtxp = nullptr;
        // Search forward from vvtxp, making new edges from vMoveVtxp forward
        for (const V3GraphEdge& edge : vvtxp->outEdges()) {
            if (edge.weight() == 0) continue;  // Was cut

            // OrderGraph is a bipartite graph, so we know it's an OrderLogicVertex
            const OrderLogicVertex* const lVtxp = edge.top()->as<OrderLogicVertex>();

            // Do not construct dependencies across exclusive domains.
            if (domainsExclusive(domainp, lVtxp->domainp())) continue;

            // there is a path from this vvtx to a logic vertex. Add the new edge.
            if (!vMoveVtxp) vMoveVtxp = new OrderMoveVertex{*m_moveGraphp, nullptr, domainp};
            OrderMoveVertex* const lMoveVxp = static_cast<OrderMoveVertex*>(lVtxp->userp());
            addEdge(vMoveVtxp, lMoveVxp);
        }
        return vMoveVtxp;
    }

public:
    static std::unique_ptr<OrderMoveGraph> apply(OrderGraph& orderGraph,
                                                 const V3Order::TrigToSenMap& trigToSen) {
        return std::move(OrderMoveGraphBuilder{orderGraph, trigToSen}.m_moveGraphp);
    }
};

//======================================================================
// OrderMoveGraph implementation

std::unique_ptr<OrderMoveGraph> OrderMoveGraph::build(OrderGraph& orderGraph,
                                                      const V3Order::TrigToSenMap& trigToSen) {
    return OrderMoveGraphBuilder::apply(orderGraph, trigToSen);
}
