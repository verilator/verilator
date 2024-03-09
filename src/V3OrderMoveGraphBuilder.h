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
//  Move graph builder for ordering
//
//*************************************************************************

#ifndef VERILATOR_V3ORDERMOVEGRAPHBUILDER_H_
#define VERILATOR_V3ORDERMOVEGRAPHBUILDER_H_

#include "config_build.h"
#include "verilatedos.h"

#include "V3Ast.h"
#include "V3Graph.h"
#include "V3Order.h"
#include "V3OrderGraph.h"

template <class T_MoveVertex>
class V3OrderMoveGraphBuilder final {
    // V3OrderMoveGraphBuilder takes as input the fine-grained bipartite OrderGraph of
    // OrderLogicVertex and OrderVarVertex vertices. It produces a slightly coarsened graph to
    // drive the code scheduling.
    //
    // * For the serial code scheduler, the new graph contains
    //   nodes of type OrderMoveVertex.
    //
    // * For the threaded code scheduler, the new graph contains
    //   nodes of type MTaskMoveVertex.
    //
    // * The difference in output type is abstracted away by the
    //   'T_MoveVertex' template parameter; ProcessMoveBuildGraph otherwise
    //   works the same way for both cases.

    // NODE STATE
    // AstSenTree::user1p()     -> AstSenTree:  Original AstSenTree for trigger
    const VNUser1InUse m_user1InUse;

    // TYPES
    using DomainMap = std::map<const AstSenTree*, T_MoveVertex*>;

    // MEMBERS
    const OrderGraph& m_orderGraph;  // Input OrderGraph
    // Output graph of T_MoveVertex vertices
    std::unique_ptr<V3Graph> m_outGraphp{new V3Graph};
    // Map from Trigger reference AstSenItem to the original AstSenTree
    const V3Order::TrigToSenMap& m_trigToSen;
    // Storage for domain -> T_MoveVertex, maps held in OrderVarVertex::userp()
    std::deque<DomainMap> m_domainMaps;

    // CONSTRUCTORS
    V3OrderMoveGraphBuilder(const OrderGraph& orderGraph, const V3Order::TrigToSenMap& trigToSen)
        : m_orderGraph{orderGraph}
        , m_trigToSen{trigToSen} {
        build();
    }
    virtual ~V3OrderMoveGraphBuilder() = default;
    VL_UNCOPYABLE(V3OrderMoveGraphBuilder);
    VL_UNMOVABLE(V3OrderMoveGraphBuilder);

    // METHODS
    void build() {
        // How this works:
        //  - Create a T_MoveVertex for each OrderLogicVertex.
        //  - Following each OrderLogicVertex, search forward in the context of
        //    its domain...
        //    * If we encounter another OrderLogicVertex in non-exclusive
        //      domain, make the T_MoveVertex->T_MoveVertex edge.
        //    * If we encounter an OrderVarVertex, make a Vertex for the
        //      (OrderVarVertex, domain) pair and continue to search
        //      forward in the context of the same domain.  Unless we
        //      already created that pair, in which case, we've already
        //      done the forward search, so stop.

        // For each logic vertex, make a T_MoveVertex, for each variable vertex, allocate storage
        for (V3GraphVertex* itp = m_orderGraph.verticesBeginp(); itp; itp = itp->verticesNextp()) {
            if (OrderLogicVertex* const lvtxp = itp->cast<OrderLogicVertex>()) {
                lvtxp->userp(new T_MoveVertex{*m_outGraphp, lvtxp, lvtxp->domainp()});
            } else {
                // This is an OrderVarVertex
                m_domainMaps.emplace_back();
                itp->userp(&m_domainMaps.back());
            }
        }
        // Build edges between logic vertices
        for (V3GraphVertex* itp = m_orderGraph.verticesBeginp(); itp; itp = itp->verticesNextp()) {
            if (OrderLogicVertex* const lvtxp = itp->cast<OrderLogicVertex>()) {
                iterateLogicVertex(lvtxp);
            }
        }
    }

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

    void iterateLogicVertex(const OrderLogicVertex* lvtxp) {
        AstSenTree* const domainp = lvtxp->domainp();
        T_MoveVertex* const lMoveVtxp = static_cast<T_MoveVertex*>(lvtxp->userp());
        // Search forward from lvtxp, making new edges from lMoveVtxp forward
        for (V3GraphEdge* edgep = lvtxp->outBeginp(); edgep; edgep = edgep->outNextp()) {
            if (edgep->weight() == 0) continue;  // Was cut

            // OrderGraph is a bipartite graph, so we know it's an OrderVarVertex
            const OrderVarVertex* const vvtxp = static_cast<const OrderVarVertex*>(edgep->top());

            // Look up T_MoveVertex for this domain on this variable
            DomainMap& mapp = *static_cast<DomainMap*>(vvtxp->userp());
            const auto pair = mapp.emplace(domainp, nullptr);
            // Reference to the mapped T_MoveVertex
            T_MoveVertex*& vMoveVtxp = pair.first->second;

            // On first encounter, visit downstream logic dependent on this (var, domain)
            if (pair.second) vMoveVtxp = iterateVarVertex(vvtxp, domainp);

            // If no downstream dependents from this variable, then there is no need to add this
            // variable as a dependent.
            if (!vMoveVtxp) continue;

            // Add this (variable, domain) as dependent of the logic that writes it.
            new V3GraphEdge{m_outGraphp.get(), lMoveVtxp, vMoveVtxp, 1};
        }
    }

    // Return the T_MoveVertex for this (var, domain) pair, iff it has downstream dependencies,
    // otherwise return nullptr.
    T_MoveVertex* iterateVarVertex(const OrderVarVertex* vvtxp, AstSenTree* domainp) {
        T_MoveVertex* vMoveVtxp = nullptr;
        // Search forward from vvtxp, making new edges from vMoveVtxp forward
        for (V3GraphEdge* edgep = vvtxp->outBeginp(); edgep; edgep = edgep->outNextp()) {
            if (edgep->weight() == 0) continue;  // Was cut

            // OrderGraph is a bipartite graph, so we know it's an OrderLogicVertex
            const OrderLogicVertex* const lVtxp = edgep->top()->as<OrderLogicVertex>();

            // Do not construct dependencies across exclusive domains.
            if (domainsExclusive(domainp, lVtxp->domainp())) continue;

            // there is a path from this vvtx to a logic vertex. Add the new edge.
            if (!vMoveVtxp) vMoveVtxp = new T_MoveVertex{*m_outGraphp, nullptr, domainp};
            T_MoveVertex* const lMoveVxp = static_cast<T_MoveVertex*>(lVtxp->userp());
            new V3GraphEdge{m_outGraphp.get(), vMoveVtxp, lMoveVxp, 1};
        }
        return vMoveVtxp;
    }

public:
    static std::unique_ptr<V3Graph> apply(const OrderGraph& orderGraph,
                                          const V3Order::TrigToSenMap& trigToSen) {
        return std::move(V3OrderMoveGraphBuilder{orderGraph, trigToSen}.m_outGraphp);
    }
};

#endif  // Guard
