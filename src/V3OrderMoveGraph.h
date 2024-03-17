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

#ifndef VERILATOR_V3ORDERMOVEGRAPH_H_
#define VERILATOR_V3ORDERMOVEGRAPH_H_

#include "config_build.h"
#include "verilatedos.h"

#include "V3Ast.h"
#include "V3Graph.h"
#include "V3Order.h"
#include "V3OrderGraph.h"

class OrderMoveVertex;

// Information stored for each unique (domain, scope) pair. Mainly a list of ready vertices under
// that (domain, scope). OrderMoveDomScope instances are themselves organized into a global ready
// list if they have ready vertices.
class OrderMoveDomScope final {
    // STATE
    V3List<OrderMoveVertex*> m_readyVertices;  // Ready vertices in this domain/scope
    V3ListEnt<OrderMoveDomScope*> m_listEnt;  // List entry to store this instance
    bool m_isOnList = false;  // True if DomScope is already on a list through m_listEnt
    const AstSenTree* const m_domainp;  // Domain the vertices belong to
    const AstScope* const m_scopep;  // Scope the vertices belong to

    // Key type for map below
    class DomScopeMapKey final {
        const AstSenTree* const m_domainp;
        const AstScope* const m_scopep;

    public:
        DomScopeMapKey(const AstSenTree* domainp, const AstScope* scopep)
            : m_domainp{domainp}
            , m_scopep{scopep} {}

        struct Hash final {
            size_t operator()(const DomScopeMapKey& key) const {
                V3Hash hash{reinterpret_cast<uintptr_t>(key.m_domainp)};
                hash += reinterpret_cast<uintptr_t>(key.m_scopep);
                return hash.value();
            }
        };

        struct Equal final {
            bool operator()(const DomScopeMapKey& a, const DomScopeMapKey& b) const {
                return a.m_domainp == b.m_domainp && a.m_scopep == b.m_scopep;
            }
        };
    };

    using DomScopeMap = std::unordered_map<DomScopeMapKey, OrderMoveDomScope, DomScopeMapKey::Hash,
                                           DomScopeMapKey::Equal>;
    // Map from Domain/Scope to the corresponding DomScope instance
    static DomScopeMap s_dsMap;

public:
    // STATIC MEMBERS
    static OrderMoveDomScope& getOrCreate(const AstSenTree* domainp, const AstScope* scopep) {
        return s_dsMap
            .emplace(std::piecewise_construct,  //
                     std::forward_as_tuple(domainp, scopep),  //
                     std::forward_as_tuple(domainp, scopep))
            .first->second;
    }
    static void clear() { s_dsMap.clear(); }

    // CONSTRUCTOR
    OrderMoveDomScope(const AstSenTree* domainp, const AstScope* scopep)
        : m_domainp{domainp}
        , m_scopep{scopep} {}
    ~OrderMoveDomScope() = default;
    VL_UNCOPYABLE(OrderMoveDomScope);
    VL_UNMOVABLE(OrderMoveDomScope);

    // MEMBERS
    V3List<OrderMoveVertex*>& readyVertices() { return m_readyVertices; }
    const AstSenTree* domainp() const { return m_domainp; }
    const AstScope* scopep() const { return m_scopep; }

    bool isOnList() const { return m_isOnList; }
    void unlinkFrom(V3List<OrderMoveDomScope*>& list) {
        UASSERT_OBJ(m_isOnList, m_domainp, "unlinkFrom, but DomScope is not on a list");
        m_isOnList = false;
        m_listEnt.unlink(list, this);
    }
    void appendTo(V3List<OrderMoveDomScope*>& list) {
        UASSERT_OBJ(!m_isOnList, m_domainp, "appendTo, but DomScope is already on a list");
        m_isOnList = true;
        m_listEnt.pushBack(list, this);
    }
    void prependTo(V3List<OrderMoveDomScope*>& list) {
        UASSERT_OBJ(!m_isOnList, m_domainp, "prependTo, but DomScope is already on a list");
        m_isOnList = true;
        m_listEnt.pushFront(list, this);
    }
    OrderMoveDomScope* nextp() const { return m_listEnt.nextp(); }
};

//======================================================================
// Graph type

// OrderMoveGraph is constructed from the fine-grained OrderGraph.
// It is a slightly coarsened representation of dependencies used to drive serialization.
class OrderMoveGraph final : public V3Graph {
public:
    // Build an OrderMoveGraph from an OrderGraph
    static std::unique_ptr<OrderMoveGraph> build(const OrderGraph&, const V3Order::TrigToSenMap&);
};

//======================================================================
// Vertex types

class OrderMoveVertex final : public V3GraphVertex {
    VL_RTTI_IMPL(OrderMoveVertex, V3GraphVertex)

    // The corresponding logic vertex, or nullptr if this MoveVertex stands for a variable vertex.
    OrderLogicVertex* const m_logicp;
    OrderMoveDomScope& m_domScope;  // DomScope this vertex is under
    V3ListEnt<OrderMoveVertex*> m_listEnt;  // List entry to store this Vertex

    // METHODS
    std::string dotColor() const override { return logicp() ? logicp()->dotColor() : "yellow"; }

    std::string name() const override VL_MT_STABLE {
        std::string nm;
        if (!logicp()) {
            nm = "var";
        } else {
            nm = logicp()->name() + "\\n";
            nm += "MV:";
            nm += +" d=" + cvtToHex(logicp()->domainp());
            nm += +" s=" + cvtToHex(logicp()->scopep());
        }
        if (userp()) nm += "\nu=" + cvtToHex(userp());
        return nm;
    }

public:
    // CONSTRUCTORS
    OrderMoveVertex(OrderMoveGraph& graph, OrderLogicVertex* lVtxp,
                    const AstSenTree* domainp) VL_MT_DISABLED;
    ~OrderMoveVertex() override = default;
    VL_UNCOPYABLE(OrderMoveVertex);

    OrderLogicVertex* logicp() const VL_MT_STABLE { return m_logicp; }
    OrderMoveDomScope& domScope() const { return m_domScope; }

    void unlinkFrom(V3List<OrderMoveVertex*>& list) { m_listEnt.unlink(list, this); }
    void appendTo(V3List<OrderMoveVertex*>& list) { m_listEnt.pushBack(list, this); }
    void moveAppend(V3List<OrderMoveVertex*>& src, V3List<OrderMoveVertex*>& dst) {
        m_listEnt.moveAppend(src, dst, this);
    }
    OrderMoveVertex* nextp() const { return m_listEnt.nextp(); }
};

//======================================================================
// Serializer for OrderMoveGraph

class OrderMoveGraphSerializer final {
    // STATE
    V3List<OrderMoveDomScope*> m_readyDomScopeps;  // List of DomScopes which have ready vertices
    OrderMoveDomScope* m_nextDomScopep = nullptr;  // Next DomScope to yield from

    // METHODS

    void ready(OrderMoveVertex* vtxp) {
        UASSERT_OBJ(!vtxp->user(), vtxp, "'ready' called on vertex with pending dependencies");
        if (vtxp->logicp()) {
            // Add this vertex to the ready list of its DomScope
            OrderMoveDomScope& domScope = vtxp->domScope();
            vtxp->appendTo(domScope.readyVertices());
            // Add the DomScope to the global ready list if not there yet
            if (!domScope.isOnList()) domScope.appendTo(m_readyDomScopeps);
        } else {  // This is a bit nonsense at this point, but equivalent to the old version
            // Remove dependency on vertex we are returning. This might add vertices to
            // currReadyList.
            for (V3GraphEdge *edgep = vtxp->outBeginp(), *nextp; edgep; edgep = nextp) {
                nextp = edgep->outNextp();
                // The dependent variable
                OrderMoveVertex* const dVtxp = edgep->top()->as<OrderMoveVertex>();
                // Update number of dependencies
                const uint32_t nDeps = dVtxp->user() - 1;
                dVtxp->user(nDeps);
                // If no more dependencies, mark it ready
                if (!nDeps) ready(dVtxp);
            }
        }
    }

public:
    // CONSTRUCTOR
    OrderMoveGraphSerializer(OrderMoveGraph& moveGraph) {
        // Set V3GraphVertex::user() to the number of incoming edges (upstream dependencies)
        for (V3GraphVertex *vtxp = moveGraph.verticesBeginp(), *nextp; vtxp; vtxp = nextp) {
            nextp = vtxp->verticesNextp();
            uint32_t nDeps = 0;
            for (V3GraphEdge* edgep = vtxp->inBeginp(); edgep; edgep = edgep->inNextp()) ++nDeps;
            vtxp->user(nDeps);
        }
    }
    ~OrderMoveGraphSerializer() = default;
    VL_UNCOPYABLE(OrderMoveGraphSerializer);

    // Add a seed vertex to the ready lists
    void addSeed(OrderMoveVertex* vtxp) { ready(vtxp); }

    OrderMoveVertex* getNext() {
        if (!m_nextDomScopep) m_nextDomScopep = m_readyDomScopeps.begin();
        OrderMoveDomScope* const currDomScopep = m_nextDomScopep;
        // If nothing is ready, we are done
        if (!currDomScopep) return nullptr;

        V3List<OrderMoveVertex*>& currReadyList = currDomScopep->readyVertices();
        // This is the vertex we are returning now
        OrderMoveVertex* const mVtxp = currReadyList.begin();
        UASSERT(mVtxp, "DomScope on ready list, but has no ready vertices");
        // Unlink vertex from ready list under the DomScope
        mVtxp->unlinkFrom(currReadyList);

        // Nonsesne, but what we used to do
        if (currReadyList.empty()) currDomScopep->unlinkFrom(m_readyDomScopeps);

        // Remove dependency on vertex we are returning. This might add vertices to currReadyList.
        for (V3GraphEdge *edgep = mVtxp->outBeginp(), *nextp; edgep; edgep = nextp) {
            nextp = edgep->outNextp();
            // The dependent variable
            OrderMoveVertex* const dVtxp = edgep->top()->as<OrderMoveVertex>();
            // Update number of dependencies
            const uint32_t nDeps = dVtxp->user() - 1;
            dVtxp->user(nDeps);
            // If no more dependencies, mark it ready
            if (!nDeps) ready(dVtxp);
        }

        // If no more ready vertices in the current DomScope, prefer to continue with a new scope
        // under the same domain.
        if (currReadyList.empty()) {
            m_nextDomScopep = nullptr;
            for (OrderMoveDomScope* dsp = m_readyDomScopeps.begin(); dsp; dsp = dsp->nextp()) {
                if (dsp->domainp() == currDomScopep->domainp()) {
                    m_nextDomScopep = dsp;
                    break;
                }
            }
        }

        // Finally yield the selected vertex
        return mVtxp;
    }
};

#endif  // Guard
