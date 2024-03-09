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
//  Serial code ordering
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Graph.h"
#include "V3List.h"
#include "V3OrderCFuncEmitter.h"
#include "V3OrderInternal.h"
#include "V3OrderMoveGraphBuilder.h"

#include <memory>

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################

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
    OrderMoveDomScope* nextp() const { return m_listEnt.nextp(); }
};

OrderMoveDomScope::DomScopeMap OrderMoveDomScope::s_dsMap;

// ######################################################################
//  OrderMoveVertex constructor

class OrderMoveVertex final : public V3GraphVertex {
    VL_RTTI_IMPL(OrderMoveVertex, V3GraphVertex)

    // The corresponding logic vertex, or nullptr if this MoveVertex stands for a variable vertex.
    OrderLogicVertex* const m_logicp;
    OrderMoveDomScope& m_domScope;  // DomScope this vertex is under
    V3ListEnt<OrderMoveVertex*> m_listEnt;  // List entry for ready list under DomScope

    // METHODS
    std::string dotColor() const override { return logicp() ? logicp()->dotColor() : ""; }

    std::string name() const override VL_MT_STABLE {
        if (!logicp()) {
            return "var";
        } else {
            std::string nm = logicp()->name() + "\\n";
            nm += "MV:";
            nm += +" d=" + cvtToHex(logicp()->domainp());
            nm += +" s=" + cvtToHex(logicp()->scopep());
            return nm;
        }
    }

public:
    // CONSTRUCTORS
    OrderMoveVertex(V3Graph& graph, OrderLogicVertex* lVtxp,
                    const AstSenTree* domainp) VL_MT_DISABLED
        : V3GraphVertex{&graph},
          m_logicp{lVtxp},
          m_domScope{OrderMoveDomScope::getOrCreate(domainp, lVtxp ? lVtxp->scopep() : nullptr)} {
        UASSERT_OBJ(!lVtxp || lVtxp->domainp() == domainp, lVtxp, "Wrong domain for Move vertex");
    }
    ~OrderMoveVertex() override = default;

    OrderLogicVertex* logicp() const VL_MT_STABLE { return m_logicp; }
    OrderMoveDomScope& domScope() const { return m_domScope; }

    void unlinkFrom(V3List<OrderMoveVertex*>& list) { m_listEnt.unlink(list, this); }
    void appendTo(V3List<OrderMoveVertex*>& list) { m_listEnt.pushBack(list, this); }
};

//######################################################################
// OrderSerial class

class OrderSerial final {
    // STATE
    std::unique_ptr<V3Graph> m_moveGraphp;  // Graph of logic elements to move
    V3List<OrderMoveDomScope*> m_readyDomScopeps;  // List of DomScopes which have ready vertices
    V3OrderCFuncEmitter m_emitter;  // Code emitter to construct the result

    // METHODS

    // Take the given waiting logic vertex, and move it to the ready list its DomScope
    void logicReady(OrderMoveVertex* lVtxp) {
        UASSERT_OBJ(lVtxp->logicp(), lVtxp, "logicReady called on variable vertex");
        UASSERT_OBJ(lVtxp->inEmpty(), lVtxp, "logicReady called on vertex with incoming edge");
        // Add this logic vertex to the ready list of its DomScope
        OrderMoveDomScope& domScope = lVtxp->domScope();
        lVtxp->appendTo(domScope.readyVertices());
        // Add the DomScope to the global ready list if not there yet
        if (!domScope.isOnList()) domScope.appendTo(m_readyDomScopeps);
    }

    // Remove the given variable vertex, and check if any of its dependents are ready
    void varReady(OrderMoveVertex* vVtxp) {
        UASSERT_OBJ(!vVtxp->logicp(), vVtxp, "varReady called on logic vertex");
        UASSERT_OBJ(vVtxp->inEmpty(), vVtxp, "varReady called on vertex with incoming edge");
        // Remove dependency of consumer logic on this variable, and mark them ready if this is
        // the last dependency.
        for (V3GraphEdge *edgep = vVtxp->outBeginp(), *nextp; edgep; edgep = nextp) {
            // Pick up next as we are deleting it
            nextp = edgep->outNextp();
            // The dependent logic
            OrderMoveVertex* const lVtxp = edgep->top()->as<OrderMoveVertex>();
            UASSERT_OBJ(lVtxp->logicp(), lVtxp, "The move graph should be bipartite");
            // Delete this edge
            VL_DO_DANGLING(edgep->unlinkDelete(), edgep);
            // If this was the last dependency, the consumer logic is ready
            if (lVtxp->inEmpty()) logicReady(lVtxp);
        }

        // Can delete the vertex now
        VL_DO_DANGLING(vVtxp->unlinkDelete(m_moveGraphp.get()), vVtxp);
    }

    void process(const OrderGraph& orderGraph, const std::string& tag,
                 const V3Order::TrigToSenMap& trigToSen) {
        // Build the move graph
        m_moveGraphp = V3OrderMoveGraphBuilder<OrderMoveVertex>::apply(orderGraph, trigToSen);
        if (dumpGraphLevel() >= 9) m_moveGraphp->dumpDotFilePrefixed(tag + "_ordermv_start");
        m_moveGraphp->removeRedundantEdgesMax(&V3GraphEdge::followAlwaysTrue);
        if (dumpGraphLevel() >= 4) m_moveGraphp->dumpDotFilePrefixed(tag + "_ordermv_simpl");

        // Mark initially ready vertices (those with no dependencies)
        for (V3GraphVertex* vtxp = m_moveGraphp->verticesBeginp(); vtxp;
             vtxp = vtxp->verticesNextp()) {
            if (!vtxp->inEmpty()) continue;
            OrderMoveVertex* const mVtxp = vtxp->as<OrderMoveVertex>();
            if (mVtxp->logicp()) {
                logicReady(mVtxp);
            } else {
                varReady(mVtxp);
            }
        }

        // Emit all logic as they become ready
        for (OrderMoveDomScope *currDomScopep = m_readyDomScopeps.begin(), *nextDomScopep;
             currDomScopep; currDomScopep = nextDomScopep) {
            m_emitter.forceNewFunction();

            // Emit all logic ready under the current DomScope
            V3List<OrderMoveVertex*>& currReadyList = currDomScopep->readyVertices();
            UASSERT(!currReadyList.empty(), "DomScope on ready list, not has no ready vertices");
            while (OrderMoveVertex* const lVtxp = currReadyList.begin()) {
                UASSERT_OBJ(&lVtxp->domScope() == currDomScopep, lVtxp, "DomScope mismatch");
                // Unlink vertex from ready list under the DomScope
                lVtxp->unlinkFrom(currReadyList);
                // Unlink DomScope from the global ready list if this is the last vertex
                // TODO: should do this later
                if (currReadyList.empty()) currDomScopep->unlinkFrom(m_readyDomScopeps);

                // Actually emit the logic under this vertex
                m_emitter.emitLogic(lVtxp->logicp());

                // Remove dependency of produced variables on this logic, and mark them ready if
                // this is the last producer.
                for (V3GraphEdge *edgep = lVtxp->outBeginp(), *nextp; edgep; edgep = nextp) {
                    // Pick up next as we are deleting it
                    nextp = edgep->outNextp();
                    // The dependent variable
                    OrderMoveVertex* const vVtxp = edgep->top()->as<OrderMoveVertex>();
                    UASSERT_OBJ(!vVtxp->logicp(), vVtxp, "The move graph should be bipartite");
                    // Delete this edge
                    VL_DO_DANGLING(edgep->unlinkDelete(), edgep);
                    // If this was the last producer, the produced variable is ready
                    if (vVtxp->inEmpty()) varReady(vVtxp);
                }

                // Can delete the vertex now
                VL_DO_DANGLING(lVtxp->unlinkDelete(m_moveGraphp.get()), lVtxp);
            }

            // Done with this DomScope, pick a new one to emit. Prefer a new scope under the
            // same domain. If there isn't one, just pick teh head of the global ready list
            nextDomScopep = m_readyDomScopeps.begin();
            for (OrderMoveDomScope* huntp = nextDomScopep; huntp; huntp = huntp->nextp()) {
                if (huntp->domainp() == currDomScopep->domainp()) {
                    nextDomScopep = huntp;
                    break;
                }
            }
        }

        UASSERT(m_moveGraphp->empty(), "Waiting vertices remain, but none are ready");
    }

    // CONSTRUCTOR
    OrderSerial(const OrderGraph& orderGraph, const std::string& tag,
                const V3Order::TrigToSenMap& trigToSen, bool slow)
        : m_emitter{tag, slow} {
        OrderMoveDomScope::clear();
        process(orderGraph, tag, trigToSen);
        OrderMoveDomScope::clear();
    }

    ~OrderSerial() = default;

public:
    // Order the logic
    static std::vector<AstActive*> apply(const OrderGraph& graph, const std::string& tag,
                                         const V3Order::TrigToSenMap& trigToSen, bool slow) {
        return OrderSerial{graph, tag, trigToSen, slow}.m_emitter.getAndClearActiveps();
    }
};

std::vector<AstActive*> V3Order::createSerial(const OrderGraph& graph, const std::string& tag,
                                              const TrigToSenMap& trigToSen, bool slow) {

    UINFO(2, "  Constructing serial code for '" + tag + "'");
    return OrderSerial::apply(graph, tag, trigToSen, slow);
}
