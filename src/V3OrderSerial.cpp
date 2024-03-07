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

#include <vector>

VL_DEFINE_DEBUG_FUNCTIONS;

class OrderMoveDomScope;

class OrderMoveVertex final : public V3GraphVertex {
    VL_RTTI_IMPL(OrderMoveVertex, V3GraphVertex)
    enum OrderMState : uint8_t { POM_WAIT, POM_READY, POM_MOVED };

    OrderLogicVertex* const m_logicp;
    OrderMState m_state;  // Movement state
    OrderMoveDomScope* m_domScopep;  // Domain/scope list information

protected:
    friend class OrderProcess;
    friend class OrderMoveVertexMaker;
    // These only contain the "next" item,
    // for the head of the list, see the same var name under OrderProcess
    V3ListEnt<OrderMoveVertex*> m_pomWaitingE;  // List of nodes needing inputs to become ready
    V3ListEnt<OrderMoveVertex*> m_readyVerticesE;  // List of ready under domain/scope
public:
    // CONSTRUCTORS
    OrderMoveVertex(V3Graph* graphp, OrderLogicVertex* logicp) VL_MT_DISABLED
        : V3GraphVertex{graphp},
          m_logicp{logicp},
          m_state{POM_WAIT},
          m_domScopep{nullptr} {}
    ~OrderMoveVertex() override = default;

    // METHODS
    string dotColor() const override {
        if (logicp()) {
            return logicp()->dotColor();
        } else {
            return "";
        }
    }

    string name() const override VL_MT_STABLE {
        string nm;
        if (VL_UNCOVERABLE(!logicp())) {  // Avoid crash when debugging
            nm = "nul";  // LCOV_EXCL_LINE
        } else {
            nm = logicp()->name();
            nm += (string{"\\nMV:"} + " d=" + cvtToHex(logicp()->domainp())
                   + " s=" + cvtToHex(logicp()->scopep()));
        }
        return nm;
    }
    OrderLogicVertex* logicp() const VL_MT_STABLE { return m_logicp; }
    bool isWait() const { return m_state == POM_WAIT; }
    void setReady() VL_MT_DISABLED {
        UASSERT(m_state == POM_WAIT, "Wait->Ready on node not in proper state");
        m_state = POM_READY;
    }
    void setMoved() VL_MT_DISABLED {
        UASSERT(m_state == POM_READY, "Ready->Moved on node not in proper state");
        m_state = POM_MOVED;
    }
    OrderMoveDomScope* domScopep() const { return m_domScopep; }
    OrderMoveVertex* pomWaitingNextp() const { return m_pomWaitingE.nextp(); }
    void domScopep(OrderMoveDomScope* ds) { m_domScopep = ds; }
};

//######################################################################

class OrderProcess;

class OrderMoveDomScope final {
    // Information stored for each unique loop, domain & scope trifecta
public:
    V3ListEnt<OrderMoveDomScope*> m_readyDomScopeE;  // List of next ready dom scope
    V3List<OrderMoveVertex*> m_readyVertices;  // Ready vertices with same domain & scope
private:
    bool m_onReadyList = false;  // True if DomScope is already on list of ready dom/scopes
    const AstSenTree* const m_domainp;  // Domain all vertices belong to
    const AstScope* const m_scopep;  // Scope all vertices belong to

    using DomScopeKey = std::pair<const AstSenTree*, const AstScope*>;
    using DomScopeMap = std::map<DomScopeKey, OrderMoveDomScope*>;
    static DomScopeMap s_dsMap;  // Structure registered for each dom/scope pairing

public:
    OrderMoveDomScope(const AstSenTree* domainp, const AstScope* scopep)
        : m_domainp{domainp}
        , m_scopep{scopep} {}
    OrderMoveDomScope* readyDomScopeNextp() const { return m_readyDomScopeE.nextp(); }
    const AstSenTree* domainp() const { return m_domainp; }
    const AstScope* scopep() const { return m_scopep; }
    // Check the domScope is on ready list, add if not
    void ready(OrderProcess* opp);
    // Mark one vertex as finished, remove from ready list if done
    void movedVertex(OrderProcess* opp, OrderMoveVertex* vertexp);
    // STATIC MEMBERS (for lookup)
    static void clear() {
        for (const auto& itr : s_dsMap) delete itr.second;
        s_dsMap.clear();
    }
    V3List<OrderMoveVertex*>& readyVertices() { return m_readyVertices; }
    static OrderMoveDomScope* findCreate(const AstSenTree* domainp, const AstScope* scopep) {
        const DomScopeKey key = std::make_pair(domainp, scopep);
        const auto pair = s_dsMap.emplace(key, nullptr);
        if (pair.second) pair.first->second = new OrderMoveDomScope{domainp, scopep};
        return pair.first->second;
    }
    string name() const {
        return string{"MDS:"} + " d=" + cvtToHex(domainp()) + " s=" + cvtToHex(scopep());
    }
};

// ######################################################################
//  OrderMoveVertexMaker and related

class OrderMoveVertexMaker final
    : public V3OrderMoveGraphBuilder<OrderMoveVertex>::MoveVertexMaker {
    // MEMBERS
    V3Graph* m_pomGraphp;
    V3List<OrderMoveVertex*>* m_pomWaitingp;

public:
    // CONSTRUCTORS
    OrderMoveVertexMaker(V3Graph* pomGraphp, V3List<OrderMoveVertex*>* pomWaitingp)
        : m_pomGraphp{pomGraphp}
        , m_pomWaitingp{pomWaitingp} {}
    // METHODS
    OrderMoveVertex* makeVertexp(OrderLogicVertex* lvertexp, const OrderEitherVertex*,
                                 const AstSenTree* domainp) override {
        OrderMoveVertex* const resultp = new OrderMoveVertex{m_pomGraphp, lvertexp};
        AstScope* const scopep = lvertexp ? lvertexp->scopep() : nullptr;
        resultp->domScopep(OrderMoveDomScope::findCreate(domainp, scopep));
        resultp->m_pomWaitingE.pushBack(*m_pomWaitingp, resultp);
        return resultp;
    }

private:
    VL_UNCOPYABLE(OrderMoveVertexMaker);
};

OrderMoveDomScope::DomScopeMap OrderMoveDomScope::s_dsMap;

std::ostream& operator<<(std::ostream& lhs, const OrderMoveDomScope& rhs) {
    lhs << rhs.name();
    return lhs;
}

//######################################################################
// OrderProcess class

class OrderProcess final {
    // STATE
    const OrderGraph& m_graph;  // The ordering graph

    // Map from Trigger reference AstSenItem to the original AstSenTree
    const V3Order::TrigToSenMap& m_trigToSen;

    const string m_tag;  // Substring to add to generated names

    V3Graph m_pomGraph;  // Graph of logic elements to move
    V3List<OrderMoveVertex*> m_pomWaiting;  // List of nodes needing inputs to become ready
    friend class OrderMoveDomScope;
    V3List<OrderMoveDomScope*> m_pomReadyDomScope;  // List of ready domain/scope pairs, by loopId

    V3OrderCFuncEmitter m_emitter;

    // METHODS
    // processMove* routines schedule serial execution
    void processMove();
    void processMoveClear();
    void processMoveBuildGraph();
    void processMovePrepReady();
    void processMoveReadyOne(OrderMoveVertex* vertexp);
    void processMoveDoneOne(OrderMoveVertex* vertexp);

    // CONSTRUCTOR
    OrderProcess(const OrderGraph& graph, const string& tag,
                 const V3Order::TrigToSenMap& trigToSen, bool slow)
        : m_graph{graph}
        , m_trigToSen{trigToSen}
        , m_tag{tag}
        , m_emitter{tag, slow} {
        UINFO(2, "  Construct Move Graph...\n");
        processMoveBuildGraph();
        // Different prefix (ordermv) as it's not the same graph
        if (dumpGraphLevel() >= 4) m_pomGraph.dumpDotFilePrefixed(m_tag + "_ordermv_start");
        m_pomGraph.removeRedundantEdgesMax(&V3GraphEdge::followAlwaysTrue);
        if (dumpGraphLevel() >= 4) m_pomGraph.dumpDotFilePrefixed(m_tag + "_ordermv_simpl");

        UINFO(2, "  Move...\n");
        processMove();
    }

    ~OrderProcess() = default;

public:
    // Order the logic
    static std::vector<AstActive*> main(const OrderGraph& graph, const string& tag,
                                        const V3Order::TrigToSenMap& trigToSen, bool slow) {
        return OrderProcess{graph, tag, trigToSen, slow}.m_emitter.getAndClearActiveps();
    }
};

//######################################################################
// OrderMoveDomScope methods

// Check the domScope is on ready list, add if not
void OrderMoveDomScope::ready(OrderProcess* opp) {
    if (!m_onReadyList) {
        m_onReadyList = true;
        m_readyDomScopeE.pushBack(opp->m_pomReadyDomScope, this);
    }
}

// Mark one vertex as finished, remove from ready list if done
void OrderMoveDomScope::movedVertex(OrderProcess* opp, OrderMoveVertex* vertexp) {
    UASSERT_OBJ(m_onReadyList, vertexp,
                "Moving vertex from ready when nothing was on que as ready.");
    if (m_readyVertices.empty()) {  // Else more work to get to later
        m_onReadyList = false;
        m_readyDomScopeE.unlink(opp->m_pomReadyDomScope, this);
    }
}

void OrderProcess::processMoveClear() {
    OrderMoveDomScope::clear();
    m_pomWaiting.reset();
    m_pomReadyDomScope.reset();
    m_pomGraph.clear();
}

void OrderProcess::processMoveBuildGraph() {
    // Build graph of only vertices
    UINFO(5, "  MoveBuildGraph\n");
    processMoveClear();
    // Vertex::user->OrderMoveVertex*, last edge added or nullptr=none
    m_pomGraph.userClearVertices();

    OrderMoveVertexMaker createOrderMoveVertex(&m_pomGraph, &m_pomWaiting);
    V3OrderMoveGraphBuilder<OrderMoveVertex> serialPMBG(&m_graph, &m_pomGraph, m_trigToSen,
                                                        &createOrderMoveVertex);
    serialPMBG.build();
}

//######################################################################
// OrderVisitor - Moving

void OrderProcess::processMove() {
    // The graph routines have already sorted the vertexes and edges into best->worst order
    //   Make a new waiting graph with only OrderLogicVertex's
    //   (Order is preserved in the recreation so the sorting is preserved)
    //   Move any node with all inputs ready to a "ready" graph mapped by domain and then scope
    //   While waiting graph ! empty  (and also known: something in ready graph)
    //     For all scopes in domain of top ready vertex
    //       For all vertexes in domain&scope of top ready vertex
    //           Make ordered activation block for this module
    //           Add that new activation to the list of calls to make.
    //           Move logic to ordered active
    //           Any children that have all inputs now ready move from waiting->ready graph
    //           (This may add nodes the for loop directly above needs to detext)
    processMovePrepReady();

    // New domain... another loop
    UINFO(5, "  MoveIterate\n");
    while (!m_pomReadyDomScope.empty()) {
        // Start with top node on ready list's domain & scope
        OrderMoveDomScope* domScopep = m_pomReadyDomScope.begin();
        OrderMoveVertex* const topVertexp
            = domScopep->readyVertices().begin();  // lintok-begin-on-ref
        UASSERT(topVertexp, "domScope on ready list without any nodes ready under it");
        // Work on all scopes ready inside this domain
        while (domScopep) {
            UINFO(6, "   MoveDomain l=" << domScopep->domainp() << endl);
            // Process all nodes ready under same domain & scope
            m_emitter.forceNewFunction();
            V3List<OrderMoveVertex*>& readyVertices = domScopep->readyVertices();
            while (OrderMoveVertex* vertexp = readyVertices.begin()) {
                UASSERT_OBJ(vertexp->domScopep() == domScopep, vertexp, "Domain mismatch");
                m_emitter.emitLogic(vertexp->logicp());
                processMoveDoneOne(vertexp);
            }
            // Done with scope/domain pair, pick new scope under same domain, or nullptr if none
            // left
            OrderMoveDomScope* domScopeNextp = nullptr;
            for (OrderMoveDomScope* huntp = m_pomReadyDomScope.begin(); huntp;
                 huntp = huntp->readyDomScopeNextp()) {
                if (huntp->domainp() == domScopep->domainp()) {
                    domScopeNextp = huntp;
                    break;
                }
            }
            domScopep = domScopeNextp;
        }
    }
    UASSERT(m_pomWaiting.empty(),
            "Didn't converge; nodes waiting, none ready, perhaps some input activations lost.");
    // Cleanup memory
    processMoveClear();
}

void OrderProcess::processMovePrepReady() {
    // Make list of ready nodes
    UINFO(5, "  MovePrepReady\n");
    for (OrderMoveVertex* vertexp = m_pomWaiting.begin(); vertexp;) {
        OrderMoveVertex* const nextp = vertexp->pomWaitingNextp();
        if (vertexp->isWait() && vertexp->inEmpty()) processMoveReadyOne(vertexp);
        vertexp = nextp;
    }
}

void OrderProcess::processMoveReadyOne(OrderMoveVertex* vertexp) {
    // Recursive!
    // Move one node from waiting to ready list
    vertexp->setReady();
    // Remove node from waiting list
    vertexp->m_pomWaitingE.unlink(m_pomWaiting, vertexp);
    if (vertexp->logicp()) {
        // Add to ready list (indexed by domain and scope)
        vertexp->m_readyVerticesE.pushBack(vertexp->domScopep()->m_readyVertices, vertexp);
        vertexp->domScopep()->ready(this);
    } else {
        // vertexp represents a non-logic vertex.
        // Recurse to mark its following neighbors ready.
        processMoveDoneOne(vertexp);
    }
}

void OrderProcess::processMoveDoneOne(OrderMoveVertex* vertexp) {
    // Move one node from ready to completion
    vertexp->setMoved();
    // Unlink from ready lists
    if (vertexp->logicp()) {
        vertexp->m_readyVerticesE.unlink(vertexp->domScopep()->m_readyVertices, vertexp);
        vertexp->domScopep()->movedVertex(this, vertexp);
    }
    // Don't need to add it to another list, as we're done with it
    // Mark our outputs as one closer to ready
    for (V3GraphEdge *edgep = vertexp->outBeginp(), *nextp; edgep; edgep = nextp) {
        nextp = edgep->outNextp();
        OrderMoveVertex* const toVertexp = static_cast<OrderMoveVertex*>(edgep->top());
        UINFO(9, "          Clear to " << (toVertexp->inEmpty() ? "[EMP] " : "      ") << toVertexp
                                       << endl);
        // Delete this edge
        VL_DO_DANGLING(edgep->unlinkDelete(), edgep);
        if (toVertexp->inEmpty()) {
            // If destination node now has all inputs resolved; recurse to move that vertex
            // This is thus depth first (before width) which keeps the
            // resulting executable's d-cache happy.
            processMoveReadyOne(toVertexp);
        }
    }
}

std::vector<AstActive*> V3Order::createSerial(const OrderGraph& graph, const std::string& tag,
                                              const TrigToSenMap& trigToSen, bool slow) {

    return OrderProcess::main(graph, tag, trigToSen, slow);
}
