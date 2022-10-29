// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Ordering constraint graph
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2022 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
//
// OrderGraph is a bipartite graph, with the two parts being formed of only OrderLogicVertex and
// OrderVarVertex vertices respectively (i.e.: edges are always between OrderLogicVertex and
// OrderVarVertex, and never between two OrderLogicVertex or OrderVarVertex). The graph represents
// both fine-grained dependencies, and additional ordering constraints between logic blocks and
// variables. The fact that OrderGraph is bipartite is important and we take advantage of this fact
// in various algorithms, so this property must be maintained.
//
// Both OrderLogicVertex and OrderVarVertex derives from OrderEitherVertex, so OrderGraph is
// composed only of OrderEitherVertex vertices.
//
// OrderLogicVertex holds a 'logic block', which is just some computational construct that is
// ordered as a single unit. Ordering of these logic blocks is determined by the variables they
// read and write, which is represented by the edges between OrderLogicVertex and OrderVarVertex
// instances (and hence the graph is bipartite).
//
// OrderVarVertex is abstract, and has various concrete subtypes that represent various ordering
// constraints imposed by variables accessed by logic blocks. The concrete subtypes and their
// roles are:
//
// OrderVarStdVertex:   Data dependencies for combinational logic and delayed assignment
//                      updates (AssignPost).
// OrderVarPostVertex:  Ensures all sequential logic blocks reading a signal do so before any
//                      combinational or delayed assignments update that signal.
// OrderVarPordVertex:  Ensures a _d = _q AssignPre used to implement delayed (non-blocking)
//                      assignments is the first write of a _d, before any sequential blocks
//                      write to that _d.
// OrderVarPreVertex:   This is an optimization. Try to ensure that a _d = _q AssignPre is the
//                      last read of a _q, after all reads of that _q by sequential logic. The
//                      model is still correct if we cannot satisfy this due to other interfering
//                      constraints. If respecting this constraint is possible, then combined
//                      with the OrderVarPordVertex constraint we get that all writes to _d are
//                      after all reads of a _q, which then allows us to eliminate the _d
//                      completely and assign to the _q directly. This means these delayed
//                      assignments can be implemented without temporary storage (the redundant
//                      storage is eliminated in V3LifePost).
//
// Ordering constraints are represented by directed edges, where the source of an edge needs to be
// ordered before the sink of an edge. A constraint can be either hard (must be satisfied),
// represented by a non cutable edge, or a constraint can be soft (ideally should be satisfied, but
// is ok not to if other hard constraints interfere), represented by a cutable edge. Edges
// otherwise carry no additional information. TODO: what about weight?
//
// Note: It is required for hard (non-cutable) constraints to form a DAG, but together with the
// soft constraints the graph can be arbitrary so long as it remains bipartite.
//
//*************************************************************************

#ifndef VERILATOR_V3ORDERGRAPH_H_
#define VERILATOR_V3ORDERGRAPH_H_

#include "config_build.h"
#include "verilatedos.h"

#include "V3Ast.h"
#include "V3Graph.h"

class OrderLogicVertex;
class OrderVarVertex;

//======================================================================

enum OrderWeights : uint8_t {
    WEIGHT_COMBO = 1,  // Breakable combo logic
    WEIGHT_POST = 2,  // Post-delayed used var
    WEIGHT_PRE = 3,  // Breakable pre-delayed used var
    WEIGHT_MEDIUM = 8,  // Medium weight just so dot graph looks nice
    WEIGHT_NORMAL = 32  // High weight just so dot graph looks nice
};

//======================================================================
// Graph type

class OrderGraph final : public V3Graph {
public:
    // METHODS

    // Methods to add edges representing constraints, utilizing the type system to help us ensure
    // the graph remains bipartite.
    inline void addHardEdge(OrderLogicVertex* fromp, OrderVarVertex* top, int weight);
    inline void addHardEdge(OrderVarVertex* fromp, OrderLogicVertex* top, int weight);
    inline void addSoftEdge(OrderLogicVertex* fromp, OrderVarVertex* top, int weight);
    inline void addSoftEdge(OrderVarVertex* fromp, OrderLogicVertex* top, int weight);
};

//======================================================================
// Vertex types

class OrderEitherVertex VL_NOT_FINAL : public V3GraphVertex {
    // Event domain of vertex. For OrderLogicVertex this represents the conditions when the logic
    // block must be executed. For OrderVarVertex, this is the union of the domains of all the
    // OrderLogicVertex vertices that drive the variable. If initially set to nullptr (e.g.: all
    // OrderVarVertex and those OrderLogicVertices that represent combinational logic), then the
    // ordering algorithm will compute the domain automatically based on the edges representing
    // data-flow (those between OrderLogicVertex and OrderVarStdVertex), otherwise the domain is
    // as given (e.g.: for those OrderLogicVertices that represent clocked logic).
    AstSenTree* m_domainp;

protected:
    // CONSTRUCTOR
    OrderEitherVertex(OrderGraph* graphp, AstSenTree* domainp)
        : V3GraphVertex{graphp}
        , m_domainp{domainp} {}
    ~OrderEitherVertex() override = default;

public:
    // METHODS
    virtual bool domainMatters() = 0;

    // ACCESSORS
    AstSenTree* domainp() const { return m_domainp; }
    void domainp(AstSenTree* domainp) {
#if VL_DEBUG
        UASSERT(!m_domainp, "Domain should only be set once");
#endif
        m_domainp = domainp;
    }
};

class OrderLogicVertex final : public OrderEitherVertex {
    AstNode* const m_nodep;  // The logic this vertex represents
    AstScope* const m_scopep;  // Scope the logic is under
    AstSenTree* const m_hybridp;  // Additional sensitivities for hybrid combinational logic

public:
    // CONSTRUCTOR
    OrderLogicVertex(OrderGraph* graphp, AstScope* scopep, AstSenTree* domainp,
                     AstSenTree* hybridp, AstNode* nodep)
        : OrderEitherVertex{graphp, domainp}
        , m_nodep{nodep}
        , m_scopep{scopep}
        , m_hybridp{hybridp} {
        UASSERT_OBJ(scopep, nodep, "Must not be null");
        UASSERT_OBJ(!(domainp && hybridp), nodep, "Cannot have bot domainp and hybridp set");
    }
    ~OrderLogicVertex() override = default;

    // METHODS
    bool domainMatters() override { return true; }

    // ACCESSORS
    AstNode* nodep() const { return m_nodep; }
    AstScope* scopep() const { return m_scopep; }
    AstSenTree* hybridp() const { return m_hybridp; }

    // LCOV_EXCL_START // Debug code
    string name() const override {
        return (cvtToHex(m_nodep) + "\\n " + cvtToStr(nodep()->typeName()));
    }
    string dotShape() const override { return VN_IS(m_nodep, Active) ? "doubleoctagon" : "rect"; }
    // LCOV_EXCL_STOP
};

class OrderVarVertex VL_NOT_FINAL : public OrderEitherVertex {
    AstVarScope* const m_vscp;

public:
    // CONSTRUCTOR
    OrderVarVertex(OrderGraph* graphp, AstVarScope* vscp)
        : OrderEitherVertex{graphp, nullptr}
        , m_vscp{vscp} {}
    ~OrderVarVertex() override = default;

    // ACCESSORS
    AstVarScope* vscp() const { return m_vscp; }

    // LCOV_EXCL_START // Debug code
    string dotShape() const override final { return "ellipse"; }
    virtual string nameSuffix() const = 0;
    string name() const override final {
        return cvtToHex(m_vscp) + " " + nameSuffix() + "\\n " + m_vscp->name();
    }
    // LCOV_EXCL_STOP
};

class OrderVarStdVertex final : public OrderVarVertex {
public:
    // CONSTRUCTOR
    OrderVarStdVertex(OrderGraph* graphp, AstVarScope* vscp)
        : OrderVarVertex{graphp, vscp} {}
    ~OrderVarStdVertex() override = default;

    // METHODS
    bool domainMatters() override { return true; }

    // LCOV_EXCL_START // Debug code
    string nameSuffix() const override { return ""; }
    string dotColor() const override { return "grey"; }
    // LCOV_EXCL_STOP
};

class OrderVarPreVertex final : public OrderVarVertex {
public:
    // CONSTRUCTOR
    OrderVarPreVertex(OrderGraph* graphp, AstVarScope* vscp)
        : OrderVarVertex{graphp, vscp} {}
    ~OrderVarPreVertex() override = default;

    // METHODS
    bool domainMatters() override { return false; }

    // LCOV_EXCL_START // Debug code
    string nameSuffix() const override { return "PRE"; }
    string dotColor() const override { return "green"; }
    // LCOV_EXCL_STOP
};

class OrderVarPostVertex final : public OrderVarVertex {
public:
    // CONSTRUCTOR
    OrderVarPostVertex(OrderGraph* graphp, AstVarScope* vscp)
        : OrderVarVertex{graphp, vscp} {}
    ~OrderVarPostVertex() override = default;

    // METHODS
    bool domainMatters() override { return false; }

    // LCOV_EXCL_START // Debug code
    string nameSuffix() const override { return "POST"; }
    string dotColor() const override { return "red"; }
    // LCOV_EXCL_STOP
};

class OrderVarPordVertex final : public OrderVarVertex {
public:
    // CONSTRUCTOR
    OrderVarPordVertex(OrderGraph* graphp, AstVarScope* vscp)
        : OrderVarVertex{graphp, vscp} {}
    ~OrderVarPordVertex() override = default;

    // METHODS
    bool domainMatters() override { return false; }

    // LCOV_EXCL_START // Debug code
    string nameSuffix() const override { return "PORD"; }
    string dotColor() const override { return "blue"; }
    // LCOV_EXCL_STOP
};

//======================================================================
// Edge type

class OrderEdge final : public V3GraphEdge {
    friend class OrderGraph;  // Only the OrderGraph can create these
    // CONSTRUCTOR
    OrderEdge(OrderGraph* graphp, OrderEitherVertex* fromp, OrderEitherVertex* top, int weight,
              bool cutable)
        : V3GraphEdge{graphp, fromp, top, weight, cutable} {}
    ~OrderEdge() override = default;

    // LCOV_EXCL_START // Debug code
    string dotColor() const override { return cutable() ? "green" : "red"; }
    // LCOV_EXCL_STOP
};

//======================================================================
// Inline methods

void OrderGraph::addHardEdge(OrderLogicVertex* fromp, OrderVarVertex* top, int weight) {
    new OrderEdge{this, fromp, top, weight, /* cutable: */ false};
}
void OrderGraph::addHardEdge(OrderVarVertex* fromp, OrderLogicVertex* top, int weight) {
    new OrderEdge{this, fromp, top, weight, /* cutable: */ false};
}
void OrderGraph::addSoftEdge(OrderLogicVertex* fromp, OrderVarVertex* top, int weight) {
    new OrderEdge{this, fromp, top, weight, /* cutable: */ true};
}
void OrderGraph::addSoftEdge(OrderVarVertex* fromp, OrderLogicVertex* top, int weight) {
    new OrderEdge{this, fromp, top, weight, /* cutable: */ true};
}

#endif  // Guard
