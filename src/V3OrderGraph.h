// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Block code ordering
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
//  OrderGraph Class Hierarchy:
//
//      V3GraphVertex
//        OrderMoveVertex
//        MTaskMoveVertex
//        OrderEitherVertex
//          OrderLogicVertex
//          OrderVarVertex
//            OrderVarStdVertex
//            OrderVarPreVertex
//            OrderVarPostVertex
//            OrderVarPordVertex
//
//      V3GraphEdge
//        OrderEdge
//          OrderPostCutEdge
//          OrderPreCutEdge
//*************************************************************************

#ifndef VERILATOR_V3ORDERGRAPH_H_
#define VERILATOR_V3ORDERGRAPH_H_

#include "config_build.h"
#include "verilatedos.h"

#include "V3Ast.h"
#include "V3Graph.h"

#include <unordered_map>

class OrderMoveVertex;
class OrderMoveVertexMaker;
class OrderMoveDomScope;

//######################################################################

enum OrderWeights : uint8_t {
    WEIGHT_COMBO = 1,  // Breakable combo logic
    WEIGHT_POST = 2,  // Post-delayed used var
    WEIGHT_PRE = 3,  // Breakable pre-delayed used var
    WEIGHT_MEDIUM = 8,  // Medium weight just so dot graph looks nice
    WEIGHT_NORMAL = 32  // High weight just so dot graph looks nice
};

//######################################################################
// Graph types

class OrderGraph final : public V3Graph {
public:
    OrderGraph() = default;
    virtual ~OrderGraph() override = default;
    // METHODS
    virtual void loopsVertexCb(V3GraphVertex* vertexp) override;
};

//######################################################################
// Vertex types

class OrderEitherVertex VL_NOT_FINAL : public V3GraphVertex {
    AstSenTree* m_domainp;  // Clock domain (nullptr = to be computed as we iterate)

protected:
    // CONSTRUCTOR
    OrderEitherVertex(V3Graph* graphp, AstSenTree* domainp)
        : V3GraphVertex{graphp}
        , m_domainp{domainp} {}
    virtual ~OrderEitherVertex() override = default;

public:
    // METHODS
    virtual bool domainMatters() = 0;

    // ACCESSORS
    AstSenTree* domainp() const { return m_domainp; }
    void domainp(AstSenTree* domainp) { m_domainp = domainp; }
};

class OrderLogicVertex final : public OrderEitherVertex {
    AstNode* const m_nodep;  // The logic this vertex represents
    AstScope* const m_scopep;  // Scope the logic is under
    AstSenTree* const m_hybridp;

public:
    // CONSTRUCTOR
    OrderLogicVertex(V3Graph* graphp, AstScope* scopep, AstSenTree* domainp, AstSenTree* hybridp,
                     AstNode* nodep)
        : OrderEitherVertex{graphp, domainp}
        , m_nodep{nodep}
        , m_scopep{scopep}
        , m_hybridp{hybridp} {
        UASSERT_OBJ(scopep, nodep, "Must not be null");
        UASSERT_OBJ(!(domainp && hybridp), nodep, "Cannot have bot domainp and hybridp set");
    }
    virtual ~OrderLogicVertex() override = default;

    // METHODS
    virtual bool domainMatters() override { return true; }

    // ACCESSORS
    AstNode* nodep() const { return m_nodep; }
    AstScope* scopep() const { return m_scopep; }
    AstSenTree* hybridp() const { return m_hybridp; }

    // LCOV_EXCL_START // Debug code
    virtual string name() const override {
        return (cvtToHex(m_nodep) + "\\n " + cvtToStr(nodep()->typeName()));
    }
    virtual string dotShape() const override {
        return VN_IS(m_nodep, Active) ? "doubleoctagon" : "rect";
    }
    // LCOV_EXCL_STOP
};

class OrderVarVertex VL_NOT_FINAL : public OrderEitherVertex {
    AstVarScope* const m_vscp;

public:
    // CONSTRUCTOR
    OrderVarVertex(V3Graph* graphp, AstVarScope* vscp)
        : OrderEitherVertex{graphp, nullptr}
        , m_vscp{vscp} {}
    virtual ~OrderVarVertex() override = default;

    // ACCESSORS
    AstVarScope* vscp() const { return m_vscp; }

    // LCOV_EXCL_START // Debug code
    virtual string dotShape() const override final { return "ellipse"; }
    virtual string nameSuffix() const = 0;
    virtual string name() const override final {
        return cvtToHex(m_vscp) + " " + nameSuffix() + "\\n " + m_vscp->name();
    }
    // LCOV_EXCL_STOP
};

class OrderVarStdVertex final : public OrderVarVertex {
public:
    // CONSTRUCTOR
    OrderVarStdVertex(V3Graph* graphp, AstVarScope* varScp)
        : OrderVarVertex{graphp, varScp} {}
    virtual ~OrderVarStdVertex() override = default;

    // METHODS
    virtual bool domainMatters() override { return true; }

    // LCOV_EXCL_START // Debug code
    virtual string nameSuffix() const override { return ""; }
    virtual string dotColor() const override { return "grey"; }
    // LCOV_EXCL_STOP
};

class OrderVarPreVertex final : public OrderVarVertex {
public:
    // CONSTRUCTOR
    OrderVarPreVertex(V3Graph* graphp, AstVarScope* varScp)
        : OrderVarVertex{graphp, varScp} {}
    virtual ~OrderVarPreVertex() override = default;

    // METHODS
    virtual bool domainMatters() override { return false; }

    // LCOV_EXCL_START // Debug code
    virtual string nameSuffix() const override { return "PRE"; }
    virtual string dotColor() const override { return "green"; }
    // LCOV_EXCL_STOP
};

class OrderVarPostVertex final : public OrderVarVertex {
public:
    // CONSTRUCTOR
    OrderVarPostVertex(V3Graph* graphp, AstVarScope* varScp)
        : OrderVarVertex{graphp, varScp} {}
    virtual ~OrderVarPostVertex() override = default;

    // METHODS
    virtual bool domainMatters() override { return false; }

    // LCOV_EXCL_START // Debug code
    virtual string nameSuffix() const override { return "POST"; }
    virtual string dotColor() const override { return "red"; }
    // LCOV_EXCL_STOP
};

class OrderVarPordVertex final : public OrderVarVertex {
public:
    // CONSTRUCTOR
    OrderVarPordVertex(V3Graph* graphp, AstVarScope* varScp)
        : OrderVarVertex{graphp, varScp} {}
    virtual ~OrderVarPordVertex() override = default;

    // METHODS
    virtual bool domainMatters() override { return false; }

    // LCOV_EXCL_START // Debug code
    virtual string nameSuffix() const override { return "PORD"; }
    virtual string dotColor() const override { return "blue"; }
    // LCOV_EXCL_STOP
};

//######################################################################
// Edge types

class OrderEdge VL_NOT_FINAL : public V3GraphEdge {
public:
    // CONSTRUCTOR
    OrderEdge(V3Graph* graphp, V3GraphVertex* fromp, V3GraphVertex* top, int weight,
              bool cutable = false)
        : V3GraphEdge{graphp, fromp, top, weight, cutable} {}
    virtual ~OrderEdge() override = default;
};

class OrderPostCutEdge final : public OrderEdge {
    // Edge created from output of post assignment
public:
    // CONSTRUCTOR
    OrderPostCutEdge(V3Graph* graphp, V3GraphVertex* fromp, V3GraphVertex* top)
        : OrderEdge{graphp, fromp, top, WEIGHT_COMBO, CUTABLE} {}
    virtual ~OrderPostCutEdge() override = default;

    // LCOV_EXCL_START // Debug code
    virtual string dotColor() const override { return "palegreen"; }
    // LCOV_EXCL_STOP
};

class OrderPreCutEdge final : public OrderEdge {
    // Edge created from var_PREVAR->consuming logic vertex
    // Always breakable, just results in performance loss
    // in which case we can't optimize away the pre/post delayed assignments
public:
    // CONSTRUCTOR
    OrderPreCutEdge(V3Graph* graphp, V3GraphVertex* fromp, V3GraphVertex* top)
        : OrderEdge{graphp, fromp, top, WEIGHT_PRE, CUTABLE} {}
    virtual ~OrderPreCutEdge() override = default;

    // LCOV_EXCL_START // Debug code
    virtual string dotColor() const override { return "khaki"; }
    // LCOV_EXCL_STOP
};

//######################################################################
//--- Following only under the move graph, not the main graph

class OrderMoveVertex final : public V3GraphVertex {
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
    OrderMoveVertex(V3Graph* graphp, OrderLogicVertex* logicp)
        : V3GraphVertex{graphp}
        , m_logicp{logicp}
        , m_state{POM_WAIT}
        , m_domScopep{nullptr} {}
    virtual ~OrderMoveVertex() override = default;

    // METHODS
    virtual string dotColor() const override {
        if (logicp()) {
            return logicp()->dotColor();
        } else {
            return "";
        }
    }

    virtual string name() const override {
        string nm;
        if (VL_UNCOVERABLE(!logicp())) {  // Avoid crash when debugging
            nm = "nul";  // LCOV_EXCL_LINE
        } else {
            nm = logicp()->name();
            nm += (string("\\nMV:") + " d=" + cvtToHex(logicp()->domainp())
                   + " s=" + cvtToHex(logicp()->scopep()));
        }
        return nm;
    }
    OrderLogicVertex* logicp() const { return m_logicp; }
    bool isWait() const { return m_state == POM_WAIT; }
    void setReady() {
        UASSERT(m_state == POM_WAIT, "Wait->Ready on node not in proper state");
        m_state = POM_READY;
    }
    void setMoved() {
        UASSERT(m_state == POM_READY, "Ready->Moved on node not in proper state");
        m_state = POM_MOVED;
    }
    OrderMoveDomScope* domScopep() const { return m_domScopep; }
    OrderMoveVertex* pomWaitingNextp() const { return m_pomWaitingE.nextp(); }
    void domScopep(OrderMoveDomScope* ds) { m_domScopep = ds; }
};

// Similar to OrderMoveVertex, but modified for threaded code generation.
class MTaskMoveVertex final : public V3GraphVertex {
    //  This could be more compact, since we know m_varp and m_logicp
    //  cannot both be set. Each MTaskMoveVertex represents a logic node
    //  or a var node, it can't be both.
    OrderLogicVertex* const m_logicp;  // Logic represented by this vertex
    const OrderEitherVertex* const m_varp;  // Var represented by this vertex
    const AstSenTree* const m_domainp;

public:
    MTaskMoveVertex(V3Graph* graphp, OrderLogicVertex* logicp, const OrderEitherVertex* varp,
                    const AstSenTree* domainp)
        : V3GraphVertex{graphp}
        , m_logicp{logicp}
        , m_varp{varp}
        , m_domainp{domainp} {
        UASSERT(!(logicp && varp), "MTaskMoveVertex: logicp and varp may not both be set!\n");
    }
    virtual ~MTaskMoveVertex() override = default;

    // ACCESSORS
    OrderLogicVertex* logicp() const { return m_logicp; }
    const OrderEitherVertex* varp() const { return m_varp; }
    const AstScope* scopep() const { return m_logicp ? m_logicp->scopep() : nullptr; }
    const AstSenTree* domainp() const { return m_domainp; }

    virtual string dotColor() const override {
        if (logicp()) {
            return logicp()->dotColor();
        } else {
            return "yellow";
        }
    }
    virtual string name() const override {
        string nm;
        if (logicp()) {
            nm = logicp()->name();
            nm += (string("\\nMV:") + " d=" + cvtToHex(logicp()->domainp()) + " s="
                   + cvtToHex(logicp()->scopep())
                   // "color()" represents the mtask ID.
                   + "\\nt=" + cvtToStr(color()));
        } else {
            nm = "nolog\\nt=" + cvtToStr(color());
        }
        return nm;
    }
};

#endif  // Guard
