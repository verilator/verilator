// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Block code ordering
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2021 by Wilson Snyder. This program is free software; you
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
//          OrderInputsVertex
//          OrderLogicVertex
//          OrderVarVertex
//            OrderVarStdVertex
//            OrderVarPreVertex
//            OrderVarPostVertex
//            OrderVarPordVertex
//
//      V3GraphEdge
//        OrderEdge
//          OrderComboCutEdge
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

class OrderVisitor;
class OrderMoveVertex;
class OrderMoveVertexMaker;
class OrderMoveDomScope;

//######################################################################

enum OrderWeights : uint8_t {
    WEIGHT_INPUT = 1,  // Low weight just so dot graph looks nice
    WEIGHT_COMBO = 1,  // Breakable combo logic
    WEIGHT_POST = 2,  // Post-delayed used var
    WEIGHT_PRE = 3,  // Breakable pre-delayed used var
    WEIGHT_MEDIUM = 8,  // Medium weight just so dot graph looks nice
    WEIGHT_NORMAL = 32
};  // High weight just so dot graph looks nice

struct OrderVEdgeType {
    enum en : uint8_t {
        VERTEX_UNKNOWN = 0,
        VERTEX_INPUTS,
        VERTEX_LOGIC,
        VERTEX_VARSTD,
        VERTEX_VARPRE,
        VERTEX_VARPOST,
        VERTEX_VARPORD,
        VERTEX_VARSETTLE,
        VERTEX_MOVE,
        EDGE_STD,
        EDGE_COMBOCUT,
        EDGE_PRECUT,
        EDGE_POSTCUT,
        _ENUM_END
    };
    const char* ascii() const {
        static const char* const names[]
            = {"%E-vedge",      "VERTEX_INPUTS",  "VERTEX_LOGIC",   "VERTEX_VARSTD",
               "VERTEX_VARPRE", "VERTEX_VARPOST", "VERTEX_VARPORD", "VERTEX_VARSETTLE",
               "VERTEX_MOVE",   "EDGE_STD",       "EDGE_COMBOCUT",  "EDGE_PRECUT",
               "EDGE_POSTCUT",  "_ENUM_END"};
        return names[m_e];
    }
    enum en m_e;
    inline OrderVEdgeType()
        : m_e{VERTEX_UNKNOWN} {}
    // cppcheck-suppress noExplicitConstructor
    inline OrderVEdgeType(en _e)
        : m_e{_e} {}
    explicit inline OrderVEdgeType(int _e)
        : m_e(static_cast<en>(_e)) {}  // Need () or GCC 4.8 false warning
    operator en() const { return m_e; }
};
inline bool operator==(const OrderVEdgeType& lhs, const OrderVEdgeType& rhs) {
    return lhs.m_e == rhs.m_e;
}
inline bool operator==(const OrderVEdgeType& lhs, OrderVEdgeType::en rhs) {
    return lhs.m_e == rhs;
}
inline bool operator==(OrderVEdgeType::en lhs, const OrderVEdgeType& rhs) {
    return lhs == rhs.m_e;
}

//######################################################################
// Graph types

class OrderGraph final : public V3Graph {
public:
    OrderGraph() = default;
    virtual ~OrderGraph() override = default;
    // Methods
    virtual void loopsVertexCb(V3GraphVertex* vertexp) override;
};

//######################################################################
// Vertex types

class OrderEitherVertex VL_NOT_FINAL : public V3GraphVertex {
    AstScope* m_scopep;  // Scope the vertex is in
    AstSenTree* m_domainp;  // Clock domain (nullptr = to be computed as we iterate)
    bool m_isFromInput = false;  // From input, or derived therefrom (conservatively false)
protected:
    OrderEitherVertex(V3Graph* graphp, const OrderEitherVertex& old)
        : V3GraphVertex{graphp, old}
        , m_scopep{old.m_scopep}
        , m_domainp{old.m_domainp}
        , m_isFromInput{old.m_isFromInput} {}

public:
    OrderEitherVertex(V3Graph* graphp, AstScope* scopep, AstSenTree* domainp)
        : V3GraphVertex{graphp}
        , m_scopep{scopep}
        , m_domainp{domainp} {}
    virtual ~OrderEitherVertex() override = default;
    virtual OrderEitherVertex* clone(V3Graph* graphp) const override = 0;
    // Methods
    virtual OrderVEdgeType type() const = 0;
    virtual bool domainMatters() = 0;  // Must be in same domain when cross edge to this vertex
    virtual string dotName() const override { return cvtToHex(m_scopep) + "_"; }
    // ACCESSORS
    void domainp(AstSenTree* domainp) { m_domainp = domainp; }
    AstScope* scopep() const { return m_scopep; }
    AstSenTree* domainp() const { return m_domainp; }
    void isFromInput(bool flag) { m_isFromInput = flag; }
    bool isFromInput() const { return m_isFromInput; }
};

class OrderInputsVertex final : public OrderEitherVertex {
    OrderInputsVertex(V3Graph* graphp, const OrderInputsVertex& old)
        : OrderEitherVertex{graphp, old} {}

public:
    OrderInputsVertex(V3Graph* graphp, AstSenTree* domainp)
        : OrderEitherVertex{graphp, nullptr, domainp} {
        isFromInput(true);  // By definition
    }
    virtual ~OrderInputsVertex() override = default;
    virtual OrderInputsVertex* clone(V3Graph* graphp) const override {
        return new OrderInputsVertex(graphp, *this);
    }
    virtual OrderVEdgeType type() const override { return OrderVEdgeType::VERTEX_INPUTS; }
    virtual string name() const override { return "*INPUTS*"; }
    virtual string dotColor() const override { return "green"; }
    virtual string dotName() const override { return ""; }
    virtual bool domainMatters() override { return false; }
};

class OrderLogicVertex final : public OrderEitherVertex {
    AstNode* m_nodep;

protected:
    OrderLogicVertex(V3Graph* graphp, const OrderLogicVertex& old)
        : OrderEitherVertex{graphp, old}
        , m_nodep{old.m_nodep} {}

public:
    OrderLogicVertex(V3Graph* graphp, AstScope* scopep, AstSenTree* domainp, AstNode* nodep)
        : OrderEitherVertex{graphp, scopep, domainp}
        , m_nodep{nodep} {}
    virtual ~OrderLogicVertex() override = default;
    virtual OrderLogicVertex* clone(V3Graph* graphp) const override {
        return new OrderLogicVertex(graphp, *this);
    }
    virtual OrderVEdgeType type() const override { return OrderVEdgeType::VERTEX_LOGIC; }
    virtual bool domainMatters() override { return true; }
    // ACCESSORS
    virtual string name() const override {
        return (cvtToHex(m_nodep) + "\\n " + cvtToStr(nodep()->typeName()));
    }
    AstNode* nodep() const { return m_nodep; }
    virtual string dotColor() const override { return "yellow"; }
};

class OrderVarVertex VL_NOT_FINAL : public OrderEitherVertex {
    AstVarScope* m_varScp;
    bool m_isClock = false;  // Used as clock
    bool m_isDelayed = false;  // Set in a delayed assignment
protected:
    OrderVarVertex(V3Graph* graphp, const OrderVarVertex& old)
        : OrderEitherVertex{graphp, old}
        , m_varScp{old.m_varScp}
        , m_isClock{old.m_isClock}
        , m_isDelayed{old.m_isDelayed} {}

public:
    OrderVarVertex(V3Graph* graphp, AstScope* scopep, AstVarScope* varScp)
        : OrderEitherVertex{graphp, scopep, nullptr}
        , m_varScp{varScp} {}
    virtual ~OrderVarVertex() override = default;
    virtual OrderVarVertex* clone(V3Graph* graphp) const override = 0;
    virtual OrderVEdgeType type() const override = 0;
    virtual FileLine* fileline() const override { return varScp()->fileline(); }
    // ACCESSORS
    AstVarScope* varScp() const { return m_varScp; }
    void isClock(bool flag) { m_isClock = flag; }
    bool isClock() const { return m_isClock; }
    void isDelayed(bool flag) { m_isDelayed = flag; }
    bool isDelayed() const { return m_isDelayed; }
};

class OrderVarStdVertex final : public OrderVarVertex {
    OrderVarStdVertex(V3Graph* graphp, const OrderVarStdVertex& old)
        : OrderVarVertex{graphp, old} {}

public:
    OrderVarStdVertex(V3Graph* graphp, AstScope* scopep, AstVarScope* varScp)
        : OrderVarVertex{graphp, scopep, varScp} {}
    virtual ~OrderVarStdVertex() override = default;
    virtual OrderVarStdVertex* clone(V3Graph* graphp) const override {
        return new OrderVarStdVertex(graphp, *this);
    }
    virtual OrderVEdgeType type() const override { return OrderVEdgeType::VERTEX_VARSTD; }
    virtual string name() const override {
        return (cvtToHex(varScp()) + "\\n " + varScp()->name());
    }
    virtual string dotColor() const override { return "skyblue"; }
    virtual bool domainMatters() override { return true; }
};
class OrderVarPreVertex final : public OrderVarVertex {
    OrderVarPreVertex(V3Graph* graphp, const OrderVarPreVertex& old)
        : OrderVarVertex{graphp, old} {}

public:
    OrderVarPreVertex(V3Graph* graphp, AstScope* scopep, AstVarScope* varScp)
        : OrderVarVertex{graphp, scopep, varScp} {}
    virtual ~OrderVarPreVertex() override = default;
    virtual OrderVarPreVertex* clone(V3Graph* graphp) const override {
        return new OrderVarPreVertex(graphp, *this);
    }
    virtual OrderVEdgeType type() const override { return OrderVEdgeType::VERTEX_VARPRE; }
    virtual string name() const override {
        return (cvtToHex(varScp()) + " PRE\\n " + varScp()->name());
    }
    virtual string dotColor() const override { return "lightblue"; }
    virtual bool domainMatters() override { return false; }
};
class OrderVarPostVertex final : public OrderVarVertex {
    OrderVarPostVertex(V3Graph* graphp, const OrderVarPostVertex& old)
        : OrderVarVertex{graphp, old} {}

public:
    OrderVarPostVertex(V3Graph* graphp, AstScope* scopep, AstVarScope* varScp)
        : OrderVarVertex{graphp, scopep, varScp} {}
    virtual OrderVarPostVertex* clone(V3Graph* graphp) const override {
        return new OrderVarPostVertex(graphp, *this);
    }
    virtual OrderVEdgeType type() const override { return OrderVEdgeType::VERTEX_VARPOST; }
    virtual ~OrderVarPostVertex() override = default;
    virtual string name() const override {
        return (cvtToHex(varScp()) + " POST\\n " + varScp()->name());
    }
    virtual string dotColor() const override { return "CadetBlue"; }
    virtual bool domainMatters() override { return false; }
};
class OrderVarPordVertex final : public OrderVarVertex {
    OrderVarPordVertex(V3Graph* graphp, const OrderVarPordVertex& old)
        : OrderVarVertex{graphp, old} {}

public:
    OrderVarPordVertex(V3Graph* graphp, AstScope* scopep, AstVarScope* varScp)
        : OrderVarVertex{graphp, scopep, varScp} {}
    virtual ~OrderVarPordVertex() override = default;
    virtual OrderVarPordVertex* clone(V3Graph* graphp) const override {
        return new OrderVarPordVertex(graphp, *this);
    }
    virtual OrderVEdgeType type() const override { return OrderVEdgeType::VERTEX_VARPORD; }
    virtual string name() const override {
        return (cvtToHex(varScp()) + " PORD\\n " + varScp()->name());
    }
    virtual string dotColor() const override { return "NavyBlue"; }
    virtual bool domainMatters() override { return false; }
};

//######################################################################
//--- Following only under the move graph, not the main graph

class OrderMoveVertex final : public V3GraphVertex {
    enum OrderMState : uint8_t { POM_WAIT, POM_READY, POM_MOVED };

    OrderLogicVertex* m_logicp;
    OrderMState m_state;  // Movement state
    OrderMoveDomScope* m_domScopep;  // Domain/scope list information

protected:
    friend class OrderVisitor;
    friend class OrderMoveVertexMaker;
    // These only contain the "next" item,
    // for the head of the list, see the same var name under OrderVisitor
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
    virtual OrderMoveVertex* clone(V3Graph* graphp) const override {
        v3fatalSrc("Unsupported");
        return nullptr;
    }
    // METHODS
    virtual OrderVEdgeType type() const { return OrderVEdgeType::VERTEX_MOVE; }
    virtual string dotColor() const override {
        if (logicp()) {
            return logicp()->dotColor();
        } else {
            return "";
        }
    }
    virtual FileLine* fileline() const override {
        if (logicp()) {
            return logicp()->fileline();
        } else {
            return nullptr;
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
    OrderLogicVertex* m_logicp;  // Logic represented by this vertex
    const OrderEitherVertex* m_varp;  // Var represented by this vertex
    const AstScope* m_scopep;
    const AstSenTree* m_domainp;

protected:
    friend class OrderVisitor;

public:
    MTaskMoveVertex(V3Graph* graphp, OrderLogicVertex* logicp, const OrderEitherVertex* varp,
                    const AstScope* scopep, const AstSenTree* domainp)
        : V3GraphVertex{graphp}
        , m_logicp{logicp}
        , m_varp{varp}
        , m_scopep{scopep}
        , m_domainp{domainp} {
        UASSERT(!(logicp && varp), "MTaskMoveVertex: logicp and varp may not both be set!\n");
    }
    virtual ~MTaskMoveVertex() override = default;
    virtual MTaskMoveVertex* clone(V3Graph* graphp) const override {
        v3fatalSrc("Unsupported");
        return nullptr;
    }
    virtual OrderVEdgeType type() const { return OrderVEdgeType::VERTEX_MOVE; }
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
    // ACCESSORS
    OrderLogicVertex* logicp() const { return m_logicp; }
    const OrderEitherVertex* varp() const { return m_varp; }
    const AstScope* scopep() const { return m_scopep; }
    const AstSenTree* domainp() const { return m_domainp; }
};

//######################################################################
// Edge types

class OrderEdge VL_NOT_FINAL : public V3GraphEdge {
protected:
    OrderEdge(V3Graph* graphp, V3GraphVertex* fromp, V3GraphVertex* top, const OrderEdge& old)
        : V3GraphEdge{graphp, fromp, top, old} {}

public:
    OrderEdge(V3Graph* graphp, V3GraphVertex* fromp, V3GraphVertex* top, int weight,
              bool cutable = false)
        : V3GraphEdge{graphp, fromp, top, weight, cutable} {}
    virtual ~OrderEdge() override = default;
    virtual OrderVEdgeType type() const { return OrderVEdgeType::EDGE_STD; }
    virtual OrderEdge* clone(V3Graph* graphp, V3GraphVertex* fromp,
                             V3GraphVertex* top) const override {
        return new OrderEdge(graphp, fromp, top, *this);
    }
    // When ordering combo blocks with stronglyConnected, follow edges not
    // involving pre/pos variables
    virtual bool followComboConnected() const { return true; }
    static bool followComboConnected(const V3GraphEdge* edgep) {
        const OrderEdge* oedgep = dynamic_cast<const OrderEdge*>(edgep);
        if (!oedgep) v3fatalSrc("Following edge of non-OrderEdge type");
        return (oedgep->followComboConnected());
    }
};

class OrderComboCutEdge final : public OrderEdge {
    // Edge created from output of combo logic
    // Breakable if the output var is also a input,
    // in which case we'll need a change detect loop around this var.
    OrderComboCutEdge(V3Graph* graphp, V3GraphVertex* fromp, V3GraphVertex* top,
                      const OrderComboCutEdge& old)
        : OrderEdge{graphp, fromp, top, old} {}

public:
    OrderComboCutEdge(V3Graph* graphp, V3GraphVertex* fromp, V3GraphVertex* top)
        : OrderEdge{graphp, fromp, top, WEIGHT_COMBO, CUTABLE} {}
    virtual OrderVEdgeType type() const override { return OrderVEdgeType::EDGE_COMBOCUT; }
    virtual ~OrderComboCutEdge() override = default;
    virtual OrderComboCutEdge* clone(V3Graph* graphp, V3GraphVertex* fromp,
                                     V3GraphVertex* top) const override {
        return new OrderComboCutEdge(graphp, fromp, top, *this);
    }
    virtual string dotColor() const override { return "yellowGreen"; }
    virtual bool followComboConnected() const override { return true; }
};

class OrderPostCutEdge final : public OrderEdge {
    // Edge created from output of post assignment
    // Breakable if the output var feeds back to input combo logic or another clock pin
    // in which case we'll need a change detect loop around this var.
    OrderPostCutEdge(V3Graph* graphp, V3GraphVertex* fromp, V3GraphVertex* top,
                     const OrderPostCutEdge& old)
        : OrderEdge{graphp, fromp, top, old} {}

public:
    OrderPostCutEdge(V3Graph* graphp, V3GraphVertex* fromp, V3GraphVertex* top)
        : OrderEdge{graphp, fromp, top, WEIGHT_COMBO, CUTABLE} {}
    virtual OrderVEdgeType type() const override { return OrderVEdgeType::EDGE_POSTCUT; }
    virtual ~OrderPostCutEdge() override = default;
    virtual OrderPostCutEdge* clone(V3Graph* graphp, V3GraphVertex* fromp,
                                    V3GraphVertex* top) const override {
        return new OrderPostCutEdge(graphp, fromp, top, *this);
    }
    virtual string dotColor() const override { return "PaleGreen"; }
    virtual bool followComboConnected() const override { return false; }
};

class OrderPreCutEdge final : public OrderEdge {
    // Edge created from var_PREVAR->consuming logic vertex
    // Always breakable, just results in performance loss
    // in which case we can't optimize away the pre/post delayed assignments
    OrderPreCutEdge(V3Graph* graphp, V3GraphVertex* fromp, V3GraphVertex* top,
                    const OrderPreCutEdge& old)
        : OrderEdge{graphp, fromp, top, old} {}

public:
    OrderPreCutEdge(V3Graph* graphp, V3GraphVertex* fromp, V3GraphVertex* top)
        : OrderEdge{graphp, fromp, top, WEIGHT_PRE, CUTABLE} {}
    virtual OrderVEdgeType type() const override { return OrderVEdgeType::EDGE_PRECUT; }
    virtual OrderPreCutEdge* clone(V3Graph* graphp, V3GraphVertex* fromp,
                                   V3GraphVertex* top) const override {
        return new OrderPreCutEdge(graphp, fromp, top, *this);
    }
    virtual ~OrderPreCutEdge() override = default;
    virtual string dotColor() const override { return "khaki"; }
    virtual bool followComboConnected() const override { return false; }
};

#endif  // Guard
