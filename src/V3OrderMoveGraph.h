// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Ordering graph
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
// TODO: Fix comment
//
//*************************************************************************

#ifndef VERILATOR_V3ORDERMOVEGRAPH_H_
#define VERILATOR_V3ORDERMOVEGRAPH_H_

#include "config_build.h"
#include "verilatedos.h"

#include "V3Ast.h"
#include "V3Graph.h"
#include "V3OrderGraph.h"

#include <unordered_map>

class OrderMoveDomScope;

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
    ~OrderMoveVertex() override = default;

    // METHODS
    string dotColor() const override {
        if (logicp()) {
            return logicp()->dotColor();
        } else {
            return "";
        }
    }

    string name() const override {
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
    ~MTaskMoveVertex() override = default;

    // ACCESSORS
    OrderLogicVertex* logicp() const { return m_logicp; }
    const OrderEitherVertex* varp() const { return m_varp; }
    const AstScope* scopep() const { return m_logicp ? m_logicp->scopep() : nullptr; }
    const AstSenTree* domainp() const { return m_domainp; }

    string dotColor() const override {
        if (logicp()) {
            return logicp()->dotColor();
        } else {
            return "yellow";
        }
    }
    string name() const override {
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
