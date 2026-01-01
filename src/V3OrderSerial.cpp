// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Block code ordering
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2026 by Wilson Snyder. This program is free software; you
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

#include "V3OrderCFuncEmitter.h"
#include "V3OrderInternal.h"

#include <memory>

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// OrderSerial class

AstNodeStmt* V3Order::createSerial(OrderMoveGraph& moveGraph, const std::string& tag, bool slow) {

    UINFO(2, "  Constructing serial code for '" + tag + "'");

    // Serializer
    OrderMoveGraphSerializer serializer{moveGraph};

    // Add initially ready vertices (those with no dependencies) to the serializer as seeds
    for (V3GraphVertex& vtx : moveGraph.vertices()) {
        if (vtx.inEmpty()) serializer.addSeed(vtx.as<OrderMoveVertex>());
    }

    // Emit all logic as they become ready
    V3OrderCFuncEmitter emitter{tag, slow};
    OrderMoveDomScope* prevDomScopep = nullptr;
    while (OrderMoveVertex* const mVtxp = serializer.getNext()) {
        // We only really care about logic vertices
        if (OrderLogicVertex* const logicp = mVtxp->logicp()) {
            // Force a new function if the domain or scope changed, for better combining.
            OrderMoveDomScope* const domScopep = &mVtxp->domScope();
            if (domScopep != prevDomScopep) emitter.forceNewFunction();
            prevDomScopep = domScopep;
            // Emit the logic under this vertex
            emitter.emitLogic(logicp);
        }
        // Can delete the vertex now
        VL_DO_DANGLING(mVtxp->unlinkDelete(&moveGraph), mVtxp);
    }

    // Delete the remaining variable vertices
    for (V3GraphVertex* const vtxp : moveGraph.vertices().unlinkable()) {
        if (!vtxp->as<OrderMoveVertex>()->logicp()) {
            VL_DO_DANGLING(vtxp->unlinkDelete(&moveGraph), vtxp);
        }
    }

    return emitter.getStmts();
}
