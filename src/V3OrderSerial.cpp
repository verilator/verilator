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

#include "V3OrderCFuncEmitter.h"
#include "V3OrderInternal.h"
#include "V3OrderMoveGraph.h"

#include <memory>

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// OrderSerial class

std::vector<AstActive*> V3Order::createSerial(OrderGraph& graph, const std::string& tag,
                                              const TrigToSenMap& trigToSen, bool slow) {

    UINFO(2, "  Constructing serial code for '" + tag + "'");

    // Build the move graph
    OrderMoveDomScope::clear();
    const std::unique_ptr<OrderMoveGraph> moveGraphp = OrderMoveGraph::build(graph, trigToSen);
    if (dumpGraphLevel() >= 9) moveGraphp->dumpDotFilePrefixed(tag + "_ordermv");

    // Serializer
    OrderMoveGraphSerializer serializer{*moveGraphp};

    // Add initially ready vertices (those with no dependencies) to the serializer as seeds
    for (V3GraphVertex& vtx : moveGraphp->vertices()) {
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
        VL_DO_DANGLING(mVtxp->unlinkDelete(moveGraphp.get()), mVtxp);
    }

    // Delete the remaining variable vertices
    for (V3GraphVertex* const vtxp : moveGraphp->vertices().unlinkable()) {
        if (!vtxp->as<OrderMoveVertex>()->logicp()) {
            VL_DO_DANGLING(vtxp->unlinkDelete(moveGraphp.get()), vtxp);
        }
    }

    UASSERT(moveGraphp->empty(), "Waiting vertices remain, but none are ready");
    OrderMoveDomScope::clear();

    return emitter.getAndClearActiveps();
}
