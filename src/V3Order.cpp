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
// V3Order's Transformations:
//
//  Compute near optimal scheduling of always/wire statements
//  Make a graph of the entire netlist
//
//      For seq logic
//          Add logic_sensitive_vertex for this list of SenItems
//              Add edge for each sensitive_var->logic_sensitive_vertex
//          For AssignPre's
//              Add vertex for this logic
//                  Add edge logic_sensitive_vertex->logic_vertex
//                  Add edge logic_consumed_var_PREVAR->logic_vertex
//                  Add edge logic_vertex->logic_generated_var (same as if comb)
//                  Add edge logic_vertex->generated_var_PREORDER
//                      Cutable dependency to attempt to order dlyed
//                      assignments to avoid saving state, thus we prefer
//                              a <= b ...      As the opposite order would
//                              b <= c ...      require the old value of b.
//                  Add edge consumed_var_POST->logic_vertex
//                      This prevents a consumer of the "early" value to be
//                      scheduled after we've changed to the next-cycle value
//          For Logic
//              Add vertex for this logic
//                  Add edge logic_sensitive_vertex->logic_vertex
//                  Add edge logic_generated_var_PREORDER->logic_vertex
//                      This ensures the AssignPre gets scheduled before this logic
//                  Add edge logic_vertex->consumed_var_PREVAR
//                  Add edge logic_vertex->consumed_var_POSTVAR
//                  Add edge logic_vertex->logic_generated_var (same as if comb)
//          For AssignPost's
//              Add vertex for this logic
//                  Add edge logic_sensitive_vertex->logic_vertex
//                  Add edge logic_consumed_var->logic_vertex (same as if comb)
//                  Add edge logic_vertex->logic_generated_var (same as if comb)
//                  Add edge consumed_var_POST->logic_vertex (same as if comb)
//
//      For comb logic
//          For comb logic
//              Add vertex for this logic
//              Add edge logic_consumed_var->logic_vertex
//              Add edge logic_vertex->logic_generated_var
//                  Mark it cutable, as circular logic may require
//                  the generated signal to become a primary input again.
//
//
//
//   Rank the graph starting at INPUTS (see V3Graph)
//
//   Visit the graph's logic vertices in ranked order
//      For all logic vertices with all inputs already ordered
//         Make ordered block for this module
//         For all ^^ in same domain
//              Move logic to ordered activation
//      When we have no more choices, we move to the next module
//      and make a new block.  Add that new activation block to the list of calls to make.
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3OrderInternal.h"
#include "V3Sched.h"

#include <memory>
#include <vector>

VL_DEFINE_DEBUG_FUNCTIONS;

void V3Order::orderOrderGraph(OrderGraph& graph, const std::string& tag) {
    // Dump data
    if (dumpGraphLevel()) graph.dumpDotFilePrefixed(tag + "_orderg_pre");

    // Break cycles. Note that the OrderGraph only contains cuttable cycles
    // (soft constraints). Actual logic loops must have been eliminated by
    // the introduction of Hybid sensitivity expressions, before invoking
    // ordering (e.g. in V3SchedAcyclic).
    graph.acyclic(&V3GraphEdge::followAlwaysTrue);
    if (dumpGraphLevel()) graph.dumpDotFilePrefixed(tag + "_orderg_acyc");

    // Assign ranks so we know what to follow, then sort vertices and edges by that ordering
    graph.order();
    if (dumpGraphLevel()) graph.dumpDotFilePrefixed(tag + "_orderg_order");
}

//######################################################################

AstCFunc* V3Order::order(AstNetlist* netlistp,  //
                         const std::vector<V3Sched::LogicByScope*>& logic,  //
                         const V3Order::TrigToSenMap& trigToSen,
                         const string& tag,  //
                         bool parallel,  //
                         bool slow,  //
                         const ExternalDomainsProvider& externalDomains) {
    FileLine* const flp = netlistp->fileline();

    // Create the result function
    AstCFunc* const funcp = [&]() {
        AstScope* const scopeTopp = netlistp->topScopep()->scopep();
        AstCFunc* const resp = new AstCFunc{flp, "_eval_" + tag, scopeTopp, ""};
        resp->dontCombine(true);
        resp->isStatic(false);
        resp->isLoose(true);
        resp->slow(slow);
        resp->isConst(false);
        resp->declPrivate(true);
        scopeTopp->addBlocksp(resp);
        return resp;
    }();

    if (v3Global.opt.profExec()) {
        funcp->addStmtsp(new AstCStmt{flp, "VL_EXEC_TRACE_ADD_RECORD(vlSymsp).sectionPush(\"func "
                                               + tag + "\");\n"});
    }

    // Build the OrderGraph
    const std::unique_ptr<OrderGraph> graph = buildOrderGraph(netlistp, logic, trigToSen);
    // Order it
    orderOrderGraph(*graph, tag);
    // Assign sensitivity domains to combinational logic
    processDomains(netlistp, *graph, tag, trigToSen, externalDomains);

    if (parallel) {
        // Construct the parallel ExecGraph
        AstExecGraph* const execGraphp = createParallel(*graph, tag, trigToSen, slow);
        // Add the ExecGraph to the result function.
        funcp->addStmtsp(execGraphp);
    } else {
        // Construct the serial code
        const std::vector<AstActive*> activeps = createSerial(*graph, tag, trigToSen, slow);
        // Add the resulting Active blocks to the result function
        for (AstNode* const nodep : activeps) funcp->addStmtsp(nodep);
    }

    // Dump data
    if (dumpGraphLevel()) graph->dumpDotFilePrefixed(tag + "_orderg_done");

    // Dispose of the remnants of the inputs
    for (auto* const lbsp : logic) lbsp->deleteActives();

    if (v3Global.opt.profExec()) {
        funcp->addStmtsp(new AstCStmt{flp, "VL_EXEC_TRACE_ADD_RECORD(vlSymsp).sectionPop();\n"});
    }

    // Done
    return funcp;
}
