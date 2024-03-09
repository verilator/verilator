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
//  Class used to construct AstCFuncs from a sequence of OrderLogicVertex's
//
//*************************************************************************

#ifndef VERILATOR_V3ORDERCFUNCEMITTER_H_
#define VERILATOR_V3ORDERCFUNCEMITTER_H_

#include "config_build.h"
#include "verilatedos.h"

#include "V3Ast.h"
#include "V3Graph.h"
#include "V3OrderGraph.h"

#include <limits>
#include <map>
#include <vector>

class V3OrderCFuncEmitter final {
    // Name component to add to function - must be unique
    const std::string m_tag;
    // True if creating slow functions
    const bool m_slow;
    // Whether to split functions
    const bool m_split = v3Global.opt.outputSplitCFuncs();
    // Size of code emitted so in the current function - for splitting
    size_t m_size = 0;
    // Maximum size of code per function
    const size_t m_splitSize = []() -> size_t {
        // Don't want to split with procCFuncs
        if (v3Global.opt.profCFuncs()) return std::numeric_limits<size_t>::max();
        // Otherwise split at the specified size (- 1, so we can do >= comparison)
        if (const size_t limit = v3Global.opt.outputSplitCFuncs()) return limit - 1;
        return std::numeric_limits<size_t>::max();
    }();
    // Current function being populated
    AstCFunc* m_funcp = nullptr;
    // Function ordinals to ensure unique names
    std::map<std::pair<AstNodeModule*, std::string>, unsigned> m_funcNums;
    // The result Active blocks that must be invoked to run the code in the order it was emitted
    std::vector<AstActive*> m_activeps;

    // Create a unique name for a new function
    std::string cfuncName(FileLine* flp, AstScope* scopep, AstNodeModule* modp,
                          AstSenTree* domainp) {
        std::string name = "_" + m_tag;
        name += domainp->isMulti() ? "_comb" : "_sequent";
        name += "__" + scopep->nameDotless();
        name += "__" + std::to_string(m_funcNums[{modp, name}]++);
        if (v3Global.opt.profCFuncs()) name += "__PROF__" + flp->profileFuncname();
        return name;
    }

public:
    // CONSTRUCTOR
    V3OrderCFuncEmitter(const std::string& tag, bool slow)
        : m_tag{tag}
        , m_slow{slow} {}
    VL_UNCOPYABLE(V3OrderCFuncEmitter);
    VL_UNMOVABLE(V3OrderCFuncEmitter);

    // Force the creation of a new function
    void forceNewFunction() {
        m_size = 0;
        m_funcp = nullptr;
    }

    // Retrieve Active block, which when executed will call the constructed functions
    std::vector<AstActive*> getAndClearActiveps() {
        forceNewFunction();
        return std::move(m_activeps);
    }

    // Emit one logic vertex
    void emitLogic(const OrderLogicVertex* lVtxp) {
        // Sensitivity domain of logic we are emitting
        AstSenTree* const domainp = lVtxp->domainp();
        // We are move the logic into a CFunc, so unlink it from the input AstActive
        AstNode* const logicp = lVtxp->nodep()->unlinkFrBack();
        // If the logic is a procedure, we need to do a few special things
        AstNodeProcedure* const procp = VN_CAST(logicp, NodeProcedure);

        // Some properties to consider
        const bool suspendable = procp && procp->isSuspendable();
        const bool needProcess = procp && procp->needProcess();
        // TODO: This is a bit muddy: 'initial forever @(posedge clk) begin ... end' is a fancy
        //       way of saying always @(posedge clk), so it might be quite hot...
        //       Also, if m_funcp is slow, but this one isn't we should force a new function
        const bool slow = m_slow && !(suspendable && VN_IS(procp, Always));

        // Put suspendable processes into individual functions on their own
        if (suspendable) forceNewFunction();
        // When profCFuncs, create a new function for each logic vertex
        if (v3Global.opt.profCFuncs()) forceNewFunction();
        // If the new domain is different, force a new function as it needs to be called separately
        if (!m_activeps.empty() && m_activeps.back()->sensesp() != domainp) forceNewFunction();

        // Process procedures per statement, so we can split CFuncs within procedures.
        // Everything else is handled as a unit.
        AstNode* const headp = [&]() -> AstNode* {
            if (!procp) return logicp;  // Not a procedure, handle as a unit
            AstNode* const stmtsp = procp->stmtsp();
            if (stmtsp) stmtsp->unlinkFrBackWithNext();
            // Procedure is no longer needed and can be deleted right now
            VL_DO_DANGLING(procp->deleteTree(), procp);
            return stmtsp;
        }();
        // Process each statement in the list starting at headp
        for (AstNode *currp = headp, *nextp; currp; currp = nextp) {
            nextp = currp->nextp();
            // Unlink the current statement from the next statement (if any)
            if (nextp) nextp->unlinkFrBackWithNext();
            // Split the function if too large, but don't split suspendable processes
            if (!suspendable && m_size >= m_splitSize) forceNewFunction();
            // Create a new function if we don't have a current one
            if (!m_funcp) {
                UASSERT_OBJ(!m_size, currp, "Should have used forceNewFunction");
                FileLine* const flp = currp->fileline();
                AstScope* const scopep = lVtxp->scopep();
                AstNodeModule* const modp = scopep->modp();
                const std::string name = cfuncName(flp, scopep, modp, domainp);
                m_funcp = new AstCFunc{flp, name, scopep, suspendable ? "VlCoroutine" : ""};
                if (needProcess) m_funcp->setNeedProcess();
                m_funcp->isStatic(false);
                m_funcp->isLoose(true);
                m_funcp->slow(slow);
                scopep->addBlocksp(m_funcp);
                // Create call to the new functino
                AstCCall* const callp = new AstCCall{flp, m_funcp};
                callp->dtypeSetVoid();
                // Call it under an AstActive with the same sensitivity
                if (m_activeps.empty() || m_activeps.back()->sensesp() != domainp) {
                    m_activeps.emplace_back(new AstActive{flp, name, domainp});
                }
                m_activeps.back()->addStmtsp(callp->makeStmt());
            }
            // Add the code to the current function
            m_funcp->addStmtsp(currp);
            // If splitting, add in the size of the code we just added
            if (m_split) m_size += currp->nodeCount();
        }
        // Put suspendable processes into individual functions on their own
        if (suspendable) forceNewFunction();
    }
};

#endif  // Guard
