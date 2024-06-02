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
//  Initial graph dependency builder for ordering
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3AstUserAllocator.h"
#include "V3Graph.h"
#include "V3OrderGraph.h"
#include "V3OrderInternal.h"
#include "V3Sched.h"

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// Order information stored under each AstNode::user1p()...

class OrderUser final {
    // Stored in AstVarScope::user1p, a list of all the various vertices
    // that can exist for one given scoped variable
public:
    // TYPES
    enum class VarVertexType : uint8_t {  // Types of vertices we can create
        STD = 0,
        PRE = 1,
        PORD = 2,
        POST = 3
    };

private:
    // Vertex of each type (if non nullptr)
    std::array<OrderVarVertex*, static_cast<size_t>(VarVertexType::POST) + 1> m_vertexps;

public:
    // METHODS
    OrderVarVertex* getVarVertex(OrderGraph* graphp, AstVarScope* varscp, VarVertexType type) {
        const unsigned idx = static_cast<unsigned>(type);
        OrderVarVertex* vertexp = m_vertexps[idx];
        if (!vertexp) {
            switch (type) {
            case VarVertexType::STD: vertexp = new OrderVarStdVertex{graphp, varscp}; break;
            case VarVertexType::PRE: vertexp = new OrderVarPreVertex{graphp, varscp}; break;
            case VarVertexType::PORD: vertexp = new OrderVarPordVertex{graphp, varscp}; break;
            case VarVertexType::POST: vertexp = new OrderVarPostVertex{graphp, varscp}; break;
            }
            m_vertexps[idx] = vertexp;
        }
        return vertexp;
    }

    // CONSTRUCTORS
    OrderUser() { m_vertexps.fill(nullptr); }
    ~OrderUser() = default;
};

//######################################################################
// OrderBuildVisitor builds the ordering graph of the entire netlist, and
// removes any nodes that are no longer required once the graph is built

class OrderGraphBuilder final : public VNVisitor {
    // TYPES
    enum VarUsage : uint8_t { VU_CON = 0x1, VU_GEN = 0x2 };
    using VarVertexType = OrderUser::VarVertexType;

    // NODE STATE
    //  AstVarScope::user1    -> OrderUser instance for variable (via m_orderUser)
    //  AstVarScope::user2    -> VarUsage within logic blocks
    //  AstVarScope::user3    -> bool: Hybrid sensitivity
    const VNUser1InUse user1InUse;
    const VNUser2InUse user2InUse;
    const VNUser3InUse user3InUse;
    AstUser1Allocator<AstVarScope, OrderUser> m_orderUser;

    // STATE
    OrderGraph* const m_graphp = new OrderGraph;  // The ordering graph built by this visitor
    OrderLogicVertex* m_logicVxp = nullptr;  // Current logic block being analyzed

    // Map from Trigger reference AstSenItem to the original AstSenTree
    const V3Order::TrigToSenMap& m_trigToSen;

    // Current AstScope being processed
    AstScope* m_scopep = nullptr;
    // Sensitivity list for clocked logic, nullptr for combinational and hybrid logic
    AstSenTree* m_domainp = nullptr;
    // Sensitivity list for hybrid logic, nullptr for everything else
    AstSenTree* m_hybridp = nullptr;

    bool m_inClocked = false;  // Underneath clocked AstActive
    bool m_inPre = false;  // Underneath AstAssignPre
    bool m_inPost = false;  // Underneath AstAssignPost/AstAlwaysPost
    std::function<bool(const AstVarScope*)> m_readTriggersCombLogic;

    // METHODS

    void iterateLogic(AstNode* nodep) {
        UASSERT_OBJ(!m_logicVxp, nodep, "Should not nest");
        // Reset VarUsage
        AstNode::user2ClearTree();
        // Create LogicVertex for this logic node
        m_logicVxp = new OrderLogicVertex{m_graphp, m_scopep, m_domainp, m_hybridp, nodep};
        // Gather variable dependencies based on usage
        iterateChildren(nodep);
        // Finished with this logic
        m_logicVxp = nullptr;
    }

    OrderVarVertex* getVarVertex(AstVarScope* varscp, VarVertexType type) {
        return m_orderUser(varscp).getVarVertex(m_graphp, varscp, type);
    }

    // VISITORS
    void visit(AstActive* nodep) override {
        UASSERT_OBJ(!nodep->sensesStorep(), nodep,
                    "AstSenTrees should have been made global in V3ActiveTop");
        UASSERT_OBJ(m_scopep, nodep, "AstActive not under AstScope");
        UASSERT_OBJ(!m_logicVxp, nodep, "AstActive under logic");
        UASSERT_OBJ(!m_inClocked && !m_domainp && !m_hybridp, nodep, "Should not nest");

        // This is the original sensitivity of the block (i.e.: not the ref into the TRIGGERVEC)

        const AstSenTree* const senTreep = nodep->sensesp()->hasCombo()
                                               ? nodep->sensesp()
                                               : m_trigToSen.at(nodep->sensesp()->sensesp());

        m_inClocked = senTreep->hasClocked();

        // Note: We don't need to analyze the sensitivity list, as currently all sensitivity
        // lists simply reference an entry in a trigger vector, which are all set external to
        // the code being ordered.

        // Combinational and hybrid logic will have it's domain assigned based on the driver
        // domains. For clocked logic, we already know its domain.
        if (!senTreep->hasCombo() && !senTreep->hasHybrid()) m_domainp = nodep->sensesp();

        // Hybrid logic also includes additional sensitivities
        if (senTreep->hasHybrid()) {
            m_hybridp = nodep->sensesp();
            // Mark AstVarScopes that are explicit sensitivities
            AstNode::user3ClearTree();
            senTreep->foreach([](const AstVarRef* refp) {  //
                refp->varScopep()->user3(true);
            });
            m_readTriggersCombLogic = [](const AstVarScope* vscp) { return !vscp->user3(); };
        } else {
            // Always triggers
            m_readTriggersCombLogic = [](const AstVarScope*) { return true; };
        }

        // Analyze logic underneath
        iterateChildren(nodep);

        //
        m_inClocked = false;
        m_domainp = nullptr;
        m_hybridp = nullptr;
    }
    void visit(AstNodeVarRef* nodep) override {
        // As we explicitly not visit (see ignored nodes below) any subtree that is not relevant
        // for ordering, we should be able to assert this:
        UASSERT_OBJ(m_scopep, nodep, "AstVarRef not under scope");
        UASSERT_OBJ(m_logicVxp, nodep, "AstVarRef not under logic");
        AstVarScope* const varscp = nodep->varScopep();
        UASSERT_OBJ(varscp, nodep, "Var didn't get varscoped in V3Scope.cpp");

        // Variable reference in logic. Add data dependency.

        // Check whether this variable was already generated/consumed in the same logic. We
        // don't want to add extra edges if the logic has many usages of the same variable,
        // so only proceed on first encounter.
        const bool prevGen = varscp->user2() & VU_GEN;
        const bool prevCon = varscp->user2() & VU_CON;

        // Compute whether the variable is produced (written) here
        bool gen = !prevGen && nodep->access().isWriteOrRW();

        // Compute whether the value is consumed (read) here
        bool con = false;
        if (!prevCon && nodep->access().isReadOrRW()) {
            con = true;
            if (prevGen && !m_inClocked) {
                // Dangerous assumption:
                // If a variable is consumed in the same combinational process that produced it
                // earlier, consider it something like:
                //      foo = 1
                //      foo = foo + 1
                // and still optimize. Note this will break though:
                //      if (sometimes) foo = 1
                //      foo = foo + 1
                // TODO: Do this properly with liveness analysis (i.e.: if live, it's consumed)
                //       Note however that this construct is not nicely synthesizable (yields
                //       latch?).
                con = false;
            }
        }

        // Note: See V3OrderGraph.h about the roles of the various vertex types

        // Variable is produced
        if (gen) {
            // Update VarUsage
            varscp->user2(varscp->user2() | VU_GEN);
            // Add edges for produced variables
            if (!m_inClocked || m_inPost) {
                // Combinational logic
                OrderVarVertex* const varVxp = getVarVertex(varscp, VarVertexType::STD);
                // Add edge from producing LogicVertex -> produced VarStdVertex
                if (m_inPost) {
                    m_graphp->addSoftEdge(m_logicVxp, varVxp, WEIGHT_COMBO);
                } else {
                    m_graphp->addHardEdge(m_logicVxp, varVxp, WEIGHT_NORMAL);
                }

                // Add edge from produced VarPostVertex -> to producing LogicVertex

                // For m_inPost:
                //    Add edge consumed_var_POST->logic_vertex
                //    This prevents a consumer of the "early" value to be scheduled
                //   after we've changed to the next-cycle value
                // ALWAYS do it:
                //    There maybe a wire a=b; between the two blocks
                OrderVarVertex* const postVxp = getVarVertex(varscp, VarVertexType::POST);
                m_graphp->addHardEdge(postVxp, m_logicVxp, WEIGHT_POST);
            } else if (m_inPre) {  // AstAssignPre
                // Add edge from producing LogicVertex -> produced VarPordVertex
                OrderVarVertex* const ordVxp = getVarVertex(varscp, VarVertexType::PORD);
                m_graphp->addHardEdge(m_logicVxp, ordVxp, WEIGHT_NORMAL);
                // Add edge from producing LogicVertex -> produced VarStdVertex
                OrderVarVertex* const varVxp = getVarVertex(varscp, VarVertexType::STD);
                m_graphp->addHardEdge(m_logicVxp, varVxp, WEIGHT_NORMAL);
            } else {
                // Sequential (clocked) logic
                // Add edge from produced VarPordVertex -> to producing LogicVertex
                OrderVarVertex* const ordVxp = getVarVertex(varscp, VarVertexType::PORD);
                m_graphp->addHardEdge(ordVxp, m_logicVxp, WEIGHT_NORMAL);
                // Add edge from producing LogicVertex-> to produced VarStdVertex
                OrderVarVertex* const varVxp = getVarVertex(varscp, VarVertexType::STD);
                m_graphp->addHardEdge(m_logicVxp, varVxp, WEIGHT_NORMAL);
            }
        }

        // Variable is consumed
        if (con) {
            // Update VarUsage
            varscp->user2(varscp->user2() | VU_CON);
            // Add edges
            if (!m_inClocked || m_inPost) {
                // Combinational logic
                if (m_readTriggersCombLogic(varscp)) {
                    // Ignore explicit sensitivities
                    OrderVarVertex* const varVxp = getVarVertex(varscp, VarVertexType::STD);
                    // Add edge from consumed VarStdVertex -> to consuming LogicVertex
                    m_graphp->addHardEdge(varVxp, m_logicVxp, WEIGHT_MEDIUM);
                }
            } else if (m_inPre) {
                // AstAssignPre logic
                // Add edge from consumed VarPreVertex -> to consuming LogicVertex
                // This one is cutable (vs the producer) as there's only one such consumer,
                // but may be many producers
                OrderVarVertex* const preVxp = getVarVertex(varscp, VarVertexType::PRE);
                m_graphp->addSoftEdge(preVxp, m_logicVxp, WEIGHT_PRE);
            } else {
                // Sequential (clocked) logic
                // Add edge from consuming LogicVertex -> to consumed VarPreVertex
                // Generation of 'pre' because we want to indicate it should be before
                // AstAssignPre
                OrderVarVertex* const preVxp = getVarVertex(varscp, VarVertexType::PRE);
                m_graphp->addHardEdge(m_logicVxp, preVxp, WEIGHT_NORMAL);
                // Add edge from consuming LogicVertex -> to consumed VarPostVertex
                OrderVarVertex* const postVxp = getVarVertex(varscp, VarVertexType::POST);
                m_graphp->addHardEdge(m_logicVxp, postVxp, WEIGHT_POST);
            }
        }
    }
    void visit(AstCCall* nodep) override { iterateChildren(nodep); }

    //--- Logic akin to SystemVerilog Processes (AstNodeProcedure)
    void visit(AstInitial* nodep) override {  // LCOV_EXCL_START
        nodep->v3fatalSrc("AstInitial should not need ordering");
    }  // LCOV_EXCL_STOP
    void visit(AstInitialStatic* nodep) override {  // LCOV_EXCL_START
        nodep->v3fatalSrc("AstInitialStatic should not need ordering");
    }  // LCOV_EXCL_STOP
    void visit(AstInitialAutomatic* nodep) override {  //
        iterateLogic(nodep);
    }
    void visit(AstAlways* nodep) override {  //
        iterateLogic(nodep);
    }
    void visit(AstAlwaysPost* nodep) override {
        UASSERT_OBJ(!m_inPost, nodep, "Should not nest");
        m_inPost = true;
        iterateLogic(nodep);
        m_inPost = false;
    }
    void visit(AstAlwaysObserved* nodep) override {  //
        iterateLogic(nodep);
    }
    void visit(AstAlwaysReactive* nodep) override {  //
        iterateLogic(nodep);
    }
    void visit(AstFinal* nodep) override {  // LCOV_EXCL_START
        nodep->v3fatalSrc("AstFinal should not need ordering");
    }  // LCOV_EXCL_STOP

    //--- Logic akin go SystemVerilog continuous assignments
    void visit(AstAssignAlias* nodep) override {  //
        iterateLogic(nodep);
    }
    void visit(AstAssignW* nodep) override { iterateLogic(nodep); }
    void visit(AstAssignPre* nodep) override {
        UASSERT_OBJ(!m_inPre, nodep, "Should not nest");
        VL_RESTORER(m_inPre);
        m_inPre = true;
        iterateLogic(nodep);
    }
    void visit(AstAssignPost* nodep) override {
        UASSERT_OBJ(!m_inPost, nodep, "Should not nest");
        VL_RESTORER(m_inPost);
        m_inPost = true;
        iterateLogic(nodep);
    }

    //--- Verilator concoctions
    void visit(AstAlwaysPublic* nodep) override {  //
        iterateLogic(nodep);
    }
    void visit(AstCoverToggle* nodep) override {  //
        iterateLogic(nodep);
    }

    //--- Ignored nodes
    void visit(AstVar*) override {}
    void visit(AstVarScope* nodep) override {}
    void visit(AstCell*) override {}  // Only interested in the respective AstScope
    void visit(AstTypeTable*) override {}
    void visit(AstConstPool*) override {}
    void visit(AstClass*) override {}
    void visit(AstCFunc*) override {
        // Calls to DPI exports handled with AstCCall. /* verilator public */ functions are
        // ignored for now (and hence potentially mis-ordered), but could use the same or
        // similar mechanism as DPI exports. Every other impure function (including those
        // that may set a non-local variable) must have been inlined in V3Task.
    }

    //---
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

    // CONSTRUCTOR
    OrderGraphBuilder(AstNetlist* /*nodep*/, const std::vector<V3Sched::LogicByScope*>& coll,
                      const V3Order::TrigToSenMap& trigToSen)
        : m_trigToSen{trigToSen} {
        // Build the graph
        for (const V3Sched::LogicByScope* const lbsp : coll) {
            for (const auto& pair : *lbsp) {
                m_scopep = pair.first;
                iterate(pair.second);
                m_scopep = nullptr;
            }
        }
    }
    ~OrderGraphBuilder() override = default;

public:
    // Process the netlist and return the constructed ordering graph. It's 'process' because
    // this visitor does change the tree (removes some nodes related to DPI export trigger).
    static std::unique_ptr<OrderGraph> apply(AstNetlist* nodep,
                                             const std::vector<V3Sched::LogicByScope*>& coll,
                                             const V3Order::TrigToSenMap& trigToSen) {
        return std::unique_ptr<OrderGraph>{OrderGraphBuilder{nodep, coll, trigToSen}.m_graphp};
    }
};

std::unique_ptr<OrderGraph>
V3Order::buildOrderGraph(AstNetlist* netlistp,  //
                         const std::vector<V3Sched::LogicByScope*>& coll,  //
                         const V3Order::TrigToSenMap& trigToSen) {
    return OrderGraphBuilder::apply(netlistp, coll, trigToSen);
}
