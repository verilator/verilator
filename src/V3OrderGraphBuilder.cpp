// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Block code ordering
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2003-2026 Wilson Snyder
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

#include <unordered_map>
#include <unordered_set>

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
    // Vertex of each type (if non-nullptr)
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
    enum VarAccess : uint8_t { VA_READ = 0x1, VA_WRITE = 0x2 };
    using VarVertexType = OrderUser::VarVertexType;

    // NODE STATE
    //  AstVarScope::user1    -> OrderUser instance for variable (via m_orderUser)
    //  AstVarScope::user2    -> VarUsage within logic blocks
    //  AstVarScope::user3    -> bool: Hybrid sensitivity
    //  AstVarScope::user4    -> VarAccess within logic blocks
    const VNUser1InUse user1InUse;
    const VNUser2InUse user2InUse;
    const VNUser3InUse user3InUse;
    const VNUser4InUse user4InUse;
    AstUser1Allocator<AstVarScope, OrderUser> m_orderUser;

    // STATE
    OrderGraph* const m_graphp = new OrderGraph;  // The ordering graph built by this visitor
    OrderLogicVertex* m_logicVxp = nullptr;  // Current logic block being analyzed
    std::vector<AstVarScope*> m_accessedVscps;  // Variables accessed by the current logic block
    std::unordered_set<const AstVarScope*>
        m_parentAccessedVscps;  // Variables directly accessed by parent logic
    std::unordered_map<const AstScope*, std::array<OrderLogicVertex*, 2>>
        m_wrapperPhases;  // Evaluation and publication vertices for each receiver
    std::unordered_map<const AstScope*, AstVarScope*>
        m_wrapperPhasePorts;  // Clock port anchoring each receiver phase edge
    const V3Order::FreshReads* const
        m_freshReadsp;  // Edge captures provided by local NBA lowering
    const V3Order::BoundaryUses* const
        m_boundaryUsesp;  // Port contracts for local scheduling operations
    std::unordered_set<const AstVarScope*>
        m_freshReadSet;  // Captured values consumed by the current operation

    // Map from Trigger reference AstSenItem to the original AstSenTree
    const V3Order::TrigToSenMap& m_trigToSen;  // Original sensitivities for each trigger

    // Current AstScope being processed
    AstScope* m_scopep = nullptr;  // Selected scheduling boundary
    // Sensitivity list for clocked logic, nullptr for combinational and hybrid logic
    AstSenTree* m_domainp = nullptr;
    // Sensitivity list for hybrid logic, nullptr for everything else
    AstSenTree* m_hybridp = nullptr;

    bool m_inClocked = false;  // Underneath clocked AstActive
    bool m_inPre = false;  // Underneath AlwaysPre
    bool m_inPost = false;  // Underneath AstAlwaysPost
    std::function<bool(const AstVarScope*)> m_readTriggersCombLogic;
    V3Sched::util::VarScopeSet m_forceReadEdgeIgnores;
    const bool m_parallel;  // Ordering for multi-threaded execution (record variable accesses)

    // What covergroup reference formal arguments are bound to at construction
    const V3Sched::CovergroupRefBindings&
        m_cgRefBindings;  // Covergroup reference bindings for local Order
    // Bindings reachable from the covergroup sample() being walked, nullptr when not in one
    const V3Sched::CovergroupRefBindings::Bindings* m_cgRefBoundps = nullptr;

    // METHODS

    void iterateLogic(AstNode* nodep) {
        UASSERT_OBJ(!m_logicVxp, nodep, "Should not nest");
        // Reset VarUsage and VarAccess
        AstNode::user2ClearTree();
        AstNode::user4ClearTree();
        m_forceReadEdgeIgnores.clear();
        if (!m_inClocked)
            V3Sched::util::collectForceReadEdgeIgnores(nodep, m_forceReadEdgeIgnores);
        // Create LogicVertex for this logic node
        m_logicVxp = new OrderLogicVertex{m_graphp, m_scopep, m_domainp, m_hybridp, nodep};
        // Gather variable dependencies based on usage
        iterateChildren(nodep);
        if (m_parallel) {
            // Emit one access record for each variable this logic block accessed
            for (AstVarScope* const vscp : m_accessedVscps) {
                const int recorded = vscp->user4();
                const VAccess access = recorded == (VA_READ | VA_WRITE) ? VAccess::READWRITE
                                       : recorded == VA_WRITE           ? VAccess::WRITE
                                                                        : VAccess::READ;
                m_logicVxp->addVarAccess(vscp, access);
            }
            m_accessedVscps.clear();
        }
        // Finished with this logic
        m_logicVxp = nullptr;
        m_forceReadEdgeIgnores.clear();
    }

    OrderVarVertex* getVarVertex(AstVarScope* varscp, VarVertexType type) {
        return m_orderUser(varscp).getVarVertex(m_graphp, varscp, type);
    }

    static bool isSubgraphWrapperCall(const AstCCall* nodep) {
        const AstCFunc* const funcp = nodep->funcp();
        return funcp->subgraphWrapper();
    }

    static bool isUnderScope(const AstScope* scopep, const AstScope* basep) {
        for (const AstScope* scanp = scopep; scanp; scanp = scanp->aboveScopep()) {
            if (scanp == basep) return true;
        }
        return false;
    }

    static bool containsSubgraphWrapperCall(AstActive* nodep) {
        bool found = false;
        nodep->foreach([&](AstCCall* callp) {
            if (isSubgraphWrapperCall(callp)) found = true;
        });
        return found;
    }

    bool shouldGroupSubgraphWrapperActive(AstActive* nodep) const {
        for (AstNode* stmtp = nodep->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
            if (VN_IS(stmtp, NodeProcedure)) return false;
        }
        return containsSubgraphWrapperCall(nodep);
    }

    void addSubgraphWrapperUsage(AstCCall* nodep) {
        UASSERT_OBJ(m_boundaryUsesp, nodep, "Missing subgraph boundary contracts");
        const auto contract = m_boundaryUsesp->find(nodep->funcp());
        UASSERT_OBJ(contract != m_boundaryUsesp->end(), nodep,
                    "Missing contract for shared subgraph function");
        AstScope* const implementationScopep = nodep->funcp()->scopep();
        AstScope* const boundaryScopep = nodep->subgraphReceiverScopep()
                                             ? nodep->subgraphReceiverScopep()
                                             : implementationScopep;
        const V3Order::BoundaryContract::Operation operation = contract->second.m_operation;
        const bool portOperation = operation != V3Order::BoundaryContract::Operation::SETTLE;
        const bool publish = operation != V3Order::BoundaryContract::Operation::CLOCK_EVAL;
        if (portOperation) {
            std::array<OrderLogicVertex*, 2>& phases = m_wrapperPhases[boundaryScopep];
            UASSERT_OBJ(!phases[publish], nodep,
                        "Duplicate subgraph operation phase for receiver");
            phases[publish] = m_logicVxp;
            AstVarScope* phasePortp = contract->second.m_clockp;
            if (boundaryScopep != implementationScopep
                && phasePortp->scopep() == implementationScopep) {
                for (AstVarScope* vscp = boundaryScopep->varsp(); vscp;
                     vscp = VN_AS(vscp->nextp(), VarScope)) {
                    if (vscp->varp() == phasePortp->varp()) {
                        phasePortp = vscp;
                        break;
                    }
                }
            }
            UASSERT_OBJ(phasePortp->scopep() == boundaryScopep
                            || !isUnderScope(phasePortp->scopep(), implementationScopep),
                        nodep, "Subgraph phase port missing from receiver");
            m_wrapperPhasePorts[boundaryScopep] = phasePortp;
        }
        std::unordered_map<const AstVar*, AstVarScope*> receiverVars;
        if (boundaryScopep != implementationScopep) {
            UASSERT_OBJ(boundaryScopep->modp() == implementationScopep->modp(), nodep,
                        "Subgraph receiver has a different specialization");
            for (AstVarScope* vscp = boundaryScopep->varsp(); vscp;
                 vscp = VN_AS(vscp->nextp(), VarScope)) {
                receiverVars.emplace(vscp->varp(), vscp);
            }
        }
        const auto receiverVar = [&](AstVarScope* vscp) {
            if (!receiverVars.empty() && vscp->scopep() == implementationScopep) {
                const auto it = receiverVars.find(vscp->varp());
                UASSERT_OBJ(it != receiverVars.end(), nodep,
                            "Shared subgraph port missing from receiver scope");
                return it->second;
            }
            return vscp;
        };
        for (AstVarScope* const portp : contract->second.m_ports) {
            AstVarScope* const vscp = receiverVar(portp);
            const bool boundaryPort = vscp->scopep() == boundaryScopep && vscp->varp()->isIO();
            if (isUnderScope(vscp->scopep(), boundaryScopep) && !boundaryPort
                && !m_parentAccessedVscps.count(vscp)) {
                continue;
            }
            accountVarAccess(vscp, publish ? VAccess::WRITE : VAccess::READ, nodep);
        }
        // The saved input is a boundary dependency even when the shared function's own
        // contract contains only the captured value's later uses.
        if (!m_inPost && m_freshReadsp) {
            const auto it = m_freshReadsp->find(boundaryScopep);
            if (it != m_freshReadsp->end()) {
                for (AstVarScope* const savedp : it->second) {
                    accountVarAccess(savedp, VAccess::READ, nodep);
                }
            }
        }
    }

    // VISITORS
    void visit(AstActive* nodep) override {
        UASSERT_OBJ(!nodep->senTreeStorep(), nodep,
                    "AstSenTrees should have been made global in V3ActiveTop");
        UASSERT_OBJ(m_scopep, nodep, "AstActive not under AstScope");
        UASSERT_OBJ(!m_logicVxp, nodep, "AstActive under logic");
        UASSERT_OBJ(!m_inClocked && !m_domainp && !m_hybridp, nodep, "Should not nest");

        VL_RESTORER(m_domainp);
        VL_RESTORER(m_hybridp);
        VL_RESTORER(m_inClocked);

        // This is the original sensitivity of the block (i.e.: not the ref into the trigger vec)

        const AstSenTree* const senTreep = nodep->sentreep()->hasCombo()
                                               ? nodep->sentreep()
                                               : m_trigToSen.at(nodep->sentreep());

        m_inClocked = senTreep->hasClocked();

        // Note: We don't need to analyze the sensitivity list, as currently all sensitivity
        // lists simply reference an entry in a trigger vector, which are all set external to
        // the code being ordered.

        // Combinational and hybrid logic will have it's domain assigned based on the driver
        // domains. For clocked logic, we already know its domain.
        if (!senTreep->hasCombo() && !senTreep->hasHybrid()) m_domainp = nodep->sentreep();

        // Hybrid logic also includes additional sensitivities
        if (senTreep->hasHybrid()) {
            m_hybridp = nodep->sentreep();
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

        // Treat a subgraph wrapper and its boundary contract as one parent graph vertex.
        if (shouldGroupSubgraphWrapperActive(nodep)) {
            iterateLogic(nodep);
        } else {
            iterateChildren(nodep);
        }
    }
    void visit(AstNodeVarRef* nodep) override {
        // As we explicitly not visit (see ignored nodes below) any subtree that is not relevant
        // for ordering, we should be able to assert this:
        UASSERT_OBJ(m_scopep, nodep, "AstVarRef not under scope");
        UASSERT_OBJ(m_logicVxp, nodep, "AstVarRef not under logic");
        AstVarScope* const varscp = nodep->varScopep();
        UASSERT_OBJ(varscp, nodep, "Var didn't get varscoped in V3Scope.cpp");
        // Reading a covergroup 'ref' formal reads whatever it was bound to at construction.
        // The formal itself is a pointer member fixed at construction, so it is not itself
        // interesting to ordering.
        const AstVar* const varp = nodep->varp();
        if (m_cgRefBoundps && varp->covergroupRefMember()) {
            // Covergroup params are considered const-ref
            UASSERT_OBJ(nodep->access().isReadOnly(), nodep, "covergroup ref argument is written");
            for (AstVarScope* const boundp : *m_cgRefBoundps) {
                accountVarAccess(boundp, VAccess::READ, nodep);
            }
        } else {
            accountVarAccess(varscp, nodep->access(), nodep);
        }
    }

    // Record the raw access for the multi-threaded data hazard fixer
    void recordRawAccess(AstVarScope* varscp, const VAccess& access, AstNode* nodep) {
        if (!m_parallel) return;
        uint8_t recorded = 0;
        if (access.isWriteOrRW()) recorded |= VA_WRITE;
        if (access.isReadOrRW()) recorded |= VA_READ;
        UASSERT_OBJ(recorded, nodep, "Unknown variable access type");
        // Accumulate access type, record the variable on first access only
        if (!varscp->user4Or(recorded)) m_accessedVscps.push_back(varscp);
    }

    // Add the graph edges, and record the raw access, for one access of one variable
    void accountVarAccess(AstVarScope* varscp, const VAccess& access, AstNode* nodep) {
        // Variable reference in logic. Add data dependency.
        recordRawAccess(varscp, access, nodep);

        // Check whether this variable was already generated/consumed in the same logic. We
        // don't want to add extra edges if the logic has many usages of the same variable,
        // so only proceed on first encounter.
        const bool prevGen = varscp->user2() & VU_GEN;
        const bool prevCon = varscp->user2() & VU_CON;

        // Compute whether the variable is produced (written) here
        const bool gen = !prevGen && access.isWriteOrRW() && !varscp->varp()->ignoreSchedWrite();

        // Compute whether the value is consumed (read) here
        bool con = false;
        if (!prevCon && access.isReadOrRW()) {
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
            if (!m_inClocked) {
                // Ignored reads and references from within covergroups do not
                // add to the combinational sensitivity of the block
                if (m_forceReadEdgeIgnores.count(varscp) || m_cgRefBoundps) con = false;
            }
        }

        // Note: See V3OrderGraph.h about the roles of the various vertex types

        // Variable is produced
        if (gen) {
            // Update VarUsage
            varscp->user2Or(VU_GEN);
            // Add edges for produced variables
            if (m_inPost) {
                if (!varscp->varp()->ignorePostWrite()) {
                    // Add edge from producing LogicVertex -> produced VarStdVertex
                    OrderVarVertex* const varVxp = getVarVertex(varscp, VarVertexType::STD);
                    m_graphp->addHardEdge(m_logicVxp, varVxp, WEIGHT_NORMAL);
                }
                OrderVarVertex* const postVxp = getVarVertex(varscp, VarVertexType::POST);
                // Add edge from produced VarPostVertex -> to producing LogicVertex
                m_graphp->addHardEdge(postVxp, m_logicVxp, WEIGHT_POST);
            } else if (!m_inClocked) {  // Combinational logic
                // Add edge from producing LogicVertex -> produced VarStdVertex
                OrderVarVertex* const varVxp = getVarVertex(varscp, VarVertexType::STD);
                m_graphp->addHardEdge(m_logicVxp, varVxp, WEIGHT_NORMAL);
                // Add edge from produced VarPostVertex -> to producing LogicVertex
                OrderVarVertex* const postVxp = getVarVertex(varscp, VarVertexType::POST);
                m_graphp->addHardEdge(postVxp, m_logicVxp, WEIGHT_POST);
            } else if (m_inClocked && m_freshReadSet.count(varscp)) {
                // Captured inputs become available to the child helper on this same edge.
                OrderVarVertex* const varVxp = getVarVertex(varscp, VarVertexType::STD);
                m_graphp->addHardEdge(m_logicVxp, varVxp, WEIGHT_NORMAL);
            } else if (m_inPre) {  // AstAlwaysPre
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
            varscp->user2Or(VU_CON);
            // Add edges
            if (m_inPost) {
                // Combinational logic
                if (!varscp->varp()->ignorePostRead() && m_readTriggersCombLogic(varscp)) {
                    // Ignore explicit sensitivities
                    OrderVarVertex* const varVxp = getVarVertex(varscp, VarVertexType::STD);
                    // Add edge from consumed VarStdVertex -> to consuming LogicVertex
                    m_graphp->addHardEdge(varVxp, m_logicVxp, WEIGHT_MEDIUM);
                }
            } else if (m_inClocked && !m_inPre && m_freshReadSet.count(varscp)) {
                // This clocked helper reads a value captured on the current edge. Treat it as
                // a fresh value, so the capture assignment must precede the helper call.
                OrderVarVertex* const varVxp = getVarVertex(varscp, VarVertexType::STD);
                m_graphp->addHardEdge(varVxp, m_logicVxp, WEIGHT_NORMAL);
            } else if (!m_inClocked) {  // Combinational logic
                if (m_readTriggersCombLogic(varscp)) {
                    // Ignore explicit sensitivities
                    OrderVarVertex* const varVxp = getVarVertex(varscp, VarVertexType::STD);
                    // Add edge from consumed VarStdVertex -> to consuming LogicVertex
                    m_graphp->addHardEdge(varVxp, m_logicVxp, WEIGHT_MEDIUM);
                }
            } else if (m_inPre) {
                // AstAlwaysPre logic
                // Add edge from consumed VarPreVertex -> to consuming LogicVertex
                // This one is cutable (vs the producer) as there's only one such consumer,
                // but may be many producers
                OrderVarVertex* const preVxp = getVarVertex(varscp, VarVertexType::PRE);
                m_graphp->addSoftEdge(preVxp, m_logicVxp, WEIGHT_PRE);
            } else {
                // Sequential (clocked) logic
                // Add edge from consuming LogicVertex -> to consumed VarPreVertex
                // Generation of 'pre' because we want to indicate it should be before
                // AstAlwaysPre
                OrderVarVertex* const preVxp = getVarVertex(varscp, VarVertexType::PRE);
                m_graphp->addHardEdge(m_logicVxp, preVxp, WEIGHT_NORMAL);
                // Add edge from consuming LogicVertex -> to consumed VarPostVertex
                OrderVarVertex* const postVxp = getVarVertex(varscp, VarVertexType::POST);
                m_graphp->addHardEdge(m_logicVxp, postVxp, WEIGHT_POST);
            }
        }
    }
    void visit(AstCCall* nodep) override {
        if (isSubgraphWrapperCall(nodep)) addSubgraphWrapperUsage(nodep);
        iterateChildren(nodep);
    }
    // A covergroup sample() is not inlined and may read design signals through cross-scope
    // references held by the covergroup. This attributes those references to the calling block.
    void visit(AstCMethodCall* nodep) override {
        iterateChildren(nodep);
        AstCFunc* const funcp = nodep->funcp();
        if (!funcp->isCovergroupSample()) return;
        // Since sample is a built-in, we never expect recursion.
        UASSERT_OBJ(!m_cgRefBoundps, nodep, "Covergroup sample() calls another sample()");
        VL_RESTORER(m_cgRefBoundps);
        // Reference formals are bound per covergroup object. If the call handle matches
        // one that we recorded, use that info. If the call handle isn't something we
        // recorded (eg array-element construction), use the union of references across
        // the covergroup type.
        const AstVarScope* instp = nullptr;
        if (const AstVarRef* const fromRefp = VN_CAST(nodep->fromp(), VarRef)) {
            instp = fromRefp->varScopep();
        }
        m_cgRefBoundps = &m_cgRefBindings.forSample(instp, VN_AS(funcp->scopep()->modp(), Class));
        iterateChildren(funcp);
    }

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
    void visit(AstAlwaysPre* nodep) override {
        UASSERT_OBJ(!m_inPre, nodep, "Should not nest");
        VL_RESTORER(m_inPre);
        m_inPre = true;
        iterateLogic(nodep);
    }
    void visit(AstAlwaysPost* nodep) override {
        UASSERT_OBJ(!m_inPost, nodep, "Should not nest");
        VL_RESTORER(m_inPost);
        m_inPost = true;
        iterateLogic(nodep);
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

    //--- Verilator concoctions
    void visit(AstCoverToggle* nodep) override {  //
        iterateLogic(nodep);
    }

    //--- Ignored nodes
    void visit(AstVar*) override {}
    void visit(AstVarScope* nodep) override { nodep->v3fatalSrc("Should not reach V3Order"); }
    void visit(AstCell* nodep) override { nodep->v3fatalSrc("Should not reach V3Order"); }
    void visit(AstTypeTable* nodep) override { nodep->v3fatalSrc("Should not reach V3Order"); }
    void visit(AstConstPool* nodep) override { nodep->v3fatalSrc("Should not reach V3Order"); }
    void visit(AstClass* nodep) override { nodep->v3fatalSrc("Should not reach V3Order"); }
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
                      const V3Order::TrigToSenMap& trigToSen,
                      const V3Sched::CovergroupRefBindings& cgRefBindings, bool parallel,
                      const V3Order::FreshReads* freshReadsp,
                      const V3Order::BoundaryUses* boundaryUsesp)
        : m_freshReadsp{freshReadsp}
        , m_boundaryUsesp{boundaryUsesp}
        , m_trigToSen{trigToSen}
        , m_parallel{parallel}
        , m_cgRefBindings{cgRefBindings} {
        if (freshReadsp) {
            for (const auto& pair : *freshReadsp) {
                for (AstVarScope* const savedp : pair.second) m_freshReadSet.emplace(savedp);
            }
        }
        // Keep internal state hidden unless logic outside a subgraph helper also accesses it.
        const bool hasSubgraphWrapper
            = std::any_of(coll.begin(), coll.end(), [](const V3Sched::LogicByScope* lbsp) {
                  return std::any_of(lbsp->begin(), lbsp->end(), [](const auto& pair) {
                      return containsSubgraphWrapperCall(pair.second);
                  });
              });
        if (hasSubgraphWrapper) {
            for (const V3Sched::LogicByScope* const lbsp : coll) {
                for (const auto& pair : *lbsp) {
                    AstActive* const activep = pair.second;
                    if (containsSubgraphWrapperCall(activep)) continue;
                    activep->foreach([&](AstNodeVarRef* refp) {
                        m_parentAccessedVscps.insert(refp->varScopep());
                    });
                }
            }
        }
        // Build the graph
        for (const V3Sched::LogicByScope* const lbsp : coll) {
            for (const auto& pair : *lbsp) {
                m_scopep = pair.first;
                iterate(pair.second);
                m_scopep = nullptr;
            }
        }
        // Internal NBA temporaries are deliberately absent from a port-only contract.
        // Preserve the local transaction's pre-before-post order explicitly.
        for (const auto& entry : m_wrapperPhases) {
            const std::array<OrderLogicVertex*, 2>& phases = entry.second;
            UASSERT_OBJ(phases[0] && phases[1], entry.first,
                        "Incomplete subgraph operation phases");
            OrderVarPhaseVertex* const phaseVxp
                = new OrderVarPhaseVertex{m_graphp, m_wrapperPhasePorts.at(entry.first)};
            m_graphp->addHardEdge(phases[0], phaseVxp, WEIGHT_NORMAL);
            m_graphp->addHardEdge(phaseVxp, phases[1], WEIGHT_NORMAL);
        }
    }
    ~OrderGraphBuilder() override = default;

public:
    // Process the netlist and return the constructed ordering graph. It's 'process' because
    // this visitor does change the tree (removes some nodes related to DPI export trigger).
    static std::unique_ptr<OrderGraph> apply(AstNetlist* nodep,
                                             const std::vector<V3Sched::LogicByScope*>& coll,
                                             const V3Order::TrigToSenMap& trigToSen,
                                             const V3Sched::CovergroupRefBindings& cgRefBindings,
                                             bool parallel, const V3Order::FreshReads* freshReadsp,
                                             const V3Order::BoundaryUses* boundaryUsesp) {
        return std::unique_ptr<OrderGraph>{OrderGraphBuilder{nodep, coll, trigToSen, cgRefBindings,
                                                             parallel, freshReadsp, boundaryUsesp}
                                               .m_graphp};
    }
};

std::unique_ptr<OrderGraph>
V3Order::buildOrderGraph(AstNetlist* netlistp,  //
                         const std::vector<V3Sched::LogicByScope*>& coll,  //
                         const V3Order::TrigToSenMap& trigToSen,  //
                         const V3Sched::CovergroupRefBindings& cgRefBindings,  //
                         bool parallel, const V3Order::FreshReads* freshReadsp,
                         const V3Order::BoundaryUses* boundaryUsesp) {
    return OrderGraphBuilder::apply(netlistp, coll, trigToSen, cgRefBindings, parallel,
                                    freshReadsp, boundaryUsesp);
}
