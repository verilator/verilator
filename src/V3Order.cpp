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

#include "config_build.h"
#include "verilatedos.h"

#include "V3Order.h"

#include "V3Ast.h"
#include "V3AstUserAllocator.h"
#include "V3Const.h"
#include "V3EmitV.h"
#include "V3File.h"
#include "V3Global.h"
#include "V3Graph.h"
#include "V3GraphStream.h"
#include "V3List.h"
#include "V3OrderGraph.h"
#include "V3OrderMoveGraph.h"
#include "V3Partition.h"
#include "V3PartitionGraph.h"
#include "V3Sched.h"
#include "V3SenTree.h"
#include "V3SplitVar.h"
#include "V3Stats.h"

#include <algorithm>
#include <deque>
#include <iomanip>
#include <map>
#include <memory>
#include <sstream>
#include <unordered_map>
#include <vector>

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

class OrderBuildVisitor final : public VNVisitor {
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
    const std::unordered_map<const AstSenItem*, const AstSenTree*>& m_trigToSen;

    // Current AstScope being processed
    AstScope* m_scopep = nullptr;
    // Sensitivity list for clocked logic, nullptr for combinational and hybird logic
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

        // Note: We don't need to analyse the sensitivity list, as currently all sensitivity
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
        m_inPre = true;
        iterateLogic(nodep);
        m_inPre = false;
    }
    void visit(AstAssignPost* nodep) override {
        UASSERT_OBJ(!m_inPost, nodep, "Should not nest");
        m_inPost = true;
        iterateLogic(nodep);
        m_inPost = false;
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
    OrderBuildVisitor(AstNetlist* /*nodep*/, const std::vector<V3Sched::LogicByScope*>& coll,
                      const std::unordered_map<const AstSenItem*, const AstSenTree*>& trigToSen)
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
    ~OrderBuildVisitor() override = default;

public:
    // Process the netlist and return the constructed ordering graph. It's 'process' because
    // this visitor does change the tree (removes some nodes related to DPI export trigger).
    static std::unique_ptr<OrderGraph>
    process(AstNetlist* nodep, const std::vector<V3Sched::LogicByScope*>& coll,
            const std::unordered_map<const AstSenItem*, const AstSenTree*>& trigToSen) {
        return std::unique_ptr<OrderGraph>{OrderBuildVisitor{nodep, coll, trigToSen}.m_graphp};
    }
};

//######################################################################

class OrderProcess;

class OrderMoveDomScope final {
    // Information stored for each unique loop, domain & scope trifecta
public:
    V3ListEnt<OrderMoveDomScope*> m_readyDomScopeE;  // List of next ready dom scope
    V3List<OrderMoveVertex*> m_readyVertices;  // Ready vertices with same domain & scope
private:
    bool m_onReadyList = false;  // True if DomScope is already on list of ready dom/scopes
    const AstSenTree* const m_domainp;  // Domain all vertices belong to
    const AstScope* const m_scopep;  // Scope all vertices belong to

    using DomScopeKey = std::pair<const AstSenTree*, const AstScope*>;
    using DomScopeMap = std::map<DomScopeKey, OrderMoveDomScope*>;
    static DomScopeMap s_dsMap;  // Structure registered for each dom/scope pairing

public:
    OrderMoveDomScope(const AstSenTree* domainp, const AstScope* scopep)
        : m_domainp{domainp}
        , m_scopep{scopep} {}
    OrderMoveDomScope* readyDomScopeNextp() const { return m_readyDomScopeE.nextp(); }
    const AstSenTree* domainp() const { return m_domainp; }
    const AstScope* scopep() const { return m_scopep; }
    // Check the domScope is on ready list, add if not
    void ready(OrderProcess* opp);
    // Mark one vertex as finished, remove from ready list if done
    void movedVertex(OrderProcess* opp, OrderMoveVertex* vertexp);
    // STATIC MEMBERS (for lookup)
    static void clear() {
        for (const auto& itr : s_dsMap) delete itr.second;
        s_dsMap.clear();
    }
    V3List<OrderMoveVertex*>& readyVertices() { return m_readyVertices; }
    static OrderMoveDomScope* findCreate(const AstSenTree* domainp, const AstScope* scopep) {
        const DomScopeKey key = std::make_pair(domainp, scopep);
        const auto iter = s_dsMap.find(key);
        if (iter != s_dsMap.end()) {
            return iter->second;
        } else {
            OrderMoveDomScope* domScopep = new OrderMoveDomScope(domainp, scopep);
            s_dsMap.emplace(key, domScopep);
            return domScopep;
        }
    }
    string name() const {
        return (string("MDS:") + " d=" + cvtToHex(domainp()) + " s=" + cvtToHex(scopep()));
    }
};

OrderMoveDomScope::DomScopeMap OrderMoveDomScope::s_dsMap;

std::ostream& operator<<(std::ostream& lhs, const OrderMoveDomScope& rhs) {
    lhs << rhs.name();
    return lhs;
}

//######################################################################
// ProcessMoveBuildGraph

template <class T_MoveVertex>
class ProcessMoveBuildGraph final {
    // ProcessMoveBuildGraph takes as input the fine-grained bipartite OrderGraph of
    // OrderLogicVertex and OrderVarVertex vertices. It produces a slightly coarsened graph to
    // drive the code scheduling.
    //
    // * For the serial code scheduler, the new graph contains
    //   nodes of type OrderMoveVertex.
    //
    // * For the threaded code scheduler, the new graph contains
    //   nodes of type MTaskMoveVertex.
    //
    // * The difference in output type is abstracted away by the
    //   'T_MoveVertex' template parameter; ProcessMoveBuildGraph otherwise
    //   works the same way for both cases.

    // NODE STATE
    // AstSenTree::user1p()     -> AstSenTree:  Original AstSenTree for trigger

    // TYPES
    using DomainMap = std::map<const AstSenTree*, T_MoveVertex*>;

public:
    class MoveVertexMaker VL_NOT_FINAL {
    public:
        // Clients of ProcessMoveBuildGraph must supply MoveVertexMaker
        // which creates new T_MoveVertex's. Each new vertex wraps lvertexp
        // (which may be nullptr.)
        virtual T_MoveVertex* makeVertexp(OrderLogicVertex* lvertexp,
                                          const OrderEitherVertex* varVertexp,
                                          const AstSenTree* domainp)
            = 0;
    };

private:
    // MEMBERS
    const OrderGraph* const m_graphp;  // Input OrderGraph
    V3Graph* const m_outGraphp;  // Output graph of T_MoveVertex vertices
    // Map from Trigger reference AstSenItem to the original AstSenTree
    const std::unordered_map<const AstSenItem*, const AstSenTree*>& m_trigToSen;
    MoveVertexMaker* const m_vxMakerp;  // Factory class for T_MoveVertex's
    // Storage for domain -> T_MoveVertex, maps held in OrderVarVertex::userp()
    std::deque<DomainMap> m_domainMaps;

public:
    // CONSTRUCTORS
    ProcessMoveBuildGraph(
        const OrderGraph* logicGraphp,  // Input graph of OrderLogicVertex etc.
        V3Graph* outGraphp,  // Output graph of T_MoveVertex's
        const std::unordered_map<const AstSenItem*, const AstSenTree*>& trigToSen,
        MoveVertexMaker* vxMakerp)
        : m_graphp{logicGraphp}
        , m_outGraphp{outGraphp}
        , m_trigToSen{trigToSen}
        , m_vxMakerp{vxMakerp} {}
    virtual ~ProcessMoveBuildGraph() = default;

    // METHODS
    void build() {
        // How this works:
        //  - Create a T_MoveVertex for each OrderLogicVertex.
        //  - Following each OrderLogicVertex, search forward in the context of
        //    its domain...
        //    * If we encounter another OrderLogicVertex in non-exclusive
        //      domain, make the T_MoveVertex->T_MoveVertex edge.
        //    * If we encounter an OrderVarVertex, make a Vertex for the
        //      (OrderVarVertex, domain) pair and continue to search
        //      forward in the context of the same domain.  Unless we
        //      already created that pair, in which case, we've already
        //      done the forward search, so stop.

        // For each logic vertex, make a T_MoveVertex, for each variable vertex, allocate storage
        for (V3GraphVertex* itp = m_graphp->verticesBeginp(); itp; itp = itp->verticesNextp()) {
            if (OrderLogicVertex* const lvtxp = dynamic_cast<OrderLogicVertex*>(itp)) {
                lvtxp->userp(m_vxMakerp->makeVertexp(lvtxp, nullptr, lvtxp->domainp()));
            } else {
                // This is an OrderVarVertex
                m_domainMaps.emplace_back();
                itp->userp(&m_domainMaps.back());
            }
        }
        // Build edges between logic vertices
        for (V3GraphVertex* itp = m_graphp->verticesBeginp(); itp; itp = itp->verticesNextp()) {
            if (OrderLogicVertex* const lvtxp = dynamic_cast<OrderLogicVertex*>(itp)) {
                iterateLogicVertex(lvtxp);
            }
        }
    }

private:
    // Returns the AstSenItem that originally corresponds to this AstSenTree, or nullptr if no
    // original AstSenTree, or if the original AstSenTree had multiple AstSenItems.
    const AstSenItem* getOrigSenItem(AstSenTree* senTreep) {
        if (!senTreep->user1p()) {
            // Find the original simple AstSenTree, if any
            AstNode* const origp = [&]() -> AstSenItem* {
                // If more than one AstSenItems, then not a simple AstSenTree
                if (senTreep->sensesp()->nextp()) return nullptr;

                // Find the original AstSenTree
                auto it = m_trigToSen.find(senTreep->sensesp());
                if (it == m_trigToSen.end()) return nullptr;

                // If more than one AstSenItems on the original, then not a simple AstSenTree
                if (it->second->sensesp()->nextp()) return nullptr;

                // Else we found it.
                return it->second->sensesp();
            }();

            // We use the node itself as a sentinel to denote 'no original node'
            senTreep->user1p(origp ? origp : senTreep);
        }

        return senTreep->user1p() == senTreep ? nullptr : VN_AS(senTreep->user1p(), SenItem);
    }

    bool domainsExclusive(AstSenTree* fromp, AstSenTree* top) {
        // Return 'true' if we can prove that both 'from' and 'to' cannot both
        // be active on the same evaluation, or false if we can't prove this.
        //
        // This detects the case of 'always @(posedge clk)'
        // and 'always @(negedge clk)' being exclusive.
        //
        // Are there any other cases we need to handle? Maybe not,
        // because these are not exclusive:
        //   always @(posedge A or posedge B)
        //   always @(negedge A)
        //
        // ... unless you know more about A and B, which sounds hard.

        const AstSenItem* const fromSenItemp = getOrigSenItem(fromp);
        if (!fromSenItemp) return false;
        const AstSenItem* const toSenItemp = getOrigSenItem(top);
        if (!toSenItemp) return false;

        const AstNodeVarRef* const fromVarrefp = fromSenItemp->varrefp();
        if (!fromVarrefp) return false;
        const AstNodeVarRef* const toVarrefp = toSenItemp->varrefp();
        if (!toVarrefp) return false;

        // We know nothing about the relationship between different clocks here,
        // so only proceed if strictly the same clock.
        if (fromVarrefp->varScopep() != toVarrefp->varScopep()) return false;

        return fromSenItemp->edgeType().exclusiveEdge(toSenItemp->edgeType());
    }

    void iterateLogicVertex(const OrderLogicVertex* lvtxp) {
        AstSenTree* const domainp = lvtxp->domainp();
        T_MoveVertex* const lMoveVtxp = static_cast<T_MoveVertex*>(lvtxp->userp());
        // Search forward from lvtxp, making new edges from lMoveVtxp forward
        for (V3GraphEdge* edgep = lvtxp->outBeginp(); edgep; edgep = edgep->outNextp()) {
            if (edgep->weight() == 0) continue;  // Was cut

            // OrderGraph is a bipartite graph, so we know it's an OrderVarVertex
            const OrderVarVertex* const vvtxp = static_cast<const OrderVarVertex*>(edgep->top());

            // Look up T_MoveVertex for this domain on this variable
            DomainMap& mapp = *static_cast<DomainMap*>(vvtxp->userp());
            const auto pair = mapp.emplace(domainp, nullptr);
            // Reference to the mapped T_MoveVertex
            T_MoveVertex*& vMoveVtxp = pair.first->second;

            // On first encounter, visit downstream logic dependent on this (var, domain)
            if (pair.second) vMoveVtxp = iterateVarVertex(vvtxp, domainp);

            // If no downstream dependents from this variable, then there is no need to add this
            // variable as a dependent.
            if (!vMoveVtxp) continue;

            // Add this (variable, domain) as dependent of the logic that writes it.
            new V3GraphEdge{m_outGraphp, lMoveVtxp, vMoveVtxp, 1};
        }
    }

    // Return the T_MoveVertex for this (var, domain) pair, iff it has downstream dependencies,
    // otherwise return nullptr.
    T_MoveVertex* iterateVarVertex(const OrderVarVertex* vvtxp, AstSenTree* domainp) {
        T_MoveVertex* vMoveVtxp = nullptr;
        // Search forward from vvtxp, making new edges from vMoveVtxp forward
        for (V3GraphEdge* edgep = vvtxp->outBeginp(); edgep; edgep = edgep->outNextp()) {
            if (edgep->weight() == 0) continue;  // Was cut

            // OrderGraph is a bipartite graph, so we know it's an OrderLogicVertex
            const OrderLogicVertex* const lvtxp
                = static_cast<const OrderLogicVertex*>(edgep->top());

            // Do not construct dependencies across exclusive domains.
            if (domainsExclusive(domainp, lvtxp->domainp())) continue;

            // there is a path from this vvtx to a logic vertex. Add the new edge.
            if (!vMoveVtxp) vMoveVtxp = m_vxMakerp->makeVertexp(nullptr, vvtxp, domainp);
            T_MoveVertex* const lMoveVxp = static_cast<T_MoveVertex*>(lvtxp->userp());
            new V3GraphEdge{m_outGraphp, vMoveVtxp, lMoveVxp, 1};
        }
        return vMoveVtxp;
    }

    VL_UNCOPYABLE(ProcessMoveBuildGraph);
};

// ######################################################################
//  OrderMoveVertexMaker and related

class OrderMoveVertexMaker final : public ProcessMoveBuildGraph<OrderMoveVertex>::MoveVertexMaker {
    // MEMBERS
    V3Graph* m_pomGraphp;
    V3List<OrderMoveVertex*>* m_pomWaitingp;

public:
    // CONSTRUCTORS
    OrderMoveVertexMaker(V3Graph* pomGraphp, V3List<OrderMoveVertex*>* pomWaitingp)
        : m_pomGraphp{pomGraphp}
        , m_pomWaitingp{pomWaitingp} {}
    // METHODS
    OrderMoveVertex* makeVertexp(OrderLogicVertex* lvertexp, const OrderEitherVertex*,
                                 const AstSenTree* domainp) override {
        OrderMoveVertex* const resultp = new OrderMoveVertex(m_pomGraphp, lvertexp);
        AstScope* const scopep = lvertexp ? lvertexp->scopep() : nullptr;
        resultp->domScopep(OrderMoveDomScope::findCreate(domainp, scopep));
        resultp->m_pomWaitingE.pushBack(*m_pomWaitingp, resultp);
        return resultp;
    }

private:
    VL_UNCOPYABLE(OrderMoveVertexMaker);
};

class OrderMTaskMoveVertexMaker final
    : public ProcessMoveBuildGraph<MTaskMoveVertex>::MoveVertexMaker {
    V3Graph* m_pomGraphp;

public:
    explicit OrderMTaskMoveVertexMaker(V3Graph* pomGraphp)
        : m_pomGraphp{pomGraphp} {}
    MTaskMoveVertex* makeVertexp(OrderLogicVertex* lvertexp, const OrderEitherVertex* varVertexp,
                                 const AstSenTree* domainp) override {
        return new MTaskMoveVertex{m_pomGraphp, lvertexp, varVertexp, domainp};
    }

private:
    VL_UNCOPYABLE(OrderMTaskMoveVertexMaker);
};

class OrderVerticesByDomainThenScope final {
    PartPtrIdMap m_ids;

public:
    bool operator()(const V3GraphVertex* lhsp, const V3GraphVertex* rhsp) const {
        const MTaskMoveVertex* const l_vxp = static_cast<const MTaskMoveVertex*>(lhsp);
        const MTaskMoveVertex* const r_vxp = static_cast<const MTaskMoveVertex*>(rhsp);
        uint64_t l_id = m_ids.findId(l_vxp->domainp());
        uint64_t r_id = m_ids.findId(r_vxp->domainp());
        if (l_id < r_id) return true;
        if (l_id > r_id) return false;
        l_id = m_ids.findId(l_vxp->scopep());
        r_id = m_ids.findId(r_vxp->scopep());
        return l_id < r_id;
    }
};

struct MTaskVxIdLessThan final {
    // Sort vertex's, which must be AbstractMTask's, into a deterministic
    // order by comparing their serial IDs.
    bool operator()(const V3GraphVertex* lhsp, const V3GraphVertex* rhsp) const {
        const AbstractMTask* const lmtaskp = static_cast<const AbstractLogicMTask*>(lhsp);
        const AbstractMTask* const rmtaskp = static_cast<const AbstractLogicMTask*>(rhsp);
        return lmtaskp->id() < rmtaskp->id();
    }
};

//######################################################################
// OrderProcess class

class OrderProcess final : VNDeleter {
    // NODE STATE
    //  AstNode::user4  -> Used by V3Const::constifyExpensiveEdit

    // STATE
    OrderGraph& m_graph;  // The ordering graph

    // Map from Trigger reference AstSenItem to the original AstSenTree
    const std::unordered_map<const AstSenItem*, const AstSenTree*>& m_trigToSen;

    // This is a function provided by the invoker of the ordering that can provide additional
    // sensitivity expression that when triggered indicates the passed AstVarScope might have
    // changed external to the code being ordered.
    const V3Order::ExternalDomainsProvider m_externalDomains;

    SenTreeFinder m_finder;  // Global AstSenTree manager
    AstSenTree* const m_deleteDomainp;  // Dummy AstSenTree indicating needs deletion
    const string m_tag;  // Subtring to add to generated names
    const bool m_slow;  // Ordering slow code
    std::vector<AstNode*> m_result;  // The result nodes (~statements) in their sequential order

    AstCFunc* m_pomNewFuncp = nullptr;  // Current function being created
    int m_pomNewStmts = 0;  // Statements in function being created
    V3Graph m_pomGraph;  // Graph of logic elements to move
    V3List<OrderMoveVertex*> m_pomWaiting;  // List of nodes needing inputs to become ready
    friend class OrderMoveDomScope;
    V3List<OrderMoveDomScope*> m_pomReadyDomScope;  // List of ready domain/scope pairs, by loopId
    std::map<std::pair<AstNodeModule*, std::string>, unsigned> m_funcNums;  // Function ordinals

    // METHODS

    void process(bool multiThreaded);
    void processDomains();
    void processDomainsIterate(OrderEitherVertex* vertexp);
    void processEdgeReport();

    // processMove* routines schedule serial execution
    void processMove();
    void processMoveClear();
    void processMoveBuildGraph();
    void processMovePrepReady();
    void processMoveReadyOne(OrderMoveVertex* vertexp);
    void processMoveDoneOne(OrderMoveVertex* vertexp);
    void processMoveOne(OrderMoveVertex* vertexp, OrderMoveDomScope* domScopep, int level);
    AstActive* processMoveOneLogic(const OrderLogicVertex* lvertexp, AstCFunc*& newFuncpr,
                                   int& newStmtsr);

    // processMTask* routines schedule threaded execution
    struct MTaskState {
        AstMTaskBody* m_mtaskBodyp = nullptr;
        std::list<const OrderLogicVertex*> m_logics;
        ExecMTask* m_execMTaskp = nullptr;
        MTaskState() = default;
    };
    void processMTasks();

    string cfuncName(AstNodeModule* modp, AstSenTree* domainp, AstScope* scopep,
                     AstNode* forWhatp) {
        string name = "_" + m_tag;
        name += domainp->isMulti() ? "_comb" : "_sequent";
        name = name + "__" + scopep->nameDotless();
        const unsigned funcnum = m_funcNums.emplace(std::make_pair(modp, name), 0).first->second++;
        name = name + "__" + cvtToStr(funcnum);
        if (v3Global.opt.profCFuncs()) {
            name += "__PROF__" + forWhatp->fileline()->profileFuncname();
        }
        return name;
    }

    // Make a domain that merges the two domains
    AstSenTree* combineDomains(AstSenTree* ap, AstSenTree* bp) {
        if (ap == m_deleteDomainp) return bp;
        UASSERT_OBJ(bp != m_deleteDomainp, bp, "Should not be delete domain");
        AstSenTree* const senTreep = ap->cloneTree(false);
        senTreep->addSensesp(bp->sensesp()->cloneTree(true));
        V3Const::constifyExpensiveEdit(senTreep);  // Remove duplicates
        senTreep->multi(true);  // Comment that it was made from 2 domains
        AstSenTree* const resultp = m_finder.getSenTree(senTreep);
        VL_DO_DANGLING(senTreep->deleteTree(), senTreep);  // getSenTree clones, so delete this
        return resultp;
    }

    // Only for member initialization in constructor
    static AstSenTree* makeDeleteDomainSenTree(FileLine* fl) {
        return new AstSenTree{fl, new AstSenItem{fl, AstSenItem::Illegal{}}};
    }

    // CONSTRUCTOR
    OrderProcess(AstNetlist* netlistp, OrderGraph& graph,
                 const std::unordered_map<const AstSenItem*, const AstSenTree*>& trigToSen,
                 const string& tag, bool slow,
                 const V3Order::ExternalDomainsProvider& externalDomains)
        : m_graph{graph}
        , m_trigToSen{trigToSen}
        , m_externalDomains{externalDomains}
        , m_finder{netlistp}
        , m_deleteDomainp{makeDeleteDomainSenTree(netlistp->fileline())}
        , m_tag{tag}
        , m_slow{slow} {
        pushDeletep(m_deleteDomainp);
    }

    ~OrderProcess() override = default;

public:
    // Order the logic
    static std::vector<AstNode*>
    main(AstNetlist* netlistp, OrderGraph& graph,
         const std::unordered_map<const AstSenItem*, const AstSenTree*>& trigToSen,
         const string& tag, bool parallel, bool slow,
         const V3Order::ExternalDomainsProvider& externalDomains) {
        OrderProcess visitor{netlistp, graph, trigToSen, tag, slow, externalDomains};
        visitor.process(parallel);
        return std::move(visitor.m_result);
    }
};

//######################################################################
// OrderMoveDomScope methods

// Check the domScope is on ready list, add if not
void OrderMoveDomScope::ready(OrderProcess* opp) {
    if (!m_onReadyList) {
        m_onReadyList = true;
        m_readyDomScopeE.pushBack(opp->m_pomReadyDomScope, this);
    }
}

// Mark one vertex as finished, remove from ready list if done
void OrderMoveDomScope::movedVertex(OrderProcess* opp, OrderMoveVertex* vertexp) {
    UASSERT_OBJ(m_onReadyList, vertexp,
                "Moving vertex from ready when nothing was on que as ready.");
    if (m_readyVertices.empty()) {  // Else more work to get to later
        m_onReadyList = false;
        m_readyDomScopeE.unlink(opp->m_pomReadyDomScope, this);
    }
}

//######################################################################

void OrderProcess::processDomains() {
    for (V3GraphVertex* itp = m_graph.verticesBeginp(); itp; itp = itp->verticesNextp()) {
        OrderEitherVertex* const vertexp = dynamic_cast<OrderEitherVertex*>(itp);
        UASSERT(vertexp, "Null or vertex not derived from EitherVertex");
        processDomainsIterate(vertexp);
    }
}

void OrderProcess::processDomainsIterate(OrderEitherVertex* vertexp) {
    // The graph routines have already sorted the vertexes and edges into best->worst order
    // Assign clock domains to each signal.
    //     Sequential logic is forced into the same sequential domain.
    //     Combo logic may be pushed into a seq domain if all its inputs are the same domain,
    //     else, if all inputs are from flops, it's end-of-sequential code
    //     else, it's full combo code
    if (vertexp->domainp()) return;  // Already processed, or sequential logic

    UINFO(5, "    pdi: " << vertexp << endl);
    AstSenTree* domainp = nullptr;
    if (OrderLogicVertex* const lvtxp = dynamic_cast<OrderLogicVertex*>(vertexp)) {
        domainp = lvtxp->hybridp();
    }

    std::vector<AstSenTree*> externalDomainps;

    for (V3GraphEdge* edgep = vertexp->inBeginp(); edgep; edgep = edgep->inNextp()) {
        OrderEitherVertex* const fromVertexp = static_cast<OrderEitherVertex*>(edgep->fromp());
        if (edgep->weight() && fromVertexp->domainMatters()) {
            AstSenTree* fromDomainp = fromVertexp->domainp();
            UASSERT(!fromDomainp->hasCombo(), "There should be no need for combinational domains");

            if (OrderVarVertex* const varVtxp = dynamic_cast<OrderVarVertex*>(fromVertexp)) {
                AstVarScope* const vscp = varVtxp->vscp();
                // Add in any external domains
                externalDomainps.clear();
                m_externalDomains(vscp, externalDomainps);
                for (AstSenTree* const externalDomainp : externalDomainps) {
                    UASSERT_OBJ(!externalDomainp->hasCombo(), vscp,
                                "There should be no need for combinational domains");
                    fromDomainp = combineDomains(fromDomainp, externalDomainp);
                }
            }

            // Irrelevant input vertex (never triggered)
            if (fromDomainp == m_deleteDomainp) continue;

            // First input to this vertex
            if (!domainp) domainp = fromDomainp;

            // Make a domain that merges the two domains
            if (domainp != fromDomainp) domainp = combineDomains(domainp, fromDomainp);
        }
    }

    // If nothing triggers this vertex, we can delete the corresponding logic
    if (!domainp) domainp = m_deleteDomainp;

    // Set the domain of the vertex
    vertexp->domainp(domainp);
    UINFO(5, "      done d=" << cvtToHex(vertexp->domainp())
                             << (domainp == m_deleteDomainp       ? " [DEL]"
                                 : vertexp->domainp()->hasCombo() ? " [COMB]"
                                 : vertexp->domainp()->isMulti()  ? " [MULT]"
                                                                  : "")
                             << " " << vertexp << endl);
}

//######################################################################
// OrderVisitor - Move graph construction

void OrderProcess::processEdgeReport() {
    // Make report of all signal names and what clock edges they have
    const string filename = v3Global.debugFilename(m_tag + "_order_edges.txt");
    const std::unique_ptr<std::ofstream> logp{V3File::new_ofstream(filename)};
    if (logp->fail()) v3fatal("Can't write " << filename);

    std::deque<string> report;

    // Rebuild the trigger to original AstSenTree map using equality key comparison, as
    // merging domains have created new AstSenTree instances which are not in the map
    std::unordered_map<VNRef<const AstSenItem>, const AstSenTree*> trigToSen;
    for (const auto& pair : m_trigToSen) trigToSen.emplace(*pair.first, pair.second);

    for (V3GraphVertex* itp = m_graph.verticesBeginp(); itp; itp = itp->verticesNextp()) {
        if (OrderVarVertex* const vvertexp = dynamic_cast<OrderVarVertex*>(itp)) {
            string name(vvertexp->vscp()->prettyName());
            if (dynamic_cast<OrderVarPreVertex*>(itp)) {
                name += " {PRE}";
            } else if (dynamic_cast<OrderVarPostVertex*>(itp)) {
                name += " {POST}";
            } else if (dynamic_cast<OrderVarPordVertex*>(itp)) {
                name += " {PORD}";
            }
            std::ostringstream os;
            os.setf(std::ios::left);
            os << "  " << cvtToHex(vvertexp->vscp()) << " " << std::setw(50) << name << " ";
            AstSenTree* const senTreep = vvertexp->domainp();
            if (senTreep == m_deleteDomainp) {
                os << "DELETED";
            } else {
                for (AstSenItem* senItemp = senTreep->sensesp(); senItemp;
                     senItemp = VN_AS(senItemp->nextp(), SenItem)) {
                    if (senItemp != senTreep->sensesp()) os << " or ";
                    const auto it = trigToSen.find(*senItemp);
                    if (it != trigToSen.end()) {
                        V3EmitV::verilogForTree(it->second, os);
                    } else {
                        V3EmitV::verilogForTree(senItemp, os);
                    }
                }
            }
            report.push_back(os.str());
        }
    }

    *logp << "Signals and their clock domains:\n";
    stable_sort(report.begin(), report.end());
    for (const string& i : report) *logp << i << '\n';
}

void OrderProcess::processMoveClear() {
    OrderMoveDomScope::clear();
    m_pomWaiting.reset();
    m_pomReadyDomScope.reset();
    m_pomGraph.clear();
}

void OrderProcess::processMoveBuildGraph() {
    // Build graph of only vertices
    UINFO(5, "  MoveBuildGraph\n");
    processMoveClear();
    // Vertex::user->OrderMoveVertex*, last edge added or nullptr=none
    m_pomGraph.userClearVertices();

    OrderMoveVertexMaker createOrderMoveVertex(&m_pomGraph, &m_pomWaiting);
    ProcessMoveBuildGraph<OrderMoveVertex> serialPMBG(&m_graph, &m_pomGraph, m_trigToSen,
                                                      &createOrderMoveVertex);
    serialPMBG.build();
}

//######################################################################
// OrderVisitor - Moving

void OrderProcess::processMove() {
    // The graph routines have already sorted the vertexes and edges into best->worst order
    //   Make a new waiting graph with only OrderLogicVertex's
    //   (Order is preserved in the recreation so the sorting is preserved)
    //   Move any node with all inputs ready to a "ready" graph mapped by domain and then scope
    //   While waiting graph ! empty  (and also known: something in ready graph)
    //     For all scopes in domain of top ready vertex
    //       For all vertexes in domain&scope of top ready vertex
    //           Make ordered activation block for this module
    //           Add that new activation to the list of calls to make.
    //           Move logic to ordered active
    //           Any children that have all inputs now ready move from waiting->ready graph
    //           (This may add nodes the for loop directly above needs to detext)
    processMovePrepReady();

    // New domain... another loop
    UINFO(5, "  MoveIterate\n");
    while (!m_pomReadyDomScope.empty()) {
        // Start with top node on ready list's domain & scope
        OrderMoveDomScope* domScopep = m_pomReadyDomScope.begin();
        OrderMoveVertex* const topVertexp
            = domScopep->readyVertices().begin();  // lintok-begin-on-ref
        UASSERT(topVertexp, "domScope on ready list without any nodes ready under it");
        // Work on all scopes ready inside this domain
        while (domScopep) {
            UINFO(6, "   MoveDomain l=" << domScopep->domainp() << endl);
            // Process all nodes ready under same domain & scope
            m_pomNewFuncp = nullptr;
            while (OrderMoveVertex* vertexp
                   = domScopep->readyVertices().begin()) {  // lintok-begin-on-ref
                processMoveOne(vertexp, domScopep, 1);
            }
            // Done with scope/domain pair, pick new scope under same domain, or nullptr if none
            // left
            OrderMoveDomScope* domScopeNextp = nullptr;
            for (OrderMoveDomScope* huntp = m_pomReadyDomScope.begin(); huntp;
                 huntp = huntp->readyDomScopeNextp()) {
                if (huntp->domainp() == domScopep->domainp()) {
                    domScopeNextp = huntp;
                    break;
                }
            }
            domScopep = domScopeNextp;
        }
    }
    UASSERT(m_pomWaiting.empty(),
            "Didn't converge; nodes waiting, none ready, perhaps some input activations lost.");
    // Cleanup memory
    processMoveClear();
}

void OrderProcess::processMovePrepReady() {
    // Make list of ready nodes
    UINFO(5, "  MovePrepReady\n");
    for (OrderMoveVertex* vertexp = m_pomWaiting.begin(); vertexp;) {
        OrderMoveVertex* const nextp = vertexp->pomWaitingNextp();
        if (vertexp->isWait() && vertexp->inEmpty()) processMoveReadyOne(vertexp);
        vertexp = nextp;
    }
}

void OrderProcess::processMoveReadyOne(OrderMoveVertex* vertexp) {
    // Recursive!
    // Move one node from waiting to ready list
    vertexp->setReady();
    // Remove node from waiting list
    vertexp->m_pomWaitingE.unlink(m_pomWaiting, vertexp);
    if (vertexp->logicp()) {
        // Add to ready list (indexed by domain and scope)
        vertexp->m_readyVerticesE.pushBack(vertexp->domScopep()->m_readyVertices, vertexp);
        vertexp->domScopep()->ready(this);
    } else {
        // vertexp represents a non-logic vertex.
        // Recurse to mark its following neighbors ready.
        processMoveDoneOne(vertexp);
    }
}

void OrderProcess::processMoveDoneOne(OrderMoveVertex* vertexp) {
    // Move one node from ready to completion
    vertexp->setMoved();
    // Unlink from ready lists
    if (vertexp->logicp()) {
        vertexp->m_readyVerticesE.unlink(vertexp->domScopep()->m_readyVertices, vertexp);
        vertexp->domScopep()->movedVertex(this, vertexp);
    }
    // Don't need to add it to another list, as we're done with it
    // Mark our outputs as one closer to ready
    for (V3GraphEdge *edgep = vertexp->outBeginp(), *nextp; edgep; edgep = nextp) {
        nextp = edgep->outNextp();
        OrderMoveVertex* const toVertexp = static_cast<OrderMoveVertex*>(edgep->top());
        UINFO(9, "          Clear to " << (toVertexp->inEmpty() ? "[EMP] " : "      ") << toVertexp
                                       << endl);
        // Delete this edge
        VL_DO_DANGLING(edgep->unlinkDelete(), edgep);
        if (toVertexp->inEmpty()) {
            // If destination node now has all inputs resolved; recurse to move that vertex
            // This is thus depth first (before width) which keeps the
            // resulting executable's d-cache happy.
            processMoveReadyOne(toVertexp);
        }
    }
}

void OrderProcess::processMoveOne(OrderMoveVertex* vertexp, OrderMoveDomScope* domScopep,
                                  int level) {
    UASSERT_OBJ(vertexp->domScopep() == domScopep, vertexp, "Domain mismatch; list misbuilt?");
    const OrderLogicVertex* const lvertexp = vertexp->logicp();
    const AstScope* const scopep = lvertexp->scopep();
    UINFO(5, "    POSmove l" << std::setw(3) << level << " d=" << cvtToHex(lvertexp->domainp())
                             << " s=" << cvtToHex(scopep) << " " << lvertexp << endl);
    AstActive* const newActivep
        = processMoveOneLogic(lvertexp, m_pomNewFuncp /*ref*/, m_pomNewStmts /*ref*/);
    if (newActivep) m_result.push_back(newActivep);
    processMoveDoneOne(vertexp);
}

AstActive* OrderProcess::processMoveOneLogic(const OrderLogicVertex* lvertexp,
                                             AstCFunc*& newFuncpr, int& newStmtsr) {
    AstActive* activep = nullptr;
    AstScope* const scopep = lvertexp->scopep();
    AstSenTree* const domainp = lvertexp->domainp();
    AstNode* nodep = lvertexp->nodep();
    AstNodeModule* const modp = scopep->modp();
    UASSERT(modp, "nullptr");

    // We are move the logic into a CFunc, so unlink it from the AstActive
    nodep->unlinkFrBack();

    // Process procedures per statement (unless profCFuncs), so we can split CFuncs within
    // procedures. Everything else is handled in one go
    bool suspendable = false;
    bool slow = m_slow;
    if (AstNodeProcedure* const procp = VN_CAST(nodep, NodeProcedure)) {
        suspendable = procp->isSuspendable();
        if (suspendable) slow = slow && !VN_IS(procp, Always);
        nodep = procp->stmtsp();
        pushDeletep(procp);
    }

    // Put suspendable processes into individual functions on their own
    if (suspendable) newFuncpr = nullptr;

    // When profCFuncs, create a new function for all logic block
    if (v3Global.opt.profCFuncs()) newFuncpr = nullptr;

    while (nodep) {
        // Split the CFunc if too large (but not when profCFuncs)
        if (!suspendable && !v3Global.opt.profCFuncs()
            && (v3Global.opt.outputSplitCFuncs()
                && v3Global.opt.outputSplitCFuncs() < newStmtsr)) {
            // Put every statement into a unique function to ease profiling or reduce function
            // size
            newFuncpr = nullptr;
        }
        if (!newFuncpr && domainp != m_deleteDomainp) {
            const string name = cfuncName(modp, domainp, scopep, nodep);
            newFuncpr
                = new AstCFunc{nodep->fileline(), name, scopep, suspendable ? "VlCoroutine" : ""};
            newFuncpr->isStatic(false);
            newFuncpr->isLoose(true);
            newFuncpr->slow(slow);
            newStmtsr = 0;
            scopep->addBlocksp(newFuncpr);
            // Create top call to it
            AstCCall* const callp = new AstCCall{nodep->fileline(), newFuncpr};
            callp->dtypeSetVoid();
            // Where will we be adding the call?
            AstActive* const newActivep = new AstActive{nodep->fileline(), name, domainp};
            newActivep->addStmtsp(callp->makeStmt());
            if (!activep) {
                activep = newActivep;
            } else {
                activep->addNext(newActivep);
            }
            UINFO(6, "      New " << newFuncpr << endl);
        }

        AstNode* const nextp = nodep->nextp();
        // When processing statements in a procedure, unlink the current statement
        if (nodep->backp()) nodep->unlinkFrBack();

        if (domainp == m_deleteDomainp) {
            VL_DO_DANGLING(pushDeletep(nodep), nodep);
        } else {
            newFuncpr->addStmtsp(nodep);
            // Add in the number of nodes we're adding
            if (v3Global.opt.outputSplitCFuncs()) newStmtsr += nodep->nodeCount();
        }

        nodep = nextp;
    }
    // Put suspendable processes into individual functions on their own
    if (suspendable) newFuncpr = nullptr;

    return activep;
}

void OrderProcess::processMTasks() {
    // For nondeterminism debug:
    V3Partition::hashGraphDebug(&m_graph, "V3Order's m_graph");

    // We already produced a graph of every var, input, and logic
    // block and all dependencies; this is 'm_graph'.
    //
    // Now, starting from m_graph, make a slightly-coarsened graph representing
    // only logic, and discarding edges we know we can ignore.
    // This is quite similar to the 'm_pomGraph' of the serial code gen:
    V3Graph logicGraph;
    OrderMTaskMoveVertexMaker create_mtask_vertex(&logicGraph);
    ProcessMoveBuildGraph<MTaskMoveVertex> mtask_pmbg(&m_graph, &logicGraph, m_trigToSen,
                                                      &create_mtask_vertex);
    mtask_pmbg.build();

    // Needed? We do this for m_pomGraph in serial mode, so do it here too:
    logicGraph.removeRedundantEdges(&V3GraphEdge::followAlwaysTrue);

    // Partition logicGraph into LogicMTask's. The partitioner will annotate
    // each vertex in logicGraph with a 'color' which is really an mtask ID
    // in this context.
    V3Partition partitioner(&m_graph, &logicGraph);
    V3Graph mtasks;
    partitioner.go(&mtasks);

    std::unordered_map<unsigned /*mtask id*/, MTaskState> mtaskStates;

    // Iterate through the entire logicGraph. For each logic node,
    // attach it to a per-MTask ordered list of logic nodes.
    // This is the order we'll execute logic nodes within the MTask.
    //
    // MTasks may span scopes and domains, so sort by both here:
    GraphStream<OrderVerticesByDomainThenScope> emit_logic(&logicGraph);
    const V3GraphVertex* moveVxp;
    while ((moveVxp = emit_logic.nextp())) {
        const MTaskMoveVertex* const movep = static_cast<const MTaskMoveVertex*>(moveVxp);
        // Only care about logic vertices
        if (!movep->logicp()) continue;

        const unsigned mtaskId = movep->color();
        UASSERT(mtaskId > 0, "Every MTaskMoveVertex should have an mtask assignment >0");

        // Add this logic to the per-mtask order
        mtaskStates[mtaskId].m_logics.push_back(movep->logicp());

        // Since we happen to be iterating over every logic node,
        // take this opportunity to annotate each AstVar with the id's
        // of mtasks that consume it and produce it. We'll use this
        // information in V3EmitC when we lay out var's in memory.
        const OrderLogicVertex* const logicp = movep->logicp();
        for (const V3GraphEdge* edgep = logicp->inBeginp(); edgep; edgep = edgep->inNextp()) {
            const OrderVarVertex* const pre_varp
                = dynamic_cast<const OrderVarVertex*>(edgep->fromp());
            if (!pre_varp) continue;
            AstVar* const varp = pre_varp->vscp()->varp();
            // varp depends on logicp, so logicp produces varp,
            // and vice-versa below
            varp->addProducingMTaskId(mtaskId);
        }
        for (const V3GraphEdge* edgep = logicp->outBeginp(); edgep; edgep = edgep->outNextp()) {
            const OrderVarVertex* const post_varp
                = dynamic_cast<const OrderVarVertex*>(edgep->top());
            if (!post_varp) continue;
            AstVar* const varp = post_varp->vscp()->varp();
            varp->addConsumingMTaskId(mtaskId);
        }
        // TODO? We ignore IO vars here, so those will have empty mtask
        // signatures. But we could also give those mtask signatures.
    }

    // Create the AstExecGraph node which represents the execution
    // of the MTask graph.
    FileLine* const rootFlp = v3Global.rootp()->fileline();
    AstExecGraph* const execGraphp = new AstExecGraph{rootFlp, m_tag};
    m_result.push_back(execGraphp);

    // Create CFuncs and bodies for each MTask.
    GraphStream<MTaskVxIdLessThan> emit_mtasks(&mtasks);
    const V3GraphVertex* mtaskVxp;
    while ((mtaskVxp = emit_mtasks.nextp())) {
        const AbstractLogicMTask* const mtaskp = static_cast<const AbstractLogicMTask*>(mtaskVxp);

        // Create a body for this mtask
        AstMTaskBody* const bodyp = new AstMTaskBody(rootFlp);
        MTaskState& state = mtaskStates[mtaskp->id()];
        state.m_mtaskBodyp = bodyp;

        // Create leaf CFunc's to run this mtask's logic,
        // and create a set of AstActive's to call those CFuncs.
        // Add the AstActive's into the AstMTaskBody.
        const AstSenTree* last_domainp = nullptr;
        AstCFunc* leafCFuncp = nullptr;
        int leafStmts = 0;
        for (const OrderLogicVertex* logicp : state.m_logics) {
            if (logicp->domainp() != last_domainp) {
                // Start a new leaf function.
                leafCFuncp = nullptr;
            }
            last_domainp = logicp->domainp();

            AstActive* const newActivep
                = processMoveOneLogic(logicp, leafCFuncp /*ref*/, leafStmts /*ref*/);
            if (newActivep) bodyp->addStmtsp(newActivep);
        }

        // Translate the LogicMTask graph into the corresponding ExecMTask
        // graph, which will outlive V3Order and persist for the remainder
        // of verilator's processing.
        // - The LogicMTask graph points to MTaskMoveVertex's
        //   and OrderLogicVertex's which are ephemeral to V3Order.
        // - The ExecMTask graph and the AstMTaskBody's produced here
        //   persist until code generation time.
        V3Graph* const depGraphp = execGraphp->depGraphp();
        state.m_execMTaskp = new ExecMTask(depGraphp, bodyp, mtaskp->id());
        // Cross-link each ExecMTask and MTaskBody
        //  Q: Why even have two objects?
        //  A: One is an AstNode, the other is a GraphVertex,
        //     to combine them would involve multiple inheritance...
        state.m_mtaskBodyp->execMTaskp(state.m_execMTaskp);
        for (V3GraphEdge* inp = mtaskp->inBeginp(); inp; inp = inp->inNextp()) {
            const V3GraphVertex* fromVxp = inp->fromp();
            const AbstractLogicMTask* const fromp
                = static_cast<const AbstractLogicMTask*>(fromVxp);
            const MTaskState& fromState = mtaskStates[fromp->id()];
            new V3GraphEdge(depGraphp, fromState.m_execMTaskp, state.m_execMTaskp, 1);
        }
        execGraphp->addMTaskBodiesp(bodyp);
    }
}

//######################################################################
// OrderVisitor - Top processing

void OrderProcess::process(bool multiThreaded) {
    // Dump data
    if (dumpGraph()) m_graph.dumpDotFilePrefixed(m_tag + "_orderg_pre");

    // Break cycles. Each strongly connected subgraph (including cutable
    // edges) will have its own color, and corresponds to a loop in the
    // original graph. However the new graph will be acyclic (the removed
    // edges are actually still there, just with weight 0).
    UINFO(2, "  Acyclic & Order...\n");
    m_graph.acyclic(&V3GraphEdge::followAlwaysTrue);
    if (dumpGraph()) m_graph.dumpDotFilePrefixed(m_tag + "_orderg_acyc");

    // Assign ranks so we know what to follow
    // Then, sort vertices and edges by that ordering
    m_graph.order();
    if (dumpGraph()) m_graph.dumpDotFilePrefixed(m_tag + "_orderg_order");

    // Assign logic vertices to new domains
    UINFO(2, "  Domains...\n");
    processDomains();
    if (dumpGraph()) m_graph.dumpDotFilePrefixed(m_tag + "_orderg_domain");

    if (dump()) processEdgeReport();

    if (!multiThreaded) {
        UINFO(2, "  Construct Move Graph...\n");
        processMoveBuildGraph();
        // Different prefix (ordermv) as it's not the same graph
        if (dumpGraph() >= 4) m_pomGraph.dumpDotFilePrefixed(m_tag + "_ordermv_start");
        m_pomGraph.removeRedundantEdges(&V3GraphEdge::followAlwaysTrue);
        if (dumpGraph() >= 4) m_pomGraph.dumpDotFilePrefixed(m_tag + "_ordermv_simpl");

        UINFO(2, "  Move...\n");
        processMove();
    } else {
        UINFO(2, "  Set up mtasks...\n");
        processMTasks();
    }

    // Dump data
    if (dumpGraph()) m_graph.dumpDotFilePrefixed(m_tag + "_orderg_done");
}

//######################################################################

namespace V3Order {

AstCFunc* order(AstNetlist* netlistp,  //
                const std::vector<V3Sched::LogicByScope*>& logic,  //
                const std::unordered_map<const AstSenItem*, const AstSenTree*>& trigToSen,
                const string& tag,  //
                bool parallel,  //
                bool slow,  //
                const ExternalDomainsProvider& externalDomains) {
    // Order the code
    const std::unique_ptr<OrderGraph> graph
        = OrderBuildVisitor::process(netlistp, logic, trigToSen);
    const auto& nodeps
        = OrderProcess::main(netlistp, *graph, trigToSen, tag, parallel, slow, externalDomains);

    // Create the result function
    AstScope* const scopeTopp = netlistp->topScopep()->scopep();
    AstCFunc* const funcp = new AstCFunc{netlistp->fileline(), "_eval_" + tag, scopeTopp, ""};
    funcp->dontCombine(true);
    funcp->isStatic(false);
    funcp->isLoose(true);
    funcp->slow(slow);
    funcp->isConst(false);
    funcp->declPrivate(true);
    scopeTopp->addBlocksp(funcp);

    // Add ordered statements to the result function
    for (AstNode* const nodep : nodeps) funcp->addStmtsp(nodep);

    // Dispose of the remnants of the inputs
    for (auto* const lbsp : logic) lbsp->deleteActives();

    // Done
    return funcp;
}

}  // namespace V3Order
