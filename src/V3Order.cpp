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
//      Add master "*INPUTS*" vertex.
//      For inputs on top level
//          Add vertex for each input var.
//              Add edge INPUTS->var_vertex
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
#include "V3Partition.h"
#include "V3PartitionGraph.h"
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
#include <unordered_set>
#include <vector>

//######################################################################
// Utilities

static bool domainsExclusive(const AstSenTree* fromp, const AstSenTree* top) {
    // Return 'true' if we can prove that both 'from' and 'to' cannot both
    // be active on the same eval pass, or false if we can't prove this.
    //
    // This detects the case of 'always @(posedge clk)'
    // and 'always @(negedge clk)' being exclusive. It also detects
    // that initial/settle blocks and post-initial blocks are exclusive.
    //
    // Are there any other cases we need to handle? Maybe not,
    // because these are not exclusive:
    //   always @(posedge A or posedge B)
    //   always @(negedge A)
    //
    // ... unless you know more about A and B, which sounds hard.

    const bool toInitial = top->hasInitial() || top->hasSettle();
    const bool fromInitial = fromp->hasInitial() || fromp->hasSettle();
    if (toInitial != fromInitial) return true;

    const AstSenItem* const fromSenListp = fromp->sensesp();
    const AstSenItem* const toSenListp = top->sensesp();

    UASSERT_OBJ(fromSenListp, fromp, "sensitivity list empty");
    UASSERT_OBJ(toSenListp, top, "sensitivity list empty");

    if (fromSenListp->nextp()) return false;
    if (toSenListp->nextp()) return false;

    const AstNodeVarRef* const fromVarrefp = fromSenListp->varrefp();
    const AstNodeVarRef* const toVarrefp = toSenListp->varrefp();
    if (!fromVarrefp || !toVarrefp) return false;

    // We know nothing about the relationship between different clocks here,
    // so give up on proving anything.
    if (fromVarrefp->varScopep() != toVarrefp->varScopep()) return false;

    return fromSenListp->edgeType().exclusiveEdge(toSenListp->edgeType());
}

// Predicate returning true if the LHS of the given assignment is a signal marked as clocker
static bool isClockerAssignment(AstNodeAssign* nodep) {
    class Visitor final : public VNVisitor {
    public:
        bool m_clkAss = false;  // There is signals marked as clocker in the assignment
    private:
        // METHODS
        VL_DEBUG_FUNC;  // Declare debug()
        virtual void visit(AstNodeAssign* nodep) override {
            if (const AstVarRef* const varrefp = VN_CAST(nodep->lhsp(), VarRef)) {
                if (varrefp->varp()->attrClocker() == VVarAttrClocker::CLOCKER_YES) {
                    m_clkAss = true;
                    UINFO(6, "node was marked as clocker " << varrefp << endl);
                }
            }
            iterateChildren(nodep->rhsp());
        }
        virtual void visit(AstNodeMath*) override {}  // Accelerate
        virtual void visit(AstNode* nodep) override { iterateChildren(nodep); }
    } visitor;
    visitor.iterate(nodep);
    return visitor.m_clkAss;
}

//######################################################################
// Functions for above graph classes

void OrderGraph::loopsVertexCb(V3GraphVertex* vertexp) {
    if (debug()) cout << "-Info-Loop: " << vertexp << "\n";
    if (OrderLogicVertex* const vvertexp = dynamic_cast<OrderLogicVertex*>(vertexp)) {
        std::cerr << vvertexp->nodep()->fileline()->warnOther()
                  << "     Example path: " << vvertexp->nodep()->typeName() << endl;
    }
    if (OrderVarVertex* const vvertexp = dynamic_cast<OrderVarVertex*>(vertexp)) {
        std::cerr << vvertexp->varScp()->fileline()->warnOther()
                  << "     Example path: " << vvertexp->varScp()->prettyName() << endl;
    }
}

//######################################################################
// The class is used for propagating the clocker attribute for further
// avoiding marking clock signals as circular.
// Transformation:
//    while (newClockerMarked)
//        check all assignments
//            if RHS is marked as clocker:
//                mark LHS as clocker as well.
//                newClockerMarked = true;
//
// In addition it also check whether clock and data signals are mixed, and
// produce a CLKDATA warning if so.
//

class OrderClkMarkVisitor final : public VNVisitor {
    bool m_hasClk = false;  // flag indicating whether there is clock signal on rhs
    bool m_inClocked = false;  // Currently inside a sequential block
    bool m_newClkMarked;  // Flag for deciding whether a new run is needed
    bool m_inAss = false;  // Currently inside of a assignment
    int m_childClkWidth = 0;  // If in hasClk, width of clock signal in child

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    virtual void visit(AstNodeAssign* nodep) override {
        m_hasClk = false;
        m_inAss = true;
        m_childClkWidth = 0;
        iterateAndNextNull(nodep->rhsp());
        m_inAss = false;
        if (m_hasClk) {
            // do the marking
            if (nodep->lhsp()->width() > m_childClkWidth) {
                nodep->v3warn(CLKDATA, "Clock is assigned to part of data signal "
                                           << nodep->lhsp()->prettyNameQ());
                UINFO(4, "CLKDATA: lhs with width " << nodep->lhsp()->width() << endl);
                UINFO(4, "     but rhs clock with width " << m_childClkWidth << endl);
                return;  // skip the marking
            }

            const AstVarRef* const lhsp = VN_CAST(nodep->lhsp(), VarRef);
            if (lhsp && (lhsp->varp()->attrClocker() == VVarAttrClocker::CLOCKER_UNKNOWN)) {
                lhsp->varp()->attrClocker(VVarAttrClocker::CLOCKER_YES);  // mark as clocker
                m_newClkMarked = true;  // enable a further run since new clocker is marked
                UINFO(5, "node is newly marked as clocker by assignment " << lhsp << endl);
            }
        }
    }
    virtual void visit(AstVarRef* nodep) override {
        if (m_inAss && nodep->varp()->attrClocker() == VVarAttrClocker::CLOCKER_YES) {
            if (m_inClocked) {
                nodep->v3warn(CLKDATA,
                              "Clock used as data (on rhs of assignment) in sequential block "
                                  << nodep->prettyNameQ());
            } else {
                m_hasClk = true;
                m_childClkWidth = nodep->width();  // Pass up
                UINFO(5, "node is already marked as clocker " << nodep << endl);
            }
        }
    }
    virtual void visit(AstConcat* nodep) override {
        if (m_inAss) {
            iterateAndNextNull(nodep->lhsp());
            const int lw = m_childClkWidth;
            iterateAndNextNull(nodep->rhsp());
            const int rw = m_childClkWidth;
            m_childClkWidth = lw + rw;  // Pass up
        }
    }
    virtual void visit(AstNodeSel* nodep) override {
        if (m_inAss) {
            iterateChildren(nodep);
            // Pass up result width
            if (m_childClkWidth > nodep->width()) m_childClkWidth = nodep->width();
        }
    }
    virtual void visit(AstSel* nodep) override {
        if (m_inAss) {
            iterateChildren(nodep);
            if (m_childClkWidth > nodep->width()) m_childClkWidth = nodep->width();
        }
    }
    virtual void visit(AstReplicate* nodep) override {
        if (m_inAss) {
            iterateChildren(nodep);
            if (VN_IS(nodep->rhsp(), Const)) {
                m_childClkWidth = m_childClkWidth * VN_AS(nodep->rhsp(), Const)->toUInt();
            } else {
                m_childClkWidth = nodep->width();  // can not check in this case.
            }
        }
    }
    virtual void visit(AstActive* nodep) override {
        m_inClocked = nodep->hasClocked();
        iterateChildren(nodep);
        m_inClocked = false;
    }
    virtual void visit(AstNode* nodep) override { iterateChildren(nodep); }

    // CONSTRUCTORS
    explicit OrderClkMarkVisitor(AstNode* nodep) {
        do {
            m_newClkMarked = false;
            iterate(nodep);
        } while (m_newClkMarked);
    }
    virtual ~OrderClkMarkVisitor() override = default;

public:
    static void process(AstNetlist* nodep) { OrderClkMarkVisitor{nodep}; }
};

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
    OrderVarVertex* getVarVertex(V3Graph* graphp, AstScope* scopep, AstVarScope* varscp,
                                 VarVertexType type) {
        const unsigned idx = static_cast<unsigned>(type);
        OrderVarVertex* vertexp = m_vertexps[idx];
        if (!vertexp) {
            switch (type) {
            case VarVertexType::STD:
                vertexp = new OrderVarStdVertex(graphp, scopep, varscp);
                break;
            case VarVertexType::PRE:
                vertexp = new OrderVarPreVertex(graphp, scopep, varscp);
                break;
            case VarVertexType::PORD:
                vertexp = new OrderVarPordVertex(graphp, scopep, varscp);
                break;
            case VarVertexType::POST:
                vertexp = new OrderVarPostVertex(graphp, scopep, varscp);
                break;
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
    const VNUser1InUse user1InUse;
    const VNUser2InUse user2InUse;
    AstUser1Allocator<AstVarScope, OrderUser> m_orderUser;

    // STATE
    // The ordering graph built by this visitor
    OrderGraph* const m_graphp = new OrderGraph;
    // Singleton vertex that all top level inputs depend on
    OrderInputsVertex* const m_inputsVxp = new OrderInputsVertex{m_graphp, nullptr};
    // Singleton DPI Export trigger event vertex
    OrderVarVertex* const m_dpiExportTriggerVxp
        = v3Global.rootp()->dpiExportTriggerp()
              ? getVarVertex(v3Global.rootp()->dpiExportTriggerp(), VarVertexType::STD)
              : nullptr;

    OrderLogicVertex* m_activeSenVxp = nullptr;  // Sensitivity vertex for clocked logic
    OrderLogicVertex* m_logicVxp = nullptr;  // Current loic block being analyzed

    // Current AstScope being processed
    AstScope* m_scopep = nullptr;
    // Sensitivity list for non-combinational logic (incl. initial and settle),
    // nullptr for combinational logic
    AstSenTree* m_domainp = nullptr;

    bool m_inClocked = false;  // Underneath clocked AstActive
    bool m_inClkAss = false;  // Underneath AstNodeAssign to clock
    bool m_inPre = false;  // Underneath AstAssignPre
    bool m_inPost = false;  // Underneath AstAssignPost/AstAlwaysPost
    bool m_inPostponed = false;  // Underneath AstAlwaysPostponed

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    void iterateLogic(AstNode* nodep) {
        UASSERT_OBJ(!m_logicVxp, nodep, "Should not nest");
        // Reset VarUsage
        AstNode::user2ClearTree();
        // Create LogicVertex for this logic node
        m_logicVxp = new OrderLogicVertex(m_graphp, m_scopep, m_domainp, nodep);
        // If this logic has a clocked activation, add a link from the sensitivity list LogicVertex
        // to this LogicVertex.
        if (m_activeSenVxp) new OrderEdge(m_graphp, m_activeSenVxp, m_logicVxp, WEIGHT_NORMAL);
        // Gather variable dependencies based on usage
        iterateChildren(nodep);
        // Finished with this logic
        m_logicVxp = nullptr;
    }

    OrderVarVertex* getVarVertex(AstVarScope* varscp, VarVertexType type) {
        return m_orderUser(varscp).getVarVertex(m_graphp, m_scopep, varscp, type);
    }

    // VISITORS
    virtual void visit(AstSenTree* nodep) override {
        // This should only find the global AstSenTrees under the AstTopScope, which we ignore
        // here. We visit AstSenTrees separately when encountering the AstActive that references
        // them.
        UASSERT_OBJ(!m_scopep, nodep, "AstSenTrees should have been made global in V3ActiveTop");
    }
    virtual void visit(AstScope* nodep) override {
        UASSERT_OBJ(!m_scopep, nodep, "Should not nest");
        m_scopep = nodep;
        iterateChildren(nodep);
        m_scopep = nullptr;
    }
    virtual void visit(AstActive* nodep) override {
        UASSERT_OBJ(!nodep->sensesStorep(), nodep,
                    "AstSenTrees should have been made global in V3ActiveTop");
        UASSERT_OBJ(m_scopep, nodep, "AstActive not under AstScope");
        UASSERT_OBJ(!m_logicVxp, nodep, "AstActive under logic");
        UASSERT_OBJ(!m_inClocked && !m_activeSenVxp && !m_domainp, nodep, "Should not nest");

        m_inClocked = nodep->sensesp()->hasClocked();

        // Analyze variable references in sensitivity list. Note that non-clocked sensitivity lists
        // don't reference any variables (have no clocks), so the sensitivity list vertex would
        // have no incoming dependencies and is hence redundant, therefore we only do this for
        // clocked sensitivity lists.
        if (m_inClocked) {
            // Add LogicVertex for the sensitivity list of this AstActive.
            m_activeSenVxp = new OrderLogicVertex(m_graphp, m_scopep, nodep->sensesp(), nodep);
            // Analyze variables in the sensitivity list
            iterateChildren(nodep->sensesp());
        }

        // Ignore the sensitivity domain for combinational logic. We will assign combinational
        // logic to a domain later, based on the domains of incoming variables.
        if (!nodep->sensesp()->hasCombo()) m_domainp = nodep->sensesp();

        // Analyze logic underneath
        iterateChildren(nodep);

        //
        m_inClocked = false;
        m_activeSenVxp = nullptr;
        m_domainp = nullptr;
    }
    virtual void visit(AstNodeVarRef* nodep) override {
        // As we explicitly not visit (see ignored nodes below) any subtree that is not relevant
        // for ordering, we should be able to assert this:
        UASSERT_OBJ(m_scopep, nodep, "AstVarRef not under scope");
        UASSERT_OBJ(m_logicVxp || m_activeSenVxp, nodep,
                    "AstVarRef not under logic nor sensitivity list");
        AstVarScope* const varscp = nodep->varScopep();
        UASSERT_OBJ(varscp, nodep, "Var didn't get varscoped in V3Scope.cpp");
        if (!m_logicVxp) {
            // Variable reference in sensitivity list. Add clock dependency.

            UASSERT_OBJ(!nodep->access().isWriteOrRW(), nodep,
                        "How can a sensitivity list be writing a variable?");
            // Add edge from sensed VarStdVertex -> to sensitivity list LogicVertex
            OrderVarVertex* const varVxp = getVarVertex(varscp, VarVertexType::STD);
            varVxp->isClock(true);
            new OrderEdge(m_graphp, varVxp, m_activeSenVxp, WEIGHT_MEDIUM);
        } else {
            // Variable reference in logic. Add data dependency.

            // Check whether this variable was already generated/consumed in the same logic. We
            // don't want to add extra edges if the logic has many usages of the same variable,
            // so only proceed on first encounter.
            const bool prevGen = varscp->user2() & VU_GEN;
            const bool prevCon = varscp->user2() & VU_CON;

            // Compute whether the variable is produced (written) here
            bool gen = false;
            if (!prevGen && nodep->access().isWriteOrRW()) {
                gen = true;
                if (m_inPostponed) {
                    // IEE 1800-2017 (4.2.9) forbids any value updates in the postponed region, but
                    // Verilator generated trigger signals for $strobe are cleared after the
                    // display is executed. This is both safe to ignore (because their single read
                    // is in the same AstAlwaysPostponed, just prior to the clear), and is
                    // necessary to ignore to avoid a circular logic (UNOPTFLAT) warning.
                    UASSERT_OBJ(prevCon, nodep, "Should have been consumed in same process");
                    gen = false;
                }
            }

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

                // TODO: Explain how the following two exclusions are useful
                if (varscp->varp()->attrClockEn() && !m_inPre && !m_inPost && !m_inClocked) {
                    // 'clock_enable' attribute on this signal: user's worrying about it for us
                    con = false;
                }
                if (m_inClkAss
                    && (varscp->varp()->attrClocker() != VVarAttrClocker::CLOCKER_YES)) {
                    // 'clocker' attribute on some other signal in same logic: same as
                    // 'clock_enable' attribute above
                    con = false;
                    UINFO(4, "nodep used as clock_enable " << varscp << " in "
                                                           << m_logicVxp->nodep() << endl);
                }
            }

            // Roles of vertices:
            // VarVertexType::STD:  Data dependencies for combinational logic and delayed
            //                      assignment updates (AssignPost).
            // VarVertexType::POST: Ensures all sequential blocks reading a signal do so before
            //                      any combinational or delayed assignments update that signal.
            // VarVertexType::PORD: Ensures a _d = _q AssignPre is the first write of a _d,
            //                      before any sequential blocks write to that _d.
            // VarVertexType::PRE:  This is an optimization. Try to ensure that a _d = _q
            //                      AssignPre is the last read of a _q, after all reads of that
            //                      _q by sequential logic. Note: The model is still correct if we
            //                      cannot satisfy this due to other constraints. If this ordering
            //                      is possible, then combined with the PORD constraint we get
            //                      that all writes to _d are after all reads of a _q, which then
            //                      allows us to eliminate the _d completely and assign to the _q
            //                      directly (this is what V3LifePost does).

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
                        new OrderPostCutEdge(m_graphp, m_logicVxp, varVxp);
                        // Mark the VarVertex as being produced by a delayed (non-blocking)
                        // assignment. This is used to control marking internal clocks
                        // circular, which must only happen if they are generated by delayed
                        // assignment.
                        varVxp->isDelayed(true);
                        UINFO(5, "     Found delayed assignment (post) " << varVxp << endl);
                    } else if (varscp->varp()->attrClocker() == VVarAttrClocker::CLOCKER_YES) {
                        // If the variable has the 'clocker' attribute, avoid making it
                        // circular by adding a hard edge instead of normal cuttable edge.
                        new OrderEdge(m_graphp, m_logicVxp, varVxp, WEIGHT_NORMAL);
                    } else {
                        new OrderComboCutEdge(m_graphp, m_logicVxp, varVxp);
                    }

                    // Add edge from produced VarPostVertex -> to producing LogicVertex

                    // For m_inPost:
                    //    Add edge consumed_var_POST->logic_vertex
                    //    This prevents a consumer of the "early" value to be scheduled
                    //   after we've changed to the next-cycle value
                    // ALWAYS do it:
                    //    There maybe a wire a=b; between the two blocks
                    OrderVarVertex* const postVxp = getVarVertex(varscp, VarVertexType::POST);
                    new OrderEdge(m_graphp, postVxp, m_logicVxp, WEIGHT_POST);
                } else if (m_inPre) {  // AstAssignPre
                    // Add edge from producing LogicVertex -> produced VarPordVertex
                    OrderVarVertex* const ordVxp = getVarVertex(varscp, VarVertexType::PORD);
                    new OrderEdge(m_graphp, m_logicVxp, ordVxp, WEIGHT_NORMAL);
                    // Add edge from producing LogicVertex -> produced VarStdVertex
                    OrderVarVertex* const varVxp = getVarVertex(varscp, VarVertexType::STD);
                    new OrderEdge(m_graphp, m_logicVxp, varVxp, WEIGHT_NORMAL);
                } else {
                    // Sequential (clocked) logic
                    // Add edge from produced VarPordVertex -> to producing LogicVertex
                    OrderVarVertex* const ordVxp = getVarVertex(varscp, VarVertexType::PORD);
                    new OrderEdge(m_graphp, ordVxp, m_logicVxp, WEIGHT_NORMAL);
                    // Add edge from producing LogicVertex-> to produced VarStdVertex
                    OrderVarVertex* const varVxp = getVarVertex(varscp, VarVertexType::STD);
                    new OrderEdge(m_graphp, m_logicVxp, varVxp, WEIGHT_NORMAL);
                }
            }

            // Variable is consumed
            if (con) {
                // Update VarUsage
                varscp->user2(varscp->user2() | VU_CON);
                // Add edges
                if (!m_inClocked || m_inPost) {
                    // Combinational logic
                    OrderVarVertex* const varVxp = getVarVertex(varscp, VarVertexType::STD);
                    // Add edge from consumed VarStdVertex -> to consuming LogicVertex
                    new OrderEdge(m_graphp, varVxp, m_logicVxp, WEIGHT_MEDIUM);
                } else if (m_inPre) {
                    // AstAssignPre logic
                    // Add edge from consumed VarPreVertex -> to consuming LogicVertex
                    // This one is cutable (vs the producer) as there's only one such consumer,
                    // but may be many producers
                    OrderVarVertex* const preVxp = getVarVertex(varscp, VarVertexType::PRE);
                    new OrderPreCutEdge(m_graphp, preVxp, m_logicVxp);
                } else {
                    // Sequential (clocked) logic
                    // Add edge from consuming LogicVertex -> to consumed VarPreVertex
                    // Generation of 'pre' because we want to indicate it should be before
                    // AstAssignPre
                    OrderVarVertex* const preVxp = getVarVertex(varscp, VarVertexType::PRE);
                    new OrderEdge(m_graphp, m_logicVxp, preVxp, WEIGHT_NORMAL);
                    // Add edge from consuming LogicVertex -> to consumed VarPostVertex
                    OrderVarVertex* const postVxp = getVarVertex(varscp, VarVertexType::POST);
                    new OrderEdge(m_graphp, m_logicVxp, postVxp, WEIGHT_POST);
                }
            }
        }
    }
    virtual void visit(AstDpiExportUpdated* nodep) override {
        // This is under a logic block (AstAlways) sensitive to a change in the DPI export trigger.
        // We just need to add an edge to the enclosing logic vertex (the vertex for the
        // AstAlways).
        OrderVarVertex* const varVxp = getVarVertex(nodep->varScopep(), VarVertexType::STD);
        new OrderComboCutEdge(m_graphp, m_logicVxp, varVxp);
        // Only used for ordering, so we can get rid of it here
        nodep->unlinkFrBack();
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }
    virtual void visit(AstCCall* nodep) override {
        // Calls to 'context' imported DPI function may call DPI exported functions
        if (m_dpiExportTriggerVxp && nodep->funcp()->dpiImportWrapper()
            && nodep->funcp()->dpiContext()) {
            UASSERT_OBJ(m_logicVxp, nodep, "Call not under logic");
            new OrderEdge(m_graphp, m_logicVxp, m_dpiExportTriggerVxp, WEIGHT_NORMAL);
        }
        iterateChildren(nodep);
    }

    //--- Logic akin to SystemVerilog Processes (AstNodeProcedure)
    virtual void visit(AstInitial* nodep) override {  //
        iterateLogic(nodep);
    }
    virtual void visit(AstInitialAutomatic* nodep) override {  //
        iterateLogic(nodep);
    }
    virtual void visit(AstInitialStatic* nodep) override {  //
        iterateLogic(nodep);
    }
    virtual void visit(AstAlways* nodep) override {  //
        iterateLogic(nodep);
    }
    virtual void visit(AstAlwaysPost* nodep) override {
        UASSERT_OBJ(!m_inPost, nodep, "Should not nest");
        m_inPost = true;
        iterateLogic(nodep);
        m_inPost = false;
    }
    virtual void visit(AstAlwaysPostponed* nodep) override {
        UASSERT_OBJ(!m_inPostponed, nodep, "Should not nest");
        m_inPostponed = true;
        iterateLogic(nodep);
        m_inPostponed = false;
    }
    virtual void visit(AstFinal* nodep) override {  // LCOV_EXCL_START
        nodep->v3fatalSrc("AstFinal should have been removed already");
    }  // LCOV_EXCL_STOP

    //--- Logic akin go SystemVerilog continuous assignments
    virtual void visit(AstAssignAlias* nodep) override {  //
        iterateLogic(nodep);
    }
    virtual void visit(AstAssignW* nodep) override {
        UASSERT_OBJ(!m_inClkAss, nodep, "Should not nest");
        m_inClkAss = isClockerAssignment(nodep);
        iterateLogic(nodep);
        m_inClkAss = false;
    }
    virtual void visit(AstAssignPre* nodep) override {
        UASSERT_OBJ(!m_inClkAss && !m_inPre, nodep, "Should not nest");
        m_inClkAss = isClockerAssignment(nodep);
        m_inPre = true;
        iterateLogic(nodep);
        m_inPre = false;
        m_inClkAss = false;
    }
    virtual void visit(AstAssignPost* nodep) override {
        UASSERT_OBJ(!m_inClkAss && !m_inPost, nodep, "Should not nest");
        m_inClkAss = isClockerAssignment(nodep);
        m_inPost = true;
        iterateLogic(nodep);
        m_inPost = false;
        m_inClkAss = false;
    }

    //--- Verilator concoctions
    virtual void visit(AstAlwaysPublic* nodep) override {  //
        iterateLogic(nodep);
    }
    virtual void visit(AstCoverToggle* nodep) override {  //
        iterateLogic(nodep);
    }

    //--- Ignored nodes
    virtual void visit(AstVar*) override {}
    virtual void visit(AstVarScope* nodep) override {}
    virtual void visit(AstCell*) override {}  // Only interested in the respective AstScope
    virtual void visit(AstTypeTable*) override {}
    virtual void visit(AstConstPool*) override {}
    virtual void visit(AstClass*) override {}
    virtual void visit(AstCFunc*) override {
        // Calls to DPI exports handled with AstCCall. /* verilator public */ functions are
        // ignored for now (and hence potentially mis-ordered), but could use the same or
        // similar mechanism as DPI exports. Every other impure function (including those
        // that may set a non-local variable) must have been inlined in V3Task.
    }

    //---
    virtual void visit(AstNode* nodep) override { iterateChildren(nodep); }

    // CONSTRUCTOR
    explicit OrderBuildVisitor(AstNetlist* nodep) {
        // Enable debugging (3 is default if global debug; we want acyc debugging)
        if (debug()) m_graphp->debug(5);

        // Add edges from the InputVertex to all top level input signal VarStdVertex
        for (AstVarScope* vscp = nodep->topScopep()->scopep()->varsp(); vscp;
             vscp = VN_AS(vscp->nextp(), VarScope)) {
            if (vscp->varp()->isNonOutput()) {
                OrderVarVertex* const varVxp = getVarVertex(vscp, VarVertexType::STD);
                new OrderEdge(m_graphp, m_inputsVxp, varVxp, WEIGHT_INPUT);
            }
        }

        // Build the rest of the graph
        iterate(nodep);
    }
    ~OrderBuildVisitor() override = default;

public:
    // Process the netlist and return the constructed ordering graph. It's 'process' because
    // this visitor does change the tree (removes some nodes related to DPI export trigger).
    static std::unique_ptr<OrderGraph> process(AstNetlist* nodep) {
        return std::unique_ptr<OrderGraph>{OrderBuildVisitor{nodep}.m_graphp};
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

inline std::ostream& operator<<(std::ostream& lhs, const OrderMoveDomScope& rhs) {
    lhs << rhs.name();
    return lhs;
}

//######################################################################
// ProcessMoveBuildGraph

template <class T_MoveVertex>
class ProcessMoveBuildGraph final {
    // ProcessMoveBuildGraph takes as input the fine-grained graph of
    // OrderLogicVertex, OrderVarVertex, etc; this is 'm_graph' in
    // OrderVisitor. It produces a slightly coarsened graph to drive the
    // code scheduling.
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

    // TYPES
    using VxDomPair = std::pair<const V3GraphVertex*, const AstSenTree*>;
    using Logic2Move = std::unordered_map<const OrderLogicVertex*, T_MoveVertex*>;

public:
    class MoveVertexMaker VL_NOT_FINAL {
    public:
        // Clients of ProcessMoveBuildGraph must supply MoveVertexMaker
        // which creates new T_MoveVertex's. Each new vertex wraps lvertexp
        // (which may be nullptr.)
        virtual T_MoveVertex* makeVertexp(  //
            OrderLogicVertex* lvertexp, const OrderEitherVertex* varVertexp,
            const AstScope* scopep, const AstSenTree* domainp)
            = 0;
        virtual void freeVertexp(T_MoveVertex* freeMep) = 0;
    };

private:
    // MEMBERS
    const V3Graph* m_graphp;  // Input graph of OrderLogicVertex's etc
    V3Graph* m_outGraphp;  // Output graph of T_MoveVertex's
    MoveVertexMaker* const m_vxMakerp;  // Factory class for T_MoveVertex's
    Logic2Move m_logic2move;  // Map Logic to Vertex
    // Maps an (original graph vertex, domain) pair to a T_MoveVertex
    // Not std::unordered_map, because std::pair doesn't provide std::hash
    std::map<VxDomPair, T_MoveVertex*> m_var2move;

public:
    // CONSTRUCTORS
    ProcessMoveBuildGraph(const V3Graph* logicGraphp,  // Input graph of OrderLogicVertex etc.
                          V3Graph* outGraphp,  // Output graph of T_MoveVertex's
                          MoveVertexMaker* vxMakerp)
        : m_graphp{logicGraphp}
        , m_outGraphp{outGraphp}
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

        // For each logic node, make a T_MoveVertex
        for (V3GraphVertex* itp = m_graphp->verticesBeginp(); itp; itp = itp->verticesNextp()) {
            if (OrderLogicVertex* const lvertexp = dynamic_cast<OrderLogicVertex*>(itp)) {
                T_MoveVertex* const moveVxp = m_vxMakerp->makeVertexp(
                    lvertexp, nullptr, lvertexp->scopep(), lvertexp->domainp());
                if (moveVxp) {
                    // Cross link so we can find it later
                    m_logic2move[lvertexp] = moveVxp;
                }
            }
        }
        // Build edges between logic vertices
        for (V3GraphVertex* itp = m_graphp->verticesBeginp(); itp; itp = itp->verticesNextp()) {
            if (OrderLogicVertex* const lvertexp = dynamic_cast<OrderLogicVertex*>(itp)) {
                T_MoveVertex* const moveVxp = m_logic2move[lvertexp];
                if (moveVxp) iterate(moveVxp, lvertexp, lvertexp->domainp());
            }
        }
    }

private:
    // Return true if moveVxp has downstream dependencies
    bool iterate(T_MoveVertex* moveVxp, const V3GraphVertex* origVxp, const AstSenTree* domainp) {
        bool madeDeps = false;
        // Search forward from given original vertex, making new edges from
        // moveVxp forward
        for (V3GraphEdge* edgep = origVxp->outBeginp(); edgep; edgep = edgep->outNextp()) {
            if (edgep->weight() == 0) {  // Was cut
                continue;
            }
            const int weight = edgep->weight();
            if (const OrderLogicVertex* const toLVertexp
                = dynamic_cast<const OrderLogicVertex*>(edgep->top())) {

                // Do not construct dependencies across exclusive domains.
                if (domainsExclusive(domainp, toLVertexp->domainp())) continue;

                // Path from vertexp to a logic vertex; new edge.
                // Note we use the last edge's weight, not some function of
                // multiple edges
                new OrderEdge(m_outGraphp, moveVxp, m_logic2move[toLVertexp], weight);
                madeDeps = true;
            } else {
                // This is an OrderVarVertex or other vertex representing
                // data. (Could be var, settle, or input type vertex.)
                const V3GraphVertex* nonLogicVxp = edgep->top();
                const VxDomPair key(nonLogicVxp, domainp);
                if (!m_var2move[key]) {
                    const OrderEitherVertex* const eithp
                        = dynamic_cast<const OrderEitherVertex*>(nonLogicVxp);
                    T_MoveVertex* const newMoveVxp
                        = m_vxMakerp->makeVertexp(nullptr, eithp, eithp->scopep(), domainp);
                    m_var2move[key] = newMoveVxp;

                    // Find downstream logics that depend on (var, domain)
                    if (!iterate(newMoveVxp, edgep->top(), domainp)) {
                        // No downstream dependencies, so remove this
                        // intermediate vertex.
                        m_var2move[key] = nullptr;
                        m_vxMakerp->freeVertexp(newMoveVxp);
                        continue;
                    }
                }

                // Create incoming edge, from previous logic that writes
                // this var, to the Vertex representing the (var,domain)
                new OrderEdge(m_outGraphp, moveVxp, m_var2move[key], weight);
                madeDeps = true;
            }
        }
        return madeDeps;
    }
    VL_UNCOPYABLE(ProcessMoveBuildGraph);
};

//######################################################################
// OrderMoveVertexMaker and related

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
    virtual OrderMoveVertex* makeVertexp(OrderLogicVertex* lvertexp, const OrderEitherVertex*,
                                         const AstScope* scopep,
                                         const AstSenTree* domainp) override {
        OrderMoveVertex* const resultp = new OrderMoveVertex(m_pomGraphp, lvertexp);
        resultp->domScopep(OrderMoveDomScope::findCreate(domainp, scopep));
        resultp->m_pomWaitingE.pushBack(*m_pomWaitingp, resultp);
        return resultp;
    }
    virtual void freeVertexp(OrderMoveVertex* freeMep) override {
        freeMep->m_pomWaitingE.unlink(*m_pomWaitingp, freeMep);
        freeMep->unlinkDelete(m_pomGraphp);
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
    virtual MTaskMoveVertex* makeVertexp(OrderLogicVertex* lvertexp,
                                         const OrderEitherVertex* varVertexp,
                                         const AstScope* scopep,
                                         const AstSenTree* domainp) override {
        // Exclude initial/settle logic from the mtasks graph.
        // We'll output time-zero logic separately.
        if (domainp->hasInitial() || domainp->hasSettle()) return nullptr;
        return new MTaskMoveVertex(m_pomGraphp, lvertexp, varVertexp, scopep, domainp);
    }
    virtual void freeVertexp(MTaskMoveVertex* freeMep) override {
        freeMep->unlinkDelete(m_pomGraphp);
    }

private:
    VL_UNCOPYABLE(OrderMTaskMoveVertexMaker);
};

class OrderVerticesByDomainThenScope final {
    PartPtrIdMap m_ids;

public:
    virtual bool operator()(const V3GraphVertex* lhsp, const V3GraphVertex* rhsp) const {
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

class MTaskVxIdLessThan final {
public:
    MTaskVxIdLessThan() = default;
    virtual ~MTaskVxIdLessThan() = default;

    // Sort vertex's, which must be AbstractMTask's, into a deterministic
    // order by comparing their serial IDs.
    virtual bool operator()(const V3GraphVertex* lhsp, const V3GraphVertex* rhsp) const {
        const AbstractMTask* const lmtaskp = static_cast<const AbstractLogicMTask*>(lhsp);
        const AbstractMTask* const rmtaskp = static_cast<const AbstractLogicMTask*>(rhsp);
        return lmtaskp->id() < rmtaskp->id();
    }
};

//######################################################################
// OrderProcess class

class OrderProcess final : VNDeleter {
    // NODE STATE
    //  AstNode::user3  -> Used by loop reporting
    //  AstNode::user4  -> Used by V3Const::constifyExpensiveEdit
    const VNUser3InUse user3InUse;

    // STATE
    OrderGraph& m_graph;  // The ordering graph
    OrderInputsVertex& m_inputsVtx;  // The singleton OrderInputsVertex
    SenTreeFinder m_finder;  // Global AstSenTree manager
    AstSenTree* const m_comboDomainp;  // The combinational domain AstSenTree
    AstSenTree* const m_deleteDomainp;  // Dummy AstSenTree indicating needs deletion
    AstScope& m_scopetop;  // The top level AstScope

    AstCFunc* m_pomNewFuncp = nullptr;  // Current function being created
    int m_pomNewStmts = 0;  // Statements in function being created
    V3Graph m_pomGraph;  // Graph of logic elements to move
    V3List<OrderMoveVertex*> m_pomWaiting;  // List of nodes needing inputs to become ready
    friend class OrderMoveDomScope;
    V3List<OrderMoveDomScope*> m_pomReadyDomScope;  // List of ready domain/scope pairs, by loopId
    std::vector<OrderVarStdVertex*> m_unoptflatVars;  // Vector of variables in UNOPTFLAT loop
    std::map<std::pair<AstNodeModule*, std::string>, unsigned> m_funcNums;  // Function ordinals

    // STATS
    std::array<VDouble0, OrderVEdgeType::_ENUM_END> m_statCut;  // Count of each edge type cut

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    void process();
    void processCircular();
    using VertexVec = std::deque<OrderEitherVertex*>;
    void processInputs();
    void processInputsInIterate(OrderEitherVertex* vertexp, VertexVec& todoVec);
    void processInputsOutIterate(OrderEitherVertex* vertexp, VertexVec& todoVec);
    void processSensitive();
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
    enum InitialLogicE : uint8_t { LOGIC_INITIAL, LOGIC_SETTLE };
    void processMTasksInitial(InitialLogicE logic_type);

    string cfuncName(AstNodeModule* modp, AstSenTree* domainp, AstScope* scopep,
                     AstNode* forWhatp) {
        string name = domainp->hasCombo()     ? "_combo"
                      : domainp->hasInitial() ? "_initial"
                      : domainp->hasSettle()  ? "_settle"
                      : domainp->isMulti()    ? "_multiclk"
                                              : "_sequent";
        name = name + "__" + scopep->nameDotless();
        const unsigned funcnum = m_funcNums.emplace(std::make_pair(modp, name), 0).first->second++;
        name = name + "__" + cvtToStr(funcnum);
        if (v3Global.opt.profCFuncs()) {
            name += "__PROF__" + forWhatp->fileline()->profileFuncname();
        }
        return name;
    }

    bool nodeIsInitial(const OrderLogicVertex* LVtxp) {
        return LVtxp && (VN_IS(LVtxp->nodep(), Initial) || VN_IS(LVtxp->nodep(), InitialStatic));
    }

    void nodeMarkCircular(OrderVarVertex* vertexp, OrderEdge* edgep) {
        // To be marked circular requires being a clock assigned in a delayed assignment, or
        // having a cutable in or out edge, none of which is true for the DPI export trigger.
        AstVarScope* const nodep = vertexp->varScp();
        UASSERT(nodep != v3Global.rootp()->dpiExportTriggerp(),
                "DPI export trigger should not be marked circular");
        const OrderLogicVertex* fromLVtxp = nullptr;
        const OrderLogicVertex* toLVtxp = nullptr;
        if (edgep) {
            fromLVtxp = dynamic_cast<OrderLogicVertex*>(edgep->fromp());
            toLVtxp = dynamic_cast<OrderLogicVertex*>(edgep->top());
        }
        //
        if (nodeIsInitial(fromLVtxp) || nodeIsInitial(toLVtxp)) {
            // IEEE does not specify ordering between initial blocks, so we
            // can do whatever we want. We especially do not want to
            // evaluate multiple times, so do not mark the edge circular
        } else {
            nodep->circular(true);
            ++m_statCut[vertexp->type()];
            if (edgep) ++m_statCut[edgep->type()];
            //
            if (vertexp->isClock()) {
                // Seems obvious; no warning yet
                // nodep->v3warn(GENCLK, "Signal unoptimizable: Generated clock:
                // "<<nodep->prettyNameQ());
            } else if (nodep->varp()->isSigPublic()) {
                nodep->v3warn(UNOPT,
                              "Signal unoptimizable: Feedback to public clock or circular logic: "
                                  << nodep->prettyNameQ());
                if (!nodep->fileline()->warnIsOff(V3ErrorCode::UNOPT)
                    && !nodep->fileline()->lastWarnWaived()) {
                    nodep->fileline()->modifyWarnOff(V3ErrorCode::UNOPT,
                                                     true);  // Complain just once
                    // Give the user an example.
                    const bool tempWeight = (edgep && edgep->weight() == 0);
                    // Else the below loop detect can't see the loop
                    if (tempWeight) edgep->weight(1);
                    // Calls OrderGraph::loopsVertexCb
                    m_graph.reportLoops(&OrderEdge::followComboConnected, vertexp);
                    if (tempWeight) edgep->weight(0);
                }
            } else {
                // We don't use UNOPT, as there are lots of V2 places where
                // it was needed, that aren't any more
                // First v3warn not inside warnIsOff so we can see the suppressions with --debug
                nodep->v3warn(UNOPTFLAT,
                              "Signal unoptimizable: Feedback to clock or circular logic: "
                                  << nodep->prettyNameQ());
                if (!nodep->fileline()->warnIsOff(V3ErrorCode::UNOPTFLAT)
                    && !nodep->fileline()->lastWarnWaived()) {
                    nodep->fileline()->modifyWarnOff(V3ErrorCode::UNOPTFLAT,
                                                     true);  // Complain just once
                    // Give the user an example.
                    const bool tempWeight = (edgep && edgep->weight() == 0);
                    // Else the below loop detect can't see the loop
                    if (tempWeight) edgep->weight(1);
                    // Calls OrderGraph::loopsVertexCb
                    m_graph.reportLoops(&OrderEdge::followComboConnected, vertexp);
                    if (tempWeight) edgep->weight(0);
                    if (v3Global.opt.reportUnoptflat()) {
                        // Report candidate variables for splitting
                        reportLoopVars(vertexp);
                        // Do a subgraph for the UNOPTFLAT loop
                        OrderGraph loopGraph;
                        m_graph.subtreeLoops(&OrderEdge::followComboConnected, vertexp,
                                             &loopGraph);
                        loopGraph.dumpDotFilePrefixedAlways("unoptflat");
                    }
                }
            }
        }
    }

    // Find all variables in an UNOPTFLAT loop
    //
    // Ignore vars that are 1-bit wide and don't worry about generated
    // variables (PRE and POST vars, __Vdly__, __Vcellin__ and __VCellout).
    // What remains are candidates for splitting to break loops.
    //
    // node->user3 is used to mark if we have done a particular variable.
    // vertex->user is used to mark if we have seen this vertex before.
    //
    // @todo We could be cleverer in the future and consider just
    //       the width that is generated/consumed.
    void reportLoopVars(OrderVarVertex* vertexp) {
        m_graph.userClearVertices();
        AstNode::user3ClearTree();
        m_unoptflatVars.clear();
        reportLoopVarsIterate(vertexp, vertexp->color());
        AstNode::user3ClearTree();
        m_graph.userClearVertices();
        // May be very large vector, so only report the "most important"
        // elements. Up to 10 of the widest
        std::cerr << V3Error::warnMore() << "... Widest candidate vars to split:\n";
        std::stable_sort(m_unoptflatVars.begin(), m_unoptflatVars.end(),
                         [](OrderVarStdVertex* vsv1p, OrderVarStdVertex* vsv2p) -> bool {
                             return vsv1p->varScp()->varp()->width()
                                    > vsv2p->varScp()->varp()->width();
                         });
        std::unordered_set<const AstVar*> canSplitList;
        int lim = m_unoptflatVars.size() < 10 ? m_unoptflatVars.size() : 10;
        for (int i = 0; i < lim; i++) {
            OrderVarStdVertex* const vsvertexp = m_unoptflatVars[i];
            AstVar* const varp = vsvertexp->varScp()->varp();
            const bool canSplit = V3SplitVar::canSplitVar(varp);
            std::cerr << V3Error::warnMore() << "    " << varp->fileline() << " "
                      << varp->prettyName() << std::dec << ", width " << varp->width()
                      << ", fanout " << vsvertexp->fanout();
            if (canSplit) {
                std::cerr << ", can split_var";
                canSplitList.insert(varp);
            }
            std::cerr << '\n';
        }
        // Up to 10 of the most fanned out
        std::cerr << V3Error::warnMore() << "... Most fanned out candidate vars to split:\n";
        std::stable_sort(m_unoptflatVars.begin(), m_unoptflatVars.end(),
                         [](OrderVarStdVertex* vsv1p, OrderVarStdVertex* vsv2p) -> bool {
                             return vsv1p->fanout() > vsv2p->fanout();
                         });
        lim = m_unoptflatVars.size() < 10 ? m_unoptflatVars.size() : 10;
        for (int i = 0; i < lim; i++) {
            OrderVarStdVertex* const vsvertexp = m_unoptflatVars[i];
            AstVar* const varp = vsvertexp->varScp()->varp();
            const bool canSplit = V3SplitVar::canSplitVar(varp);
            std::cerr << V3Error::warnMore() << "    " << varp->fileline() << " "
                      << varp->prettyName() << ", width " << std::dec << varp->width()
                      << ", fanout " << vsvertexp->fanout();
            if (canSplit) {
                std::cerr << ", can split_var";
                canSplitList.insert(varp);
            }
            std::cerr << '\n';
        }
        if (!canSplitList.empty()) {
            std::cerr << V3Error::warnMore()
                      << "... Suggest add /*verilator split_var*/ to appropriate variables above."
                      << std::endl;
        }
        V3Stats::addStat("Order, SplitVar, candidates", canSplitList.size());
        m_unoptflatVars.clear();
    }

    void reportLoopVarsIterate(V3GraphVertex* vertexp, uint32_t color) {
        if (vertexp->user()) return;  // Already done
        vertexp->user(1);
        if (OrderVarStdVertex* const vsvertexp = dynamic_cast<OrderVarStdVertex*>(vertexp)) {
            // Only reporting on standard variable vertices
            AstVar* const varp = vsvertexp->varScp()->varp();
            if (!varp->user3()) {
                const string name = varp->prettyName();
                if ((varp->width() != 1) && (name.find("__Vdly") == string::npos)
                    && (name.find("__Vcell") == string::npos)) {
                    // Variable to report on and not yet done
                    m_unoptflatVars.push_back(vsvertexp);
                }
                varp->user3Inc();
            }
        }
        // Iterate through all the to and from vertices of the same color
        for (V3GraphEdge* edgep = vertexp->outBeginp(); edgep; edgep = edgep->outNextp()) {
            if (edgep->top()->color() == color) reportLoopVarsIterate(edgep->top(), color);
        }
        for (V3GraphEdge* edgep = vertexp->inBeginp(); edgep; edgep = edgep->inNextp()) {
            if (edgep->fromp()->color() == color) reportLoopVarsIterate(edgep->fromp(), color);
        }
    }

    // Only for member initialization in constructor
    static OrderInputsVertex& findInputVertex(OrderGraph& graph) {
        for (V3GraphVertex* vtxp = graph.verticesBeginp(); vtxp; vtxp = vtxp->verticesNextp()) {
            if (auto* const ivtxp = dynamic_cast<OrderInputsVertex*>(vtxp)) return *ivtxp;
        }
        VL_UNREACHABLE
    }

    // Only for member initialization in constructor
    static AstSenTree* makeDeleteDomainSenTree(FileLine* fl) {
        // TODO: Using "Never" instead of "Settle" causes a test failure, it probably shouldn't ...
        return new AstSenTree{fl, new AstSenItem{fl, AstSenItem::Settle{}}};
    }

    // CONSTRUCTOR
    OrderProcess(AstNetlist* netlistp, OrderGraph& graph)
        : m_graph{graph}
        , m_inputsVtx{findInputVertex(graph)}
        , m_finder{netlistp}
        , m_comboDomainp{m_finder.getComb()}
        , m_deleteDomainp{makeDeleteDomainSenTree(netlistp->fileline())}
        , m_scopetop{*netlistp->topScopep()->scopep()} {
        pushDeletep(m_deleteDomainp);
    }

    ~OrderProcess() override {
        // Stats
        for (int type = 0; type < OrderVEdgeType::_ENUM_END; type++) {
            const double count = double(m_statCut[type]);
            if (count != 0.0) {
                V3Stats::addStat(string("Order, cut, ") + OrderVEdgeType(type).ascii(), count);
            }
        }
    }

public:
    // Order the logic
    static void main(AstNetlist* netlistp, OrderGraph& graph) {
        OrderProcess{netlistp, graph}.process();
    }
};

//######################################################################
// OrderMoveDomScope methods

// Check the domScope is on ready list, add if not
inline void OrderMoveDomScope::ready(OrderProcess* opp) {
    if (!m_onReadyList) {
        m_onReadyList = true;
        m_readyDomScopeE.pushBack(opp->m_pomReadyDomScope, this);
    }
}

// Mark one vertex as finished, remove from ready list if done
inline void OrderMoveDomScope::movedVertex(OrderProcess* opp, OrderMoveVertex* vertexp) {
    UASSERT_OBJ(m_onReadyList, vertexp,
                "Moving vertex from ready when nothing was on que as ready.");
    if (m_readyVertices.empty()) {  // Else more work to get to later
        m_onReadyList = false;
        m_readyDomScopeE.unlink(opp->m_pomReadyDomScope, this);
    }
}

//######################################################################
// OrderProcess methods

void OrderProcess::processInputs() {
    m_graph.userClearVertices();  // Vertex::user()   // 1 if input recursed, 2 if marked as input,
                                  // 3 if out-edges recursed
    // Start at input vertex, process from input-to-output order
    VertexVec todoVec;  // List of newly-input marked vectors we need to process
    todoVec.push_front(&m_inputsVtx);
    m_inputsVtx.isFromInput(true);  // By definition
    while (!todoVec.empty()) {
        OrderEitherVertex* const vertexp = todoVec.back();
        todoVec.pop_back();
        processInputsOutIterate(vertexp, todoVec);
    }
}

void OrderProcess::processInputsInIterate(OrderEitherVertex* vertexp, VertexVec& todoVec) {
    // Propagate PrimaryIn through simple assignments
    if (vertexp->user()) return;  // Already processed
    if (false && debug() >= 9) {
        UINFO(9, " InIIter " << vertexp << endl);
        if (OrderLogicVertex* const vvertexp = dynamic_cast<OrderLogicVertex*>(vertexp)) {
            vvertexp->nodep()->dumpTree(cout, "-            TT: ");
        }
    }
    vertexp->user(1);  // Processing
    // First handle all inputs to this vertex, in most cases they'll be already processed earlier
    // Also, determine if this vertex is an input
    int inonly = 1;  // 0=no, 1=maybe, 2=yes until a no
    for (V3GraphEdge* edgep = vertexp->inBeginp(); edgep; edgep = edgep->inNextp()) {
        OrderEitherVertex* const frVertexp = static_cast<OrderEitherVertex*>(edgep->fromp());
        processInputsInIterate(frVertexp, todoVec);
        if (frVertexp->isFromInput()) {
            if (inonly == 1) inonly = 2;
        } else if (dynamic_cast<OrderVarPostVertex*>(frVertexp)) {
            // Ignore post assignments, just for ordering
        } else {
            // UINFO(9, "    InItStopDueTo " << frVertexp << endl);
            inonly = 0;
            break;
        }
    }

    if (inonly == 2
        && vertexp->user() < 2) {  // Set it.  Note may have already been set earlier, too
        UINFO(9, "   Input reassignment: " << vertexp << endl);
        vertexp->isFromInput(true);
        vertexp->user(2);  // 2 means on list
        // Can't work on out-edges of a node we know is an input immediately,
        // as it might visit other nodes before their input state is resolved.
        // So push to list and work on it later when all in-edges known resolved
        todoVec.push_back(vertexp);
    }
    // UINFO(9, "  InIdone " << vertexp << endl);
}

void OrderProcess::processInputsOutIterate(OrderEitherVertex* vertexp, VertexVec& todoVec) {
    if (vertexp->user() == 3) return;  // Already out processed
    // UINFO(9, " InOIter " << vertexp << endl);
    // First make sure input path is fully recursed
    processInputsInIterate(vertexp, todoVec);
    // Propagate PrimaryIn through simple assignments
    UASSERT_OBJ(vertexp->isFromInput(), vertexp,
                "processInputsOutIterate only for input marked vertexes");
    vertexp->user(3);  // out-edges processed

    {
        // Propagate PrimaryIn through simple assignments, following target of vertex
        for (V3GraphEdge* edgep = vertexp->outBeginp(); edgep; edgep = edgep->outNextp()) {
            OrderEitherVertex* const toVertexp = static_cast<OrderEitherVertex*>(edgep->top());
            if (OrderVarStdVertex* const vvertexp = dynamic_cast<OrderVarStdVertex*>(toVertexp)) {
                processInputsInIterate(vvertexp, todoVec);
            }
            if (OrderLogicVertex* const vvertexp = dynamic_cast<OrderLogicVertex*>(toVertexp)) {
                if (VN_IS(vvertexp->nodep(), NodeAssign)) {
                    processInputsInIterate(vvertexp, todoVec);
                }
            }
        }
    }
}

//######################################################################
// OrderVisitor - Circular detection

void OrderProcess::processCircular() {
    // Take broken edges and add circular flags
    // The change detect code will use this to force changedets
    for (V3GraphVertex* itp = m_graph.verticesBeginp(); itp; itp = itp->verticesNextp()) {
        if (OrderVarStdVertex* const vvertexp = dynamic_cast<OrderVarStdVertex*>(itp)) {
            if (vvertexp->isClock() && !vvertexp->isFromInput()) {
                // If a clock is generated internally, we need to do another
                // loop through the entire evaluation.  This fixes races; see
                // t_clk_dpulse test.
                //
                // This all seems to hinge on how the clock is generated. If
                // it is generated by delayed assignment, we need the loop. If
                // it is combinatorial, we do not (and indeed it will break
                // other tests such as t_gated_clk_1.
                if (!v3Global.opt.orderClockDly()) {
                    UINFO(5, "Circular Clock, no-order-clock-delay " << vvertexp << endl);
                    nodeMarkCircular(vvertexp, nullptr);
                } else if (vvertexp->isDelayed()) {
                    UINFO(5, "Circular Clock, delayed " << vvertexp << endl);
                    nodeMarkCircular(vvertexp, nullptr);
                } else {
                    UINFO(5, "Circular Clock, not delayed " << vvertexp << endl);
                }
            }
            // Also mark any cut edges
            for (V3GraphEdge* edgep = vvertexp->outBeginp(); edgep; edgep = edgep->outNextp()) {
                if (edgep->weight() == 0) {  // was cut
                    OrderEdge* const oedgep = dynamic_cast<OrderEdge*>(edgep);
                    UASSERT_OBJ(oedgep, vvertexp->varScp(), "Cutable edge not of proper type");
                    UINFO(6, "      CutCircularO: " << vvertexp->name() << endl);
                    nodeMarkCircular(vvertexp, oedgep);
                }
            }
            for (V3GraphEdge* edgep = vvertexp->inBeginp(); edgep; edgep = edgep->inNextp()) {
                if (edgep->weight() == 0) {  // was cut
                    OrderEdge* const oedgep = dynamic_cast<OrderEdge*>(edgep);
                    UASSERT_OBJ(oedgep, vvertexp->varScp(), "Cutable edge not of proper type");
                    UINFO(6, "      CutCircularI: " << vvertexp->name() << endl);
                    nodeMarkCircular(vvertexp, oedgep);
                }
            }
        }
    }
}

void OrderProcess::processSensitive() {
    // Sc sensitives are required on all inputs that go to a combo
    // block.  (Not inputs that go only to clocked blocks.)
    for (V3GraphVertex* itp = m_graph.verticesBeginp(); itp; itp = itp->verticesNextp()) {
        if (OrderVarStdVertex* const vvertexp = dynamic_cast<OrderVarStdVertex*>(itp)) {
            if (vvertexp->varScp()->varp()->isNonOutput()) {
                // UINFO(0, "  scsen " << vvertexp << endl);
                for (V3GraphEdge* edgep = vvertexp->outBeginp(); edgep;
                     edgep = edgep->outNextp()) {
                    if (OrderEitherVertex* const toVertexp
                        = dynamic_cast<OrderEitherVertex*>(edgep->top())) {
                        if (edgep->weight() && toVertexp->domainp()) {
                            // UINFO(0, "      " << toVertexp->domainp() << endl);
                            if (toVertexp->domainp()->hasCombo()) {
                                vvertexp->varScp()->varp()->scSensitive(true);
                            }
                        }
                    }
                }
            }
        }
    }
}

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
    OrderVarVertex* const vvertexp = dynamic_cast<OrderVarVertex*>(vertexp);
    AstSenTree* domainp = nullptr;
    if (vvertexp && vvertexp->varScp()->varp()->isNonOutput()) domainp = m_comboDomainp;
    if (vvertexp && vvertexp->varScp()->isCircular()) domainp = m_comboDomainp;
    if (!domainp) {
        for (V3GraphEdge* edgep = vertexp->inBeginp(); edgep; edgep = edgep->inNextp()) {
            OrderEitherVertex* const fromVertexp = static_cast<OrderEitherVertex*>(edgep->fromp());
            if (edgep->weight() && fromVertexp->domainMatters()) {
                UINFO(9, "     from d=" << cvtToHex(fromVertexp->domainp()) << " " << fromVertexp
                                        << endl);
                if (!domainp  // First input to this vertex
                    || domainp->hasSettle()  // or, we can ignore being in the settle domain
                    || domainp->hasInitial()) {
                    domainp = fromVertexp->domainp();
                } else if (domainp->hasCombo()) {
                    // Once in combo, keep in combo; already as severe as we can get
                } else if (fromVertexp->domainp()->hasCombo()) {
                    // Any combo input means this vertex must remain combo
                    domainp = m_comboDomainp;
                } else if (fromVertexp->domainp()->hasSettle()
                           || fromVertexp->domainp()->hasInitial()) {
                    // Ignore that we have a constant (initial) input
                } else if (domainp != fromVertexp->domainp()) {
                    // Make a domain that merges the two domains
                    const bool ddebug = debug() >= 9;

                    if (ddebug) {  // LCOV_EXCL_START

                        cout << endl;
                        UINFO(0, "      conflicting domain " << fromVertexp << endl);
                        UINFO(0, "         dorig=" << domainp << endl);
                        domainp->dumpTree(cout);
                        UINFO(0, "         d2   =" << fromVertexp->domainp() << endl);
                        fromVertexp->domainp()->dumpTree(cout);
                    }  // LCOV_EXCL_STOP
                    AstSenTree* const newtreep = domainp->cloneTree(false);
                    AstSenItem* newtree2p = fromVertexp->domainp()->sensesp()->cloneTree(true);
                    UASSERT_OBJ(newtree2p, fromVertexp->domainp(),
                                "No senitem found under clocked domain");
                    newtreep->addSensesp(newtree2p);
                    newtree2p = nullptr;  // Below edit may replace it
                    V3Const::constifyExpensiveEdit(newtreep);  // Remove duplicates
                    newtreep->multi(true);  // Comment that it was made from 2 clock domains
                    domainp = m_finder.getSenTree(newtreep);
                    if (ddebug) {  // LCOV_EXCL_START
                        UINFO(0, "         dnew =" << newtreep << endl);
                        newtreep->dumpTree(cout);
                        UINFO(0, "         find =" << domainp << endl);
                        domainp->dumpTree(cout);
                        cout << endl;
                    }  // LCOV_EXCL_STOP
                    VL_DO_DANGLING(newtreep->deleteTree(), newtreep);
                }
            }
        }  // next input edgep
        // Default the domain
        // This is a node which has only constant inputs, or is otherwise indeterminate.
        // It should have already been copied into the settle domain.  Presumably it has
        // inputs which we never trigger, or nothing it's sensitive to, so we can rip it out.
        if (!domainp && vertexp->scopep()) domainp = m_deleteDomainp;
        // However, anything that is public RW must be added to the combo domain since the
        // user may change it at any time
        if (domainp && vvertexp && vvertexp->varScp()->varp()->isSigUserRWPublic())
            domainp = m_comboDomainp;
    }
    //
    vertexp->domainp(domainp);
    if (vertexp->domainp()) {
        UINFO(5, "      done d=" << cvtToHex(vertexp->domainp())
                                 << (vertexp->domainp() == m_deleteDomainp ? " [DEL]" : "")
                                 << (vertexp->domainp()->hasClocked() ? " [CLKD]" : "")
                                 << (vertexp->domainp()->hasSettle() ? " [SETL]" : "")
                                 << (vertexp->domainp()->hasInitial() ? " [INIT]" : "")
                                 << (vertexp->domainp()->hasCombo() ? " [COMB]" : "")
                                 << (vertexp->domainp()->isMulti() ? " [MULT]" : "") << " "
                                 << vertexp << endl);
    }
}

//######################################################################
// OrderVisitor - Move graph construction

void OrderProcess::processEdgeReport() {
    // Make report of all signal names and what clock edges they have
    const string filename = v3Global.debugFilename("order_edges.txt");
    const std::unique_ptr<std::ofstream> logp{V3File::new_ofstream(filename)};
    if (logp->fail()) v3fatal("Can't write " << filename);
    // Testing emitter: V3EmitV::verilogForTree(v3Global.rootp(), *logp);

    std::deque<string> report;

    for (V3GraphVertex* itp = m_graph.verticesBeginp(); itp; itp = itp->verticesNextp()) {
        if (OrderVarVertex* const vvertexp = dynamic_cast<OrderVarVertex*>(itp)) {
            string name(vvertexp->varScp()->prettyName());
            if (dynamic_cast<OrderVarPreVertex*>(itp)) {
                name += " {PRE}";
            } else if (dynamic_cast<OrderVarPostVertex*>(itp)) {
                name += " {POST}";
            } else if (dynamic_cast<OrderVarPordVertex*>(itp)) {
                name += " {PORD}";
            }
            std::ostringstream os;
            os.setf(std::ios::left);
            os << "  " << cvtToHex(vvertexp->varScp()) << " " << std::setw(50) << name << " ";
            AstSenTree* const sentreep = vvertexp->domainp();
            if (sentreep) V3EmitV::verilogForTree(sentreep, os);
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
    ProcessMoveBuildGraph<OrderMoveVertex> serialPMBG(&m_graph, &m_pomGraph,
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
    if (newActivep) m_scopetop.addActivep(newActivep);
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
    if (VN_IS(nodep, SenTree)) {
        // Just ignore sensitivities, we'll deal with them when we move statements that need them
    } else {  // Normal logic
        // Move the logic into a CFunc
        nodep->unlinkFrBack();

        // Process procedures per statement (unless profCFuncs), so we can split CFuncs within
        // procedures. Everything else is handled in one go
        AstNodeProcedure* const procp = VN_CAST(nodep, NodeProcedure);
        if (procp && !v3Global.opt.profCFuncs()) {
            nodep = procp->bodysp();
            pushDeletep(procp);
        }

        while (nodep) {
            // Make or borrow a CFunc to contain the new statements
            if (v3Global.opt.profCFuncs()
                || (v3Global.opt.outputSplitCFuncs()
                    && v3Global.opt.outputSplitCFuncs() < newStmtsr)) {
                // Put every statement into a unique function to ease profiling or reduce function
                // size
                newFuncpr = nullptr;
            }
            if (!newFuncpr && domainp != m_deleteDomainp) {
                const string name = cfuncName(modp, domainp, scopep, nodep);
                newFuncpr = new AstCFunc(nodep->fileline(), name, scopep);
                newFuncpr->isStatic(false);
                newFuncpr->isLoose(true);
                newStmtsr = 0;
                if (domainp->hasInitial() || domainp->hasSettle()) newFuncpr->slow(true);
                scopep->addActivep(newFuncpr);
                // Create top call to it
                AstCCall* const callp = new AstCCall(nodep->fileline(), newFuncpr);
                // Where will we be adding the call?
                AstActive* const newActivep = new AstActive(nodep->fileline(), name, domainp);
                newActivep->addStmtsp(callp);
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
                UINFO(4, " Ordering deleting pre-settled " << nodep << endl);
                VL_DO_DANGLING(pushDeletep(nodep), nodep);
            } else {
                newFuncpr->addStmtsp(nodep);
                if (v3Global.opt.outputSplitCFuncs()) {
                    // Add in the number of nodes we're adding
                    newStmtsr += nodep->nodeCount();
                }
            }

            nodep = nextp;
        }
    }
    return activep;
}

void OrderProcess::processMTasksInitial(InitialLogicE logic_type) {
    // Emit initial/settle logic. Initial blocks won't be part of the
    // mtask partition, aren't eligible for parallelism.
    //
    int initStmts = 0;
    AstCFunc* initCFunc = nullptr;
    const AstScope* lastScopep = nullptr;
    for (V3GraphVertex* initVxp = m_graph.verticesBeginp(); initVxp;
         initVxp = initVxp->verticesNextp()) {
        OrderLogicVertex* const initp = dynamic_cast<OrderLogicVertex*>(initVxp);
        if (!initp) continue;
        if ((logic_type == LOGIC_INITIAL) && !initp->domainp()->hasInitial()) continue;
        if ((logic_type == LOGIC_SETTLE) && !initp->domainp()->hasSettle()) continue;
        if (initp->scopep() != lastScopep) {
            // Start new cfunc, don't let the cfunc cross scopes
            initCFunc = nullptr;
            lastScopep = initp->scopep();
        }
        AstActive* const newActivep
            = processMoveOneLogic(initp, initCFunc /*ref*/, initStmts /*ref*/);
        if (newActivep) m_scopetop.addActivep(newActivep);
    }
}

void OrderProcess::processMTasks() {
    // For nondeterminism debug:
    V3Partition::hashGraphDebug(&m_graph, "V3Order's m_graph");

    processMTasksInitial(LOGIC_INITIAL);
    processMTasksInitial(LOGIC_SETTLE);

    // We already produced a graph of every var, input, logic, and settle
    // block and all dependencies; this is 'm_graph'.
    //
    // Now, starting from m_graph, make a slightly-coarsened graph representing
    // only logic, and discarding edges we know we can ignore.
    // This is quite similar to the 'm_pomGraph' of the serial code gen:
    V3Graph logicGraph;
    OrderMTaskMoveVertexMaker create_mtask_vertex(&logicGraph);
    ProcessMoveBuildGraph<MTaskMoveVertex> mtask_pmbg(&m_graph, &logicGraph, &create_mtask_vertex);
    mtask_pmbg.build();

    // Needed? We do this for m_pomGraph in serial mode, so do it here too:
    logicGraph.removeRedundantEdges(&V3GraphEdge::followAlwaysTrue);

    // Partition logicGraph into LogicMTask's. The partitioner will annotate
    // each vertex in logicGraph with a 'color' which is really an mtask ID
    // in this context.
    V3Partition partitioner(&logicGraph);
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
        const unsigned mtaskId = movep->color();
        UASSERT(mtaskId > 0, "Every MTaskMoveVertex should have an mtask assignment >0");
        if (movep->logicp()) {
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
                AstVar* const varp = pre_varp->varScp()->varp();
                // varp depends on logicp, so logicp produces varp,
                // and vice-versa below
                varp->addProducingMTaskId(mtaskId);
            }
            for (const V3GraphEdge* edgep = logicp->outBeginp(); edgep;
                 edgep = edgep->outNextp()) {
                const OrderVarVertex* const post_varp
                    = dynamic_cast<const OrderVarVertex*>(edgep->top());
                if (!post_varp) continue;
                AstVar* const varp = post_varp->varScp()->varp();
                varp->addConsumingMTaskId(mtaskId);
            }
            // TODO? We ignore IO vars here, so those will have empty mtask
            // signatures. But we could also give those mtask signatures.
        }
    }

    // Create the AstExecGraph node which represents the execution
    // of the MTask graph.
    FileLine* const rootFlp = v3Global.rootp()->fileline();
    AstExecGraph* const execGraphp = new AstExecGraph{rootFlp, "eval"};
    m_scopetop.addActivep(execGraphp);

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
        execGraphp->addMTaskBodyp(bodyp);
    }
}

//######################################################################
// OrderVisitor - Top processing

void OrderProcess::process() {
    // Dump data
    m_graph.dumpDotFilePrefixed("orderg_pre");

    // Break cycles. Each strongly connected subgraph (including cutable
    // edges) will have its own color, and corresponds to a loop in the
    // original graph. However the new graph will be acyclic (the removed
    // edges are actually still there, just with weight 0).
    UINFO(2, "  Acyclic & Order...\n");
    m_graph.acyclic(&V3GraphEdge::followAlwaysTrue);
    m_graph.dumpDotFilePrefixed("orderg_acyc");

    // Assign ranks so we know what to follow
    // Then, sort vertices and edges by that ordering
    m_graph.order();
    m_graph.dumpDotFilePrefixed("orderg_order");

    // This finds everything that can be traced from an input (which by
    // definition are the source clocks). After this any vertex which was
    // traced has isFromInput() true.
    UINFO(2, "  Process Clocks...\n");
    processInputs();  // must be before processCircular

    UINFO(2, "  Process Circulars...\n");
    processCircular();  // must be before processDomains

    // Assign logic vertices to new domains
    UINFO(2, "  Domains...\n");
    processDomains();
    m_graph.dumpDotFilePrefixed("orderg_domain");

    if (debug() && v3Global.opt.dumpTree()) processEdgeReport();

    if (!v3Global.opt.mtasks()) {
        UINFO(2, "  Construct Move Graph...\n");
        processMoveBuildGraph();
        if (debug() >= 4) {
            m_pomGraph.dumpDotFilePrefixed(
                "ordermv_start");  // Different prefix (ordermv) as it's not the same graph
        }
        m_pomGraph.removeRedundantEdges(&V3GraphEdge::followAlwaysTrue);
        if (debug() >= 4) m_pomGraph.dumpDotFilePrefixed("ordermv_simpl");

        UINFO(2, "  Move...\n");
        processMove();
    } else {
        UINFO(2, "  Set up mtasks...\n");
        processMTasks();
    }

    // Any SC inputs feeding a combo domain must be marked, so we can make them sc_sensitive
    UINFO(2, "  Sensitive...\n");
    processSensitive();  // must be after processDomains

    // Dump data
    m_graph.dumpDotFilePrefixed("orderg_done");
    if (false && debug()) {
        const string dfilename
            = v3Global.opt.makeDir() + "/" + v3Global.opt.prefix() + "_INT_order";
        const std::unique_ptr<std::ofstream> logp{V3File::new_ofstream(dfilename)};
        if (logp->fail()) v3fatal("Can't write " << dfilename);
        m_graph.dump(*logp);
    }
}

//######################################################################
// Order class functions

void V3Order::orderAll(AstNetlist* netlistp) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    // Propagate 'clocker' attribute through logic
    OrderClkMarkVisitor::process(netlistp);
    // Build ordering graph
    std::unique_ptr<OrderGraph> orderGraph = OrderBuildVisitor::process(netlistp);
    // Order the netlist
    OrderProcess::main(netlistp, *orderGraph);
    // Reset debug level
    orderGraph->debug(V3Error::debugDefault());
    // Dump tree
    V3Global::dumpCheckGlobalTree("order", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}
