// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Block code ordering
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2020 by Wilson Snyder.  This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
//
// Verilator is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
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

#include "V3Ast.h"
#include "V3Const.h"
#include "V3EmitCBase.h"
#include "V3EmitV.h"
#include "V3File.h"
#include "V3Global.h"
#include "V3Graph.h"
#include "V3GraphStream.h"
#include "V3List.h"
#include "V3Partition.h"
#include "V3PartitionGraph.h"
#include "V3SenTree.h"
#include "V3Stats.h"

#include "V3Order.h"
#include "V3OrderGraph.h"

#include <algorithm>
#include <cstdarg>
#include <deque>
#include <iomanip>
#include <map>
#include <memory>
#include <sstream>
#include <vector>
#include VL_INCLUDE_UNORDERED_MAP
#include VL_INCLUDE_UNORDERED_SET

class OrderMoveDomScope;

static bool domainsExclusive(const AstSenTree* fromp, const AstSenTree* top);

//######################################################################
// Functions for above graph classes

void OrderGraph::loopsVertexCb(V3GraphVertex* vertexp) {
    if (debug()) cout<<"-Info-Loop: "<<vertexp<<" "<<endl;
    if (OrderLogicVertex* vvertexp = dynamic_cast<OrderLogicVertex*>(vertexp)) {
        std::cerr<<vvertexp->nodep()->fileline()->warnOther()
                 <<"     Example path: "
                 <<vvertexp->nodep()->typeName()<<endl;
    }
    if (OrderVarVertex* vvertexp = dynamic_cast<OrderVarVertex*>(vertexp)) {
        std::cerr<<vvertexp->varScp()->fileline()->warnOther()
                 <<"     Example path: "
                 <<vvertexp->varScp()->prettyName()<<endl;
    }
};

//######################################################################

class OrderMoveDomScope {
    // Information stored for each unique loop, domain & scope trifecta
public:
    V3ListEnt<OrderMoveDomScope*>       m_readyDomScopeE;// List of next ready dom scope
    V3List<OrderMoveVertex*>    m_readyVertices;        // Ready vertices with same domain & scope
private:
    bool                        m_onReadyList;          // True if DomScope is already on list of ready dom/scopes
    const AstSenTree*           m_domainp;              // Domain all vertices belong to
    const AstScope*             m_scopep;               // Scope all vertices belong to

    typedef std::pair<const AstSenTree*, const AstScope*> DomScopeKey;
    typedef std::map<DomScopeKey, OrderMoveDomScope*> DomScopeMap;
    static DomScopeMap  s_dsMap;        // Structure registered for each dom/scope pairing

public:
    OrderMoveDomScope(const AstSenTree* domainp, const AstScope* scopep)
        : m_onReadyList(false), m_domainp(domainp), m_scopep(scopep) {}
    OrderMoveDomScope* readyDomScopeNextp() const { return m_readyDomScopeE.nextp(); }
    const AstSenTree* domainp() const { return m_domainp; }
    const AstScope* scopep() const { return m_scopep; }
    void ready(OrderVisitor* ovp);  // Check the domScope is on ready list, add if not
    void movedVertex(OrderVisitor* ovp, OrderMoveVertex* vertexp);  // Mark one vertex as finished, remove from ready list if done
    // STATIC MEMBERS (for lookup)
    static void clear() {
        for (DomScopeMap::iterator it=s_dsMap.begin(); it!=s_dsMap.end(); ++it) {
            delete it->second;
        }
        s_dsMap.clear();
    }
    V3List<OrderMoveVertex*>& readyVertices() { return m_readyVertices; }
    static OrderMoveDomScope* findCreate(const AstSenTree* domainp,
                                         const AstScope* scopep) {
        const DomScopeKey key = make_pair(domainp, scopep);
        DomScopeMap::iterator iter = s_dsMap.find(key);
        if (iter != s_dsMap.end()) {
            return iter->second;
        } else {
            OrderMoveDomScope* domScopep = new OrderMoveDomScope(domainp, scopep);
            s_dsMap.insert(make_pair(key, domScopep));
            return domScopep;
        }
    }
    string name() const {
        return (string("MDS:")
                +" d="+cvtToHex(domainp())
                +" s="+cvtToHex(scopep()));
    }
};

OrderMoveDomScope::DomScopeMap  OrderMoveDomScope::s_dsMap;

inline std::ostream& operator<< (std::ostream& lhs, const OrderMoveDomScope& rhs) {
    lhs<<rhs.name();
    return lhs;
}

//######################################################################
// Order information stored under each AstNode::user1p()...

// Types of vertex we can create
enum WhichVertex { WV_STD, WV_PRE, WV_PORD, WV_POST, WV_SETL,
                   WV_MAX};

class OrderUser {
    // Stored in AstVarScope::user1p, a list of all the various vertices
    // that can exist for one given variable
private:
    OrderVarVertex*     m_vertexp[WV_MAX];      // Vertex of each type (if non NULL)
public:
    // METHODS
    OrderVarVertex* newVarUserVertex(V3Graph* graphp, AstScope* scopep,
                                     AstVarScope* varscp, WhichVertex type, bool* createdp=NULL) {
        UASSERT_OBJ(type < WV_MAX, varscp, "Bad case");
        OrderVarVertex* vertexp = m_vertexp[type];
        if (!vertexp) {
            UINFO(6,"New vertex "<<varscp<<endl);
            if (createdp) *createdp = true;
            switch (type) {
            case WV_STD:  vertexp = new OrderVarStdVertex   (graphp, scopep, varscp); break;
            case WV_PRE:  vertexp = new OrderVarPreVertex   (graphp, scopep, varscp); break;
            case WV_PORD: vertexp = new OrderVarPordVertex  (graphp, scopep, varscp); break;
            case WV_POST: vertexp = new OrderVarPostVertex  (graphp, scopep, varscp); break;
            case WV_SETL: vertexp = new OrderVarSettleVertex(graphp, scopep, varscp); break;
            default: varscp->v3fatalSrc("Bad case");
            }
            m_vertexp[type] = vertexp;
        } else {
            if (createdp) *createdp = false;
        }
        return vertexp;
    }

public:
    // CONSTRUCTORS
    OrderUser() {
        for (int i=0; i<WV_MAX; i++) m_vertexp[i] = NULL;
    }
    ~OrderUser() {}
};


//######################################################################
// Comparator classes

//! Comparator for width of associated variable
struct OrderVarWidthCmp {
    bool operator() (OrderVarStdVertex* vsv1p, OrderVarStdVertex* vsv2p) {
        return vsv1p->varScp()->varp()->width()
            > vsv2p->varScp()->varp()->width();
    }
};

//! Comparator for fanout of vertex
struct OrderVarFanoutCmp {
    bool operator() (OrderVarStdVertex* vsv1p, OrderVarStdVertex* vsv2p) {
        return vsv1p->fanout() > vsv2p->fanout();
    }
};

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
class OrderClkMarkVisitor : public AstNVisitor {
private:
    bool m_hasClk;              // flag indicating whether there is clock signal on rhs
    bool m_inClocked;           // Currently inside a sequential block
    bool m_newClkMarked;        // Flag for deciding whether a new run is needed
    bool m_inAss;               // Currently inside of a assignment
    int  m_childClkWidth;       // If in hasClk, width of clock signal in child
    int  m_rightClkWidth;       // Clk width on the RHS

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    virtual void visit(AstNodeAssign* nodep) {
        m_hasClk = false;
        if (AstVarRef* varrefp = VN_CAST(nodep->rhsp(), VarRef)) {
            this->visit(varrefp);
            m_rightClkWidth = varrefp->width();
            if (varrefp->varp()->attrClocker() == VVarAttrClocker::CLOCKER_YES) {
                if (m_inClocked) {
                    varrefp->v3warn(CLKDATA, "Clock used as data (on rhs of assignment) in sequential block "
                                    <<varrefp->prettyNameQ()<<endl);
                } else {
                    m_hasClk = true;
                    UINFO(5, "node is already marked as clocker "<<varrefp<<endl);
                }
            }
        } else {
            m_inAss = true;
            m_childClkWidth = 0;
            iterateAndNextNull(nodep->rhsp());
            m_rightClkWidth = m_childClkWidth;
            m_inAss = false;
        }

        // do the marking
        if (m_hasClk) {
            if (nodep->lhsp()->width() > m_rightClkWidth) {
                nodep->v3warn(CLKDATA, "Clock is assigned to part of data signal "
                              <<nodep->lhsp()<<endl);
                UINFO(4, "CLKDATA: lhs with width " << nodep->lhsp()->width() <<endl);
                UINFO(4, "     but rhs clock with width " << m_rightClkWidth <<endl);
                return;  // skip the marking
            }

            const AstVarRef* lhsp = VN_CAST(nodep->lhsp(), VarRef);
            if (lhsp && (lhsp->varp()->attrClocker() == VVarAttrClocker::CLOCKER_UNKNOWN)) {
                lhsp->varp()->attrClocker(VVarAttrClocker::CLOCKER_YES);  // mark as clocker
                m_newClkMarked = true;  // enable a further run since new clocker is marked
                UINFO(5, "node is newly marked as clocker by assignment "<<lhsp<<endl);
            }
        }
    }

    virtual void visit(AstVarRef* nodep) {
        if (m_inAss && nodep->varp()->attrClocker() == VVarAttrClocker::CLOCKER_YES) {
            if (m_inClocked) {
                nodep->v3warn(CLKDATA,
                              "Clock used as data (on rhs of assignment) in sequential block "
                              <<nodep->prettyNameQ());
            } else {
                m_hasClk = true;
                m_childClkWidth = nodep->width();  // Pass up
                UINFO(5, "node is already marked as clocker "<<nodep<<endl);
            }
        }
    }
    virtual void visit(AstConcat* nodep) {
        if (m_inAss) {
            iterateAndNextNull(nodep->lhsp());
            int lw = m_childClkWidth;
            iterateAndNextNull(nodep->rhsp());
            int rw = m_childClkWidth;
            m_childClkWidth = lw + rw;  // Pass up
        }
    }
    virtual void visit(AstNodeSel* nodep) {
        if (m_inAss) {
            iterateChildren(nodep);
            // Pass up result width
            if (m_childClkWidth > nodep->width()) m_childClkWidth = nodep->width();
        }
    }
    virtual void visit(AstSel* nodep) {
        if (m_inAss) {
            iterateChildren(nodep);
            if (m_childClkWidth > nodep->width()) m_childClkWidth = nodep->width();
        }
    }
    virtual void visit(AstReplicate* nodep) {
        if (m_inAss) {
            iterateChildren(nodep);
            if (VN_IS(nodep->rhsp(), Const)) {
                m_childClkWidth = m_childClkWidth * VN_CAST(nodep->rhsp(), Const)->toUInt();
            } else {
                m_childClkWidth = nodep->width();  // can not check in this case.
            }
        }
    }
    virtual void visit(AstActive* nodep) {
        m_inClocked = nodep->hasClocked();
        iterateChildren(nodep);
        m_inClocked = false;
    }
    virtual void visit(AstNode* nodep) {
        iterateChildren(nodep);
    }

public:
    // CONSTRUCTORS
    explicit OrderClkMarkVisitor(AstNode* nodep) {
        m_hasClk    = false;
        m_inClocked = false;
        m_inAss     = false;
        m_childClkWidth = 0;
        m_rightClkWidth = 0;
        do {
            m_newClkMarked = false;
            iterate(nodep);
        } while (m_newClkMarked);
    }
    virtual ~OrderClkMarkVisitor() {}
};

//######################################################################
// The class checks if the assignment generates a clock.

class OrderClkAssVisitor : public AstNVisitor {
private:
    bool m_clkAss;  // There is signals marked as clocker in the assignment
    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()
    virtual void visit(AstNodeAssign* nodep) {
        if (const AstVarRef* varrefp = VN_CAST(nodep->lhsp(), VarRef)) {
            if (varrefp->varp()->attrClocker() == VVarAttrClocker::CLOCKER_YES) {
                m_clkAss = true;
                UINFO(6, "node was marked as clocker "<<varrefp<<endl);
            }
        }
        iterateChildren(nodep->rhsp());
    }
    virtual void visit(AstVarRef* nodep) {
        // Previous versions checked attrClocker() here, but this breaks
        // the updated t_clocker VCD test.
        // If reenable this visitor note AstNodeMath short circuit below
    }
    virtual void visit(AstNodeMath* nodep) {}  // Accelerate
    virtual void visit(AstNode* nodep) {
        iterateChildren(nodep);
    }
public:
    // CONSTRUCTORS
    explicit OrderClkAssVisitor(AstNode* nodep) {
        m_clkAss = false;
        iterate(nodep);
    }
    virtual ~OrderClkAssVisitor() {}
    // METHODS
    bool isClkAss() { return m_clkAss; }
};

//######################################################################
// ProcessMoveBuildGraph

template <class T_MoveVertex>
class ProcessMoveBuildGraph {
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
    typedef std::pair<const V3GraphVertex*, const AstSenTree*> VxDomPair;
    // Maps an (original graph vertex, domain) pair to a T_MoveVertex
    // Not vl_unordered_map, because std::pair doesn't provide std::hash
    typedef std::map<VxDomPair, T_MoveVertex*> Var2Move;
    typedef vl_unordered_map<const OrderLogicVertex*, T_MoveVertex*> Logic2Move;

public:
    class MoveVertexMaker {
    public:
        // Clients of ProcessMoveBuildGraph must supply MoveVertexMaker
        // which creates new T_MoveVertex's. Each new vertex wraps lvertexp
        // (which may be NULL.)
        virtual T_MoveVertex* makeVertexp(OrderLogicVertex* lvertexp,
                                          const OrderEitherVertex* varVertexp,
                                          const AstScope* scopep,
                                          const AstSenTree* domainp) = 0;
        virtual void freeVertexp(T_MoveVertex* freeMep) = 0;
    };

private:
    // MEMBERS
    const V3Graph*   m_graphp;          // Input graph of OrderLogicVertex's etc
    V3Graph*         m_outGraphp;       // Output graph of T_MoveVertex's
    MoveVertexMaker* m_vxMakerp;        // Factory class for T_MoveVertex's
    Logic2Move       m_logic2move;      // Map Logic to Vertex
    Var2Move         m_var2move;        // Map Vars to Vertex

public:
    // CONSTRUCTORS
    ProcessMoveBuildGraph(const V3Graph* logicGraphp,  // Input graph of OrderLogicVertex etc.
                          V3Graph* outGraphp,  // Output graph of T_MoveVertex's
                          MoveVertexMaker* vxMakerp)
        : m_graphp(logicGraphp),
          m_outGraphp(outGraphp),
          m_vxMakerp(vxMakerp) {}
    virtual ~ProcessMoveBuildGraph() {}

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
        for (V3GraphVertex* itp = m_graphp->verticesBeginp(); itp;
             itp=itp->verticesNextp()) {
            if (OrderLogicVertex* lvertexp = dynamic_cast<OrderLogicVertex*>(itp)) {
                T_MoveVertex* moveVxp =
                    m_vxMakerp->makeVertexp(lvertexp, NULL, lvertexp->scopep(),
                                            lvertexp->domainp());
                if (moveVxp) {
                    // Cross link so we can find it later
                    m_logic2move[lvertexp] = moveVxp;
                }
            }
        }
        // Build edges between logic vertices
        for (V3GraphVertex* itp = m_graphp->verticesBeginp(); itp;
             itp=itp->verticesNextp()) {
            if (OrderLogicVertex* lvertexp = dynamic_cast<OrderLogicVertex*>(itp)) {
                T_MoveVertex* moveVxp = m_logic2move[lvertexp];
                if (moveVxp) {
                    iterate(moveVxp, lvertexp, lvertexp->domainp());
                }
            }
        }
    }

private:
    // Return true if moveVxp has downstream dependencies
    bool iterate(T_MoveVertex* moveVxp, const V3GraphVertex* origVxp,
                 const AstSenTree* domainp) {
        bool madeDeps = false;
        // Search forward from given original vertex, making new edges from
        // moveVxp forward
        for (V3GraphEdge* edgep = origVxp->outBeginp(); edgep; edgep=edgep->outNextp()) {
            if (edgep->weight()==0) {  // Was cut
                continue;
            }
            int weight = edgep->weight();
            if (const OrderLogicVertex* toLVertexp =
                dynamic_cast<const OrderLogicVertex*>(edgep->top())) {

                // Do not construct dependencies across exclusive domains.
                if (domainsExclusive(domainp, toLVertexp->domainp())) continue;

                // Path from vertexp to a logic vertex; new edge.
                // Note we use the last edge's weight, not some function of
                // multiple edges
                new OrderEdge(m_outGraphp, moveVxp,
                              m_logic2move[toLVertexp], weight);
                madeDeps = true;
            } else {
                // This is an OrderVarVertex or other vertex representing
                // data. (Could be var, settle, or input type vertex.)
                const V3GraphVertex* nonLogicVxp = edgep->top();
                VxDomPair key(nonLogicVxp, domainp);
                if (!m_var2move[key]) {
                    const OrderEitherVertex* eithp =
                        dynamic_cast<const OrderEitherVertex*>(nonLogicVxp);
                    T_MoveVertex* newMoveVxp =
                        m_vxMakerp->makeVertexp(NULL, eithp, eithp->scopep(), domainp);
                    m_var2move[key] = newMoveVxp;

                    // Find downstream logics that depend on (var, domain)
                    if (!iterate(newMoveVxp, edgep->top(), domainp)) {
                        // No downstream dependencies, so remove this
                        // intermediate vertex.
                        m_var2move[key] = NULL;
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

class OrderMoveVertexMaker
    : public ProcessMoveBuildGraph<OrderMoveVertex>::MoveVertexMaker {
    // MEMBERS
    V3Graph* m_pomGraphp;
    V3List<OrderMoveVertex*>* m_pomWaitingp;
public:
    // CONSTRUCTORS
    OrderMoveVertexMaker(V3Graph* pomGraphp,
                         V3List<OrderMoveVertex*>* pomWaitingp)
        : m_pomGraphp(pomGraphp),
          m_pomWaitingp(pomWaitingp) {}
    // METHODS
    OrderMoveVertex* makeVertexp(OrderLogicVertex* lvertexp,
                                 const OrderEitherVertex*,
                                 const AstScope* scopep,
                                 const AstSenTree* domainp) {
        OrderMoveVertex* resultp =
            new OrderMoveVertex(m_pomGraphp, lvertexp);
        resultp->domScopep(OrderMoveDomScope::findCreate(domainp, scopep));
        resultp->m_pomWaitingE.pushBack(*m_pomWaitingp, resultp);
        return resultp;
    }
    void freeVertexp(OrderMoveVertex* freeMep) {
        freeMep->m_pomWaitingE.unlink(*m_pomWaitingp, freeMep);
        freeMep->unlinkDelete(m_pomGraphp);
    }
private:
    VL_UNCOPYABLE(OrderMoveVertexMaker);
};

class OrderMTaskMoveVertexMaker
    : public ProcessMoveBuildGraph<MTaskMoveVertex>::MoveVertexMaker {
    V3Graph* m_pomGraphp;
public:
    explicit OrderMTaskMoveVertexMaker(V3Graph* pomGraphp)
        : m_pomGraphp(pomGraphp) {}
    MTaskMoveVertex* makeVertexp(OrderLogicVertex* lvertexp,
                                 const OrderEitherVertex* varVertexp,
                                 const AstScope* scopep,
                                 const AstSenTree* domainp) {
        // Exclude initial/settle logic from the mtasks graph.
        // We'll output time-zero logic separately.
        if (domainp->hasInitial() || domainp->hasSettle()) {
            return NULL;
        }
        return new MTaskMoveVertex(m_pomGraphp, lvertexp, varVertexp, scopep, domainp);
    }
    void freeVertexp(MTaskMoveVertex* freeMep) {
        freeMep->unlinkDelete(m_pomGraphp);
    }
private:
    VL_UNCOPYABLE(OrderMTaskMoveVertexMaker);
};

class OrderVerticesByDomainThenScope {
    PartPtrIdMap m_ids;
public:
    virtual bool operator()(const V3GraphVertex* lhsp,
                            const V3GraphVertex* rhsp) const {
        const MTaskMoveVertex* l_vxp = dynamic_cast<const MTaskMoveVertex*>(lhsp);
        const MTaskMoveVertex* r_vxp = dynamic_cast<const MTaskMoveVertex*>(rhsp);
        vluint64_t l_id = m_ids.findId(l_vxp->domainp());
        vluint64_t r_id = m_ids.findId(r_vxp->domainp());
        if (l_id < r_id) return true;
        if (l_id > r_id) return false;
        l_id = m_ids.findId(l_vxp->scopep());
        r_id = m_ids.findId(r_vxp->scopep());
        return l_id < r_id;
    }
};

class MTaskVxIdLessThan {
public:
    MTaskVxIdLessThan() {}
    virtual ~MTaskVxIdLessThan() {}

    // Sort vertex's, which must be AbstractMTask's, into a deterministic
    // order by comparing their serial IDs.
    virtual bool operator()(const V3GraphVertex* lhsp,
                            const V3GraphVertex* rhsp) const {
        const AbstractMTask* lmtaskp =
            dynamic_cast<const AbstractLogicMTask*>(lhsp);
        const AbstractMTask* rmtaskp =
            dynamic_cast<const AbstractLogicMTask*>(rhsp);
        return lmtaskp->id() < rmtaskp->id();
    }
};

//######################################################################
// Order class functions

class OrderVisitor : public AstNVisitor {
private:
    // NODE STATE
    // Forming graph:
    //   Entire Netlist:
    //    AstVarScope::user1p   -> OrderUser* for usage var
    //    {statement}Node::user1p-> AstModule* statement is under
    //   USER4 Cleared on each Logic stmt
    //    AstVarScope::user4()  -> VarUsage(gen/con/both).      Where already encountered signal
    // Ordering (user3/4/5 cleared between forming and ordering)
    //    AstScope::user1p()    -> AstNodeModule*. Module this scope is under
    //    AstNodeModule::user3()    -> Number of routines created
    //  Each call to V3Const::constify
    //   AstNode::user4()               Used by V3Const::constify, called below
    AstUser1InUse       m_inuser1;
    AstUser2InUse       m_inuser2;
    AstUser3InUse       m_inuser3;
    //AstUser4InUse     m_inuser4;      // Used only when building tree, so below

    // STATE
    OrderGraph          m_graph;        // Scoreboard of var usages/dependencies
    SenTreeFinder       m_finder;       // Find global sentree's and add them
    AstSenTree*         m_comboDomainp; // Combo activation tree
    AstSenTree*         m_deleteDomainp;// Delete this from tree
    AstSenTree*         m_settleDomainp;// Initial activation tree
    OrderInputsVertex*  m_inputsVxp;    // Top level vertex all inputs point from
    OrderSettleVertex*  m_settleVxp;    // Top level vertex all settlement vertexes point from
    OrderLogicVertex*   m_logicVxp;     // Current statement being tracked, NULL=ignored
    AstTopScope*        m_topScopep;    // Current top scope being processed
    AstScope*           m_scopetopp;    // Scope under TOPSCOPE
    AstNodeModule*      m_modp;         // Current module
    AstScope*           m_scopep;       // Current scope being processed
    AstActive*          m_activep;      // Current activation block
    bool                m_inSenTree;    // Underneath AstSenItem; any varrefs are clocks
    bool                m_inClocked;    // Underneath clocked block
    bool                m_inClkAss;     // Underneath AstAssign
    bool                m_inPre;        // Underneath AstAssignPre
    bool                m_inPost;       // Underneath AstAssignPost
    OrderLogicVertex*   m_activeSenVxp; // Sensitivity vertex
    std::deque<OrderUser*>      m_orderUserps;  // All created OrderUser's for later deletion.
    // STATE... for inside process
    AstCFunc*                   m_pomNewFuncp;  // Current function being created
    int                         m_pomNewStmts;  // Statements in function being created
    V3Graph                     m_pomGraph;     // Graph of logic elements to move
    V3List<OrderMoveVertex*>    m_pomWaiting;   // List of nodes needing inputs to become ready
protected:
    friend class OrderMoveDomScope;
    V3List<OrderMoveDomScope*>  m_pomReadyDomScope;     // List of ready domain/scope pairs, by loopId
    std::vector<OrderVarStdVertex*>  m_unoptflatVars;   // Vector of variables in UNOPTFLAT loop

private:
    // STATS
    VDouble0 m_statCut[OrderVEdgeType::_ENUM_END];  // Count of each edge type cut

    // TYPES
    enum VarUsage { VU_NONE=0, VU_CON=1, VU_GEN=2 };

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    void iterateNewStmt(AstNode* nodep) {
        if (m_scopep) {
            UINFO(4,"   STMT "<<nodep<<endl);
            //VV*****  We reset user4p()
            AstNode::user4ClearTree();
            UASSERT_OBJ(m_activep && m_activep->sensesp(), nodep, "NULL");
            // If inside combo logic, ignore the domain, we'll assign one based on interconnect
            AstSenTree* startDomainp = m_activep->sensesp();
            if (startDomainp->hasCombo()) startDomainp=NULL;
            m_logicVxp = new OrderLogicVertex(&m_graph, m_scopep, startDomainp, nodep);
            if (m_activeSenVxp) {
                // If in a clocked activation, add a link from the sensitivity to this block
                // Add edge logic_sensitive_vertex->logic_vertex
                new OrderEdge(&m_graph, m_activeSenVxp, m_logicVxp, WEIGHT_NORMAL);
            }
            nodep->user1p(m_modp);
            iterateChildren(nodep);
            m_logicVxp = NULL;
        }
    }

    OrderVarVertex* newVarUserVertex(AstVarScope* varscp, WhichVertex type, bool* createdp=NULL) {
        if (!varscp->user1p()) {
            OrderUser* newup = new OrderUser();
            m_orderUserps.push_back(newup);
            varscp->user1p(newup);
        }
        OrderUser* up = reinterpret_cast<OrderUser*>(varscp->user1p());
        OrderVarVertex* varVxp = up->newVarUserVertex(&m_graph, m_scopep, varscp, type, createdp);
        return varVxp;
    }

    void process();
    void processCircular();
    typedef std::deque<OrderEitherVertex*> VertexVec;
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
    AstActive* processMoveOneLogic(const OrderLogicVertex* lvertexp,
                                   AstCFunc*& newFuncpr, int& newStmtsr);

    // processMTask* routines schedule threaded execution
    struct MTaskState {
        typedef std::list<const OrderLogicVertex*> Logics;
        AstMTaskBody* m_mtaskBodyp;
        Logics m_logics;
        ExecMTask* m_execMTaskp;
        MTaskState() : m_mtaskBodyp(NULL), m_execMTaskp(NULL) {}
    };
    void processMTasks();
    typedef enum {LOGIC_INITIAL, LOGIC_SETTLE} InitialLogicE;
    void processMTasksInitial(InitialLogicE logic_type);

    string cfuncName(AstNodeModule* modp, AstSenTree* domainp,
                     AstScope* scopep, AstNode* forWhatp) {
        modp->user3Inc();
        int funcnum = modp->user3();
        string name = (domainp->hasCombo() ? "_combo"
                       : (domainp->hasInitial() ? "_initial"
                          : (domainp->hasSettle() ? "_settle"
                             : (domainp->isMulti() ? "_multiclk" : "_sequent"))));
        name = name+"__"+scopep->nameDotless()+"__"+cvtToStr(funcnum);
        if (v3Global.opt.profCFuncs()) {
            name += "__PROF__"+forWhatp->fileline()->profileFuncname();
        }
        return name;
    }

    void nodeMarkCircular(OrderVarVertex* vertexp, OrderEdge* edgep) {
        AstVarScope* nodep = vertexp->varScp();
        OrderLogicVertex* fromLVtxp = NULL;
        OrderLogicVertex* toLVtxp = NULL;
        if (edgep) {
            fromLVtxp = dynamic_cast<OrderLogicVertex*>(edgep->fromp());
            toLVtxp = dynamic_cast<OrderLogicVertex*>(edgep->top());
        }
        //
        if ((fromLVtxp && VN_IS(fromLVtxp->nodep(), Initial))
            || (toLVtxp && VN_IS(toLVtxp->nodep(), Initial))) {
            // IEEE does not specify ordering between initial blocks, so we
            // can do whatever we want. We especially do not want to
            // evaluate multiple times, so do not mark the edge circular
        }
        else {
            nodep->circular(true);
            ++m_statCut[vertexp->type()];
            if (edgep) ++m_statCut[edgep->type()];
            //
            if (vertexp->isClock()) {
                // Seems obvious; no warning yet
                //nodep->v3warn(GENCLK, "Signal unoptimizable: Generated clock: "<<nodep->prettyNameQ());
            } else if (nodep->varp()->isSigPublic()) {
                nodep->v3warn(UNOPT, "Signal unoptimizable: Feedback to public clock or circular logic: "
                              <<nodep->prettyNameQ());
                if (!nodep->fileline()->warnIsOff(V3ErrorCode::UNOPT)) {
                    nodep->fileline()->modifyWarnOff(V3ErrorCode::UNOPT, true);  // Complain just once
                    // Give the user an example.
                    bool tempWeight = (edgep && edgep->weight()==0);
                    if (tempWeight) edgep->weight(1);  // Else the below loop detect can't see the loop
                    m_graph.reportLoops(&OrderEdge::followComboConnected, vertexp);  // calls OrderGraph::loopsVertexCb
                    if (tempWeight) edgep->weight(0);
                }
            } else {
                // We don't use UNOPT, as there are lots of V2 places where
                // it was needed, that aren't any more
                // First v3warn not inside warnIsOff so we can see the suppressions with --debug
                nodep->v3warn(UNOPTFLAT, "Signal unoptimizable: Feedback to clock or circular logic: "
                              <<nodep->prettyNameQ());
                if (!nodep->fileline()->warnIsOff(V3ErrorCode::UNOPTFLAT)) {
                    nodep->fileline()->modifyWarnOff(V3ErrorCode::UNOPTFLAT, true);  // Complain just once
                    // Give the user an example.
                    bool tempWeight = (edgep && edgep->weight()==0);
                    if (tempWeight) edgep->weight(1);  // Else the below loop detect can't see the loop
                    m_graph.reportLoops(&OrderEdge::followComboConnected, vertexp);  // calls OrderGraph::loopsVertexCb
                    if (tempWeight) edgep->weight(0);
                    if (v3Global.opt.reportUnoptflat()) {
                        // Report candidate variables for splitting
                        reportLoopVars(vertexp);
                        // Do a subgraph for the UNOPTFLAT loop
                        OrderGraph loopGraph;
                        m_graph.subtreeLoops(&OrderEdge::followComboConnected,
                                             vertexp, &loopGraph);
                        loopGraph.dumpDotFilePrefixedAlways("unoptflat");
                    }
                }
            }
        }
    }

    //! Find all variables in an UNOPTFLAT loop
    //!
    //! Ignore vars that are 1-bit wide and don't worry about generated
    //! variables (PRE and POST vars, __Vdly__, __Vcellin__ and __VCellout).
    //! What remains are candidates for splitting to break loops.
    //!
    //! node->user3 is used to mark if we have done a particular variable.
    //! vertex->user is used to mark if we have seen this vertex before.
    //!
    //! @todo We could be cleverer in the future and consider just
    //!       the width that is generated/consumed.
    void reportLoopVars(OrderVarVertex* vertexp) {
        m_graph.userClearVertices();
        AstNode::user3ClearTree();
        m_unoptflatVars.clear();
        reportLoopVarsIterate(vertexp, vertexp->color());
        AstNode::user3ClearTree();
        m_graph.userClearVertices();
        // May be very large vector, so only report the "most important"
        // elements. Up to 10 of the widest
        std::cerr<<V3Error::msgPrefix()
                 <<"     Widest candidate vars to split:"<<endl;
        std::stable_sort(m_unoptflatVars.begin(), m_unoptflatVars.end(), OrderVarWidthCmp());
        int lim = m_unoptflatVars.size() < 10 ? m_unoptflatVars.size() : 10;
        for (int i = 0; i < lim; i++) {
            OrderVarStdVertex* vsvertexp = m_unoptflatVars[i];
            AstVar* varp = vsvertexp->varScp()->varp();
            std::cerr<<V3Error::msgPrefix()<<"          "
                     <<varp->fileline()<<" "<<varp->prettyName()<<std::dec
                     <<", width "<<varp->width()<<", fanout "
                     <<vsvertexp->fanout()<<endl;
        }
        // Up to 10 of the most fanned out
        std::cerr<<V3Error::msgPrefix()
                 <<"     Most fanned out candidate vars to split:"<<endl;
        std::stable_sort(m_unoptflatVars.begin(), m_unoptflatVars.end(),
                         OrderVarFanoutCmp());
        lim = m_unoptflatVars.size() < 10 ? m_unoptflatVars.size() : 10;
        for (int i = 0; i < lim; i++) {
            OrderVarStdVertex* vsvertexp = m_unoptflatVars[i];
            AstVar* varp = vsvertexp->varScp()->varp();
            std::cerr<<V3Error::msgPrefix()<<"          "
                     <<varp->fileline()<<" "<<varp->prettyName()
                     <<", width "<<std::dec<<varp->width()
                     <<", fanout "<<vsvertexp->fanout()<<endl;
        }
        m_unoptflatVars.clear();
    }

    void reportLoopVarsIterate(V3GraphVertex* vertexp, uint32_t color) {
        if (vertexp->user()) return;  // Already done
        vertexp->user(1);
        if (OrderVarStdVertex* vsvertexp = dynamic_cast<OrderVarStdVertex*>(vertexp)) {
            // Only reporting on standard variable vertices
            AstVar* varp = vsvertexp->varScp()->varp();
            if (!varp->user3()) {
                string name = varp->prettyName();
                if ((varp->width() != 1)
                    && (name.find("__Vdly") == string::npos)
                    && (name.find("__Vcell") == string::npos)) {
                    // Variable to report on and not yet done
                    m_unoptflatVars.push_back(vsvertexp);
                }
                varp->user3Inc();
            }
        }
        // Iterate through all the to and from vertices of the same color
        for (V3GraphEdge* edgep = vertexp->outBeginp(); edgep;
             edgep = edgep->outNextp()) {
            if (edgep->top()->color() == color) {
                reportLoopVarsIterate(edgep->top(), color);
            }
        }
        for (V3GraphEdge* edgep = vertexp->inBeginp(); edgep;
             edgep = edgep->inNextp()) {
            if (edgep->fromp()->color() == color) {
                reportLoopVarsIterate(edgep->fromp(), color);
            }
        }
    }
    // VISITORS
    virtual void visit(AstNetlist* nodep) {
        {
            AstUser4InUse       m_inuser4;      // Used only when building tree, so below
            iterateChildren(nodep);
        }
        // We're finished, complete the topscopes
        if (m_topScopep) { process(); m_topScopep=NULL; }
    }
    virtual void visit(AstTopScope* nodep) {
        // Process the last thing we're finishing
        UASSERT_OBJ(!m_topScopep, nodep, "Only one topscope should ever be created");
        UINFO(2,"  Loading tree...\n");
        //VV*****  We reset userp()
        AstNode::user1ClearTree();
        AstNode::user3ClearTree();
        m_graph.clear();
        m_activep = NULL;
        m_topScopep = nodep;
        m_scopetopp = nodep->scopep();
        // Find sentree's
        m_finder.main(m_topScopep);
        // ProcessDomainsIterate will use these when it needs to move
        // something to a combodomain.  This saves a ton of find() operations.
        AstSenTree* combp = new AstSenTree(nodep->fileline(),  // Gets cloned() so ok if goes out of scope
                                           new AstSenItem(nodep->fileline(), AstSenItem::Combo()));
        m_comboDomainp = m_finder.getSenTree(nodep->fileline(), combp);
        pushDeletep(combp);  // Cleanup when done
        AstSenTree* settlep = new AstSenTree(nodep->fileline(),  // Gets cloned() so ok if goes out of scope
                                             new AstSenItem(nodep->fileline(),
                                                            AstSenItem::Settle()));
        m_settleDomainp = m_finder.getSenTree(nodep->fileline(), settlep);
        pushDeletep(settlep);  // Cleanup when done
        // Fake AstSenTree we set domainp to indicate needs deletion
        m_deleteDomainp = new AstSenTree(nodep->fileline(),
                                         new AstSenItem(nodep->fileline(), AstSenItem::Settle()));
        pushDeletep(m_deleteDomainp);  // Cleanup when done
        UINFO(5,"    DeleteDomain = "<<m_deleteDomainp<<endl);
        // Base vertices
        m_activeSenVxp = NULL;
        m_inputsVxp = new OrderInputsVertex(&m_graph, NULL);
        //
        iterateChildren(nodep);
        // Done topscope, erase extra user information
        // user1p passed to next process() operation
        AstNode::user3ClearTree();
        AstNode::user4ClearTree();
    }
    virtual void visit(AstNodeModule* nodep) {
        AstNodeModule* origModp = m_modp;
        {
            m_modp = nodep;
            iterateChildren(nodep);
        }
        m_modp = origModp;
    }
    virtual void visit(AstScope* nodep) {
        UINFO(4," SCOPE "<<nodep<<endl);
        m_scopep = nodep;
        m_logicVxp = NULL;
        m_activeSenVxp = NULL;
        nodep->user1p(m_modp);
        // Iterate
        iterateChildren(nodep);
        m_scopep = NULL;
    }
    virtual void visit(AstActive* nodep) {
        // Create required activation blocks and add to module
        UINFO(4,"  ACTIVE  "<<nodep<<endl);
        m_activep = nodep;
        m_activeSenVxp = NULL;
        m_inClocked = nodep->hasClocked();
        // Grab the sensitivity list
        UASSERT_OBJ(!nodep->sensesStorep(), nodep,
                    "Senses should have been activeTop'ed to be global!");
        iterate(nodep->sensesp());
        // Collect statements under it
        iterateChildren(nodep);
        m_activep = NULL;
        m_activeSenVxp = NULL;
        m_inClocked = false;
    }
    virtual void visit(AstVarScope* nodep) {
        // Create links to all input signals
        if (m_modp->isTop() && nodep->varp()->isNonOutput()) {
            OrderVarVertex* varVxp = newVarUserVertex(nodep, WV_STD);
            new OrderEdge(&m_graph, m_inputsVxp, varVxp, WEIGHT_INPUT);
        }
    }
    virtual void visit(AstNodeVarRef* nodep) {
        if (m_scopep) {
            AstVarScope* varscp = nodep->varScopep();
            UASSERT_OBJ(varscp, nodep, "Var didn't get varscoped in V3Scope.cpp");
            if (m_inSenTree) {
                // Add CLOCK dependency... This is a root of the tree we'll trace
                UASSERT_OBJ(!nodep->lvalue(), nodep, "How can a sensitivity be setting a var?");
                OrderVarVertex* varVxp = newVarUserVertex(varscp, WV_STD);
                varVxp->isClock(true);
                new OrderEdge(&m_graph, varVxp, m_activeSenVxp, WEIGHT_MEDIUM);
            } else {
                UASSERT_OBJ(m_logicVxp, nodep, "Var ref not under a logic block");
                // What new directions is this used
                // We don't want to add extra edges if the logic block has many usages of same var
                bool gen = false;
                bool con = false;
                if (nodep->lvalue()) {
                    gen = !(varscp->user4() & VU_GEN);
                } else {
                    con = !(varscp->user4() & VU_CON);
                    if ((varscp->user4() & VU_GEN) && !m_inClocked) {
                        // Dangerous assumption:
                        // If a variable is used in the same activation which defines it first,
                        // consider it something like:
                        //              foo = 1
                        //              foo = foo + 1
                        // and still optimize.  This is the rule verilog-mode assumes for /*AS*/
                        // Note this will break though:
                        //              if (sometimes) foo = 1
                        //              foo = foo + 1
                        con = false;
                    }
                    if (varscp->varp()->attrClockEn() && !m_inPre && !m_inPost && !m_inClocked) {
                        // clock_enable attribute: user's worrying about it for us
                        con = false;
                    }
                    if (m_inClkAss && (varscp->varp()->attrClocker()
                                       != VVarAttrClocker::CLOCKER_YES)) {
                        con = false;
                        UINFO(4, "nodep used as clock_enable "<<varscp
                              <<" in "<<m_logicVxp->nodep()<<endl);
                    }
                }
                if (gen) varscp->user4(varscp->user4() | VU_GEN);
                if (con) varscp->user4(varscp->user4() | VU_CON);
                // Add edges
                if (!m_inClocked
                    || m_inPost
                    ) {
                    // Combo logic
                    {  // not settle and (combo or inPost)
                        if (gen) {
                            // Add edge logic_vertex->logic_generated_var
                            OrderVarVertex* varVxp = newVarUserVertex(varscp, WV_STD);
                            if (m_inPost) {
                                new OrderPostCutEdge(&m_graph, m_logicVxp, varVxp);
                                // Mark the vertex. Used to control marking
                                // internal clocks circular, which must only
                                // happen if they are generated by delayed
                                // assignment.
                                UINFO(5, "     Found delayed assignment (post) "
                                      << varVxp << endl);
                                varVxp->isDelayed(true);
                            } else {
                                // If the lhs is a clocker, avoid marking that as circular by
                                // putting a hard edge instead of normal cuttable
                                if (varscp->varp()->attrClocker()
                                    == VVarAttrClocker::CLOCKER_YES) {
                                    new OrderEdge(&m_graph, m_logicVxp, varVxp, WEIGHT_NORMAL);
                                } else {
                                    new OrderComboCutEdge(&m_graph, m_logicVxp, varVxp);
                                }
                            }
                            // For m_inPost:
                            //    Add edge consumed_var_POST->logic_vertex
                            //    This prevents a consumer of the "early" value to be scheduled
                            //   after we've changed to the next-cycle value
                            // ALWAYS do it:
                            //    There maybe a wire a=b; between the two blocks
                            OrderVarVertex* postVxp = newVarUserVertex(varscp, WV_POST);
                            new OrderEdge(&m_graph, postVxp, m_logicVxp, WEIGHT_POST);
                        }
                        if (con) {
                            // Add edge logic_consumed_var->logic_vertex
                            OrderVarVertex* varVxp = newVarUserVertex(varscp, WV_STD);
                            new OrderEdge(&m_graph, varVxp, m_logicVxp, WEIGHT_MEDIUM);
                        }
                    }
                } else if (m_inPre) {
                    // AstAssignPre logic
                    if (gen) {
                        // Add edge logic_vertex->generated_var_PREORDER
                        OrderVarVertex* ordVxp = newVarUserVertex(varscp, WV_PORD);
                        new OrderEdge(&m_graph, m_logicVxp, ordVxp, WEIGHT_NORMAL);
                        // Add edge logic_vertex->logic_generated_var (same as if comb)
                        OrderVarVertex* varVxp = newVarUserVertex(varscp, WV_STD);
                        new OrderEdge(&m_graph, m_logicVxp, varVxp, WEIGHT_NORMAL);
                    }
                    if (con) {
                        // Add edge logic_consumed_var_PREVAR->logic_vertex
                        // This one is cutable (vs the producer) as there's
                        // only one of these, but many producers
                        OrderVarVertex* preVxp = newVarUserVertex(varscp, WV_PRE);
                        new OrderPreCutEdge(&m_graph, preVxp, m_logicVxp);
                    }
                } else {
                    // Seq logic
                    if (gen) {
                        // Add edge logic_generated_var_PREORDER->logic_vertex
                        OrderVarVertex* ordVxp = newVarUserVertex(varscp, WV_PORD);
                        new OrderEdge(&m_graph, ordVxp, m_logicVxp, WEIGHT_NORMAL);
                        // Add edge logic_vertex->logic_generated_var (same as if comb)
                        OrderVarVertex* varVxp = newVarUserVertex(varscp, WV_STD);
                        new OrderEdge(&m_graph, m_logicVxp, varVxp, WEIGHT_NORMAL);
                    }
                    if (con) {
                        // Add edge logic_vertex->consumed_var_PREVAR
                        // Generation of 'pre' because we want to indicate
                        // it should be before AstAssignPre
                        OrderVarVertex* preVxp = newVarUserVertex(varscp, WV_PRE);
                        new OrderEdge(&m_graph, m_logicVxp, preVxp, WEIGHT_NORMAL);
                        // Add edge logic_vertex->consumed_var_POST
                        OrderVarVertex* postVxp = newVarUserVertex(varscp, WV_POST);
                        new OrderEdge(&m_graph, m_logicVxp, postVxp, WEIGHT_POST);
                    }
                }
            }
        }
    }
    virtual void visit(AstSenTree* nodep) {
        // Having a node derived from the sentree isn't required for
        // correctness, it merely makes the graph better connected
        // and improves graph algorithmic performance
        if (m_scopep) {  // Else TOPSCOPE's SENTREE list
            m_inSenTree = true;
            if (nodep->hasClocked()) {
                if (!m_activeSenVxp) {
                    m_activeSenVxp = new OrderLogicVertex(&m_graph, m_scopep, nodep, m_activep);
                }
                iterateChildren(nodep);
            }
            m_inSenTree = false;
        }
    }
    virtual void visit(AstAlways* nodep) {
        iterateNewStmt(nodep);
    }
    virtual void visit(AstAlwaysPost* nodep) {
        m_inPost = true;
        iterateNewStmt(nodep);
        m_inPost = false;
    }
    virtual void visit(AstAlwaysPublic* nodep) {
        iterateNewStmt(nodep);
    }
    virtual void visit(AstAssignAlias* nodep) {
        iterateNewStmt(nodep);
    }
    virtual void visit(AstAssignW* nodep) {
        OrderClkAssVisitor visitor(nodep);
        m_inClkAss = visitor.isClkAss();
        iterateNewStmt(nodep);
        m_inClkAss = false;
    }
    virtual void visit(AstAssignPre* nodep) {
        OrderClkAssVisitor visitor(nodep);
        m_inClkAss = visitor.isClkAss();
        m_inPre = true;
        iterateNewStmt(nodep);
        m_inPre = false;
        m_inClkAss = false;
    }
    virtual void visit(AstAssignPost* nodep) {
        OrderClkAssVisitor visitor(nodep);
        m_inClkAss = visitor.isClkAss();
        m_inPost = true;
        iterateNewStmt(nodep);
        m_inPost = false;
        m_inClkAss = false;
    }
    virtual void visit(AstCoverToggle* nodep) {
        iterateNewStmt(nodep);
    }
    virtual void visit(AstInitial* nodep) {
        // We use initials to setup parameters and static consts's which may be referenced
        // in user initial blocks.  So use ordering to sort them all out.
        iterateNewStmt(nodep);
    }
    virtual void visit(AstCFunc*) {
        // Ignore for now
        // We should detect what variables are set in the function, and make
        // settlement code for them, then set a global flag, so we call "settle"
        // on the next evaluation loop.
    }
    //--------------------
    // Default
    virtual void visit(AstNode* nodep) {
        iterateChildren(nodep);
    }
public:
    // CONSTRUCTORS
    OrderVisitor() {
        m_topScopep = NULL;
        m_scopetopp = NULL;
        m_modp = NULL;
        m_scopep = NULL;
        m_activep = NULL;
        m_inSenTree = false;
        m_inClocked = false;
        m_inClkAss = false;
        m_inPre = m_inPost = false;
        m_comboDomainp = NULL;
        m_deleteDomainp = NULL;
        m_settleDomainp = NULL;
        m_settleVxp = NULL;
        m_inputsVxp = NULL;
        m_activeSenVxp = NULL;
        m_logicVxp = NULL;
        m_pomNewFuncp = NULL;
        m_pomNewStmts = 0;
        if (debug()) m_graph.debug(5);  // 3 is default if global debug; we want acyc debugging
    }
    virtual ~OrderVisitor() {
        // Stats
        for (int type=0; type<OrderVEdgeType::_ENUM_END; type++) {
            double count = double(m_statCut[type]);
            if (count != 0.0) {
                V3Stats::addStat(string("Order, cut, ")+OrderVEdgeType(type).ascii(), count);
            }
        }
        // Destruction
        for (std::deque<OrderUser*>::iterator it=m_orderUserps.begin();
             it != m_orderUserps.end(); ++it) {
            delete *it;
        }
        m_graph.debug(V3Error::debugDefault());
    }
    void main(AstNode* nodep) {
        iterate(nodep);
    }
};

//######################################################################
// General utilities

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

    bool toInitial = top->hasInitial() || top->hasSettle();
    bool fromInitial = fromp->hasInitial() || fromp->hasSettle();
    if (toInitial != fromInitial) {
        return true;
    }

    const AstSenItem* fromSenListp = VN_CAST(fromp->sensesp(), SenItem);
    const AstSenItem* toSenListp = VN_CAST(top->sensesp(), SenItem);
    // If clk gating is ever reenabled, we may need to update this to handle
    // AstSenGate also.
    UASSERT_OBJ(fromSenListp, fromp, "sensitivity list item is not an AstSenItem");
    UASSERT_OBJ(toSenListp, top, "sensitivity list item is not an AstSenItem");

    if (fromSenListp->nextp()) return false;
    if (toSenListp->nextp()) return false;

    const AstNodeVarRef* fromVarrefp = fromSenListp->varrefp();
    const AstNodeVarRef* toVarrefp = toSenListp->varrefp();
    if (!fromVarrefp || !toVarrefp) return false;

    // We know nothing about the relationship between different clocks here,
    // so give up on proving anything.
    if (fromVarrefp->varScopep() != toVarrefp->varScopep()) return false;

    return fromSenListp->edgeType().exclusiveEdge(toSenListp->edgeType());
}

//######################################################################
// OrderMoveDomScope methods

// Check the domScope is on ready list, add if not
inline void OrderMoveDomScope::ready(OrderVisitor* ovp) {
    if (!m_onReadyList) {
        m_onReadyList = true;
        m_readyDomScopeE.pushBack(ovp->m_pomReadyDomScope, this);
    }
}

// Mark one vertex as finished, remove from ready list if done
inline void OrderMoveDomScope::movedVertex(OrderVisitor* ovp, OrderMoveVertex* vertexp) {
    UASSERT_OBJ(m_onReadyList, vertexp,
                "Moving vertex from ready when nothing was on que as ready.");
    if (m_readyVertices.empty()) {  // Else more work to get to later
        m_onReadyList = false;
        m_readyDomScopeE.unlink(ovp->m_pomReadyDomScope, this);
    }
}

//######################################################################
// OrderVisitor - Clock propagation

void OrderVisitor::processInputs() {
    m_graph.userClearVertices();  // Vertex::user()   // 1 if input recursed, 2 if marked as input, 3 if out-edges recursed
    // Start at input vertex, process from input-to-output order
    VertexVec todoVec;  // List of newly-input marked vectors we need to process
    todoVec.push_front(m_inputsVxp);
    m_inputsVxp->isFromInput(true);  // By definition
    while (!todoVec.empty()) {
        OrderEitherVertex* vertexp = todoVec.back(); todoVec.pop_back();
        processInputsOutIterate(vertexp, todoVec);
    }
}

void OrderVisitor::processInputsInIterate(OrderEitherVertex* vertexp, VertexVec& todoVec) {
    // Propagate PrimaryIn through simple assignments
    if (vertexp->user()) return;  // Already processed
    if (0 && debug()>=9) {
        UINFO(9," InIIter "<<vertexp<<endl);
        if (OrderLogicVertex* vvertexp = dynamic_cast<OrderLogicVertex*>(vertexp)) {
            vvertexp->nodep()->dumpTree(cout, "-            TT: ");
        }
    }
    vertexp->user(1);  // Processing
    // First handle all inputs to this vertex, in most cases they'll be already processed earlier
    // Also, determine if this vertex is an input
    int inonly = 1;  // 0=no, 1=maybe, 2=yes until a no
    for (V3GraphEdge* edgep = vertexp->inBeginp(); edgep; edgep=edgep->inNextp()) {
        OrderEitherVertex* frVertexp = static_cast<OrderEitherVertex*>(edgep->fromp());
        processInputsInIterate(frVertexp, todoVec);
        if (frVertexp->isFromInput()) {
            if (inonly==1) inonly = 2;
        } else if (dynamic_cast<OrderVarPostVertex*>(frVertexp)) {
            // Ignore post assignments, just for ordering
        } else {
            //UINFO(9,"    InItStopDueTo "<<frVertexp<<endl);
            inonly = 0;
            break;
        }
    }

    if (inonly == 2 && vertexp->user()<2) {  // Set it.  Note may have already been set earlier, too
        UINFO(9,"   Input reassignment: "<<vertexp<<endl);
        vertexp->isFromInput(true);
        vertexp->user(2);  // 2 means on list
        // Can't work on out-edges of a node we know is an input immediately,
        // as it might visit other nodes before their input state is resolved.
        // So push to list and work on it later when all in-edges known resolved
        todoVec.push_back(vertexp);
    }
    //UINFO(9,"  InIdone "<<vertexp<<endl);
}

void OrderVisitor::processInputsOutIterate(OrderEitherVertex* vertexp, VertexVec& todoVec) {
    if (vertexp->user()==3) return;  // Already out processed
    //UINFO(9," InOIter "<<vertexp<<endl);
    // First make sure input path is fully recursed
    processInputsInIterate(vertexp, todoVec);
    // Propagate PrimaryIn through simple assignments
    UASSERT_OBJ(vertexp->isFromInput(), vertexp,
                "processInputsOutIterate only for input marked vertexes");
    vertexp->user(3);  // out-edges processed

    {
        // Propagate PrimaryIn through simple assignments, following target of vertex
        for (V3GraphEdge* edgep = vertexp->outBeginp(); edgep; edgep=edgep->outNextp()) {
            OrderEitherVertex* toVertexp = static_cast<OrderEitherVertex*>(edgep->top());
            if (OrderVarStdVertex* vvertexp = dynamic_cast<OrderVarStdVertex*>(toVertexp)) {
                processInputsInIterate(vvertexp, todoVec);
            }
            if (OrderLogicVertex* vvertexp = dynamic_cast<OrderLogicVertex*>(toVertexp)) {
                if (VN_IS(vvertexp->nodep(), NodeAssign)) {
                    processInputsInIterate(vvertexp, todoVec);
                }
            }
        }
    }
}

//######################################################################
// OrderVisitor - Circular detection

void OrderVisitor::processCircular() {
    // Take broken edges and add circular flags
    // The change detect code will use this to force changedets
    for (V3GraphVertex* itp = m_graph.verticesBeginp(); itp; itp=itp->verticesNextp()) {
        if (OrderVarStdVertex* vvertexp = dynamic_cast<OrderVarStdVertex*>(itp)) {
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
                    UINFO(5,"Circular Clock, no-order-clock-delay "<<vvertexp<<endl);
                    nodeMarkCircular(vvertexp, NULL);
                }
                else if (vvertexp->isDelayed()) {
                    UINFO(5,"Circular Clock, delayed "<<vvertexp<<endl);
                    nodeMarkCircular(vvertexp, NULL);
                }
                else {
                    UINFO(5,"Circular Clock, not delayed "<<vvertexp<<endl);
                }
            }
            // Also mark any cut edges
            for (V3GraphEdge* edgep = vvertexp->outBeginp(); edgep; edgep=edgep->outNextp()) {
                if (edgep->weight()==0) {  // was cut
                    OrderEdge* oedgep = dynamic_cast<OrderEdge*>(edgep);
                    UASSERT_OBJ(oedgep, vvertexp->varScp(), "Cuttable edge not of proper type");
                    UINFO(6,"      CutCircularO: "<<vvertexp->name()<<endl);
                    nodeMarkCircular(vvertexp, oedgep);
                }
            }
            for (V3GraphEdge* edgep = vvertexp->inBeginp(); edgep; edgep = edgep->inNextp()) {
                if (edgep->weight()==0) {  // was cut
                    OrderEdge* oedgep = dynamic_cast<OrderEdge*>(edgep);
                    UASSERT_OBJ(oedgep, vvertexp->varScp(), "Cuttable edge not of proper type");
                    UINFO(6,"      CutCircularI: "<<vvertexp->name()<<endl);
                    nodeMarkCircular(vvertexp, oedgep);
                }
            }
        }
    }
}

void OrderVisitor::processSensitive() {
    // Sc sensitives are required on all inputs that go to a combo
    // block.  (Not inputs that go only to clocked blocks.)
    for (V3GraphVertex* itp = m_graph.verticesBeginp(); itp; itp=itp->verticesNextp()) {
        if (OrderVarStdVertex* vvertexp = dynamic_cast<OrderVarStdVertex*>(itp)) {
            if (vvertexp->varScp()->varp()->isNonOutput()) {
                //UINFO(0,"  scsen "<<vvertexp<<endl);
                for (V3GraphEdge* edgep = vvertexp->outBeginp(); edgep; edgep=edgep->outNextp()) {
                    if (OrderEitherVertex* toVertexp
                        = dynamic_cast<OrderEitherVertex*>(edgep->top())) {
                        if (edgep->weight() && toVertexp->domainp()) {
                            //UINFO(0,"      "<<toVertexp->domainp()<<endl);
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

void OrderVisitor::processDomains() {
    for (V3GraphVertex* itp = m_graph.verticesBeginp(); itp; itp=itp->verticesNextp()) {
        OrderEitherVertex* vertexp = dynamic_cast<OrderEitherVertex*>(itp);
        UASSERT(vertexp, "Null or vertex not derived from EitherVertex");
        processDomainsIterate(vertexp);
    }
}

void OrderVisitor::processDomainsIterate(OrderEitherVertex* vertexp) {
    // The graph routines have already sorted the vertexes and edges into best->worst order
    // Assign clock domains to each signal.
    //     Sequential logic is forced into the same sequential domain.
    //     Combo logic may be pushed into a seq domain if all its inputs are the same domain,
    //     else, if all inputs are from flops, it's end-of-sequential code
    //     else, it's full combo code
    if (vertexp->domainp()) return;  // Already processed, or sequential logic
    UINFO(5,"    pdi: "<<vertexp<<endl);
    OrderVarVertex* vvertexp = dynamic_cast<OrderVarVertex*>(vertexp);
    AstSenTree* domainp = NULL;
    UASSERT(m_comboDomainp, "not preset");
    if (vvertexp && vvertexp->varScp()->varp()->isNonOutput()) {
        domainp = m_comboDomainp;
    }
    if (vvertexp && vvertexp->varScp()->isCircular()) {
        domainp = m_comboDomainp;
    }
    if (!domainp) {
        for (V3GraphEdge* edgep = vertexp->inBeginp(); edgep; edgep = edgep->inNextp()) {
            OrderEitherVertex* fromVertexp = static_cast<OrderEitherVertex*>(edgep->fromp());
            if (edgep->weight()
                && fromVertexp->domainMatters()
                ) {
                UINFO(9,"     from d="<<cvtToHex(fromVertexp->domainp())
                      <<" "<<fromVertexp<<endl);
                if (!domainp  // First input to this vertex
                    || domainp->hasSettle()  // or, we can ignore being in the settle domain
                    || domainp->hasInitial()) {
                    domainp = fromVertexp->domainp();
                }
                else if (domainp->hasCombo()) {
                    // Once in combo, keep in combo; already as severe as we can get
                }
                else if (fromVertexp->domainp()->hasCombo()) {
                    // Any combo input means this vertex must remain combo
                    domainp = m_comboDomainp;
                }
                else if (fromVertexp->domainp()->hasSettle()
                         || fromVertexp->domainp()->hasInitial()) {
                    // Ignore that we have a constant (initial) input
                }
                else if (domainp != fromVertexp->domainp()) {
                    // Make a domain that merges the two domains
                    bool ddebug = debug()>=9;
                    if (ddebug) {
                        cout<<endl;
                        UINFO(0,"      conflicting domain "<<fromVertexp<<endl);
                        UINFO(0,"         dorig="<<domainp<<endl);
                        domainp->dumpTree(cout);
                        UINFO(0,"         d2   ="<<fromVertexp->domainp()<<endl);
                        fromVertexp->domainp()->dumpTree(cout);
                    }
                    AstSenTree* newtreep = domainp->cloneTree(false);
                    AstNodeSenItem* newtree2p = fromVertexp->domainp()->sensesp()->cloneTree(true);
                    UASSERT_OBJ(newtree2p, fromVertexp->domainp(),
                                "No senitem found under clocked domain");
                    newtreep->addSensesp(newtree2p);
                    newtree2p = NULL;  // Below edit may replace it
                    V3Const::constifyExpensiveEdit(newtreep);  // Remove duplicates
                    newtreep->multi(true);  // Comment that it was made from 2 clock domains
                    domainp = m_finder.getSenTree(domainp->fileline(), newtreep);
                    if (ddebug) {
                        UINFO(0,"         dnew ="<<newtreep<<endl);
                        newtreep->dumpTree(cout);
                        UINFO(0,"         find ="<<domainp<<endl);
                        domainp->dumpTree(cout);
                        cout<<endl;
                    }
                    VL_DO_DANGLING(newtreep->deleteTree(), newtreep);
                }
            }
        }  // next input edgep
        // Default the domain
        // This is a node which has only constant inputs, or is otherwise indeterminate.
        // It should have already been copied into the settle domain.  Presumably it has
        // inputs which we never trigger, or nothing it's sensitive to, so we can rip it out.
        if (!domainp && vertexp->scopep()) {
            domainp = m_deleteDomainp;
        }
    }
    //
    vertexp->domainp(domainp);
    if (vertexp->domainp()) {
        UINFO(5,"      done d="<<cvtToHex(vertexp->domainp())
              <<(vertexp->domainp()->hasCombo()?" [COMB]":"")
              <<(vertexp->domainp()->isMulti()?" [MULT]":"")
              <<" "<<vertexp<<endl);
    }
}

//######################################################################
// OrderVisitor - Move graph construction

void OrderVisitor::processEdgeReport() {
    // Make report of all signal names and what clock edges they have
    string filename = v3Global.debugFilename("order_edges.txt");
    const vl_unique_ptr<std::ofstream> logp (V3File::new_ofstream(filename));
    if (logp->fail()) v3fatal("Can't write "<<filename);
    //Testing emitter: V3EmitV::verilogForTree(v3Global.rootp(), *logp);

    std::deque<string> report;

    for (V3GraphVertex* itp = m_graph.verticesBeginp(); itp; itp=itp->verticesNextp()) {
        if (OrderVarVertex* vvertexp = dynamic_cast<OrderVarVertex*>(itp)) {
            string name (vvertexp->varScp()->prettyName());
            if (dynamic_cast<OrderVarPreVertex*>(itp)) name += " {PRE}";
            else if (dynamic_cast<OrderVarPostVertex*>(itp)) name += " {POST}";
            else if (dynamic_cast<OrderVarPordVertex*>(itp)) name += " {PORD}";
            else if (dynamic_cast<OrderVarSettleVertex*>(itp)) name += " {STL}";
            std::ostringstream os;
            os.setf(std::ios::left);
            os<<"  "<<cvtToHex(vvertexp->varScp())<<" "<<std::setw(50)<<name<<" ";
            AstSenTree* sentreep = vvertexp->domainp();
            if (sentreep) V3EmitV::verilogForTree(sentreep, os);
            report.push_back(os.str());
        }
    }

    *logp<<"Signals and their clock domains:"<<endl;
    stable_sort(report.begin(), report.end());
    for (std::deque<string>::iterator it=report.begin(); it!=report.end(); ++it) {
        *logp<<(*it)<<endl;
    }
}

void OrderVisitor::processMoveClear() {
    OrderMoveDomScope::clear();
    m_pomWaiting.reset();
    m_pomReadyDomScope.reset();
    m_pomGraph.clear();
}

void OrderVisitor::processMoveBuildGraph() {
    // Build graph of only vertices
    UINFO(5,"  MoveBuildGraph\n");
    processMoveClear();
    m_pomGraph.userClearVertices();  // Vertex::user()   // OrderMoveVertex*, last edge added or NULL for none

    OrderMoveVertexMaker createOrderMoveVertex(&m_pomGraph, &m_pomWaiting);
    ProcessMoveBuildGraph<OrderMoveVertex> serialPMBG(
        &m_graph, &m_pomGraph, &createOrderMoveVertex);
    serialPMBG.build();
}

//######################################################################
// OrderVisitor - Moving

void OrderVisitor::processMove() {
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
    UINFO(5,"  MoveIterate\n");
    while (!m_pomReadyDomScope.empty()) {
        // Start with top node on ready list's domain & scope
        OrderMoveDomScope* domScopep = m_pomReadyDomScope.begin();
        OrderMoveVertex* topVertexp = domScopep->readyVertices().begin();  // lintok-begin-on-ref
        UASSERT(topVertexp, "domScope on ready list without any nodes ready under it");
        // Work on all scopes ready inside this domain
        while (domScopep) {
            UINFO(6,"   MoveDomain l="<<domScopep->domainp()<<endl);
            // Process all nodes ready under same domain & scope
            m_pomNewFuncp = NULL;
            while (OrderMoveVertex* vertexp = domScopep->readyVertices().begin()) {  // lintok-begin-on-ref
                processMoveOne(vertexp, domScopep, 1);
            }
            // Done with scope/domain pair, pick new scope under same domain, or NULL if none left
            OrderMoveDomScope* domScopeNextp = NULL;
            for (OrderMoveDomScope* huntp = m_pomReadyDomScope.begin();
                 huntp; huntp = huntp->readyDomScopeNextp()) {
                if (huntp->domainp() == domScopep->domainp()) {
                    domScopeNextp = huntp;
                    break;
                }
            }
            domScopep = domScopeNextp;
        }
    }
    UASSERT(m_pomWaiting.empty(), "Didn't converge; nodes waiting, none ready, perhaps some input activations lost.");
    // Cleanup memory
    processMoveClear();
}

void OrderVisitor::processMovePrepReady() {
    // Make list of ready nodes
    UINFO(5,"  MovePrepReady\n");
    for (OrderMoveVertex* vertexp = m_pomWaiting.begin(); vertexp; ) {
        OrderMoveVertex* nextp = vertexp->pomWaitingNextp();
        if (vertexp->isWait() && vertexp->inEmpty()) {
            processMoveReadyOne(vertexp);
        }
        vertexp = nextp;
    }
}

void OrderVisitor::processMoveReadyOne(OrderMoveVertex* vertexp) {
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

void OrderVisitor::processMoveDoneOne(OrderMoveVertex* vertexp) {
    // Move one node from ready to completion
    vertexp->setMoved();
    // Unlink from ready lists
    if (vertexp->logicp()) {
        vertexp->m_readyVerticesE.unlink(vertexp->domScopep()->m_readyVertices, vertexp);
        vertexp->domScopep()->movedVertex(this, vertexp);
    }
    // Don't need to add it to another list, as we're done with it
    // Mark our outputs as one closer to ready
    for (V3GraphEdge* edgep = vertexp->outBeginp(), *nextp; edgep; edgep=nextp) {
        nextp = edgep->outNextp();
        OrderMoveVertex* toVertexp = static_cast<OrderMoveVertex*>(edgep->top());
        UINFO(9,"          Clear to "<<(toVertexp->inEmpty()?"[EMP] ":"      ")
              <<toVertexp<<endl);
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

void OrderVisitor::processMoveOne(OrderMoveVertex* vertexp,
                                  OrderMoveDomScope* domScopep, int level) {
    UASSERT_OBJ(vertexp->domScopep() == domScopep, vertexp, "Domain mismatch; list misbuilt?");
    const OrderLogicVertex* lvertexp = vertexp->logicp();
    const AstScope* scopep = lvertexp->scopep();
    UINFO(5,"    POSmove l"<<std::setw(3)<<level<<" d="<<cvtToHex(lvertexp->domainp())
          <<" s="<<cvtToHex(scopep)<<" "<<lvertexp<<endl);
    AstActive* newActivep = processMoveOneLogic(lvertexp, m_pomNewFuncp/*ref*/,
                                                m_pomNewStmts/*ref*/);
    if (newActivep) m_scopetopp->addActivep(newActivep);
    processMoveDoneOne(vertexp);
}

AstActive* OrderVisitor::processMoveOneLogic(const OrderLogicVertex* lvertexp,
                                             AstCFunc*& newFuncpr,
                                             int& newStmtsr) {
    AstActive* activep = NULL;
    AstScope* scopep = lvertexp->scopep();
    AstSenTree* domainp = lvertexp->domainp();
    AstNode* nodep = lvertexp->nodep();
    AstNodeModule* modp = VN_CAST(scopep->user1p(), NodeModule);  // Stashed by visitor func
    UASSERT(modp, "NULL");
    if (VN_IS(nodep, SenTree)) {
        // Just ignore sensitivities, we'll deal with them when we move statements that need them
    }
    else {  // Normal logic
        // Make or borrow a CFunc to contain the new statements
        if (v3Global.opt.profCFuncs()
            || (v3Global.opt.outputSplitCFuncs()
                && v3Global.opt.outputSplitCFuncs() < newStmtsr)) {
            // Put every statement into a unique function to ease profiling or reduce function size
            newFuncpr = NULL;
        }
        if (!newFuncpr && domainp != m_deleteDomainp) {
            string name = cfuncName(modp, domainp, scopep, nodep);
            newFuncpr = new AstCFunc(nodep->fileline(), name, scopep);
            newFuncpr->argTypes(EmitCBaseVisitor::symClassVar());
            newFuncpr->symProlog(true);
            newStmtsr = 0;
            if (domainp->hasInitial() || domainp->hasSettle()) newFuncpr->slow(true);
            scopep->addActivep(newFuncpr);
            // Where will we be adding the call?
            activep = new AstActive(nodep->fileline(), name, domainp);
            // Add a top call to it
            AstCCall* callp = new AstCCall(nodep->fileline(), newFuncpr);
            callp->argTypes("vlSymsp");
            activep->addStmtsp(callp);
            UINFO(6,"      New "<<newFuncpr<<endl);
        }

        // Move the logic to the function we're creating
        nodep->unlinkFrBack();
        if (domainp == m_deleteDomainp) {
            UINFO(4," Ordering deleting pre-settled "<<nodep<<endl);
            VL_DO_DANGLING(pushDeletep(nodep), nodep);
        } else {
            newFuncpr->addStmtsp(nodep);
            if (v3Global.opt.outputSplitCFuncs()) {
                // Add in the number of nodes we're adding
                EmitCBaseCounterVisitor visitor(nodep);
                newStmtsr += visitor.count();
            }
        }
    }
    return activep;
}

void OrderVisitor::processMTasksInitial(InitialLogicE logic_type) {
    // Emit initial/settle logic. Initial blocks won't be part of the
    // mtask partition, aren't eligible for parallelism.
    //
    int initStmts = 0;
    AstCFunc* initCFunc = NULL;
    AstScope* lastScopep = NULL;
    for (V3GraphVertex* initVxp = m_graph.verticesBeginp();
         initVxp; initVxp = initVxp->verticesNextp()) {
        OrderLogicVertex* initp = dynamic_cast<OrderLogicVertex*>(initVxp);
        if (!initp) continue;
        if ((logic_type == LOGIC_INITIAL)
            && !initp->domainp()->hasInitial()) continue;
        if ((logic_type == LOGIC_SETTLE)
            && !initp->domainp()->hasSettle()) continue;
        if (initp->scopep() != lastScopep) {
            // Start new cfunc, don't let the cfunc cross scopes
            initCFunc = NULL;
            lastScopep = initp->scopep();
        }
        AstActive* newActivep = processMoveOneLogic(initp, initCFunc/*ref*/, initStmts/*ref*/);
        if (newActivep) m_scopetopp->addActivep(newActivep);
    }
}

void OrderVisitor::processMTasks() {
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
    ProcessMoveBuildGraph<MTaskMoveVertex> mtask_pmbg(
        &m_graph, &logicGraph, &create_mtask_vertex);
    mtask_pmbg.build();

    // Needed? We do this for m_pomGraph in serial mode, so do it here too:
    logicGraph.removeRedundantEdges(&V3GraphEdge::followAlwaysTrue);

    // Partition logicGraph into LogicMTask's. The partitioner will annotate
    // each vertex in logicGraph with a 'color' which is really an mtask ID
    // in this context.
    V3Partition partitioner(&logicGraph);
    V3Graph mtasks;
    partitioner.go(&mtasks);

    vl_unordered_map<unsigned /*mtask id*/, MTaskState> mtaskStates;

    // Iterate through the entire logicGraph. For each logic node,
    // attach it to a per-MTask ordered list of logic nodes.
    // This is the order we'll execute logic nodes within the MTask.
    //
    // MTasks may span scopes and domains, so sort by both here:
    GraphStream<OrderVerticesByDomainThenScope> emit_logic(&logicGraph);
    const V3GraphVertex* moveVxp;
    while ((moveVxp = emit_logic.nextp())) {
        const MTaskMoveVertex* movep =
            dynamic_cast<const MTaskMoveVertex*>(moveVxp);
        unsigned mtaskId = movep->color();
        UASSERT(mtaskId > 0,
                "Every MTaskMoveVertex should have an mtask assignment >0");
        if (movep->logicp()) {
            // Add this logic to the per-mtask order
            mtaskStates[mtaskId].m_logics.push_back(movep->logicp());

            // Since we happen to be iterating over every logic node,
            // take this opportunity to annotate each AstVar with the id's
            // of mtasks that consume it and produce it. We'll use this
            // information in V3EmitC when we lay out var's in memory.
            const OrderLogicVertex* logicp = movep->logicp();
            for (const V3GraphEdge* edgep = logicp->inBeginp();
                 edgep; edgep = edgep->inNextp()) {
                const OrderVarVertex* pre_varp =
                    dynamic_cast<const OrderVarVertex*>(edgep->fromp());
                if (!pre_varp) continue;
                AstVar* varp = pre_varp->varScp()->varp();
                // varp depends on logicp, so logicp produces varp,
                // and vice-versa below
                varp->addProducingMTaskId(mtaskId);
            }
            for (const V3GraphEdge* edgep = logicp->outBeginp();
                 edgep; edgep = edgep->outNextp()) {
                const OrderVarVertex* post_varp
                    = dynamic_cast<const OrderVarVertex*>(edgep->top());
                if (!post_varp) continue;
                AstVar* varp = post_varp->varScp()->varp();
                varp->addConsumingMTaskId(mtaskId);
            }
            // TODO? We ignore IO vars here, so those will have empty mtask
            // signatures. But we could also give those mtask signatures.
        }
    }

    // Create the AstExecGraph node which represents the execution
    // of the MTask graph.
    FileLine* rootFlp = v3Global.rootp()->fileline();
    AstExecGraph* execGraphp = new AstExecGraph(rootFlp);
    m_scopetopp->addActivep(execGraphp);
    v3Global.rootp()->execGraphp(execGraphp);

    // Create CFuncs and bodies for each MTask.
    GraphStream<MTaskVxIdLessThan> emit_mtasks(&mtasks);
    const V3GraphVertex* mtaskVxp;
    while ((mtaskVxp = emit_mtasks.nextp())) {
        const AbstractLogicMTask* mtaskp =
            dynamic_cast<const AbstractLogicMTask*>(mtaskVxp);

        // Create a body for this mtask
        AstMTaskBody* bodyp = new AstMTaskBody(rootFlp);
        MTaskState& state = mtaskStates[mtaskp->id()];
        state.m_mtaskBodyp = bodyp;

        // Create leaf CFunc's to run this mtask's logic,
        // and create a set of AstActive's to call those CFuncs.
        // Add the AstActive's into the AstMTaskBody.
        const AstSenTree* last_domainp = NULL;
        AstCFunc* leafCFuncp = NULL;
        int leafStmts = 0;
        for (MTaskState::Logics::iterator it = state.m_logics.begin();
             it != state.m_logics.end(); ++it) {
            const OrderLogicVertex* logicp = *it;
            if (logicp->domainp() != last_domainp) {
                // Start a new leaf function.
                leafCFuncp = NULL;
            }
            last_domainp = logicp->domainp();

            AstActive* newActivep = processMoveOneLogic(logicp, leafCFuncp/*ref*/,
                                                        leafStmts/*ref*/);
            if (newActivep) bodyp->addStmtsp(newActivep);
        }

        // Translate the LogicMTask graph into the corresponding ExecMTask
        // graph, which will outlive V3Order and persist for the remainder
        // of verilator's processing.
        // - The LogicMTask graph points to MTaskMoveVertex's
        //   and OrderLogicVertex's which are ephemeral to V3Order.
        // - The ExecMTask graph and the AstMTaskBody's produced here
        //   persist until code generation time.
        state.m_execMTaskp =
            new ExecMTask(execGraphp->mutableDepGraphp(),
                          bodyp, mtaskp->id());
        // Cross-link each ExecMTask and MTaskBody
        //  Q: Why even have two objects?
        //  A: One is an AstNode, the other is a GraphVertex,
        //     to combine them would involve multiple inheritance...
        state.m_mtaskBodyp->execMTaskp(state.m_execMTaskp);
        for (V3GraphEdge* inp = mtaskp->inBeginp();
             inp; inp = inp->inNextp()) {
            const V3GraphVertex* fromVxp = inp->fromp();
            const AbstractLogicMTask* fromp =
                dynamic_cast<const AbstractLogicMTask*>(fromVxp);
            MTaskState& fromState = mtaskStates[fromp->id()];
            new V3GraphEdge(execGraphp->mutableDepGraphp(),
                            fromState.m_execMTaskp, state.m_execMTaskp, 1);
        }
        execGraphp->addMTaskBody(bodyp);
    }
}

//######################################################################
// OrderVisitor - Top processing

void OrderVisitor::process() {
    // Dump data
    m_graph.dumpDotFilePrefixed("orderg_pre");

    // Break cycles. Each strongly connected subgraph (including cutable
    // edges) will have its own color, and corresponds to a loop in the
    // original graph. However the new graph will be acyclic (the removed
    // edges are actually still there, just with weight 0).
    UINFO(2,"  Acyclic & Order...\n");
    m_graph.acyclic(&V3GraphEdge::followAlwaysTrue);
    m_graph.dumpDotFilePrefixed("orderg_acyc");

    // Assign ranks so we know what to follow
    // Then, sort vertices and edges by that ordering
    m_graph.order();
    m_graph.dumpDotFilePrefixed("orderg_order");

    // This finds everything that can be traced from an input (which by
    // definition are the source clocks). After this any vertex which was
    // traced has isFromInput() true.
    UINFO(2,"  Process Clocks...\n");
    processInputs();  // must be before processCircular

    UINFO(2,"  Process Circulars...\n");
    processCircular();  // must be before processDomains

    // Assign logic vertices to new domains
    UINFO(2,"  Domains...\n");
    processDomains();
    m_graph.dumpDotFilePrefixed("orderg_domain");

    if (debug() && v3Global.opt.dumpTree()) processEdgeReport();

    if (!v3Global.opt.mtasks()) {
        UINFO(2,"  Construct Move Graph...\n");
        processMoveBuildGraph();
        if (debug()>=4) m_pomGraph.dumpDotFilePrefixed("ordermv_start");  // Different prefix (ordermv) as it's not the same graph
        m_pomGraph.removeRedundantEdges(&V3GraphEdge::followAlwaysTrue);
        if (debug()>=4) m_pomGraph.dumpDotFilePrefixed("ordermv_simpl");

        UINFO(2,"  Move...\n");
        processMove();
    } else {
        UINFO(2,"  Set up mtasks...\n");
        processMTasks();
    }

    // Any SC inputs feeding a combo domain must be marked, so we can make them sc_sensitive
    UINFO(2,"  Sensitive...\n");
    processSensitive();  // must be after processDomains

    // Dump data
    m_graph.dumpDotFilePrefixed("orderg_done");
    if (0 && debug()) {
        string dfilename = v3Global.opt.makeDir()+"/"+v3Global.opt.prefix()+"_INT_order";
        const vl_unique_ptr<std::ofstream> logp (V3File::new_ofstream(dfilename));
        if (logp->fail()) v3fatal("Can't write "<<dfilename);
        m_graph.dump(*logp);
    }
}

//######################################################################
// Order class functions

void V3Order::orderAll(AstNetlist* nodep) {
    UINFO(2,__FUNCTION__<<": "<<endl);
    {
        OrderClkMarkVisitor markVisitor(nodep);
        OrderVisitor visitor;
        visitor.main(nodep);
    }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("order", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}
