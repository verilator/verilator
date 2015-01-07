// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Block code ordering
//
// Code available from: http://www.veripool.org/verilator
//
//*************************************************************************
//
// Copyright 2003-2015 by Wilson Snyder.  This program is free software; you can
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
//  OrderGraph Class Hierarchy:
//
//	V3GraphVertex
//	  OrderMoveVertex
//	  OrderEitherVertex
//	    OrderInputsVertex
//	    OrderSettleVertex
//	    OrderLogicVertex
//	      OrderLoopBeginVertex
//	      OrderLoopEndVertex
//	    OrderVarVertex
//	      OrderVarStdVertex
//	      OrderVarPreVertex
//	      OrderVarPostVertex
//	      OrderVarPordVertex
//	      OrderVarSettleVertex
//
//	V3GraphEdge
//	  OrderEdge
//	    OrderChangeDetEdge
//	    OrderComboCutEdge
//	    OrderPostCutEdge
//	    OrderPreCutEdge
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"
#include "V3Ast.h"
#include "V3Graph.h"

class OrderVisitor;
class OrderMoveVertex;
class OrderMoveDomScope;

//######################################################################

enum OrderWeights {
    WEIGHT_INPUT  = 1,	// Low weight just so dot graph looks nice
    WEIGHT_COMBO  = 1,	// Breakable combo logic
    WEIGHT_LOOPBE = 1,	// Connection to loop begin/end
    WEIGHT_POST   = 2,	// Post-delayed used var
    WEIGHT_PRE    = 3,	// Breakable pre-delayed used var
    WEIGHT_MEDIUM = 8,	// Medium weight just so dot graph looks nice
    WEIGHT_NORMAL = 32 };	// High   weight just so dot graph looks nice

enum OrderLoopId {
    LOOPID_UNKNOWN = 0,	// Not assigned yet
    LOOPID_NOTLOOPED=1,	// Not looped
    LOOPID_FIRST = 2,	// First assigned id (numbers increment from here)
    LOOPID_MAX = (1<<30)
};

struct OrderVEdgeType {
    enum en {
	VERTEX_UNKNOWN = 0,
	VERTEX_INPUTS,
	VERTEX_SETTLE,
	VERTEX_LOGIC,
	VERTEX_VARSTD,
	VERTEX_VARPRE,
	VERTEX_VARPOST,
	VERTEX_VARPORD,
	VERTEX_VARSETTLE,
	VERTEX_LOOPBEGIN,
	VERTEX_LOOPEND,
	VERTEX_MOVE,
	EDGE_STD,
	EDGE_CHANGEDET,
	EDGE_COMBOCUT,
	EDGE_PRECUT,
	EDGE_POSTCUT,
	_ENUM_END
    };
    const char* ascii() const {
	static const char* names[] = {
	    "%E-vedge", "VERTEX_INPUTS", "VERTEX_SETTLE", "VERTEX_LOGIC",
	    "VERTEX_VARSTD", "VERTEX_VARPRE", "VERTEX_VARPOST",
	    "VERTEX_VARPORD", "VERTEX_VARSETTLE", "VERTEX_LOOPBEGIN",
	    "VERTEX_LOOPEND", "VERTEX_MOVE",
	    "EDGE_STD", "EDGE_CHANGEDET", "EDGE_COMBOCUT",
	    "EDGE_PRECUT", "EDGE_POSTCUT", "_ENUM_END"

	};
	return names[m_e];
    }
    enum en m_e;
    inline OrderVEdgeType () : m_e(VERTEX_UNKNOWN) {}
    inline OrderVEdgeType (en _e) : m_e(_e) {}
    explicit inline OrderVEdgeType (int _e) : m_e(static_cast<en>(_e)) {}
    operator en () const { return m_e; }
  };
  inline bool operator== (OrderVEdgeType lhs, OrderVEdgeType rhs) { return (lhs.m_e == rhs.m_e); }
  inline bool operator== (OrderVEdgeType lhs, OrderVEdgeType::en rhs) { return (lhs.m_e == rhs); }
  inline bool operator== (OrderVEdgeType::en lhs, OrderVEdgeType rhs) { return (lhs == rhs.m_e); }

//######################################################################
// Graph types

class OrderGraph : public V3Graph {
public:
    OrderGraph() {}
    virtual ~OrderGraph() {}
    // Methods
    virtual void loopsVertexCb(V3GraphVertex* vertexp);
};

//! Graph for UNOPTFLAT loops
class UnoptflatGraph : public OrderGraph {
public:
    UnoptflatGraph() {}
    virtual ~UnoptflatGraph() {}
    // Methods
    virtual void loopsVertexCb(V3GraphVertex* vertexp);
};

//######################################################################
// Vertex types

class OrderEitherVertex : public V3GraphVertex {
    AstScope*	m_scopep;	// Scope the vertex is in
    AstSenTree*	m_domainp;	// Clock domain (NULL = to be computed as we iterate)
    OrderLoopId	m_inLoop;	// Loop number vertex is in
    bool	m_isFromInput;	// From input, or derrived therefrom (conservatively false)
protected:
    OrderEitherVertex(V3Graph* graphp, const OrderEitherVertex& old)
	: V3GraphVertex(graphp, old), m_scopep(old.m_scopep), m_domainp(old.m_domainp)
	, m_inLoop(old.m_inLoop), m_isFromInput(old.m_isFromInput) {}
public:
    OrderEitherVertex(V3Graph* graphp, AstScope* scopep, AstSenTree* domainp)
	: V3GraphVertex(graphp), m_scopep(scopep), m_domainp(domainp)
	, m_inLoop(LOOPID_UNKNOWN), m_isFromInput(false) {}
    virtual ~OrderEitherVertex() {}
    virtual OrderEitherVertex* clone(V3Graph* graphp) const = 0;
    // Methods
    virtual OrderVEdgeType type() const = 0;
    virtual bool domainMatters() = 0;	// Must be in same domain when cross edge to this vertex
    virtual string dotName() const { return cvtToStr((void*)m_scopep)+"_"; }
    // Accessors
    void domainp(AstSenTree* domainp) { m_domainp = domainp; }
    AstScope* scopep() const { return m_scopep; }
    AstSenTree* domainp() const { return m_domainp; }
    OrderLoopId	inLoop() const { return m_inLoop; }
    void inLoop(OrderLoopId inloop) { m_inLoop = inloop; }
    void isFromInput(bool flag) { m_isFromInput=flag; }
    bool isFromInput() const { return m_isFromInput; }
};

class OrderInputsVertex : public OrderEitherVertex {
    OrderInputsVertex(V3Graph* graphp, const OrderInputsVertex& old)
	: OrderEitherVertex(graphp, old) {}
public:
    OrderInputsVertex(V3Graph* graphp, AstSenTree* domainp)
	: OrderEitherVertex(graphp, NULL, domainp) {
	isFromInput(true);  // By definition
    }
    virtual ~OrderInputsVertex() {}
    virtual OrderInputsVertex* clone(V3Graph* graphp) const {
	return new OrderInputsVertex(graphp, *this); }
    virtual OrderVEdgeType type() const { return OrderVEdgeType::VERTEX_INPUTS; }
    virtual string name() const { return "*INPUTS*"; }
    virtual string dotColor() const { return "green"; }
    virtual string dotName() const { return ""; }
    virtual bool domainMatters() { return false; }
};

class OrderSettleVertex : public OrderEitherVertex {
    OrderSettleVertex(V3Graph* graphp, const OrderSettleVertex& old)
	: OrderEitherVertex(graphp, old) {}
public:
    OrderSettleVertex(V3Graph* graphp, AstSenTree* domainp)
	: OrderEitherVertex(graphp, NULL, domainp) {}
    virtual ~OrderSettleVertex() {}
    virtual OrderSettleVertex* clone(V3Graph* graphp) const {
	return new OrderSettleVertex(graphp, *this); }
    virtual OrderVEdgeType type() const { return OrderVEdgeType::VERTEX_SETTLE; }
    virtual string name() const { return "*SETTLE*"; }
    virtual string dotColor() const { return "green"; }
    virtual string dotName() const { return ""; }
    virtual bool domainMatters() { return true; }
};

class OrderLogicVertex : public OrderEitherVertex {
    AstNode*		m_nodep;
    OrderMoveVertex*	m_moveVxp;
protected:
    OrderLogicVertex(V3Graph* graphp, const OrderLogicVertex& old)
	: OrderEitherVertex(graphp, old), m_nodep(old.m_nodep), m_moveVxp(old.m_moveVxp) {}
public:
    OrderLogicVertex(V3Graph* graphp, AstScope* scopep, AstSenTree* domainp, AstNode* nodep)
	: OrderEitherVertex(graphp, scopep, domainp), m_nodep(nodep), m_moveVxp(NULL) {}
    virtual ~OrderLogicVertex() {}
    virtual OrderLogicVertex* clone(V3Graph* graphp) const {
	return new OrderLogicVertex(graphp, *this); }
    virtual OrderVEdgeType type() const { return OrderVEdgeType::VERTEX_LOGIC; }
    virtual bool domainMatters() { return true; }
    // Accessors
    virtual string name() const { return (cvtToStr((void*)m_nodep)+"\\n "+cvtToStr(nodep()->typeName())); }
    AstNode* nodep() const { return m_nodep; }
    virtual string dotColor() const { return "yellow"; }
    OrderMoveVertex*	moveVxp() const { return m_moveVxp; }
    void moveVxp(OrderMoveVertex* moveVxp) { m_moveVxp = moveVxp; }
};

class OrderVarVertex : public OrderEitherVertex {
    AstVarScope* m_varScp;
    OrderVarVertex*	m_pilNewVertexp;	// for processInsLoopNewVar
    bool	 m_isClock;	// Used as clock
    bool	 m_isDelayed;	// Set in a delayed assignment
protected:
    OrderVarVertex(V3Graph* graphp, const OrderVarVertex& old)
	: OrderEitherVertex(graphp, old)
	, m_varScp(old.m_varScp), m_pilNewVertexp(old.m_pilNewVertexp), m_isClock(old.m_isClock)
	, m_isDelayed(old.m_isDelayed) {}
public:
    OrderVarVertex(V3Graph* graphp, AstScope* scopep, AstVarScope* varScp)
	: OrderEitherVertex(graphp, scopep, NULL), m_varScp(varScp)
	, m_pilNewVertexp(NULL), m_isClock(false), m_isDelayed(false) {}
    virtual ~OrderVarVertex() {}
    virtual OrderVarVertex* clone (V3Graph* graphp) const = 0;
    virtual OrderVEdgeType type() const = 0;
    // Accessors
    AstVarScope* varScp() const { return m_varScp; }
    void isClock(bool flag) { m_isClock=flag; }
    bool isClock() const { return m_isClock; }
    void isDelayed(bool flag) { m_isDelayed=flag; }
    bool isDelayed() const { return m_isDelayed; }
    OrderVarVertex* pilNewVertexp() const { return m_pilNewVertexp; }
    void pilNewVertexp (OrderVarVertex* vertexp) { m_pilNewVertexp = vertexp; }
};

class OrderVarStdVertex : public OrderVarVertex {
    OrderVarStdVertex(V3Graph* graphp, const OrderVarStdVertex& old)
	: OrderVarVertex(graphp, old) {}
public:
    OrderVarStdVertex(V3Graph* graphp, AstScope* scopep, AstVarScope* varScp)
	: OrderVarVertex(graphp, scopep, varScp) {}
    virtual ~OrderVarStdVertex() {}
    virtual OrderVarStdVertex* clone(V3Graph* graphp) const {
	return new OrderVarStdVertex(graphp, *this); }
    virtual OrderVEdgeType type() const { return OrderVEdgeType::VERTEX_VARSTD; }
    virtual string name() const { return (cvtToStr((void*)varScp())+"\\n "+varScp()->name());}
    virtual string dotColor() const { return "skyblue"; }
    virtual bool domainMatters() { return true; }
};
class OrderVarPreVertex : public OrderVarVertex {
    OrderVarPreVertex(V3Graph* graphp, const OrderVarPreVertex& old)
	: OrderVarVertex(graphp, old) {}
public:
    OrderVarPreVertex(V3Graph* graphp, AstScope* scopep, AstVarScope* varScp)
	: OrderVarVertex(graphp, scopep,varScp) {}
    virtual ~OrderVarPreVertex() {}
    virtual OrderVarPreVertex* clone(V3Graph* graphp) const {
	return new OrderVarPreVertex(graphp, *this); }
    virtual OrderVEdgeType type() const { return OrderVEdgeType::VERTEX_VARPRE; }
    virtual string name() const { return (cvtToStr((void*)varScp())+" PRE\\n "+varScp()->name());}
    virtual string dotColor() const { return "lightblue"; }
    virtual bool domainMatters() { return false; }
};
class OrderVarPostVertex : public OrderVarVertex {
    OrderVarPostVertex(V3Graph* graphp, const OrderVarPostVertex& old)
	: OrderVarVertex(graphp, old) {}
public:
    OrderVarPostVertex(V3Graph* graphp, AstScope* scopep, AstVarScope* varScp)
	: OrderVarVertex(graphp, scopep,varScp) {}
    virtual OrderVarPostVertex* clone(V3Graph* graphp) const {
	return new OrderVarPostVertex(graphp, *this); }
    virtual OrderVEdgeType type() const { return OrderVEdgeType::VERTEX_VARPOST; }
    virtual ~OrderVarPostVertex() {}
    virtual string name() const { return (cvtToStr((void*)varScp())+" POST\\n "+varScp()->name());}
    virtual string dotColor() const { return "CadetBlue"; }
    virtual bool domainMatters() { return false; }
};
class OrderVarPordVertex : public OrderVarVertex {
    OrderVarPordVertex(V3Graph* graphp, const OrderVarPordVertex& old)
	: OrderVarVertex(graphp, old) {}
public:
    OrderVarPordVertex(V3Graph* graphp, AstScope* scopep, AstVarScope* varScp)
	: OrderVarVertex(graphp, scopep,varScp) {}
    virtual ~OrderVarPordVertex() {}
    virtual OrderVarPordVertex* clone(V3Graph* graphp) const {
	return new OrderVarPordVertex(graphp, *this); }
    virtual OrderVEdgeType type() const { return OrderVEdgeType::VERTEX_VARPORD; }
    virtual string name() const { return (cvtToStr((void*)varScp())+" PORD\\n "+varScp()->name());}
    virtual string dotColor() const { return "NavyBlue"; }
    virtual bool domainMatters() { return false; }
};
class OrderVarSettleVertex : public OrderVarVertex {
    OrderVarSettleVertex(V3Graph* graphp, const OrderVarSettleVertex& old)
	: OrderVarVertex(graphp, old) {}
public:
    OrderVarSettleVertex(V3Graph* graphp, AstScope* scopep, AstVarScope* varScp)
	: OrderVarVertex(graphp, scopep,varScp) {}
    virtual ~OrderVarSettleVertex() {}
    virtual OrderVarSettleVertex* clone(V3Graph* graphp) const {
	return new OrderVarSettleVertex(graphp, *this); }
    virtual OrderVEdgeType type() const { return OrderVEdgeType::VERTEX_VARSETTLE; }
    virtual string name() const { return (cvtToStr((void*)varScp())+" STL\\n "+varScp()->name());}
    virtual string dotColor() const { return "PowderBlue"; }
    virtual bool domainMatters() { return false; }
};

//######################################################################
//--- Looping constructs

class OrderLoopBeginVertex : public OrderLogicVertex {
    // A vertex can never be under two loops...
    // However, a LoopBeginVertex is not "under" the loop per se, and it may be under another loop.
    OrderLoopId	m_loopId;		// Arbitrary # to ID this loop
    uint32_t	m_loopColor;		// Color # of loop (for debug)
    OrderLoopBeginVertex(V3Graph* graphp, const OrderLoopBeginVertex& old)
	: OrderLogicVertex(graphp, *this)
	, m_loopId(old.m_loopId), m_loopColor(old.m_loopColor) {}
public:
    OrderLoopBeginVertex(V3Graph* graphp, AstScope* scopep, AstSenTree* domainp, AstUntilStable* nodep,
			 OrderLoopId loopId, uint32_t loopColor)
	: OrderLogicVertex(graphp, scopep, domainp, nodep)
	, m_loopId(loopId), m_loopColor(loopColor) {}
    virtual ~OrderLoopBeginVertex() {}
    virtual OrderLoopBeginVertex* clone(V3Graph* graphp) const {
	return new OrderLoopBeginVertex(graphp, *this);
    }
    // Methods
    virtual OrderVEdgeType type() const { return OrderVEdgeType::VERTEX_LOOPBEGIN; }
    virtual string name() const { return "LoopBegin_"+cvtToStr(loopId())+"_c"+cvtToStr(loopColor()); }
    virtual bool domainMatters() { return true; }
    virtual string dotColor() const { return "blue"; }
    AstUntilStable* untilp() const { return nodep()->castUntilStable(); }
    OrderLoopId loopId() const { return m_loopId; }
    uint32_t loopColor() const { return m_loopColor; }
};

class OrderLoopEndVertex : public OrderLogicVertex {
    // A end vertex points to the *same nodep* as the Begin, as we need it to
    // be a logic vertex for moving, but don't need a permanent node.  We
    // won't add to the output graph though, so it shouldn't matter.
    OrderLoopBeginVertex*  m_beginVertexp;	// Corresponding loop begin
    OrderLoopEndVertex(V3Graph* graphp, const OrderLoopEndVertex& old)
	: OrderLogicVertex(graphp, old), m_beginVertexp(old.m_beginVertexp) {}
public:
    OrderLoopEndVertex(V3Graph* graphp, OrderLoopBeginVertex* beginVertexp)
	: OrderLogicVertex(graphp, beginVertexp->scopep(),
			   beginVertexp->domainp(), beginVertexp->nodep())
	, m_beginVertexp(beginVertexp) {
	inLoop(beginVertexp->loopId());
    }
    virtual ~OrderLoopEndVertex() {}
    virtual OrderLoopEndVertex* clone(V3Graph* graphp) const {
	return new OrderLoopEndVertex(graphp, *this); }
    // Methods
    virtual OrderVEdgeType type() const { return OrderVEdgeType::VERTEX_LOOPEND; }
    virtual string name() const { return "LoopEnd_"+cvtToStr(inLoop())+"_c"+cvtToStr(loopColor()); }
    virtual bool domainMatters() { return false; }
    virtual string dotColor() const { return "blue"; }
    OrderLoopBeginVertex*  beginVertexp() const { return m_beginVertexp; }
    uint32_t loopColor() const { return beginVertexp()->loopColor(); }
};

//######################################################################
//--- Following only under the move graph, not the main graph

class OrderMoveVertex : public V3GraphVertex {
    typedef enum {POM_WAIT, POM_READY, POM_MOVED} OrderMState;

    OrderLogicVertex*	m_logicp;
    OrderMState		m_state;	// Movement state
    OrderMoveDomScope*	m_domScopep;	// Domain/scope list information

protected:
    friend class OrderVisitor;
    // These only contain the "next" item,
    // for the head of the list, see the same var name under OrderVisitor
    V3ListEnt<OrderMoveVertex*>	m_pomWaitingE;	// List of nodes needing inputs to become ready
    V3ListEnt<OrderMoveVertex*>	m_readyVerticesE;// List of ready under domain/scope
    // CONSTRUCTORS
    OrderMoveVertex(V3Graph* graphp, const OrderMoveVertex& old)
	: V3GraphVertex(graphp, old), m_logicp(old.m_logicp), m_state(old.m_state)
	, m_domScopep(old.m_domScopep) {}
public:
    OrderMoveVertex(V3Graph* graphp, OrderLogicVertex*	logicp)
	: V3GraphVertex(graphp), m_logicp(logicp), m_state(POM_WAIT), m_domScopep(NULL) {}
    virtual ~OrderMoveVertex() {}
    virtual OrderMoveVertex* clone(V3Graph* graphp) const {
	return new OrderMoveVertex(graphp, *this);
    }
    virtual OrderVEdgeType type() const { return OrderVEdgeType::VERTEX_MOVE; }
    virtual string dotColor() const { return logicp()->dotColor(); }
    virtual string name() const {
	string nm = logicp()->name();
	nm += (string("\\nMV:")
	       +" lp="+cvtToStr(logicp()->inLoop())
	       +" d="+cvtToStr((void*)logicp()->domainp())
	       +" s="+cvtToStr((void*)logicp()->scopep()));
	return nm;
    }
    // ACCESSORS
    OrderLogicVertex* logicp() const { return m_logicp; }
    bool isWait() const { return m_state==POM_WAIT; }
    void setReady() {
	UASSERT(m_state==POM_WAIT, "Wait->Ready on node not in proper state\n");
	m_state = POM_READY;
    }
    void setMoved() {
	UASSERT(m_state==POM_READY, "Ready->Moved on node not in proper state\n");
	m_state = POM_MOVED;
    }
    OrderMoveDomScope* domScopep() const { return m_domScopep; }
    OrderMoveVertex* pomWaitingNextp() const { return m_pomWaitingE.nextp(); }
    void domScopep(OrderMoveDomScope* ds) { m_domScopep=ds; }
};

//######################################################################
// Edge types

class OrderEdge : public V3GraphEdge {
protected:
    OrderEdge(V3Graph* graphp, V3GraphVertex* fromp, V3GraphVertex* top,
	      const OrderEdge& old)
	: V3GraphEdge(graphp, fromp, top, old) {}
public:
    OrderEdge(V3Graph* graphp, V3GraphVertex* fromp, V3GraphVertex* top,
	      int weight, bool cutable=false)
	: V3GraphEdge(graphp, fromp, top, weight, cutable) {}
    virtual ~OrderEdge() {}
    virtual OrderVEdgeType type() const { return OrderVEdgeType::EDGE_STD; }
    virtual OrderEdge* clone (V3Graph* graphp, V3GraphVertex* fromp, V3GraphVertex* top) const {
	return new OrderEdge(graphp, fromp, top, *this);
    }
    // When ordering combo blocks with stronglyConnected, follow edges not involving pre/pos variables
    virtual bool followComboConnected() const { return true; }
    virtual bool followSequentConnected() const { return true; }
    static bool followComboConnected(const V3GraphEdge* edgep) {
	const OrderEdge* oedgep = dynamic_cast<const OrderEdge*>(edgep);
	if (!oedgep) v3fatalSrc("Following edge of non-OrderEdge type");
	return (oedgep->followComboConnected());
    }
    static bool followSequentConnected(const V3GraphEdge* edgep) {
	const OrderEdge* oedgep = dynamic_cast<const OrderEdge*>(edgep);
	if (!oedgep) v3fatalSrc("Following edge of non-OrderEdge type");
	return (oedgep->followSequentConnected());
    }
};

class OrderChangeDetEdge : public OrderEdge {
    // Edge created from variable to OrderLoopEndVertex
    // Indicates a change detect will be required for this loop construct
    OrderChangeDetEdge(V3Graph* graphp, V3GraphVertex* fromp, V3GraphVertex* top,
		       const OrderChangeDetEdge& old)
	: OrderEdge(graphp, fromp, top, old) {}
public:
    OrderChangeDetEdge(V3Graph* graphp, V3GraphVertex* fromp, V3GraphVertex* top)
	: OrderEdge(graphp, fromp, top, WEIGHT_MEDIUM, false) {}
    virtual OrderVEdgeType type() const { return OrderVEdgeType::EDGE_CHANGEDET; }
    virtual ~OrderChangeDetEdge() {}
    virtual OrderChangeDetEdge* clone(V3Graph* graphp, V3GraphVertex* fromp, V3GraphVertex* top) const {
	return new OrderChangeDetEdge(graphp, fromp, top, *this);
    }
    virtual string dotColor() const { return "blue"; }
};

class OrderComboCutEdge : public OrderEdge {
    // Edge created from output of combo logic
    // Breakable if the output var is also a input,
    // in which case we'll need a change detect loop around this var.
    OrderComboCutEdge(V3Graph* graphp, V3GraphVertex* fromp, V3GraphVertex* top,
		      const OrderComboCutEdge& old)
	: OrderEdge(graphp, fromp, top, old) {}
public:
    OrderComboCutEdge(V3Graph* graphp, V3GraphVertex* fromp, V3GraphVertex* top)
	: OrderEdge(graphp, fromp, top, WEIGHT_COMBO, CUTABLE) {}
    virtual OrderVEdgeType type() const { return OrderVEdgeType::EDGE_COMBOCUT; }
    virtual ~OrderComboCutEdge() {}
    virtual OrderComboCutEdge* clone(V3Graph* graphp, V3GraphVertex* fromp, V3GraphVertex* top) const {
	return new OrderComboCutEdge(graphp, fromp, top, *this);
    }
    virtual string dotColor() const { return "yellowGreen"; }
    virtual bool followComboConnected() const { return true; }
    virtual bool followSequentConnected() const { return true; }
};

class OrderPostCutEdge : public OrderEdge {
    // Edge created from output of post assignment
    // Breakable if the output var feeds back to input combo logic or another clock pin
    // in which case we'll need a change detect loop around this var.
    OrderPostCutEdge(V3Graph* graphp, V3GraphVertex* fromp, V3GraphVertex* top,
		     const OrderPostCutEdge& old)
	: OrderEdge(graphp, fromp, top, old) {}
public:
    OrderPostCutEdge(V3Graph* graphp, V3GraphVertex* fromp, V3GraphVertex* top)
	: OrderEdge(graphp, fromp, top, WEIGHT_COMBO, CUTABLE) {}
    virtual OrderVEdgeType type() const { return OrderVEdgeType::EDGE_POSTCUT; }
    virtual ~OrderPostCutEdge() {}
    virtual OrderPostCutEdge* clone(V3Graph* graphp, V3GraphVertex* fromp, V3GraphVertex* top) const {
	return new OrderPostCutEdge(graphp, fromp, top, *this);
    }
    virtual string dotColor() const { return "PaleGreen"; }
    virtual bool followComboConnected() const { return false; }
    virtual bool followSequentConnected() const { return true; }
};

class OrderPreCutEdge : public OrderEdge {
    // Edge created from var_PREVAR->consuming logic vertex
    // Always breakable, just results in performance loss
    // in which case we can't optimize away the pre/post delayed assignments
    OrderPreCutEdge(V3Graph* graphp, V3GraphVertex* fromp, V3GraphVertex* top,
		    const OrderPreCutEdge& old)
	: OrderEdge(graphp, fromp, top, old) {}
public:
    OrderPreCutEdge(V3Graph* graphp, V3GraphVertex* fromp, V3GraphVertex* top)
	: OrderEdge(graphp, fromp, top, WEIGHT_PRE, CUTABLE) {}
    virtual OrderVEdgeType type() const { return OrderVEdgeType::EDGE_PRECUT; }
    virtual OrderPreCutEdge* clone(V3Graph* graphp, V3GraphVertex* fromp, V3GraphVertex* top) const {
	return new OrderPreCutEdge(graphp, fromp, top, *this);
    }
    virtual ~OrderPreCutEdge() {}
    virtual string dotColor() const { return "khaki"; }
    virtual bool followComboConnected() const { return false; }
    virtual bool followSequentConnected() const { return false; }
};
