// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Graph automata base class
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

#ifndef _V3GRAPHDFA_H_
#define _V3GRAPHDFA_H_ 1
#include "config_build.h"
#include "verilatedos.h"
#include <vector>

#include "V3Global.h"
#include "V3Graph.h"

class DfaGraph;
class DfaVertex;
class DfaEdge;

//=============================================================================
// NFA/DFA Graphs
/// 	The NFA graph consists of:
///		DfaVertex(START)	The starting point
///		DfaVertex()		Interior states
///		DfaVertex(ACCEPT)	The completion point
///
/// Transitions include a list of all inputs (arbitrary user pointers),
/// or epsilon, represented as a empty list of inputs.
///
/// We're only looking for matches, so the only accepting states are
/// at the end of the transformations.  (If we want the complement, we
/// call complement and the algorithm makes a REJECT state, then flips
/// accept and reject for you.)
///
/// Common transforms:
///
///	"*":	DfaVertex(START) --> [epsilon] -->DfaVertex(ACCEPT)
///
///	"L":	...->[ON_L]-->DfaVtx-->[epsilon]-->DfaVtx(ACCEPT)
///
///	"LR":	...->[ON_L]-->DfaVtx-->[epsilon]-->DfaVtx(ACCEPT)
///		   ->[ON_R]-->DfaVtx-->[epsilon]-/
///
///	"L|R":	...->DfaVtx-->[epsilon]-->DfaVtx-->[ON_L]-->DfaVtx()->[epsilon]-->DfaVtx(ACCEPT)
///			   \->[epsilon]-->DfaVtx-->[ON_R]-->DfaVtx()->[epsilon]-/
///
///	"L*":	...->DfaVtx-->[epsilon]-->DfaVtx-->[ON_L]-->DfaVtx()->[epsilon]-->DfaVtx(ACCEPT)
///			   |  		     ^\----[epsilon]<-------/		|
///			   \->[epsilon]-----------------------------------------/

class DfaGraph : public V3Graph {
    // STATE
public:
    DfaGraph() {}
    virtual ~DfaGraph() {}

    // METHODS
    /// Find start node
    DfaVertex* findStart();

    /// Convert automata: NFA to DFA
    void nfaToDfa();

    /// Simplify a DFA automata
    void dfaReduce();

    /// Complement result (must already be dfa)
    void dfaComplement();
};

//=============================================================================
// Vertex

class DfaVertex : public V3GraphVertex {
    // Each DFA state is captured in this vertex.
    // Start and accepting are members, rather than the more intuitive
    // subclasses, as subclassing them would make it harder to inherit from here.
    bool	m_start;	// Start state
    bool	m_accepting;	// Accepting state?
public:
    // CONSTRUCTORS
    DfaVertex(DfaGraph* graphp, bool start=false, bool accepting=false)
	: V3GraphVertex(graphp)
	, m_start(start), m_accepting(accepting) {}
    using V3GraphVertex::clone;  // We are overriding, not overloading clone(V3Graph*)
    virtual DfaVertex* clone(DfaGraph* graphp) {
	return new DfaVertex(graphp, start(), accepting()); }
    virtual ~DfaVertex() {}
    // ACCESSORS
    virtual string dotShape() const { return (accepting()?"doublecircle":""); }
    virtual string dotColor() const { return start()?"blue":(color()?"red":"black"); }
    bool start() const { return m_start; }
    void start(bool flag) { m_start=flag; }
    bool accepting() const { return m_accepting; }
    void accepting(bool flag) { m_accepting=flag; }
};

//============================================================================
/// Abstract type indicating a specific "input" to the NFA
typedef AstNUser* DfaInput;

//============================================================================
// Edge types

class DfaEdge : public V3GraphEdge {
    DfaInput	m_input;
    bool	m_complement;	// Invert value when doing compare
public:
    static DfaInput EPSILON() { return NULL; }
    static DfaInput NA() { return AstNUser::fromInt(1); }	// as in not-applicable
    // CONSTRUCTORS
    DfaEdge(DfaGraph* graphp, DfaVertex* fromp, DfaVertex* top, DfaInput input)
	: V3GraphEdge(graphp, fromp, top, 1)
	, m_input(input), m_complement(false) {}
    DfaEdge(DfaGraph* graphp, DfaVertex* fromp, DfaVertex* top, const DfaEdge* copyfrom)
	: V3GraphEdge(graphp, fromp, top, copyfrom->weight())
	, m_input(copyfrom->input()), m_complement(copyfrom->complement()) {}
    virtual ~DfaEdge() {}
    // METHODS
    virtual string dotColor() const {
	return (na() ? "yellow"
		: epsilon() ? "green"
		: "black"); }
    virtual string dotLabel() const {
	return (na() ? ""
		: epsilon() ? "e"
		: complement() ? ("not "+cvtToStr((void*)(input())))
		: cvtToStr((void*)(input()))); }
    virtual string dotStyle() const { return (na()||cutable())?"dashed":""; }
    bool epsilon() const { return input()==EPSILON(); }
    bool na() const { return input()==NA(); }
    bool complement() const { return m_complement; }
    void complement(bool value) { m_complement=value; }
    DfaInput	input() const { return m_input; }
};

//============================================================================

#endif // Guard
