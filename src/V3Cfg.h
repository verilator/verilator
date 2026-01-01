// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Control flow graph (CFG)
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2026 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
//
// Control flow graph (CFG) and related data structures.
//
// A control flow graph is a directed graph with with basic blocks as
// vertices connected by control flow edges. A basic block is a sequence
// of statements that are always executed as a unit (there are no branches
// targeting the middle of a basic block). The last statement in a basic
// block is called the terminator statemet. The terminator statements are
// the control flow transfer statements (branches) in the program. In this
// implementation, an unconditoinal jump (goto) is implicit and not stored
// in the basic block. A consequence of the implicit jump is that a basic
// block might be empty (not contain any statements). Conditional branches
// are represented by storing the corresponding conditional AstNodeStmt as
// the last statement in the basic block. Most importantly, only the actual
// condition check (e.g.: the 'condp' part of an AstIf) and branch is
// executed in the host basic block, but not any of the body statements of
// the conditoinal. The control flow graph has 2 unique basic blocks. The
// 'enter' block is the unique entry point of the represented program. It
// has no predecessors and itself dominates all other basic blocks. The
// 'exit' block is the unique exit point. It has no successors, and itself
// post-dominates all other basic blocks.
//
// The current implementation is designed to be immutable after
// construction. This can be relaxed in the future if necessary, however
// it is unlikely to be necessary as we cannot as of now convert a control
// flow graph back to Ast or any other form of output. We can also only
// represent 2-way conditionals, therefore all basic blocks have up to 2
// successors. The exit block has 0, blocks terminated by an unconditional
// implicit jump have exactly 1, and blocks terminated by a conditional
// branch have exactly 2 successors.
//
// Basic blocks have a unique ID, these are assigned based on the reverse
// post-ordering of the basic blocks within the control flow graph, and
// therefore they define a topological ordering of the basic blocks. The
// basic blocks within the graph are stored in this order. This means that
// in control flow graphs without back edges (loops), a basic block is
// always stored after its predecessors.
//
//*************************************************************************

#ifndef VERILATOR_V3CFG_H_
#define VERILATOR_V3CFG_H_

#include "config_build.h"
#include "verilatedos.h"

#include "V3Ast.h"
#include "V3Graph.h"

#include <functional>
#include <limits>
#include <memory>
#include <vector>

//######################################################################
// Control Flow Graph (CFG) and related data structures

class CfgGraph;
class CfgBlock;
class CfgEdge;

template <typename T_Key, typename T_Value>
class CfgMap;
template <typename T_Value>
class CfgBlockMap;
template <typename T_Value>
class CfgEdgeMap;

//######################################################################
// CfgBlock - A basic block (verticies of the control flow graph)

class CfgBlock final : public V3GraphVertex {
    friend class CfgGraph;
    template <typename T_Key, typename T_Value>
    friend class CfgMap;
    friend class CfgBuilder;

    // STATE
    CfgGraph* const m_cfgp;  // The control flow graph this CfgBlock is under
    size_t m_rpoNumber = 0;  // Reverse post-order number and unique ID of this CfgBlock

    // V3GraphEdge::user() is set to the unique id by CfgBuilder
    std::vector<AstNodeStmt*> m_stmtps;  // statements in this CfgBlock

    // PRIVATE METHODS

    // CONSTRUCTOR/DESTRUCTOR - via CfgGraph only
    inline explicit CfgBlock(CfgGraph* cfgp);
    ~CfgBlock() override = default;

public:
    // PUBLIC METHODS

    // ID (reverse post-order number) of this block
    inline size_t id();
    inline size_t id() const;

    // Is this the entry block of the CFG?
    bool isEnter() const { return inEmpty(); }
    // Is this the exit block of the CFG?
    bool isExit() const { return outEmpty(); }
    // Is this a branching block (multiple successors)?
    bool isBranch() const { return outEdges().hasMultipleElements(); }
    // Is this a control flow convergence block (multiple predecessors)?
    bool isJoin() const { return inEdges().hasMultipleElements(); }
    // Is this a join of exactly 2 paths?
    bool isTwoWayJoin() const { return inEdges().hasTwoElements(); }

    // The edge going to the taken (or uncinditional) successor, or nullptr if exit block
    inline CfgEdge* takenEdgep();
    inline const CfgEdge* takenEdgep() const;
    // The edge going to the untaken successor, or nullptr if not a branch, or exit block
    inline CfgEdge* untknEdgep();
    inline const CfgEdge* untknEdgep() const;
    // The taken successor block, or nullptr if exit block
    inline CfgBlock* takenp();
    inline const CfgBlock* takenp() const;
    // The untakens successor block, or nullptr if not a branch, or exit block
    inline CfgBlock* untknp();
    inline const CfgBlock* untknp() const;

    // The first predecessor edge, or nullptr if enter block
    inline CfgEdge* firstPredecessorEdgep();
    inline const CfgEdge* firstPredecessorEdgep() const;
    // The last predecessor edge, or nullptr if enter block
    inline CfgEdge* lastPredecessorEdgep();
    inline const CfgEdge* lastPredecessorEdgep() const;
    // The first predecessor block, or nullptr if enter block
    inline CfgBlock* firstPredecessorp();
    inline const CfgBlock* firstPredecessorp() const;
    // The last predecessor block, or nullptr if enter block
    inline CfgBlock* lastPredecessorp();
    inline const CfgBlock* lastPredecessorp() const;

    // Statements in this CfgBlock
    const std::vector<AstNodeStmt*>& stmtps() const { return m_stmtps; }

    // Ordering is done on reverese post-order numbering. For loop-free graph
    // this ensures that a block that compares less than another is not a
    // successor of the other block (it is an ancestor, or sibling).
    bool operator<(const CfgBlock& that) const { return id() < that.id(); }
    bool operator>(const CfgBlock& that) const { return id() > that.id(); }
    bool operator==(const CfgBlock& that) const { return this == &that; }

    // Iterators
    void forEachSuccessor(std::function<void(const CfgBlock&)> f) const {
        for (const V3GraphEdge& edge : outEdges()) f(*static_cast<CfgBlock*>(edge.top()));
    }
    void forEachPredecessor(std::function<void(const CfgBlock&)> f) const {
        for (const V3GraphEdge& edge : inEdges()) f(*static_cast<CfgBlock*>(edge.fromp()));
    }

    // Source location for debugging
    FileLine* fileline() const override {
        return !m_stmtps.empty() ? m_stmtps.front()->fileline() : nullptr;
    }

    // For Graphviz dumps only
    std::string name() const override;
    std::string dotShape() const override;
    std::string dotRank() const override;
};

//######################################################################
// CfgEdge - An edges of the control flow graph

class CfgEdge final : public V3GraphEdge {
    friend class CfgGraph;
    template <typename T_Key, typename T_Value>
    friend class CfgMap;

    // STATE - Immutable after construction, set by CfgBuilder
    CfgGraph* const m_cfgp;  // The control flow graph this CfgEdge is under
    size_t m_id = 0;  // Unique ID of this vertex

    // PRIVATE METHODS

    // CONSTRUCTOR/DESTRUCTOR - via CfgGraph only
    inline CfgEdge(CfgGraph* graphp, CfgBlock* srcp, CfgBlock* dstp);
    ~CfgEdge() override = default;

public:
    // METHODS

    // Unique ID of this CfgEdge - no particular meaning
    inline size_t id();
    inline size_t id() const;

    // Source/destination CfgBlock
    const CfgBlock* srcp() const { return static_cast<const CfgBlock*>(fromp()); }
    const CfgBlock* dstp() const { return static_cast<const CfgBlock*>(top()); }
    CfgBlock* srcp() { return static_cast<CfgBlock*>(fromp()); }
    CfgBlock* dstp() { return static_cast<CfgBlock*>(top()); }

    // For Graphviz dumps only
    std::string dotLabel() const override;
};

//######################################################################
// CfgGraph - The control flow graph

class CfgGraph final : public V3Graph {
    friend class CfgBlock;
    friend class CfgEdge;
    template <typename T_Key, typename T_Value>
    friend class CfgMap;
    friend class CfgBuilder;

    // STATE
    size_t m_nEdits = 0;  // Edit count of this graph
    size_t m_nLastOrdered = 0;  // Last edit count blocks were ordered
    CfgBlock* m_enterp = nullptr;  // The singular entry vertex
    CfgBlock* m_exitp = nullptr;  // The singular exit vertex
    size_t m_nBlocks = 0;  // Number of CfgBlocks in this CfgGraph
    size_t m_nEdges = 0;  // Number of CfgEdges in this CfgGraph

    // PRIVATE METHODS

    // Compute reverse post-order enumeration of blocks, and sort them
    // accordingly. Assign blocks, and edge IDs. Invalidates all previous IDs.
    void rpoBlocks();

    // Add a new CfgBlock to this graph
    CfgBlock* addBlock() {
        ++m_nEdits;
        ++m_nBlocks;
        return new CfgBlock{this};
    }

    // Add a new taken (or unconditional) CfgEdge to this CFG
    void addTakenEdge(CfgBlock* srcp, CfgBlock* dstp) {
        UASSERT_OBJ(srcp->m_cfgp == this, srcp, "'srcp' is not in this graph");
        UASSERT_OBJ(dstp->m_cfgp == this, dstp, "'dstp' is not in this graph");
        UASSERT_OBJ(!srcp->takenEdgep(), srcp, "Taken edge should be added first");
        //
        UASSERT_OBJ(dstp != m_enterp, dstp, "Enter block cannot have a predecessor");
        UASSERT_OBJ(srcp != m_exitp, srcp, "Exit block cannot have a successor");
        ++m_nEdits;
        ++m_nEdges;
        new CfgEdge{this, srcp, dstp};
    }

    // Add a new untaken CfgEdge to this CFG
    void addUntknEdge(CfgBlock* srcp, CfgBlock* dstp) {
        UASSERT_OBJ(srcp->m_cfgp == this, srcp, "'srcp' is not in this graph");
        UASSERT_OBJ(dstp->m_cfgp == this, dstp, "'dstp' is not in this graph");
        UASSERT_OBJ(srcp->takenEdgep(), srcp, "Untaken edge should be added second");
        UASSERT_OBJ(srcp->takenp() != dstp, srcp, "Untaken branch targets the same block");
        //
        UASSERT_OBJ(dstp != m_enterp, dstp, "Enter block cannot have a predecessor");
        UASSERT_OBJ(srcp != m_exitp, srcp, "Exit block cannot have a successor");
        ++m_nEdits;
        ++m_nEdges;
        new CfgEdge{this, srcp, dstp};
    }

    size_t idOf(const CfgBlock* bbp) const {
        UASSERT_OBJ(m_nEdits == m_nLastOrdered, m_enterp, "Cfg was edited but not re-ordered");
        return bbp->m_rpoNumber;
    }

    size_t idOf(const CfgEdge* edgep) const {
        UASSERT_OBJ(m_nEdits == m_nLastOrdered, m_enterp, "Cfg was edited but not re-ordered");
        return edgep->m_id;
    }

    // Implementation for insertTwoWayJoins
    CfgBlock* getOrCreateTwoWayJoinFor(CfgBlock* bbp);

    // CONSTRUCTOR - use CfgGraph::build, which might fail, so this can't be public
    CfgGraph() = default;

public:
    ~CfgGraph() override = default;

    // STATIC FUNCTIONS

    // Build CFG for the given list of statements
    static std::unique_ptr<CfgGraph> build(AstNode* stmtsp);

    // PUBLIC METHODS

    // Accessors
    const CfgBlock& enter() const { return *m_enterp; }
    const CfgBlock& exit() const { return *m_exitp; }

    // Number of basic blocks in this graph
    size_t nBlocks() const { return m_nBlocks; }
    // Number of control flow edges in this graph
    size_t nEdges() const { return m_nEdges; }

    // Create a CfgBlock map for this graph
    template <typename T_Value>
    inline CfgBlockMap<T_Value> makeBlockMap() const;
    // Create a CfgEdgeMap map for this graph
    template <typename T_Value>
    inline CfgEdgeMap<T_Value> makeEdgeMap() const;

    // Returns true iff the graph contains a loop (back-edge)
    bool containsLoop() const;

    //------------------------------------------------------------------
    // The following methods mutate this CFG and invalidate CfgBlock and
    // CfgEdge IDs and associated CfgBlockMap, CfgEdgeMap and other
    // query instances.

    // Remove empty blocks, combine sequential blocks. Keeps the enter/exit block, even if empty.
    void minimize();

    // Insert empty blocks to fix critical edges (edges that have a source with
    // multiple successors, and a destination with multiple predecessors)
    void breakCriticalEdges();

    bool insertTwoWayJoins();
};

//######################################################################
// CfgMap - Map from CfgBlock or CfgEdge to generic values

template <typename T_Key, typename T_Value>
class CfgMap VL_NOT_FINAL {
    // As opposed to a std::map/std::unordered_map, all entries are value
    // initialized at construction, and the map is always dense. This can
    // be improved if necessary but is sufficient for our current purposes.

    const CfgGraph* m_cfgp;  // The control flow graph this map is for
    size_t m_created;  // Edit count of CFG this map was created at
    std::vector<T_Value> m_map;  // The map, stored as a vector

protected:
    // CONSTRUCTOR
    explicit CfgMap(const CfgGraph* cfgp, size_t size)
        : m_cfgp{cfgp}
        , m_created{cfgp->m_nEdits}
        , m_map{size} {}

public:
    // Can create an empty map
    CfgMap()
        : m_cfgp{nullptr}
        , m_created{0} {}

    // Copyable, movable
    CfgMap(const CfgMap<T_Key, T_Value>&) = default;
    CfgMap(CfgMap<T_Key, T_Value>&&) = default;
    CfgMap<T_Key, T_Value>& operator=(const CfgMap<T_Key, T_Value>&) = default;
    CfgMap<T_Key, T_Value>& operator=(CfgMap<T_Key, T_Value>&&) = default;

    T_Value& operator[](const T_Key& key) {
        UASSERT_OBJ(m_created == m_cfgp->m_nEdits, m_cfgp->m_enterp, "Map is stale");
        UASSERT_OBJ(m_cfgp == key.m_cfgp, m_cfgp->m_enterp, "Key not in this CFG");
        return m_map.at(key.id());
    }
    const T_Value& operator[](const T_Key& key) const {
        UASSERT_OBJ(m_created == m_cfgp->m_nEdits, m_cfgp->m_enterp, "Map is stale");
        UASSERT_OBJ(m_cfgp == key.m_cfgp, m_cfgp->m_enterp, "Key not in this CFG");
        return m_map.at(key.id());
    }
    T_Value& operator[](const T_Key* keyp) {
        UASSERT_OBJ(m_created == m_cfgp->m_nEdits, m_cfgp->m_enterp, "Map is stale");
        UASSERT_OBJ(m_cfgp == keyp->m_cfgp, m_cfgp->m_enterp, "Key not in this CFG");
        return m_map.at(keyp->id());
    }
    const T_Value& operator[](const T_Key* keyp) const {
        UASSERT_OBJ(m_created == m_cfgp->m_nEdits, m_cfgp->m_enterp, "Map is stale");
        UASSERT_OBJ(m_cfgp == keyp->m_cfgp, m_cfgp->m_enterp, "Key not in this CFG");
        return m_map.at(keyp->id());
    }
};

template <typename T_Value>
class CfgBlockMap final : public CfgMap<CfgBlock, T_Value> {
    friend class CfgGraph;
    // CONSTRUCTOR - Create one via CfgGraph::makeBlockMap
    explicit CfgBlockMap(const CfgGraph* cfgp)
        : CfgMap<CfgBlock, T_Value>{cfgp, cfgp->nBlocks()} {}

public:
    // Can create an empty map
    CfgBlockMap() = default;
    // Copyable, movable
    CfgBlockMap(const CfgBlockMap&) = default;
    CfgBlockMap(CfgBlockMap&&) = default;
    CfgBlockMap& operator=(const CfgBlockMap&) = default;
    CfgBlockMap& operator=(CfgBlockMap&&) = default;
};

template <typename T_Value>
class CfgEdgeMap final : public CfgMap<CfgEdge, T_Value> {
    friend class CfgGraph;
    // CONSTRUCTOR - Create one via CfgGraph::makeEdgeMap
    explicit CfgEdgeMap(const CfgGraph* cfgp)
        : CfgMap<CfgEdge, T_Value>{cfgp, cfgp->nEdges()} {}

public:
    // Can create an empty map
    CfgEdgeMap() = default;
    // Copyable, movable
    CfgEdgeMap(const CfgEdgeMap&) = default;
    CfgEdgeMap(CfgEdgeMap&&) = default;
    CfgEdgeMap& operator=(const CfgEdgeMap&) = default;
    CfgEdgeMap& operator=(CfgEdgeMap&&) = default;
};

//######################################################################
// Innline method definitions

// --- CfgBlock ---

CfgBlock::CfgBlock(CfgGraph* cfgp)
    : V3GraphVertex{cfgp}
    , m_cfgp{cfgp} {}

size_t CfgBlock::id() { return m_cfgp->idOf(this); }
size_t CfgBlock::id() const { return m_cfgp->idOf(this); }

// Successor edges
CfgEdge* CfgBlock::takenEdgep() {  // It's always the first edge
    return isExit() ? nullptr : static_cast<CfgEdge*>(outEdges().frontp());
}
const CfgEdge* CfgBlock::takenEdgep() const {  // It's always the first edge
    return isExit() ? nullptr : static_cast<const CfgEdge*>(outEdges().frontp());
}
CfgEdge* CfgBlock::untknEdgep() {  // It's always the second (last) edge
    return isBranch() ? static_cast<CfgEdge*>(outEdges().backp()) : nullptr;
}
const CfgEdge* CfgBlock::untknEdgep() const {  // It's always the second (last) edge
    return isBranch() ? static_cast<const CfgEdge*>(outEdges().backp()) : nullptr;
}
CfgBlock* CfgBlock::takenp() {
    return isExit() ? nullptr : static_cast<CfgBlock*>(outEdges().frontp()->top());
}
const CfgBlock* CfgBlock::takenp() const {
    return isExit() ? nullptr : static_cast<CfgBlock*>(outEdges().frontp()->top());
}
CfgBlock* CfgBlock::untknp() {
    return isBranch() ? static_cast<CfgBlock*>(outEdges().backp()->top()) : nullptr;
}
const CfgBlock* CfgBlock::untknp() const {
    return isBranch() ? static_cast<const CfgBlock*>(outEdges().backp()->top()) : nullptr;
}

// Predecessor edges
CfgEdge* CfgBlock::firstPredecessorEdgep() {  //
    return static_cast<CfgEdge*>(inEdges().frontp());
}
const CfgEdge* CfgBlock::firstPredecessorEdgep() const {  //
    return static_cast<const CfgEdge*>(inEdges().frontp());
}
CfgEdge* CfgBlock::lastPredecessorEdgep() {  //
    return static_cast<CfgEdge*>(inEdges().backp());
}
const CfgEdge* CfgBlock::lastPredecessorEdgep() const {  //
    return static_cast<const CfgEdge*>(inEdges().backp());
}
CfgBlock* CfgBlock::firstPredecessorp() {  //
    return isEnter() ? nullptr : firstPredecessorEdgep()->srcp();
}
const CfgBlock* CfgBlock::firstPredecessorp() const {  //
    return isEnter() ? nullptr : firstPredecessorEdgep()->srcp();
}
CfgBlock* CfgBlock::lastPredecessorp() {  //
    return isEnter() ? nullptr : lastPredecessorEdgep()->srcp();
}
const CfgBlock* CfgBlock::lastPredecessorp() const {  //
    return isEnter() ? nullptr : lastPredecessorEdgep()->srcp();
}

// --- CfgEdge ---

CfgEdge::CfgEdge(CfgGraph* cfgp, CfgBlock* srcp, CfgBlock* dstp)
    : V3GraphEdge{cfgp, srcp, dstp, 1, false}
    , m_cfgp{cfgp} {}

size_t CfgEdge::id() { return m_cfgp->idOf(this); }
size_t CfgEdge::id() const { return m_cfgp->idOf(this); }

// --- CfgGraph ---

template <typename T_Value>
CfgBlockMap<T_Value> CfgGraph::makeBlockMap() const {
    return CfgBlockMap<T_Value>{this};
}
template <typename T_Value>
CfgEdgeMap<T_Value> CfgGraph::makeEdgeMap() const {
    return CfgEdgeMap<T_Value>{this};
}

//######################################################################
// CfgDominatorTree

class CfgDominatorTree final {
    // STATE
    CfgBlockMap<const CfgBlock*> m_bb2Idom;  // Map from CfgBlock to its immediate dominator

    // PRIVATE METHODS

    // Part of algorithm to compute m_bb2Idom, see consructor
    const CfgBlock* intersect(const CfgBlock* ap, const CfgBlock* bp);

public:
    // CONSTRUCTOR
    explicit CfgDominatorTree(const CfgGraph& cfg);
    // Can create an empty map
    CfgDominatorTree() = default;
    // Copyable, movable
    CfgDominatorTree(const CfgDominatorTree&) = default;
    CfgDominatorTree(CfgDominatorTree&&) = default;
    CfgDominatorTree& operator=(const CfgDominatorTree&) = default;
    CfgDominatorTree& operator=(CfgDominatorTree&&) = default;

    // PUBLIC METHODS

    // Return unique CfgBlock that dominates both of the given blocks, but does
    // not strictly dominate any other block that dominates both blocks. It
    // will return 'ap' or 'bp' if one dominates the other (or are the same)
    const CfgBlock* closestCommonDominator(const CfgBlock* ap, const CfgBlock* bp) const {
        while (ap != bp) {
            if (*ap < *bp) {
                bp = m_bb2Idom[bp];
            } else {
                ap = m_bb2Idom[ap];
            }
        }
        return ap;
    }

    // Returns true if 'ap' dominates 'bp'
    bool dominates(const CfgBlock* const ap, const CfgBlock* bp) {
        // Walk up the dominator tree from 'bp' until reaching 'ap' or the root
        while (true) {
            // True if 'ap' is above (or same as) 'bp'
            if (ap == bp) return true;
            // Step up the dominator tree
            bp = m_bb2Idom[bp];
            // False if reached the root
            if (!bp) return false;
        }
    }
};

//######################################################################
// V3Cfg

namespace V3Cfg {

// Compute AstVars live on entry to given CFG. That is, variables that might
// be read before wholly assigned in the CFG. Returns nullptr if the analysis
// failed due to unhandled statements or data types involved in the CFG.
// On success, returns a vector of AstVar or AstVarScope nodes live on entry.
std::unique_ptr<std::vector<AstVar*>> liveVars(const CfgGraph&);

// Same as liveVars, but return AstVarScopes insted
std::unique_ptr<std::vector<AstVarScope*>> liveVarScopes(const CfgGraph&);

}  //namespace V3Cfg

#endif  // VERILATOR_V3CFG_H_
