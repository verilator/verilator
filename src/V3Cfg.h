// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Control flow graph (CFG)
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2025 by Wilson Snyder. This program is free software; you
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
// DenseMap - This can be made generic if needed

// Map from unique non-negative integers (IDs) to generic values. As opposed
// to a std::map/std::unordered_map, in DenseMap, all entries are value
// initialized at construction, and the map is always dense. This can be
// improved if necessary but is sufficient for our current purposes.
template <typename T_Key, size_t (T_Key::*Index)() const, typename T_Value>
class DenseMap final {
    std::vector<T_Value> m_map;  // The map, stored as a vector

public:
    // CONSTRUCTOR
    explicit DenseMap(size_t size)
        : m_map{size} {}

    T_Value& operator[](const T_Key& key) { return m_map.at((key.*Index)()); }
    const T_Value& operator[](const T_Key& key) const { return m_map.at((key.*Index)()); }
};

//######################################################################
// ControlFlowGraph data structure

class ControlFlowGraph;
class BasicBlock;
class ControlFlowEdge;

// A basic block (verticies of the control flow graph)
class BasicBlock final : public V3GraphVertex {
    VL_RTTI_IMPL(BasicBlock, V3GraphVertex)
    friend class CfgBuilder;

    // STATE - Immutable after construction, set by CfgBuilder
    // V3GraphEdge::user() is set to the unique id by CfgBuilder
    std::vector<AstNodeStmt*> m_stmtps;  // statements in this BasicBlock

    // CONSTRUCTOR - via CfgBuilder only
    inline explicit BasicBlock(ControlFlowGraph* graphp);
    ~BasicBlock() override = default;

public:
    // METHODS - all const

    // Statements in this BasicBlock
    const std::vector<AstNodeStmt*>& stmtps() const { return m_stmtps; }
    // Unique ID of this BasicBlock - defines topological ordering
    size_t id() const { return V3GraphVertex::user(); }

    // The edge corresponding to the terminator branch being taken (including unonditoinal goto)
    inline const ControlFlowEdge* takenEdgep() const;
    // The edge corresponding to the terminator branch being not taken (or nullptr if goto)
    inline const ControlFlowEdge* untknEdgep() const;
    // Same as takenpEdgep/untknEdgep but returns the successor basic blocks
    inline const BasicBlock* takenSuccessorp() const;
    inline const BasicBlock* untknSuccessorp() const;

    void forEachSuccessor(std::function<void(const BasicBlock&)> f) const {
        for (const V3GraphEdge& edge : outEdges()) f(*edge.top()->as<BasicBlock>());
    }

    void forEachPredecessor(std::function<void(const BasicBlock&)> f) const {
        for (const V3GraphEdge& edge : inEdges()) f(*edge.fromp()->as<BasicBlock>());
    }

    FileLine* fileline() const override {
        return !m_stmtps.empty() ? m_stmtps.front()->fileline() : nullptr;
    }

    // For Graphviz dumps only
    std::string name() const override;
    std::string dotShape() const override;
    std::string dotRank() const override;
};

// A control flow graph edge
class ControlFlowEdge final : public V3GraphEdge {
    VL_RTTI_IMPL(ControlFlowEdge, V3GraphEdge)
    friend class CfgBuilder;

    // STATE - Immutable after construction, set by CfgBuilder
    // V3GraphEdge::user() is set to the unique id by CfgBuilder

    // CONSTRUCTOR - via CfgBuilder only
    inline ControlFlowEdge(ControlFlowGraph* graphp, BasicBlock* srcp, BasicBlock* dstp);
    ~ControlFlowEdge() override = default;

public:
    // METHODS - all const

    // Unique ID of this ControlFlowEdge - no particular meaning
    size_t id() const { return user(); }

    // Source/destination BasicBlock
    const BasicBlock& src() const { return *static_cast<BasicBlock*>(fromp()); }
    const BasicBlock& dst() const { return *static_cast<BasicBlock*>(top()); }

    // For Graphviz dumps only
    std::string dotLabel() const override;
};

template <typename T_Value>
using BasicBlockMap = DenseMap<BasicBlock, &BasicBlock::id, T_Value>;

template <typename T_Value>
using ControlFlowEdgeMap = DenseMap<ControlFlowEdge, &ControlFlowEdge::id, T_Value>;

// The control flow graph
class ControlFlowGraph final : public V3Graph {
    friend class CfgBuilder;

    // STATE - Immutable after construction, set by CfgBuilder
    BasicBlock* m_enterp = nullptr;  // The singular entry vertex
    BasicBlock* m_exitp = nullptr;  // The singular exit vertex
    size_t m_nBasicBlocks = 0;  // Number of BasicBlocks in this ControlFlowGraph
    size_t m_nEdges = 0;  // Number of ControlFlowEdges in this ControlFlowGraph

    // CONSTRUCTOR - via CfgBuilder only
    ControlFlowGraph() = default;

public:
    ~ControlFlowGraph() override = default;

    // METHODS
    void foreach(std::function<void(const BasicBlock&)> f) const {
        for (const V3GraphVertex& vtx : vertices()) f(*vtx.as<BasicBlock>());
    }

    // Accessors
    const BasicBlock& enter() const { return *m_enterp; }
    const BasicBlock& exit() const { return *m_exitp; }

    // Number of basic blocks in this graph
    size_t nBasicBlocks() const { return m_nBasicBlocks; }
    // Number of control flow edges in this graph
    size_t nEdges() const { return m_nEdges; }

    // Create a BasicBlock map for this graph
    template <typename T_Value>
    BasicBlockMap<T_Value> makeBasicBlockMap() const {
        return BasicBlockMap<T_Value>{nBasicBlocks()};
    }
    // Create a ControlFlowEdgeMap map for this graph
    template <typename T_Value>
    ControlFlowEdgeMap<T_Value> makeEdgeMap() const {
        return ControlFlowEdgeMap<T_Value>{nEdges()};
    }

    // Returns true iff the graph contains a loop (back-edge)
    bool containsLoop() const;
};

//######################################################################
// Inline method definitions

BasicBlock::BasicBlock(ControlFlowGraph* cfgp)
    : V3GraphVertex{cfgp} {}

const ControlFlowEdge* BasicBlock::takenEdgep() const {
    // It's always the first edge
    const V3GraphEdge* const frontp = outEdges().frontp();
    return static_cast<const ControlFlowEdge*>(frontp);
}

const ControlFlowEdge* BasicBlock::untknEdgep() const {
    // It's always the second (last) edge
    const V3GraphEdge* const frontp = outEdges().frontp();
    const V3GraphEdge* const backp = outEdges().backp();
    return backp != frontp ? static_cast<const ControlFlowEdge*>(backp) : nullptr;
}

const BasicBlock* BasicBlock::takenSuccessorp() const {
    const ControlFlowEdge* const edgep = takenEdgep();
    return edgep ? static_cast<const BasicBlock*>(edgep->top()) : nullptr;
}

const BasicBlock* BasicBlock::untknSuccessorp() const {
    const ControlFlowEdge* const edgep = untknEdgep();
    return edgep ? static_cast<const BasicBlock*>(edgep->top()) : nullptr;
}

ControlFlowEdge::ControlFlowEdge(ControlFlowGraph* graphp, BasicBlock* srcp, BasicBlock* dstp)
    : V3GraphEdge{graphp, srcp, dstp, 1, false} {}

//######################################################################
// ControlFlowGraph functions

namespace V3Cfg {
// Build control flow graph for given node
std::unique_ptr<const ControlFlowGraph> build(const AstNodeProcedure*);

// Compute AstVars live on entry to given CFG. That is, variables that might
// be read before wholly assigned in the CFG. Returns nullptr if the analysis
// failed due to unhandled statements or data types involved in the CFG.
// On success, returns a vector of AstVar or AstVarScope nodes live on entry.
std::unique_ptr<std::vector<AstVar*>> liveVars(const ControlFlowGraph&);

// Same as liveVars, but return AstVarScopes insted
std::unique_ptr<std::vector<AstVarScope*>> liveVarScopes(const ControlFlowGraph&);
}  //namespace V3Cfg

#endif  // VERILATOR_V3CFG_H_
