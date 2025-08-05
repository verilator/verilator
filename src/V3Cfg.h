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

class AstNode;
class BasicBlock;

//////////////////////////////////////////////////////////////////////////////
// ControlFlowGraph data structure
//////////////////////////////////////////////////////////////////////////////

// The control flow graph
class ControlFlowGraph final : public V3Graph {
    friend class CFGBuilder;
    BasicBlock* m_enterp;  // The singular entry vertex - set by CFGBuilder
    BasicBlock* m_exitp;  // The singular exit vertex - set by CFGBuilder
    size_t m_size;  // Number of blocks in this CFG - set by CFGBuilder

    // METHODS
    BasicBlock* addBasicBlock();
    void addEdge(BasicBlock* srcp, BasicBlock* dstp);

    // CONSTRUCTOR - via CFGBuilder only
    ControlFlowGraph();

public:
    // Can be destroyed by client code
    ~ControlFlowGraph() override = default;

    void foreach(std::function<void(const BasicBlock&)> f) const {
        for (const V3GraphVertex& vtx : vertices()) f(*vtx.as<BasicBlock>());
    }

    // Accessors
    BasicBlock& enter() const { return *m_enterp; }
    BasicBlock& exit() const { return *m_exitp; }
    size_t size() const { return m_size; }
};

// A basic block (verticies of the control flow graph)
class BasicBlock final : public V3GraphVertex {
    VL_RTTI_IMPL(BasicBlock, V3GraphVertex)
    friend class ControlFlowGraph;
    friend class CFGBuilder;

    std::vector<AstNode*> m_stmtps;  // statements in this basic block
    bool m_isEnter;  // Is entry block of CFG - for debug only - set by CFGBuilder
    bool m_isExit;  // Is exit block of CFG - for debug only - set by CFGBuilder
    uint32_t m_id;  // Unique ID of vertex (Reverse post-order index) - set by CFGBuilder

    int sortCmp(const V3GraphVertex* rhsp) const override {
        return m_id < rhsp->as<BasicBlock>()->m_id ? -1 : 1;
    }

    BasicBlock(ControlFlowGraph* graphp, bool isEnter, bool isExit)
        : V3GraphVertex{graphp}
        , m_isEnter{isEnter}
        , m_isExit{isExit}
        , m_id{std::numeric_limits<uint32_t>::max()}  // Will be reassigned in V3CfgBuilder
    {}
    ~BasicBlock() override = default;

public:
    void forEachSuccessor(std::function<void(const BasicBlock&)> f) const {
        for (const V3GraphEdge& edge : outEdges()) f(*edge.top()->as<BasicBlock>());
    }

    void forEachPredecessor(std::function<void(const BasicBlock&)> f) const {
        for (const V3GraphEdge& edge : inEdges()) f(*edge.fromp()->as<BasicBlock>());
    }

    std::vector<AstNode*>& stmtps() { return m_stmtps; }
    const std::vector<AstNode*>& stmtps() const { return m_stmtps; }

    uint32_t id() const { return m_id; }

    // Just for Graphviz dumps
    std::string name() const override;
    std::string dotShape() const override;
    std::string dotRank() const override;
};

// A control flow graph edge
class ControlFlowGraphEdge final : public V3GraphEdge {
    VL_RTTI_IMPL(ControlFlowGraphEdge, V3GraphEdge)
public:
    enum class Kind { ConditionTrue, ConditionFalse, Jump };

private:
    const Kind m_kind;  // Edge kind

public:
    ControlFlowGraphEdge(ControlFlowGraph* graphp, BasicBlock* srcp, BasicBlock* dstp, Kind kind)
        : V3GraphEdge{graphp, srcp, dstp, 1, false}
        , m_kind{kind} {}

    Kind kind() const { return m_kind; }

    std::string dotLabel() const override;
};

//////////////////////////////////////////////////////////////////////////////
// BasicBlockMap
//////////////////////////////////////////////////////////////////////////////

// Map from BasicBlock to a generic vale of type T_Value. As opposed to a
// std::map/std::unordered_map, in BasicBlockMap all entries are value
// initialized at construction. This can be improved but is sufficient for our
// current purposes.
template <typename T_Value>
class BasicBlockMap final {
    // The map, stored as a vector, indexed by BasicBlock::id();
    std::vector<T_Value> m_map;

public:
    BasicBlockMap(const ControlFlowGraph& cfg)
        : m_map{cfg.size()} {}

    T_Value& operator[](const BasicBlock& bb) { return m_map.at(bb.id()); }
    const T_Value& operator[](const BasicBlock& bb) const { return m_map.at(bb.id()); }
};

//////////////////////////////////////////////////////////////////////////////
// ControlFlowGraph functions
//////////////////////////////////////////////////////////////////////////////

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
