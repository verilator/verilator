// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Control flow graph (CFG) implementation
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
//  Control flow graph (CFG) implementation
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3Cfg.h"

#include "V3Ast.h"
#include "V3EmitV.h"

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// ControlFlowGraph method definitions
//######################################################################

ControlFlowGraph::ControlFlowGraph()
    : V3Graph{}
    , m_enterp{new BasicBlock{this, true, false}}
    , m_exitp{new BasicBlock{this, false, true}}
    , m_size{std::numeric_limits<size_t>::max()}  // Will be reassigned in V3CfgBuilder
{}

//######################################################################
// BasicBlock method definitions
//######################################################################

std::string BasicBlock::name() const {
    std::stringstream ss;
    ss << "BB " + std::to_string(m_id) + ":\n";
    for (AstNode* nodep : m_stmtps) {
        if (AstIf* const ifp = VN_CAST(nodep, If)) {
            ss << "if (";
            V3EmitV::debugVerilogForTree(ifp->condp(), ss);
            ss << ") ...";
        } else if (AstWhile* const whilep = VN_CAST(nodep, While)) {
            ss << "while (";
            V3EmitV::debugVerilogForTree(whilep->condp(), ss);
            ss << ") ...";
        } else {
            V3EmitV::debugVerilogForTree(nodep, ss);
        }
    }
    std::string text = VString::replaceSubstr(ss.str(), "\n", "\\l        ");
    if (m_isEnter) text = "**ENTER**\n" + text;
    if (m_isExit) text = text + "\n**EXIT**";
    return text;
}
std::string BasicBlock::dotShape() const { return "rect"; }
std::string BasicBlock::dotRank() const {
    if (m_isEnter) return "source";
    if (m_isExit) return "sink";
    return "";
}

//######################################################################
// ControlFlowGraphEdge method definitions
//######################################################################

std::string ControlFlowGraphEdge::dotLabel() const {
    switch (m_kind) {
    case Kind::ConditionTrue: return "T";
    case Kind::ConditionFalse: return "F";
    default: return "";
    }
}
