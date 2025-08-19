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

bool ControlFlowGraph::containsLoop() const {
    for (const V3GraphVertex& vtx : vertices()) {
        const BasicBlock& current = static_cast<const BasicBlock&>(vtx);
        for (const V3GraphEdge& edge : current.outEdges()) {
            const BasicBlock& successor = *static_cast<const BasicBlock*>(edge.top());
            // IDs are the reverse post-order numbering, so easy to check for a back-edge
            if (successor.id() < current.id()) return true;
        }
    }
    return false;
}

//######################################################################
// BasicBlock method definitions

std::string BasicBlock::name() const {
    std::stringstream ss;
    ss << "BB " + std::to_string(id()) + ":\n";
    for (AstNode* nodep : m_stmtps) {
        if (const AstIf* const ifp = VN_CAST(nodep, If)) {
            ss << "if (";
            V3EmitV::debugVerilogForTree(ifp->condp(), ss);
            ss << ") ...";
        } else if (const AstWhile* const whilep = VN_CAST(nodep, While)) {
            ss << "while (";
            V3EmitV::debugVerilogForTree(whilep->condp(), ss);
            ss << ") ...";
        } else {
            V3EmitV::debugVerilogForTree(nodep, ss);
        }
    }
    std::string text = VString::replaceSubstr(ss.str(), "\n", "\\l        ");
    if (inEmpty()) text = "**ENTER**\n" + text;
    if (outEmpty()) text = text + "\n**EXIT**";
    return text;
}
std::string BasicBlock::dotShape() const { return "rect"; }
std::string BasicBlock::dotRank() const {
    if (inEmpty()) return "source";
    if (outEmpty()) return "sink";
    return "";
}

//######################################################################
// ControlFlowEdge method definitions

std::string ControlFlowEdge::dotLabel() const {
    std::string label = "E" + std::to_string(id());
    const BasicBlock& source = *fromp()->as<BasicBlock>();
    const ControlFlowEdge* const untknp = source.untknEdgep();
    if (this == untknp) {
        label += " / F";
    } else if (untknp) {
        label += " / T";
    }
    return label;
}
