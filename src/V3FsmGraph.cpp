// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: FSM coverage graph helpers
//
// Code available from: https://verilator.org
//
//*************************************************************************
// The graph object is the shared in-memory state between the adjacent detect
// and lower phases in V3FsmDetect.cpp.
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "V3PchAstNoMT.h"

#include "V3FsmGraph.h"

FsmGraph::FsmGraph() {
    m_resetVertexp = new FsmPseudoVertex{this, FsmVertex::Kind::RESET_ANY, "ANY"};
    m_defaultVertexp = new FsmPseudoVertex{this, FsmVertex::Kind::DEFAULT_ANY, "default"};
}

FsmStateVertex* FsmGraph::addStateVertex(string label, int value) {
    FsmStateVertex* const vertexp = new FsmStateVertex{this, label, value};
    m_stateVertices.emplace(value, vertexp);
    return vertexp;
}

FsmPseudoVertex* FsmGraph::resetAnyVertex() { return m_resetVertexp; }

FsmPseudoVertex* FsmGraph::defaultAnyVertex() { return m_defaultVertexp; }

FsmArcEdge* FsmGraph::addArc(int fromValue, int toValue, bool isReset, bool isCond, bool isDefault,
                             FileLine* flp) {
    FsmStateVertex* const top = m_stateVertices.at(toValue);
    FsmVertex* fromp = nullptr;
    if (isReset) {
        fromp = resetAnyVertex();
    } else if (isDefault) {
        fromp = defaultAnyVertex();
    } else {
        fromp = m_stateVertices.at(fromValue);
    }
    return new FsmArcEdge{this, fromp, top, isReset, isCond, isDefault, flp};
}
