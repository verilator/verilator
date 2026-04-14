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

FsmStateVertex* FsmGraph::findStateVertex(int value) const {
    const auto it = m_stateVertices.find(value);
    return it == m_stateVertices.end() ? nullptr : it->second;
}

FsmStateVertex* FsmGraph::addStateVertex(string label, int value) {
    if (FsmStateVertex* const existingp = findStateVertex(value)) return existingp;
    FsmStateVertex* const vertexp = new FsmStateVertex{this, label, value};
    m_stateVertices.emplace(value, vertexp);
    return vertexp;
}

FsmPseudoVertex* FsmGraph::resetAnyVertex() {
    if (!m_resetVertexp) m_resetVertexp = new FsmPseudoVertex{this, FsmVertex::Kind::RESET_ANY, "ANY"};
    return m_resetVertexp;
}

FsmPseudoVertex* FsmGraph::defaultAnyVertex() {
    if (!m_defaultVertexp) {
        m_defaultVertexp = new FsmPseudoVertex{this, FsmVertex::Kind::DEFAULT_ANY, "default"};
    }
    return m_defaultVertexp;
}

FsmArcEdge* FsmGraph::addArc(int fromValue, int toValue, bool isReset, bool isCond, bool isDefault,
                             FileLine* flp) {
    FsmStateVertex* const top = findStateVertex(toValue);
    if (!top) return nullptr;
    FsmVertex* fromp = nullptr;
    if (isReset) {
        fromp = resetAnyVertex();
    } else if (isDefault) {
        fromp = defaultAnyVertex();
    } else {
        fromp = findStateVertex(fromValue);
        if (!fromp) return nullptr;
    }
    return new FsmArcEdge{this, fromp, top, isReset, isCond, isDefault, flp};
}
