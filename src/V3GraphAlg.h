// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Graph algorithm base class
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2022 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#ifndef VERILATOR_V3GRAPHALG_H_
#define VERILATOR_V3GRAPHALG_H_

#include "config_build.h"
#include "verilatedos.h"

#include "V3Global.h"
#include "V3Graph.h"

//=============================================================================
// Algorithms - common class
// For internal use, most graph algorithms use this as a base class

template <class T_Graph = V3Graph>  // Or sometimes const V3Graph
class GraphAlg VL_NOT_FINAL {
protected:
    T_Graph* const m_graphp;  // Graph we're operating upon
    const V3EdgeFuncP m_edgeFuncp;  // Function that says we follow this edge
    // CONSTRUCTORS
    GraphAlg(T_Graph* graphp, V3EdgeFuncP edgeFuncp)
        : m_graphp{graphp}
        , m_edgeFuncp{edgeFuncp} {}
    ~GraphAlg() = default;
    // METHODS
    inline bool followEdge(V3GraphEdge* edgep) {
        return (edgep->weight() && (m_edgeFuncp)(edgep));
    }
};

//============================================================================

#endif  // Guard
