// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Virtual function calls - function finder
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2003-2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#ifndef VERILATOR_V3VIRTUAL_H_
#define VERILATOR_V3VIRTUAL_H_

#include "config_build.h"
#include "verilatedos.h"

#include "V3Ast.h"
#include "V3Graph.h"

#include <memory>
#include <unordered_map>
#include <unordered_set>

//============================================================================

class V3ClassGraphVertex;

// Graph of classes - build by V3Virtual::buildClassGraph() and used to get CFuncs that may be
// called by a AstNodeCCall (due to virtualization)
class V3ClassesGraphWrapper final {
    friend class ClassGraphBuilderVisitor;

    const std::unique_ptr<V3Graph> m_graphp;  // graph of classes
    const std::unordered_map<const AstClass*, V3ClassGraphVertex*>
        m_vertexMap;  // Map from AstClass to a corresponding vertex
    const std::unordered_set<AstCFunc*>
        m_emptySet;  // Always empty set - used to return a reference to an empty set

    V3ClassesGraphWrapper(std::unique_ptr<V3Graph> graph,
                          std::unordered_map<const AstClass*, V3ClassGraphVertex*> vertexMap);

public:
    ~V3ClassesGraphWrapper();

    // Returns possible CFuncs that may be called due to a NodeCCall passed as a callp argument
    // Warning: returned set may be empty if NodeCCall is a New call or a super call - in such
    // cases only `callp->funcp()` may be called. Also, if callp is to a non-member function the
    // set will be empty - post V3Task static functions are not member functions anymore.
    const std::unordered_set<AstCFunc*>&
    getCallPossibleCFuncs(const AstNodeCCall* const callp) const&;
};

class V3Virtual final {
public:
    static std::unique_ptr<V3ClassesGraphWrapper> buildClassGraph(AstNetlist*);
};

#endif  // Guard
