// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Possible targets of calls
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
//
// Builds a graph of the class inheritance hierarchy, and from it, the
// functions directly overriding each member function. A call may then
// resolve to the function called, and the functions overriding it,
// recursively.
//
// Only usable after V3Task and before V3Descope
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3CallTargets.h"

#include "V3Graph.h"

#include <algorithm>
#include <unordered_set>

VL_DEFINE_DEBUG_FUNCTIONS;

// Vertex of the class inheritance graph
class V3CallTargetsVertex final : public V3GraphVertex {
    VL_RTTI_IMPL(V3CallTargetsVertex, V3GraphVertex)
public:
    const AstClass* const m_classp;  // The class this vertex stands for

    V3CallTargetsVertex(V3Graph* const graphp, const AstClass* const classp)
        : V3GraphVertex{graphp}
        , m_classp{classp} {}
};

V3CallTargets::V3CallTargets() {
    // The class inheritance graph, only needed to find the overriding functions
    V3Graph graph;
    // Map from classes to their vertices
    std::unordered_map<const AstClass*, V3CallTargetsVertex*> clsp2Vtxp;
    const auto getVtxp = [&](const AstClass* const classp) {
        V3CallTargetsVertex*& vtxpr = clsp2Vtxp[classp];
        if (!vtxpr) vtxpr = new V3CallTargetsVertex{&graph, classp};
        return vtxpr;
    };

    // Build the graph: V3Class moved all classes, including nested ones, under the netlist
    for (AstNodeModule* const modp : v3Global.rootp()->modulespList()) {
        const AstClass* const classp = VN_CAST(modp, Class);
        if (!classp) continue;

        // Create the vertex of this class
        V3CallTargetsVertex* const vtxp = getVtxp(classp);

        // Add edges from base classes to this, the derived class
        for (const AstClassExtends* const extp : classp->extendspList()) {
            new V3GraphEdge{&graph, getVtxp(extp->classp()), vtxp, 1};
        }
    }

    // Topological sort, so base classes come before the classes derived from them
    graph.order();

    // The virtual functions visible in each class, by name: the nearest definitions in the class
    // or its base classes. There should be only one, as a class inheriting different methods of
    // the same name must declare its own (IEEE 1800-2023 8.26.6.1), but that's not currently
    // enforced.
    using Name2Funcs = std::unordered_map<std::string, std::vector<AstCFunc*>>;
    std::unordered_map<const V3GraphVertex*, Name2Funcs> visible;
    for (V3GraphVertex& vtx : graph.vertices()) {
        Name2Funcs& visibleInThis = visible[&vtx];

        // Those visible in the base classes are visible here too, unless overridden below
        for (const V3GraphEdge& edge : vtx.inEdges()) {
            for (const auto& item : visible.at(edge.fromp())) {
                std::vector<AstCFunc*>& funcps = visibleInThis[item.first];
                for (AstCFunc* const funcp : item.second) {
                    // Few (only when multiple base classes have the same function),
                    // so a linear search is fine. Interface classes can make the same
                    // function visible through several base classes.
                    if (std::find(funcps.begin(), funcps.end(), funcp) != funcps.end()) continue;
                    funcps.push_back(funcp);
                }
            }
        }

        // The member functions of the class are under its scope, find it
        const AstClass* const classp = vtx.as<V3CallTargetsVertex>()->m_classp;
        const AstScope* const scopep = [classp]() {
            for (AstNode* const memberp : classp->memberspList()) {
                if (const AstScope* const scopep = VN_CAST(memberp, Scope)) return scopep;
            }
            classp->v3fatalSrc("No scope under class");
        }();

        // The functions of this class override the visible functions of the same name, and are
        // then virtual too, even if the overriding function does not have the 'virtual' keyword
        for (AstNode* const blockp : scopep->blockspList()) {
            AstCFunc* const cfuncp = VN_CAST(blockp, CFunc);
            if (!cfuncp) continue;
            // Constructors are not dispatched virtually so no need to record them
            if (cfuncp->isConstructor()) continue;
            const auto it = visibleInThis.find(cfuncp->name());
            const bool overrides = it != visibleInThis.end();
            if (overrides) {
                for (AstCFunc* const basep : it->second) m_overriderps[basep].push_back(cfuncp);
            }
            if (overrides || cfuncp->isVirtual()) visibleInThis[cfuncp->name()] = {cfuncp};
        }
    }
}

std::unique_ptr<V3CallTargets> V3CallTargets::build() {
    return std::unique_ptr<V3CallTargets>{new V3CallTargets};
}

const std::vector<AstCFunc*>& V3CallTargets::getDynCallees(AstCFunc* const funcp) const {
    std::vector<AstCFunc*>& calleeps = m_dynamicCalleeps[funcp];
    // Empty means not computed yet (it always holds 'funcp' itself at least)
    if (!calleeps.empty()) return calleeps;

    calleeps.push_back(funcp);
    const auto it = m_overriderps.find(funcp);
    if (it == m_overriderps.end()) return calleeps;

    // Interface classes can override a function through several paths, so avoid duplicates
    std::unordered_set<const AstCFunc*> seen{funcp};
    for (AstCFunc* const overriderp : it->second) {
        for (AstCFunc* const cfuncp : getDynCallees(overriderp)) {
            if (seen.emplace(cfuncp).second) calleeps.push_back(cfuncp);
        }
    }
    return calleeps;
}

const std::vector<AstCFunc*>& V3CallTargets::getTargets(const AstNodeCCall* const callp) const {
    AstCFunc* const funcp = callp->funcp();
    // 'superReference' means it's a statically dispatched call, e.g.: 'Base::foo()'
    if (!callp->superReference()) return getDynCallees(funcp);
    std::vector<AstCFunc*>& calleeps = m_staticCalleeps[funcp];
    if (calleeps.empty()) calleeps.push_back(funcp);
    return calleeps;
}
