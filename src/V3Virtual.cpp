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
//
// Builds a graph of inheritance (implements & extends)
// Allows for lookups of what AstCFunc may be called
// due to a virtual function call
//
// Current limitation: This only may be called after V3Task
// when AstNodeFTasks are substituted with AstCFuncs
//
//*************************************************************************
// TODO:
//  - Probably in future this phase shall have a check for overriding
//    virtual functions with static functions - currently
//    there is no such check - it shall happen before V3Task
//    since it moves static functions outside classes
//  - This shall check for error that is currently emitted in V3LinkDot
//    `Class 'Derived' implements 'Base' but is missing implementation
//     for 'function' (IEEE 1800-2023 8.26)`
//    Sometimes this error is emitted and it is a false positive
//    since the following snipped is correct but Verilator emits an error:
//
//      class Base;
//        virtual task foo();
//        endtask
//      endclass
//
//      interface class Iface;
//        pure virtual task foo();
//      endclass
//
//      class Derived extends Base implements Iface;
//        // This is legal as it is but Verilator fails
//      endclass
//
//    Mentioned `IEEE 1800-2023 8.26` says:
//    `When an interface class is implemented by a class, the required
//     implementations of interface class methods may be
//     provided by inherited virtual method implementations.`
//
//  Therefore, this shall probably become a full phase
//  and check for those errors somewhere before V3Task
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Virtual.h"

VL_DEFINE_DEBUG_FUNCTIONS;

class V3ClassGraphVertex final : public V3GraphVertex {
    VL_RTTI_IMPL(V3ClassGraphVertex, V3GraphVertex)
    friend class ClassGraphBuilderVisitor;
    enum Virtualization : uint8_t {
        NON_VIRTUAL = 0,  // Not a virtual member function
        VIRTUAL_IMPLICIT,  // virtual keyword is not next to a function definition the ancestor
                           // class has such virtual function therefore, it is treated as an
                           // virtual
        VIRTUAL,  // function explicitly defined as virtual with a keyword
        UNDEFINED_VIRTUAL,  // Function not declared in a current class however, it is inherited
                            // and it is virtual
        // Note: non-virtual inherited function may not be described with this enum - no need for
        // now as well as static functions
    };
    struct FuncInfo final {
        AstCFunc* const m_cfuncp;  // pointer to a described function
        std::unordered_set<AstCFunc*>
            m_cache;  // set of functions that may be called due to a virtual call
        Virtualization m_virtualization;  // Whether function is virtual (see Virtualization)
        bool m_cacheInitialized;  // true when m_cache stores a valid value
        FuncInfo()
            : m_cfuncp{nullptr}
            , m_virtualization{UNDEFINED_VIRTUAL}
            , m_cacheInitialized{false} {}
        FuncInfo(AstCFunc* const cfuncp, Virtualization virtualization)
            : m_cfuncp{cfuncp}
            , m_virtualization{virtualization}
            , m_cacheInitialized{false} {}
    };
    std::unordered_map<std::string, FuncInfo>
        m_funcsVirtualization;  // Map from function names to their description
    const AstClass* const m_classp;  // A class of which the function is a member of

public:
    explicit V3ClassGraphVertex(V3Graph* const graphp, const AstClass* const classp)
        : V3GraphVertex{graphp}
        , m_classp{classp} {}
    ~V3ClassGraphVertex() override = default;

    std::string name() const override { return m_classp->name(); }

    void addFunc(AstCFunc* const cfuncp) {
        m_funcsVirtualization.emplace(cfuncp->name(),
                                      FuncInfo{cfuncp, cfuncp->isVirtual()
                                                           ? V3ClassGraphVertex::VIRTUAL
                                                           : V3ClassGraphVertex::NON_VIRTUAL});
    }
    void propagateVirt(const V3ClassGraphVertex& from) {
        for (auto funcs : from.m_funcsVirtualization) {
            if (funcs.second.m_virtualization == NON_VIRTUAL) continue;
            auto& vertex = m_funcsVirtualization[funcs.first];
            if (vertex.m_virtualization == NON_VIRTUAL) vertex.m_virtualization = VIRTUAL_IMPLICIT;
        }
    }
    const std::unordered_set<AstCFunc*>& getCallPossibleCFuncs(const std::string& name) & {
        auto it = m_funcsVirtualization.find(name);
        UASSERT(it != m_funcsVirtualization.end(),
                "Unexpected call - CFunc with name '" << name << "' not found");
        FuncInfo& info = it->second;
        if (!info.m_cacheInitialized) {
            if (info.m_cfuncp) info.m_cache.insert(info.m_cfuncp);
            if (info.m_virtualization != V3ClassGraphVertex::NON_VIRTUAL) {
                for (V3GraphEdge& edge : outEdges()) {
                    V3ClassGraphVertex* const other = edge.top()->as<V3ClassGraphVertex>();
                    const std::unordered_set<AstCFunc*> otherCalls
                        = other->getCallPossibleCFuncs(name);
                    info.m_cache.insert(otherCalls.begin(), otherCalls.end());
                }
            }
            info.m_cacheInitialized = true;
        }
        return info.m_cache;
    }
};

V3ClassesGraphWrapper::V3ClassesGraphWrapper(
    std::unique_ptr<V3Graph> graph,
    std::unordered_map<const AstClass*, V3ClassGraphVertex*> vertexMap)
    : m_graphp{std::move(graph)}
    , m_vertexMap{std::move(vertexMap)} {}
V3ClassesGraphWrapper::~V3ClassesGraphWrapper()
    = default;  // Must be here because only this translation unit actually knows size
                // of the V3ClassGraphVertex which is needed for ~unique_ptr()

const std::unordered_set<AstCFunc*>&
V3ClassesGraphWrapper::getCallPossibleCFuncs(const AstNodeCCall* const callp) const& {
    // super references and AstCNew shall have AstNodeCCall::funcp() pointing to the only possible
    // AstCFunc that may be called
    if (callp->superReference() || VN_IS(callp, CNew)) return m_emptySet;
    AstNode* nodep = callp->funcp();
    while (nodep && nodep->backp()
           && (nodep->backp()->nextp() == nodep || VN_IS(nodep->backp(), Scope))) {
        nodep = nodep->backp();
    }
    AstClass* const classp = VN_CAST(nodep->backp(), Class);
    if (!classp) return m_emptySet;  // Not under class return empty set
    auto it = m_vertexMap.find(classp);
    UASSERT_OBJ(it != m_vertexMap.end(), classp, "Class not mapped");
    return it->second->getCallPossibleCFuncs(callp->funcp()->name());
}

// Build a Class graph and returns it in a V3ClassesGraphWrapper
class ClassGraphBuilderVisitor final : VNVisitor {
    std::unique_ptr<V3Graph> m_graphp;  // Graph of classes
    std::unordered_map<const AstClass*, V3ClassGraphVertex*>
        m_vertexMap;  // Maps classes to their vertices
    AstClass* m_classp = nullptr;  // Current class
    V3ClassGraphVertex* m_classVertexp = nullptr;  // vertex corresponding to a current class -
                                                   // getClassVertex(m_classp) == m_classVertexp

    V3ClassGraphVertex* getClassVertex(const AstClass* const classp) {
        auto it = m_vertexMap.find(classp);
        if (it != m_vertexMap.end()) return it->second;
        return m_vertexMap.emplace(classp, new V3ClassGraphVertex{m_graphp.get(), classp})
            .first->second;
    }

    void visit(AstCFunc* const nodep) override {
        if (!m_classp || nodep->isConstructor() || nodep->isDestructor()) return;
        UASSERT_OBJ(m_classVertexp, nodep,
                    "If function is under class m_classVertexp shall be set");
        m_classVertexp->addFunc(nodep);
    }
    void visit(AstClassExtends* const nodep) override {
        UASSERT_OBJ(m_classVertexp, nodep,
                    "m_classVertexp shall be set while visiting AstClassExtends");
        new V3GraphEdge{m_graphp.get(),
                        getClassVertex(VN_AS(nodep->childDTypep(), ClassRefDType)->classp()),
                        m_classVertexp, 1};
    }
    void visit(AstNodeModule* const nodep) override {
        VL_RESTORER(m_classp);
        VL_RESTORER(m_classVertexp);
        if ((m_classp = VN_CAST(nodep, Class))) m_classVertexp = getClassVertex(m_classp);
        iterateChildren(nodep);
    }
    void visit(AstNode* const nodep) override { iterateChildren(nodep); }

public:
    explicit ClassGraphBuilderVisitor(AstNetlist* const nodep)
        : m_graphp{new V3Graph} {
        iterate(nodep);

        // Propagate virtualization
        m_graphp->order();
        for (V3GraphVertex& graphVertex : m_graphp->vertices()) {
            V3ClassGraphVertex* const vertexp = graphVertex.as<V3ClassGraphVertex>();
            for (V3GraphEdge& outEdge : vertexp->outEdges()) {
                V3ClassGraphVertex* const successorp = outEdge.top()->as<V3ClassGraphVertex>();
                successorp->propagateVirt(*vertexp);
            }
        }
    }
    ~ClassGraphBuilderVisitor() override = default;
    std::unique_ptr<V3ClassesGraphWrapper> takeGraph() && {
        return std::unique_ptr<V3ClassesGraphWrapper>(
            new V3ClassesGraphWrapper{std::move(m_graphp), std::move(m_vertexMap)});
    }
};

std::unique_ptr<V3ClassesGraphWrapper> V3Virtual::buildClassGraph(AstNetlist* netlistp) {
    return ClassGraphBuilderVisitor{netlistp}.takeGraph();
}
