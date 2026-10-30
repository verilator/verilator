// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Resolve upward task/function references
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
// V3Upward's Transformations:
//
// Module definitions are normally shared by all instances, but an upward task/function reference
// resolves according to the instance hierarchy.
//
//      Identify module subtrees containing upward references.
//      For each affected instance hierarchy:
//          Resolve upward references by searching enclosing lexical scopes.
//          Group instances of each module by their resolved targets and child variants.
//      For each distinct group:
//          Keep the first group on the original module definition.
//          Clone the module definition for each additional group.
//          Relink upward references and child cells to the selected variants.
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Upward.h"

#include "V3Error.h"
#include "V3Global.h"
#include "V3Graph.h"
#include "V3GraphStream.h"
#include "V3Hash.h"
#include "V3UniqueNames.h"

#include <algorithm>
#include <unordered_map>
#include <vector>

VL_DEFINE_DEBUG_FUNCTIONS;

namespace {

struct ScopeInfo final {
    const AstNode* const m_parentp;  // Enclosing lexical scope, or null at module scope.
    std::unordered_map<string, AstNodeFTask*>
        m_ftasks;  // Tasks/functions declared directly in this scope.

    explicit ScopeInfo(const AstNode* parentp = nullptr)
        : m_parentp{parentp} {}
};

struct CellInfo final {
    AstCell* const m_cellp = nullptr;  // Cell to specialize.
    const AstNode* const m_scopep = nullptr;  // Lexical scope containing the cell.
};

struct ModuleInfo final {
    std::vector<AstNodeFTaskRef*> m_upwardRefps;  // Upward references in AST traversal order.
    std::vector<CellInfo> m_cells;  // Cells in the same traversal order in every clone.
    std::unordered_map<const AstNode*, ScopeInfo> m_scopes;  // Lexical-scope lookup by AST node.
};

class ModuleInfoCollector final : public VNVisitorConst {
    ModuleInfo& m_info;  // Information being collected.
    const AstNode* m_scopep;  // Current lexical scope.

    void visit(AstNodeFTaskRef* nodep) override {
        if (nodep->upwardReference()) m_info.m_upwardRefps.push_back(nodep);
        iterateChildrenConst(nodep);
    }

    void visit(AstNodeFTask* nodep) override {
        m_info.m_scopes[m_scopep].m_ftasks.emplace(nodep->name(), nodep);
        iterateChildrenConst(nodep);
    }

    void visit(AstCell* nodep) override {
        m_info.m_cells.push_back(CellInfo{nodep, m_scopep});
        iterateChildrenConst(nodep);
    }

    void visit(AstGenBlock* nodep) override { iterateScope(nodep); }

    void iterateScope(AstNode* nodep) {
        const AstNode* const parentp = m_scopep;
        m_info.m_scopes.emplace(nodep, ScopeInfo{parentp});
        VL_RESTORER(m_scopep);
        m_scopep = nodep;
        iterateChildrenConst(nodep);
    }

    void visit(AstNodeBlock* nodep) override { iterateScope(nodep); }

    void visit(AstNodeModule*) override { /* Noop. Ignore children modules. */ }

    void visit(AstNode* nodep) override { iterateChildrenConst(nodep); }

public:
    ModuleInfoCollector(AstNodeModule* nodep, ModuleInfo& info)
        : m_info{info}
        , m_scopep{nodep} {
        m_info.m_scopes.emplace(nodep, ScopeInfo{nullptr});
        iterateAndNextConstNull(nodep->stmtsp());
    }
    ~ModuleInfoCollector() override = default;
};

ModuleInfo gatherModuleInfo(AstNodeModule* nodep) {
    ModuleInfo modInfo;
    ModuleInfoCollector{nodep, modInfo};
    return modInfo;
}

struct Variant;

struct VariantKey final {
    std::vector<AstNodeFTask*> m_targetps;  // Resolved targets of this module's upward references.
    std::vector<Variant*> m_childVariantps;  // Selected variant for each child cell.

    bool operator==(const VariantKey& rhs) const {
        return m_targetps == rhs.m_targetps && m_childVariantps == rhs.m_childVariantps;
    }
};

struct VariantKeyHash final {
    size_t operator()(const VariantKey& key) const {
        V3Hash hash;
        for (const AstNodeFTask* const targetp : key.m_targetps) hash += targetp;
        for (const Variant* const childp : key.m_childVariantps) hash += childp;
        return hash.value();
    }
};

struct Variant final {
    const VariantKey m_key;  // Instance-dependent choices defining this variant.
    AstNodeModule* m_modulep = nullptr;  // Definition assigned after all variants are classified.

    explicit Variant(VariantKey&& key)
        : m_key{std::move(key)} {}
};

struct ModuleVariants final {
    std::vector<std::unique_ptr<Variant>> m_variants;  // Owned variants in discovery order.
    std::unordered_map<VariantKey, Variant*, VariantKeyHash> m_byKey;  // Interned variants.
};

struct Ancestor final {
    AstNodeModule* const m_modulep;  // Module containing the ancestor cell.
    const AstNode* const m_scopep;  // Lexical scope from which upward lookup continues.
};

class UpwardVertex final : public V3GraphVertex {
    VL_RTTI_IMPL(UpwardVertex, V3GraphVertex)

    AstNodeModule* const m_modulep;  // Module represented by this vertex.
    bool m_subtreeHasUpwardRef = false;  // Whether this module's subtree has an upward reference.

public:
    UpwardVertex(V3Graph* graphp, AstNodeModule* modulep)
        : V3GraphVertex{graphp}
        , m_modulep{modulep}
        , m_subtreeHasUpwardRef{m_modulep->hasUpwardRef()} {}

    AstNodeModule* modulep() const { return m_modulep; }

    bool subtreeHasUpwardRef() const { return m_subtreeHasUpwardRef; }
    void subtreeHasUpwardRef(bool flag) { m_subtreeHasUpwardRef = flag; }

    string name() const override { return m_modulep->prettyNameQ(); }
    string dotColor() const override {
        if (m_subtreeHasUpwardRef) return "red";
        return "black";
    }
};

class UpwardSubtreesIdentifier final : public VNVisitorConst {
    const VNUser1InUse m_user1InUse;  // AstNodeModule::user1p() -> UpwardVertex*
    V3Graph m_graph;  // Child-to-parent module dependency graph.
    AstNodeModule* m_currModulep = nullptr;  // Module containing the current AST node.

    UpwardVertex* vertex(AstNodeModule* modulep) {
        if (!modulep->user1p()) { modulep->user1p(new UpwardVertex{&m_graph, modulep}); }
        return modulep->user1u().to<UpwardVertex*>();
    }

    void visit(AstNodeModule* nodep) override {
        VL_RESTORER(m_currModulep);
        m_currModulep = nodep;
        vertex(nodep);
        iterateChildrenConst(nodep);
    }

    void addDependency(UpwardVertex* childp, UpwardVertex* parentp) {
        for (const V3GraphEdge& edge : childp->outEdges()) {
            if (edge.top() == parentp) return;
        }
        new V3GraphEdge{&m_graph, childp, parentp, 1};
    }

    void visit(AstCell* nodep) override {
        if (AstNodeModule* const modp = nodep->modp()) {
            UpwardVertex* const childp = vertex(modp);
            UpwardVertex* const parentp = vertex(m_currModulep);
            addDependency(childp, parentp);
        }
        iterateChildrenConst(nodep);
    }

    void visit(AstNode* nodep) override { iterateChildrenConst(nodep); }

    void propagate() {
        GraphStreamUnordered order{&m_graph};
        while (const V3GraphVertex* const vertexp = order.nextp()) {
            const UpwardVertex* const childp = vertexp->as<const UpwardVertex>();
            if (childp->subtreeHasUpwardRef()) {
                for (const V3GraphEdge& edge : childp->outEdges()) {
                    edge.top()->as<UpwardVertex>()->subtreeHasUpwardRef(true);
                }
            }
        }
    }

public:
    UpwardSubtreesIdentifier(AstNetlist* const rootp) {
        iterateChildrenConst(rootp);
        propagate();
    }

    bool subtreeHasUpwardRef(AstNodeModule* nodep) const {
        return nodep->user1p() && nodep->user1u().to<UpwardVertex*>()->subtreeHasUpwardRef();
    }

    void dumpDotFile() { m_graph.dumpDotFilePrefixed("upward-subtrees"); }
};

class InstanceVertex final : public V3GraphVertex {
    VL_RTTI_IMPL(InstanceVertex, V3GraphVertex)

    AstNodeModule* const m_sourcep;  // Module definition instantiated by this vertex.
    const uint32_t m_discoveryIndex;  // Stable instance traversal order.

    std::vector<AstNodeFTask*> m_targetps;  // Resolved targets of upward references.
    std::vector<InstanceVertex*> m_childps;  // One entry per source cell, including nulls.
    Variant* m_variantp = nullptr;  // Selected module variant for this instance.

public:
    InstanceVertex(V3Graph* graphp, AstNodeModule* sourcep, uint32_t discoveryIndex)
        : V3GraphVertex{graphp}
        , m_sourcep{sourcep}
        , m_discoveryIndex{discoveryIndex} {}

    uint32_t discoveryIndex() const { return m_discoveryIndex; }

    const std::vector<AstNodeFTask*>& targetps() const { return m_targetps; }
    void addTargetp(AstNodeFTask* targetp) { m_targetps.push_back(targetp); }

    const std::vector<InstanceVertex*>& childps() const { return m_childps; }
    void addChildp(InstanceVertex* childp) { m_childps.push_back(childp); }

    Variant* variantp() const { return m_variantp; }
    void variantp(Variant* variantp) { m_variantp = variantp; }

    string name() const override { return m_sourcep->prettyNameQ(); }
};

class UpwardRefUniquifier final {
    AstNetlist* const m_rootp;  // Design being rewritten.
    UpwardSubtreesIdentifier
        m_subtreesWithUpward;  // Visitor collecting subtrees with upward references.
    V3Graph m_instanceGraph;  // Graph with instances and their connections to children.
    uint32_t m_nextDiscoveryIndex = 0;  // Allows ordering instances by their appearance order.
    std::unordered_map<AstNodeModule*, ModuleInfo> m_moduleInfos;  // Cached module contents.
    std::unordered_map<AstNodeModule*, std::vector<InstanceVertex*>>
        m_instancesByModule;  // Records instances with upward references.
    std::vector<AstNodeModule*> m_instanceModules;  // Module definitions in discovery order.
    std::unordered_map<AstNodeModule*, InstanceVertex*>
        m_defaultInstances;  // Records the configuration applied to the original module
                             // definition.
    std::unordered_map<AstNodeModule*, ModuleVariants>
        m_moduleVariants;  // Owns additional configurations that require cloned modules.
    std::vector<AstNodeModule*> m_modulesToRelink;  // Deterministic child-first order.
    V3UniqueNames m_names{"__Vupward"};  // Cloned modules names.

    void buildInstanceGraph() {
        for (AstNodeModule* modulep = m_rootp->modulesp(); modulep;
             modulep = VN_AS(modulep->nextp(), NodeModule)) {
            if (modulep->isTop()) {
                std::vector<Ancestor> ancestors;
                buildInstanceGraph(modulep, ancestors);
            }
        }
    }

    InstanceVertex* buildInstanceGraph(AstNodeModule* modulep, std::vector<Ancestor>& ancestors) {
        if (!m_subtreesWithUpward.subtreeHasUpwardRef(modulep)
            || std::any_of(
                ancestors.begin(), ancestors.end(),
                [modulep](const Ancestor& ancestor) { return ancestor.m_modulep == modulep; }))
            return nullptr;

        InstanceVertex* const vertexp
            = new InstanceVertex{&m_instanceGraph, modulep, m_nextDiscoveryIndex++};
        std::vector<InstanceVertex*>& instances = m_instancesByModule[modulep];
        if (instances.empty()) m_instanceModules.push_back(modulep);
        instances.push_back(vertexp);

        ModuleInfo& info = moduleInfo(modulep);

        for (AstNodeFTaskRef* const refp : info.m_upwardRefps) {
            vertexp->addTargetp(findTarget(ancestors, refp));
        }

        for (const CellInfo& cell : info.m_cells) {
            InstanceVertex* childp = nullptr;
            if (AstNodeModule* const childModulep = cell.m_cellp->modp()) {
                ancestors.push_back(Ancestor{modulep, cell.m_scopep});
                childp = buildInstanceGraph(childModulep, ancestors);
                ancestors.pop_back();
            }
            vertexp->addChildp(childp);
            // Point child to parent so graph ranks classify child variants first.
            if (childp) { new V3GraphEdge{&m_instanceGraph, childp, vertexp, /*weight=*/1}; }
        }

        return vertexp;
    }

    ModuleInfo& moduleInfo(AstNodeModule* nodep) {
        const auto it = m_moduleInfos.find(nodep);
        if (it != m_moduleInfos.end()) return it->second;
        return m_moduleInfos.emplace(nodep, gatherModuleInfo(nodep)).first->second;
    }

    AstNodeFTask* findTarget(const std::vector<Ancestor>& ancestors, AstNodeFTaskRef* refp) {
        for (auto it = ancestors.rbegin(); it != ancestors.rend(); ++it) {
            ModuleInfo& info = moduleInfo(it->m_modulep);
            for (const AstNode* scopep = it->m_scopep; scopep;) {
                const ScopeInfo& scope = info.m_scopes[scopep];
                const auto taskIt = scope.m_ftasks.find(refp->name());
                if (taskIt != scope.m_ftasks.end()) return taskIt->second;
                scopep = scope.m_parentp;
            }
        }
        refp->v3fatalSrc("Upward task/function reference no longer resolves");
        return nullptr;  // LCOV_EXCL_LINE
    }

    static VariantKey variantKey(const InstanceVertex* vertexp) {
        VariantKey key;
        key.m_targetps = vertexp->targetps();
        key.m_childVariantps.reserve(vertexp->childps().size());
        for (const InstanceVertex* const childp : vertexp->childps()) {
            key.m_childVariantps.push_back(childp ? childp->variantp() : nullptr);
        }
        return key;
    }

    void classifyInstanceGraph() {
        m_instanceGraph.rank();
        std::stable_sort(
            m_instanceModules.begin(), m_instanceModules.end(),
            [this](AstNodeModule* lhs, AstNodeModule* rhs) {
                const auto lhsIt = m_instancesByModule.find(lhs);
                const auto rhsIt = m_instancesByModule.find(rhs);
                UASSERT(lhsIt != m_instancesByModule.end() && !lhsIt->second.empty()
                            && rhsIt != m_instancesByModule.end() && !rhsIt->second.empty(),
                        "Instances should be collected and assigned to relevant modules");
                const InstanceVertex* const lhsInstancep = lhsIt->second[0];
                const InstanceVertex* const rhsInstancep = rhsIt->second[0];
                if (lhsInstancep->rank() != rhsInstancep->rank()) {
                    return lhsInstancep->rank() < rhsInstancep->rank();
                }
                return lhsInstancep->discoveryIndex() < rhsInstancep->discoveryIndex();
            });

        for (AstNodeModule* const sourcep : m_instanceModules) {
            const std::vector<InstanceVertex*>& instanceps = m_instancesByModule[sourcep];
            bool issueRelink = false;
            ModuleVariants& variants = m_moduleVariants[sourcep];
            for (InstanceVertex* const instancep : instanceps) {
                VariantKey key = variantKey(instancep);
                if (variants.m_byKey.empty()) {
                    // Make first variant a default.
                    m_defaultInstances.emplace(sourcep, instancep);
                    variants.m_byKey.emplace(std::move(key), nullptr);
                    instancep->variantp(nullptr);
                    issueRelink = needsRelink(instancep);
                    continue;
                }
                const auto it = variants.m_byKey.find(key);
                if (it != variants.m_byKey.end()) {
                    // Reuse existing variant if already present.
                    instancep->variantp(it->second);
                } else {
                    variants.m_variants.emplace_back(std::make_unique<Variant>(std::move(key)));
                    Variant* const variantp = variants.m_variants.back().get();
                    variants.m_byKey.emplace(variantp->m_key, variantp);
                    instancep->variantp(variantp);
                    issueRelink = true;
                }
            }
            if (issueRelink) m_modulesToRelink.push_back(sourcep);
        }
    }

    static bool needsRelink(const InstanceVertex* vertexp) {
        const std::vector<InstanceVertex*>& childps = vertexp->childps();
        return !vertexp->targetps().empty()
               || std::any_of(childps.begin(), childps.end(),
                              [](const InstanceVertex* const childp) {
                                  return childp && childp->variantp();
                              });
    }

    void cloneVariantModules() {
        for (AstNodeModule* const sourcep : m_modulesToRelink) {
            const auto it = m_moduleVariants.find(sourcep);
            if (it != m_moduleVariants.end()) {
                for (const std::unique_ptr<Variant>& variantp : it->second.m_variants) {
                    variantp->m_modulep = cloneModule(sourcep);
                }
            }
        }
    }

    AstNodeModule* cloneModule(AstNodeModule* nodep) {
        AstNodeModule* const clonep = nodep->cloneTree(false);
        clonep->name(m_names.get(nodep));
        m_rootp->addModulesp(clonep);
        return clonep;
    }

    template <typename ChildVariantAt>
    void relinkModule(AstNodeModule* modulep, const std::vector<AstNodeFTask*>& targetps,
                      const ChildVariantAt& childVariantAt) {
        ModuleInfo info = moduleInfo(modulep);
        for (size_t i = 0; i < info.m_upwardRefps.size(); ++i) {
            info.m_upwardRefps[i]->taskp(targetps[i]);
        }
        for (size_t i = 0; i < info.m_cells.size(); ++i) {
            if (Variant* const childVariantp = childVariantAt(i)) {
                AstCell* const cellp = info.m_cells[i].m_cellp;
                cellp->modp(childVariantp->m_modulep);
                cellp->modName(childVariantp->m_modulep->name());
            }
        }
    }

    void relinkVariants() {
        for (AstNodeModule* const sourcep : m_modulesToRelink) {
            const InstanceVertex* const instancep = m_defaultInstances[sourcep];
            relinkModule(sourcep, instancep->targetps(), [instancep](std::size_t i) {
                const InstanceVertex* const childp = instancep->childps()[i];
                return childp ? childp->variantp() : nullptr;
            });

            const auto it = m_moduleVariants.find(sourcep);
            if (it != m_moduleVariants.end()) {
                for (const std::unique_ptr<Variant>& variantp : it->second.m_variants) {
                    relinkModule(variantp->m_modulep, variantp->m_key.m_targetps,
                                 [variantp = variantp.get()](size_t i) {
                                     return variantp->m_key.m_childVariantps[i];
                                 });
                }
            }
        }
    }

public:
    explicit UpwardRefUniquifier(AstNetlist* rootp)
        : m_rootp{rootp}
        , m_subtreesWithUpward{rootp} {
        if (dumpGraphLevel()) m_subtreesWithUpward.dumpDotFile();
        buildInstanceGraph();
        classifyInstanceGraph();
        cloneVariantModules();
        relinkVariants();
        if (dumpGraphLevel()) m_instanceGraph.dumpDotFilePrefixed("upward-uniquifier");
    }
    ~UpwardRefUniquifier() = default;
};

}  // namespace

void V3Upward::uniquify(AstNetlist* nodep) {
    if (!v3Global.hasUpwardReferences()) return;
    UINFO(2, __FUNCTION__ << ":");
    UpwardRefUniquifier{nodep};
    if (dumpTreeEitherLevel() >= 9) {
        V3Global::dumpCheckGlobalTree("upward");
    } else if (debug()) {  // on high dbg level, dump even if not explicitly told to
        v3Global.rootp()->dumpTreeFile(v3Global.debugFilename("upward.tree"));
    }
}
