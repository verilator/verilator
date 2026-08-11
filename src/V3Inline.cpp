// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Module inlining
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
// V3Inline's Transformations:
//
// Each module:
//      Look for CELL... PRAGMA INLINE_MODULE
//          Replicate the cell's module
//              Rename vars to include cell name
//          Insert cell's module declarations into the upper module
//          Merge each SCOPE of the cell's module into the SCOPE above it
//          Reparent and rename the SCOPEs below the inlined instance
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Inline.h"

#include "V3AstUserAllocator.h"
#include "V3Graph.h"
#include "V3Stats.h"

#include <unordered_map>
#include <vector>

VL_DEFINE_DEBUG_FUNCTIONS;

// CONFIG
static const int INLINE_MODS_SMALLER = 100;  // If a mod is < this # nodes, can always inline it

//######################################################################
// Bipartite module instantiation graph containing module and cell vertices

class InlineModModuleVertex;
class InlineModCellVertex;

class InlineModGraph final : public V3Graph {
    // NODE STATE
    // AstNodeModule::user4p() -> InlineModModuleVertex*, the module vertex
    // AstCell::user4p()       -> InlineModCellVertex*, the cell vertex

    VNUser4InUse m_user4InUse;

public:
    InlineModGraph()
        : V3Graph{} {}
    ~InlineModGraph() override = default;

    // METHODS
    InlineModModuleVertex* getInlineModModuleVertexp(AstNodeModule* modp);
    InlineModCellVertex* getInlineModCellVertexp(AstCell* cellp);
    void addEdge(InlineModModuleVertex& from, InlineModCellVertex& to);
    void addEdge(InlineModCellVertex& from, InlineModModuleVertex& to);

    // debug
    std::string dotRankDir() const override { return "LR"; }
};

class InlineModEitherVertex VL_NOT_FINAL : public V3GraphVertex {
    VL_RTTI_IMPL(InlineModEitherVertex, V3GraphVertex)
protected:
    explicit InlineModEitherVertex(InlineModGraph& graph)
        : V3GraphVertex{&graph} {}
};

class InlineModModuleVertex final : public InlineModEitherVertex {
    VL_RTTI_IMPL(InlineModModuleVertex, InlineModEitherVertex)
    AstNodeModule* const m_modp;  // The module
    const char* m_noInlineHardWyp = nullptr;  // First reason the module can never be inlined
    const char* m_noInlineSoftWyp = nullptr;  // First reason not to inline unless forced
    const char* m_shouldInlineWhyp = nullptr;  // First reason why this module should be inlined
    size_t m_size = 0;  // The size (statement count) of the module
    size_t mutable m_flattenedSize = 0;  // The size of the module if flattened
    bool mutable m_flattenedSizeValid = false;  // Whether the flattened size is valid
    size_t mutable m_instanceCount = 0;  // The number of total instances of this module
    bool mutable m_instanceCountValid = false;  // Whether the instance count is valid

public:
    InlineModModuleVertex(InlineModGraph& graph, AstNodeModule* modp)
        : InlineModEitherVertex{graph}
        , m_modp{modp} {}
    ~InlineModModuleVertex() override = default;

    // ACCESSORS
    AstNodeModule* modp() const { return m_modp; }
    size_t size() const { return m_size; }
    void size(size_t value) { m_size = value; }
    void sizeInc(size_t value = 1) { m_size += value; }
    bool noInlineHard() const { return m_noInlineHardWyp; }
    void setNoInlineHard(const char* whyp) {
        if (!m_noInlineHardWyp) m_noInlineHardWyp = whyp;
    }
    bool noInlineSoft() const { return m_noInlineSoftWyp; }
    void setNoInlineSoft(const char* whyp) {
        if (!m_noInlineSoftWyp) m_noInlineSoftWyp = whyp;
    }
    bool shouldInline() const { return m_shouldInlineWhyp; }
    void setShouldInline(const char* whyp) {
        if (!m_shouldInlineWhyp) m_shouldInlineWhyp = whyp;
    }
    // Mark every instance below this module for inlining
    void setFlatten();

    // Total size of module, with all hierarchy below flattened
    size_t flattenedSize() const {
        if (!m_flattenedSizeValid) {
            m_flattenedSizeValid = true;
            m_flattenedSize = m_size;
            for (const V3GraphEdge& e1 : outEdges()) {
                for (const V3GraphEdge& e2 : e1.top()->outEdges()) {
                    InlineModModuleVertex* const mVtxp = e2.top()->as<InlineModModuleVertex>();
                    m_flattenedSize += mVtxp->flattenedSize();
                }
            }
        }
        return m_flattenedSize;
    }
    // Total number of instances of this module in the whole hierarchy of the design
    // Note this is the same as the number of AstScopes the module has.
    size_t instanceCount() const {
        if (!m_instanceCountValid) {
            m_instanceCountValid = true;
            m_instanceCount = 0;
            for (const V3GraphEdge& e1 : inEdges()) {
                for (const V3GraphEdge& e2 : e1.fromp()->inEdges()) {
                    InlineModModuleVertex* const mVtxp = e2.fromp()->as<InlineModModuleVertex>();
                    m_instanceCount += mVtxp->instanceCount();
                }
            }
            if (!m_instanceCount) {
                UASSERT_OBJ(m_modp->isTop(), m_modp, "non-top level module should have instances");
                m_instanceCount = 1;
            }
        }
        return m_instanceCount;
    }

    // debug
    FileLine* fileline() const override { return m_modp->fileline(); }
    std::string dotShape() const override { return "box"; }
    std::string dotColor() const override {
        return m_noInlineHardWyp    ? "red"
               : m_shouldInlineWhyp ? "blue"
               : m_noInlineSoftWyp  ? "orange"
                                    : "black";
    }
    std::string name() const override VL_MT_STABLE {
        std::string str = m_modp->typeName() + " "s + cvtToHex(m_modp);
        str += "\n" + m_modp->name() + " @ " + fileline()->ascii();
        str += "\ninstanceCount: " + std::to_string(instanceCount());
        str += "\nsize: " + std::to_string(m_size);
        str += "\nflattenedSize: " + std::to_string(flattenedSize());
        if (m_shouldInlineWhyp) str += "\nShouldInline: "s + m_shouldInlineWhyp;
        if (m_noInlineHardWyp) str += "\nNoInlineHard: "s + m_noInlineHardWyp;
        if (m_noInlineSoftWyp) str += "\nNoInlineSoft: "s + m_noInlineSoftWyp;
        str += "\n";
        return str;
    }
};

class InlineModCellVertex final : public InlineModEitherVertex {
    VL_RTTI_IMPL(InlineModCellVertex, InlineModEitherVertex)
    AstCell* const m_cellp;  // The cell (instance)
    const char* m_doInlineWyp = nullptr;  // First reason this instance should be inlined
    bool m_flatten = false;  // Whether this cell and below already flattened (avoid O(n^2))

public:
    InlineModCellVertex(InlineModGraph& graph, AstCell* cellp)
        : InlineModEitherVertex{graph}
        , m_cellp{cellp} {}
    ~InlineModCellVertex() override = default;

    // ACCESSORS
    AstCell* cellp() const { return m_cellp; }
    bool doInline() const { return m_doInlineWyp; }
    void setDoInline(const char* whyp) {
        if (!m_doInlineWyp) m_doInlineWyp = whyp;
    }
    bool flatten() const { return m_flatten; }
    void setFlatten() { m_flatten = true; }

    // The module vertx this cell is instantiating
    InlineModModuleVertex& instanceOf() const {
        UASSERT_OBJ(outSize1(), this, "Cell should have exactly one outgoing edge");
        return *outEdges().frontp()->top()->as<InlineModModuleVertex>();
    }
    // The module vertex this cell is instantiated in
    InlineModModuleVertex& instanceIn() const {
        UASSERT_OBJ(inSize1(), this, "Cell should have exactly one incoming edge");
        return *inEdges().frontp()->fromp()->as<InlineModModuleVertex>();
    }

    // debug
    FileLine* fileline() const override { return m_cellp->fileline(); }
    std::string dotColor() const override { return m_doInlineWyp ? "green" : "black"; }
    std::string dotShape() const override { return "ellipse"; }
    std::string name() const override VL_MT_STABLE {
        std::string str = m_cellp->typeName() + " "s + cvtToHex(m_cellp);
        str += "\n" + m_cellp->name() + " @ " + fileline()->ascii();
        if (m_doInlineWyp) str += "\nDoInline: "s + m_doInlineWyp;
        str += "\n";
        return str;
    }
};

InlineModModuleVertex* InlineModGraph::getInlineModModuleVertexp(AstNodeModule* modp) {
    if (!modp->user4p()) modp->user4p(new InlineModModuleVertex{*this, modp});
    return modp->user4u().to<InlineModModuleVertex*>();
}
InlineModCellVertex* InlineModGraph::getInlineModCellVertexp(AstCell* cellp) {
    if (!cellp->user4p()) cellp->user4p(new InlineModCellVertex{*this, cellp});
    return cellp->user4u().to<InlineModCellVertex*>();
}

void InlineModGraph::addEdge(InlineModModuleVertex& parent, InlineModCellVertex& cell) {
    UASSERT_OBJ(cell.inEmpty(), &cell, "Cell should have at most one incoming edge");
    new V3GraphEdge{this, &parent, &cell, 1, /* cutable: */ false};
}
void InlineModGraph::addEdge(InlineModCellVertex& cell, InlineModModuleVertex& submodule) {
    UASSERT_OBJ(cell.outEmpty(), &cell, "Cell should have at most one outgoing edge");
    new V3GraphEdge{this, &cell, &submodule, 1, /* cutable: */ false};
}

void InlineModModuleVertex::setFlatten() {
    for (V3GraphEdge& edge : outEdges()) {
        InlineModCellVertex& cVtx = *edge.top()->as<InlineModCellVertex>();
        if (cVtx.flatten()) continue;
        cVtx.setFlatten();
        InlineModModuleVertex& iVtx = cVtx.instanceOf();
        if (!iVtx.noInlineHard() && !iVtx.noInlineSoft()) cVtx.setDoInline("flatten parent");
        iVtx.setFlatten();
    }
}

//######################################################################
// Visitor that builds the bipartite module instantiation graph

class InlineModGraphBuilder final : public VNVisitor {
    // STATE
    std::unique_ptr<InlineModGraph> m_graphp{new InlineModGraph};  // The graph being built
    InlineModModuleVertex* m_modVtxp = nullptr;  // Vertex of module currently being iterated
    const AstScope* m_sizedScopep = nullptr;  // The scope of current module measured for size

    // VISITORS
    void visit(AstNodeModule* nodep) override {
        if (nodep == v3Global.rootp()->constPoolp()->modp()) return;  // Ignore const pool module

        UASSERT_OBJ(!m_modVtxp, nodep, "Unsupported: Nested modules");

        // Create the module vertex
        InlineModModuleVertex* const vtxp = m_graphp->getInlineModModuleVertexp(nodep);

        // Check if the module itself is not inlineable

        // TODO: All references are resolved by now, but AstIfaceRefDType::cellp and
        // the AstIntfRef records still name the interface instance, so keep it.
        if (VN_IS(nodep, Iface)) vtxp->setNoInlineHard("Interface");
        // Never inline packages - TODO: conceptually fine, but why not?
        if (VN_IS(nodep, Package)) vtxp->setNoInlineHard("Package");
        // A --lib-create library stub instance that needs tracing must not be
        // inlined, so we still know it is a lib stub in V3TraceDecl (see #7001)
        if (nodep->verilatorLib() && v3Global.opt.trace()) {
            vtxp->setNoInlineHard("verilatorLib with --trace");
        }

        // Don't inline public modules by default
        if (nodep->modPublic()) vtxp->setNoInlineSoft("Public module");

        // Iterate children
        VL_RESTORER(m_modVtxp);
        VL_RESTORER(m_sizedScopep);
        m_modVtxp = vtxp;
        m_sizedScopep = nullptr;
        iterateChildrenConst(nodep);
    }

    void visit(AstClass* nodep) override {
        // TODO allow inlining of modules that contain classes
        if (m_modVtxp) m_modVtxp->setNoInlineHard("Contains class");
    }

    void visit(AstScope* nodep) override {
        // Every instance of a module holds an identical copy of the module body under
        // its own AstScope, so only measure the size of one of them.
        if (!m_sizedScopep) m_sizedScopep = nodep;
        if (m_sizedScopep != nodep) return;
        if (m_modVtxp) m_modVtxp->sizeInc();
        iterateChildrenConst(nodep);
    }

    // Cells instantiate modules
    void visit(AstCell* nodep) override {
        UASSERT_OBJ(m_modVtxp, nodep, "Cell should be under a module");

        // Create the cell vertex
        InlineModCellVertex* const vtxp = m_graphp->getInlineModCellVertexp(nodep);

        // Add containing-module/instantiated-module edges
        m_graphp->addEdge(*m_modVtxp, *vtxp);
        m_graphp->addEdge(*vtxp, *m_graphp->getInlineModModuleVertexp(nodep->modp()));

        // Iterate children
        iterateChildrenConst(nodep);
    }

    void visit(AstPragma* nodep) override {
        if (nodep->pragType() == VPragmaType::INLINE_MODULE) {
            if (!m_modVtxp) {
                nodep->v3error("Inline pragma not under a module");  // LCOV_EXCL_LINE
            } else {
                m_modVtxp->setShouldInline("Pragma INLINE_MODULE");
            }
            VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
            return;
        }

        if (nodep->pragType() == VPragmaType::NO_INLINE_MODULE) {
            if (!m_modVtxp) {
                nodep->v3error("Inline pragma not under a module");  // LCOV_EXCL_LINE
            } else {
                m_modVtxp->setNoInlineSoft("Pragma NO_INLINE_MODULE");
            }
            VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
            return;
        }

        iterateChildrenConst(nodep);
    }

    // Base node
    void visit(AstNode* nodep) override {
        if (m_modVtxp) m_modVtxp->sizeInc();
        iterateChildrenConst(nodep);
    }

    // CONSTRUCTORS
    explicit InlineModGraphBuilder(AstNetlist* nodep) {
        // Build the module instantiation graph
        iterateConst(nodep);
        // Order vertices (any topological order is fine), can't be cyclic at this point
        m_graphp->order();
        // Check that the first vertex is the top level module (everything, including packages,
        // have a corresponding AstCell under the top level at this point).
        UASSERT_OBJ(m_graphp->vertices().frontp()->as<InlineModModuleVertex>()->modp()->isTop(),
                    nodep, "First vertex should be top level module");
#ifdef VL_DEBUG
        for (const V3GraphVertex& vtx : m_graphp->vertices()) {
            // First vertex is the top levelmodule, we checked above
            if (&vtx == m_graphp->vertices().frontp()) continue;
            // Otherwise it should have instantiations
            UASSERT_OBJ(!vtx.inEmpty(), &vtx, "Should have edges from root");
        }
#endif
    }
    ~InlineModGraphBuilder() override = default;

public:
    static std::unique_ptr<InlineModGraph> apply(AstNetlist* nodep) {
        return std::move(InlineModGraphBuilder{nodep}.m_graphp);
    }
};

//######################################################################
// Module inliner

namespace ModuleInliner {

// The scopes instantiated directly under each scope (that is parent -> children links)
using ScopeChildren = std::unordered_map<const AstScope*, std::vector<AstScope*>>;

// Record downward links from parent scopes to their child scopes
void gatherScopes(const AstNodeModule* modp, ScopeChildren& children) {
    for (AstNode* nodep = modp->stmtsp(); nodep; nodep = nodep->nextp()) {
        if (AstScope* const scopep = VN_CAST(nodep, Scope)) {
            // Note the top scope is held under the AstTopScope, so is not seen here
            UASSERT_OBJ(scopep->aboveScopep(), scopep, "Instance scope should have a scope above");
            children[scopep->aboveScopep()].push_back(scopep);
        } else if (const AstNodeModule* const subModp = VN_CAST(nodep, NodeModule)) {
            // An AstClass holds its scopes under itself
            UASSERT_OBJ(VN_IS(subModp, Class), subModp, "Nested module should be a class");
            gatherScopes(subModp, children);
        }
    }
}

// Rename the given scope, and all scopes below it, after the scope named by 'oldPrefix'
// (the original parent of 'scopep') has been inlined into the scope above it
void renameScopes(AstScope* scopep, const std::string& oldPrefix, const std::string& newPrefix,
                  const ScopeChildren& children) {
    UASSERT_OBJ(VString::startsWith(scopep->name(), oldPrefix), scopep,
                "Scope name should start with the name of the scope above it");
    scopep->name(newPrefix + scopep->name().substr(oldPrefix.size()));
    const auto it = children.find(scopep);
    if (it == children.end()) return;
    for (AstScope* const childp : it->second) {
        renameScopes(childp, oldPrefix, newPrefix, children);
    }
}

// Merge the given scope (instance) of the inlined cell into the scope above it
void inlineScope(AstScope* scopep, AstCell* cellp, const std::string& prefix,
                 AstCellInline* newCellInlinep, ScopeChildren& children) {
    AstScope* const parentScopep = scopep->aboveScopep();
    UASSERT_OBJ(parentScopep, scopep, "Inlined scope should have a scope above");
    UINFO(6, "  Inline Scope " << scopep);
    UINFO(6, "     into      " << parentScopep);

    // Move the variables of the inlined scope into the scope above
    for (AstVarScope *vscp = scopep->varsp(), *nextp; vscp; vscp = nextp) {
        nextp = VN_AS(vscp->nextp(), VarScope);
        // Note V3Scope attaches variables of non-virtual interface references to the
        // scope of the interface instance, so only update if it is this scope
        if (vscp->scopep() == scopep) vscp->scopep(parentScopep);
        // If the module was cloned, point to the cloned variable
        if (AstVar* const newVarp = VN_CAST(vscp->varp()->user3p(), Var)) {
            vscp->varp(newVarp);
            vscp->dtypeFrom(newVarp);
        }
        if (!cellp->isTrace()) vscp->trace(false);
        parentScopep->addVarsp(vscp->unlinkFrBack());
    }

    // Move the logic of the inlined scope into the scope above
    for (AstNode *nodep = scopep->blocksp(), *nextp; nodep; nodep = nextp) {
        nextp = nodep->nextp();
        nodep->unlinkFrBack();
        if (AstNodeFTask* const ftaskp = VN_CAST(nodep, NodeFTask)) {
            ftaskp->name(prefix + ftaskp->name());
        }
        // If the module was cloned, point coverage increments to the cloned declarations
        if (v3Global.opt.coverage()) {
            nodep->foreach([&](AstCoverInc* incp) {
                AstNodeCoverDecl* const declp = incp->declp();
                if (declp->perInstance()) {
                    // Not cloned, fix up the path here, as only this scope refers to it
                    if (!declp->user2SetOnce()) {
                        declp->hier(VString::dot(cellp->prettyName(), ".", declp->hier()));
                    }
                    return;
                }
                if (AstNodeCoverDecl* const newDeclp = VN_CAST(declp->user3p(), NodeCoverDecl)) {
                    incp->declp(newDeclp);
                }
            });
        }
        parentScopep->addBlocksp(nodep);
    }

    // Move the inline records of the inlined scope into the scope above
    for (AstNode *nodep = scopep->inlinesp(), *nextp; nodep; nodep = nextp) {
        nextp = nodep->nextp();
        AstCellInlineScope* const cisp = VN_AS(nodep->unlinkFrBack(), CellInlineScope);
        cisp->scopep(parentScopep);
        // If the module was cloned, point to the cloned inline record
        if (AstCellInline* const newCinlp = VN_CAST(cisp->cellp()->user3p(), CellInline)) {
            cisp->cellp(newCinlp);
        }
        parentScopep->addInlinesp(cisp);
    }
    // ... and add one for the instance we are inlining now
    if (v3Global.opt.vpi()) {
        parentScopep->addInlinesp(
            new AstCellInlineScope{cellp->fileline(), parentScopep, newCellInlinep});
    }

    // Reparent and rename the scopes instantiated under the inlined scope
    const std::string oldPrefix = scopep->name() + ".";
    const std::string newPrefix = scopep->name() + "__DOT__";
    std::vector<AstScope*> childScopeps;
    {
        const auto it = children.find(scopep);
        if (it != children.end()) {
            childScopeps = std::move(it->second);
            children.erase(it);
        }
    }
    for (AstScope* const childScopep : childScopeps) {
        // A class scope would hang off the scope of the module declaring it, but modules
        // containing classes are never inlined
        UASSERT_OBJ(!VN_IS(childScopep->modp(), Class), childScopep,
                    "Inlined scope should not contain a class scope");
        if (AstCell* const newCellp = VN_CAST(childScopep->aboveCellp()->user3p(), Cell)) {
            // If the module was cloned, point to the cloned cell
            childScopep->aboveCellp(newCellp);
        }
        childScopep->aboveScopep(parentScopep);
        renameScopes(childScopep, oldPrefix, newPrefix, children);
    }
    // Children of the inlined scope are now children of the scope above. Note this must
    // come after the erase above, as inserting into 'children' can invalidate 'it'.
    std::vector<AstScope*>& parentChildps = children[parentScopep];
    parentChildps.erase(std::remove(parentChildps.begin(), parentChildps.end(), scopep),
                        parentChildps.end());
    parentChildps.insert(parentChildps.end(), childScopeps.begin(), childScopeps.end());

    UASSERT_OBJ(!scopep->varsp() && !scopep->blocksp() && !scopep->inlinesp(), scopep,
                "Inlined scope should be empty");
}

// Inline 'cellp' into 'modp'. 'last' indicatest this is tha last instance of the inlined module
void inlineCell(AstNodeModule* modp, AstCell* cellp, bool last, InlineModGraph& graph,
                ScopeChildren& children) {
    UINFO(5, " Inline Cell  " << cellp);
    UINFO(5, " into Module  " << modp);

    // NODE STATE
    //  AstNodeCoverDecl::user2()   -> bool.     true if hier() updated
    //  AstNode::user3p()           -> AstNode*. The clone of this module level declaration
    const VNUser2InUse user2InUse;
    const VNUser3InUse user3InUse;

    VNDeleter deleter;
    deleter.pushDeletep(cellp->unlinkFrBack());

    AstNodeModule* const subModp = cellp->modp();  // The module being inlined

    // Unlink all scopes of the instantiated module, so they are not cloned with it
    std::vector<AstScope*> inlineScopeps;  // Scopes under 'cellp'
    std::vector<AstScope*> otherScopeps;  // Scopes under some other instance
    for (AstNode *nodep = subModp->stmtsp(), *nextp; nodep; nodep = nextp) {
        nextp = nodep->nextp();
        AstScope* const scopep = VN_CAST(nodep, Scope);
        if (!scopep) continue;
        scopep->unlinkFrBack();
        if (scopep->aboveCellp() == cellp) {
            inlineScopeps.push_back(scopep);
            deleter.pushDeletep(scopep);
        } else {
            otherScopeps.push_back(scopep);
        }
    }

    // Important: If this is the last cell, then don't clone the instantiated module but
    // inline the original directly. While this requires some special casing, doing so
    // saves us having to temporarily clone the module for the last cell, which
    // significantly reduces Verilator memory usage. This is especially true as often the
    // top few levels of the hierarchy are singleton wrapper modules, which we always
    // inline. In this case this special casing saves us from having to clone essentially
    // the entire netlist, which would in effect double Verilator memory consumption, or
    // worse if we put off deleting the inlined modules until the end. Not having to clone
    // large trees also improves speed.

    // The module we will yank the declarations out of and put into 'modp'
    AstNodeModule* inlinedp;
    if (last) {
        inlinedp = subModp->unlinkFrBack();
        // This is the only instantiation, so all scopes are being inlined
        UASSERT_OBJ(otherScopeps.empty(), cellp, "Last instance, but has other scopes");
    } else {
        inlinedp = subModp->cloneTree(false);
        // Compute map from the original module items to their clones
        for (AstNode *ap = subModp->inlinesp(), *bp = inlinedp->inlinesp(); ap || bp;
             ap = ap->nextp(), bp = bp->nextp()) {
            UASSERT_OBJ(ap && bp, ap ? ap : bp, "Clone has different number of children");
            ap->user3p(bp);
        }
        for (AstNode *ap = subModp->stmtsp(), *bp = inlinedp->stmtsp(); ap || bp;
             ap = ap->nextp(), bp = bp->nextp()) {
            UASSERT_OBJ(ap && bp, ap ? ap : bp, "Clone has different number of children");
            ap->user3p(bp);
        }
        // Per instance coverage declarations must not be duplicated, drop the clones
        if (v3Global.opt.coverageFsm()) {
            for (AstNode *nodep = inlinedp->stmtsp(), *nextp; nodep; nodep = nextp) {
                nextp = nodep->nextp();
                const AstNodeCoverDecl* const declp = VN_CAST(nodep, NodeCoverDecl);
                if (declp && declp->perInstance()) {
                    VL_DO_DANGLING(deleter.pushDeletep(nodep->unlinkFrBack()), nodep);
                }
            }
        }
        // Put back the scopes of the instances we are not inlining this time
        for (AstScope* const scopep : otherScopeps) subModp->addStmtsp(scopep);
    }
    deleter.pushDeletep(inlinedp);

    // Prefix for renaming inlined declarations
    const std::string prefix = cellp->name() + "__DOT__";

    // Move the inline records of the inlined module, renaming to avoid conflicts
    for (AstNode *nodep = inlinedp->inlinesp(), *nextp; nodep; nodep = nextp) {
        nextp = nodep->nextp();
        AstCellInline* const cinlp = VN_AS(nodep->unlinkFrBack(), CellInline);
        cinlp->name(prefix + cinlp->name());
        modp->addInlinesp(cinlp);
    }
    // Create inline record for resolving hierarchical references later
    AstCellInline* const newCellInlinep
        = new AstCellInline{cellp->fileline(), cellp->name(), subModp->origName()};
    modp->addInlinesp(newCellInlinep);

    // Move the module level declarations of the inlined module into 'modp'
    InlineModModuleVertex* const mVtxp = graph.getInlineModModuleVertexp(modp);
    for (AstNode *nodep = inlinedp->stmtsp(), *nextp; nodep; nodep = nextp) {
        nextp = nodep->nextp();
        nodep->unlinkFrBack();
        UASSERT_OBJ(!VN_IS(nodep, Class), nodep,
                    "Module containing a class should not be inlined");
        if (AstVar* const varp = VN_CAST(nodep, Var)) {
            varp->name(prefix + varp->name());
            // Variable is now local to 'modp', rename to avoid conflicts and clear I/O bits
            if (varp->direction() == VDirection::INOUT && varp->varType() == VVarType::WIRE) {
                varp->varType(VVarType::TRIWIRE);
            }
            varp->direction(VDirection::NONE);
            if (!cellp->isTrace()) varp->trace(false);
        } else if (AstCell* const subCellp = VN_CAST(nodep, Cell)) {
            subCellp->name(prefix + subCellp->name());
            // Need to update graph. Note the vertex of the original cell was either
            // deleted (if 'last'), or user4p is a copy made by cloneTree, so reset it.
            subCellp->user4p(nullptr);
            InlineModCellVertex* const vtxp = graph.getInlineModCellVertexp(subCellp);
            graph.addEdge(*mVtxp, *vtxp);
            graph.addEdge(*vtxp, *graph.getInlineModModuleVertexp(subCellp->modp()));
        } else if (AstTypedef* const typedefp = VN_CAST(nodep, Typedef)) {
            typedefp->name(prefix + typedefp->name());
        } else if (AstNodeCoverDecl* const declp = VN_CAST(nodep, NodeCoverDecl)) {
            // Fix path in coverage statements. Per instance ones are fixed in inlineScope.
            if (!declp->perInstance()) {
                declp->hier(VString::dot(cellp->prettyName(), ".", declp->hier()));
            }
        }
        modp->addStmtsp(nodep);
    }

    // Merge each scope (instance) of the inlined cell into the scope above it
    for (AstScope* const scopep : inlineScopeps) {
        inlineScope(scopep, cellp, prefix, newCellInlinep, children);
    }
}

// Apply all inlining decisions
void process(AstNetlist* netlistp, InlineModGraph& graph) {
    // Number of inlined instances, for statistics
    VDouble0 m_nInlined;

    // Record the scope hierarchy - we need the downward links
    ScopeChildren children;
    for (AstNodeModule* modp = netlistp->modulesp(); modp;
         modp = VN_AS(modp->nextp(), NodeModule)) {
        gatherScopes(modp, children);
    }

    // Gather all cells that need to be inlined (this is in topological order)
    std::vector<InlineModCellVertex*> cVtxps;
    for (V3GraphVertex& vtx : graph.vertices()) {
        InlineModCellVertex* const cVtxp = vtx.cast<InlineModCellVertex>();
        if (!cVtxp) continue;
        if (!cVtxp->doInline()) continue;
        cVtxps.push_back(cVtxp);
    }

    // Inline cells bottom up (leaves into roots)
    for (InlineModCellVertex* const cVtxp : vlstd::reverse_view(cVtxps)) {
        // Pick up parts before deleting
        InlineModModuleVertex& mVtx = cVtxp->instanceIn();
        InlineModModuleVertex* const iVtxp = &cVtxp->instanceOf();
        AstCell* const cellp = cVtxp->cellp();
        const bool last = iVtxp->inSize1();
        UASSERT_OBJ(!iVtxp->noInlineHard(), cellp, "Should not be inlining if not possible");

        // Update
        ++m_nInlined;
        mVtx.sizeInc(iVtxp->size());  // For debug dump only

        // Delete the cell we are inlining
        VL_DO_DANGLING(cVtxp->unlinkDelete(&graph), cVtxp);
        // Delete the module we are inlining if this is the last instance
        if (last) {
            while (!iVtxp->outEmpty()) {
                InlineModCellVertex* const tVtxp
                    = iVtxp->outEdges().frontp()->top()->as<InlineModCellVertex>();
                // Bottom up ordering ensures this
                UASSERT_OBJ(!tVtxp->doInline(), tVtxp, "Should have been inlined");
                VL_DO_DANGLING(tVtxp->unlinkDelete(&graph), tVtxp);
            }
            VL_DO_DANGLING(iVtxp->unlinkDelete(&graph), iVtxp);
        }

        // Do it
        inlineCell(mVtx.modp(), cellp, last, graph, children);
        if (dumpGraphLevel() >= 9) graph.dumpDotFilePrefixed("inlinemod-cell");
    }

    // Restore varp() == varScopep()->varp() on all references, as cloning modules for
    // inlining repointed some AstVarScopes. Hierarchical references can be anywhere.
    netlistp->foreach([](AstNodeVarRef* refp) {
        AstVarScope* const vscp = refp->varScopep();
        if (vscp && refp->varp() != vscp->varp()) refp->varp(vscp->varp());
    });

    V3Stats::addStat("Optimizations, Inlined instances", m_nInlined);
}

}  //namespace ModuleInliner

//######################################################################
// V3Inline class functions

void V3Inline::inlineAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ":");

    // Build the bipartite module instantiation graph
    std::unique_ptr<InlineModGraph> graphp = InlineModGraphBuilder::apply(nodep);
    if (dumpGraphLevel() >= 6) graphp->dumpDotFilePrefixed("inlinemod-graph");

    // Decide which instances to inline
    const size_t designSize
        = graphp->vertices().frontp()->as<InlineModModuleVertex>()->flattenedSize();
    for (V3GraphVertex& vtx : graphp->vertices()) {
        if (InlineModModuleVertex* const mVtxp = vtx.cast<InlineModModuleVertex>()) {
            // If this module is less than 10% of the design, flatten this module
            if (mVtxp->flattenedSize() * 10 < designSize) mVtxp->setFlatten();
            // Don't inline if can't inline
            if (mVtxp->noInlineHard()) continue;
            // Don't inline if soft off
            if (mVtxp->noInlineSoft()) continue;
            // If all instances of this module combined are less than 20% of the design, inline all
            size_t totalSize = mVtxp->flattenedSize() * mVtxp->instanceCount();
            if (totalSize * 5 < designSize) {
                for (V3GraphEdge& edge : mVtxp->inEdges()) {
                    InlineModCellVertex* const cVtxp = edge.fromp()->as<InlineModCellVertex>();
                    cVtxp->setDoInline("< 20% of design");
                }
            }
            // No more decisions based on module vertex
            continue;
        }

        // The instantiation
        InlineModCellVertex& cVtx = *vtx.as<InlineModCellVertex>();
        // The module instantiated by this cell
        InlineModModuleVertex& mVtx = cVtx.instanceOf();

        // Don't inline if can't inline, duh!
        if (mVtx.noInlineHard()) continue;

        // If it should be inlined, inlined it
        if (mVtx.shouldInline()) cVtx.setDoInline("should inline");
        // If --flatten, inline it
        if (v3Global.opt.flatten()) cVtx.setDoInline("--flatten");

        // Don't inline for other reasons if soft off
        if (mVtx.noInlineSoft()) continue;

        // If instatiated in exactly one static site, inline it
        if (mVtx.inSize1()) cVtx.setDoInline("Single static instance");
        // If small, inline it
        if (mVtx.size() < INLINE_MODS_SMALLER) cVtx.setDoInline("Small");
        // If inlineMult is 0, inline it
        if (v3Global.opt.inlineMult() < 1) cVtx.setDoInline("inlineMult < 1");
        // If it would yield less than the given number of ops, inline it
        const size_t inlinedSize = mVtx.inEdges().size() * mVtx.size();
        const size_t limit = v3Global.opt.inlineMult();
        if (inlinedSize < limit) cVtx.setDoInline("inlinedSize < inlineMult");
    }
    if (dumpGraphLevel() >= 6) graphp->dumpDotFilePrefixed("inlinemod-decision");

    // Inline the modules we decided to inline
    ModuleInliner::process(nodep, *graphp);
    if (dumpGraphLevel() >= 6) graphp->dumpDotFilePrefixed("inlinemod-inlined");

    V3Global::dumpCheckGlobalTree("inline", 0, dumpTreeEitherLevel() >= 3);
}
