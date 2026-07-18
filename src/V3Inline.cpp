// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Add temporaries, such as for inline nodes
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
//              Convert pins to wires that make assignments
//              Rename vars to include cell name
//          Insert cell's module statements into the upper module
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Inline.h"

#include "V3AstUserAllocator.h"
#include "V3Graph.h"
#include "V3Inst.h"
#include "V3Stats.h"

#include <unordered_set>
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

    // VISITORS
    void visit(AstNodeModule* nodep) override {
        if (nodep == v3Global.rootp()->constPoolp()->modp()) return;  // Ignore const pool module

        UASSERT_OBJ(!m_modVtxp, nodep, "Unsupported: Nested modules");

        // Create the module vertex
        InlineModModuleVertex* const vtxp = m_graphp->getInlineModModuleVertexp(nodep);

        // Check if the module itself is not inlineable

        // Inlining an interface means we no longer have a cell handle to resolve to.
        // If inlining moves post-scope this can perhaps be relaxed.
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
        m_modVtxp = vtxp;
        iterateChildrenConst(nodep);
    }

    void visit(AstClass* nodep) override {
        // TODO allow inlining of modules that contain classes
        if (m_modVtxp) m_modVtxp->setNoInlineHard("Contains class");
        iterateChildrenConst(nodep);  // TODO: this is only needed or FTaskRef cleanup
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

    // TODO: Bit nasty to do this here, but historically present, and still necessary
    void visit(AstNodeFTaskRef* nodep) override {
        if (m_modVtxp) m_modVtxp->sizeInc();
        // Remove link. V3LinkDot will reestablish it after inlining.
        // MethodCalls not currently supported by inliner, so keep linked
        if (!nodep->classOrPackagep() && !VN_IS(nodep, MethodCall)) {
            nodep->taskp(nullptr);
            VIsCached::clearCacheTree();
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
// After cell is cloned, relink the new module's contents

class InlineRelinkVisitor final : public VNVisitor {
    // NODE STATE
    //  Input:
    //   See InlineVisitor

    // STATE
    std::unordered_set<std::string> m_renamedInterfaces;  // Name of renamed interface variables
    std::unordered_set<std::string>
        m_priorInlinedCells;  // Cells previously inlined into the module being inlined here.
                              // Used to recognize VarXRefs whose inlinedDots was stamped by a
                              // prior V3Inline pass (vs. by V3Begin generate-block unrolling).
    std::unordered_set<const AstVarXRef*>
        m_pinSubstitutedXRefs;  // VarXRefs created by pin substitution in this relink pass.
                                // Their dotted/inlinedDots already represent the parent's scope
                                // and must not be rewritten on the immediate visit.
    InlineModGraph& m_graph;  // The instance graph
    AstNodeModule* const m_modp;  // The module we are inlining into
    // The vertex of the module we are inlining into, for updating the graph
    InlineModModuleVertex* const m_mVtxp = m_graph.getInlineModModuleVertexp(m_modp);
    const AstCell* const m_cellp;  // The cell being inlined

    size_t m_nPlaceholders = 0;  // Unique identifier sequence number for placeholder variables

    // VISITORS
    void visit(AstCellInline* nodep) override {
        // Inlined cell under the inline cell, need to move to avoid conflicts
        nodep->unlinkFrBack();
        m_modp->addInlinesp(nodep);
        // Rename
        nodep->name(m_cellp->name() + "__DOT__" + nodep->name());
        UINFO(6, "    Inline " << nodep);
        // Do CellInlines under this, but don't move them
        iterateChildren(nodep);
    }
    void visit(AstCell* nodep) override {
        // Cell under the inline cell, need to rename to avoid conflicts
        nodep->name(m_cellp->name() + "__DOT__" + nodep->name());
        // Need to update graph
        nodep->user4p(nullptr);  // clone copied user4p, reset to make new vertex
        InlineModCellVertex* const vtxp = m_graph.getInlineModCellVertexp(nodep);
        m_graph.addEdge(*m_mVtxp, *vtxp);
        m_graph.addEdge(*vtxp, *m_graph.getInlineModModuleVertexp(nodep->modp()));
        iterateChildren(nodep);
    }
    void visit(AstClass* nodep) override {
        nodep->name(m_cellp->name() + "__DOT__" + nodep->name());
        iterateChildren(nodep);
    }
    void visit(AstModule* nodep) override {
        m_renamedInterfaces.clear();
        iterateChildren(nodep);
    }
    void visit(AstVar* nodep) override {
        // Iterate won't hit AstIfaceRefDType directly as it is no longer underneath the module
        if (AstIfaceRefDType* const ifacerefp = VN_CAST(nodep->dtypep(), IfaceRefDType)) {
            m_renamedInterfaces.insert(nodep->name());
            // Each inlined cell that contain an interface variable need to
            // copy the IfaceRefDType and point it to the newly cloned
            // interface cell.
            AstIfaceRefDType* const newdp = ifacerefp->cloneTree(false);
            nodep->dtypep(newdp);
            ifacerefp->addNextHere(newdp);
            // Relink to point to newly cloned cell
            if (newdp->cellp()) {
                if (AstCell* const newcellp = VN_CAST(newdp->cellp()->user3p(), Cell)) {
                    newdp->cellp(newcellp);
                    newdp->cellName(newcellp->name());
                    // Tag the old ifacerefp to ensure it leaves no stale
                    // reference to the inlined cell.
                    newdp->user1(false);
                    ifacerefp->user1(true);
                }
            }
        }
        // Variable under the inline cell, need to rename to avoid conflicts
        // Also clear I/O bits, as it is now local.
        const string name = m_cellp->name() + "__DOT__" + nodep->name();
        if (!nodep->isFuncLocal() && !nodep->isClassMember()) nodep->inlineAttrReset(name);
        if (!m_cellp->isTrace()) nodep->trace(false);
        UINFOTREE(9, nodep, "", "varchanged");
    }
    void visit(AstNodeFTask* nodep) override {
        // Function under the inline cell, need to rename to avoid conflicts
        nodep->name(m_cellp->name() + "__DOT__" + nodep->name());
        iterateChildren(nodep);
    }
    void visit(AstTypedef* nodep) override {
        // Typedef under the inline cell, need to rename to avoid conflicts
        nodep->name(m_cellp->name() + "__DOT__" + nodep->name());
        iterateChildren(nodep);
    }
    void visit(AstAlias* nodep) override {
        // Don't replace port variable in the alias
    }
    void visit(AstVarRef* nodep) override {
        // If the target port is being inlined, replace reference with the
        // connected expression (a Const, VarRef, or VarXRef).
        AstNode* const pinExpr = nodep->varp()->user2p();
        if (!pinExpr) return;

        // If it's a constant, inline it
        if (AstConst* const constp = VN_CAST(pinExpr, Const)) {
            // You might think we would not try to substitute a constant for
            // a written variable, but we might need to do this if for example
            // there is an assignment to an input port, and that input port
            // is tied to a constant on the cell we are inlining. This does
            // generate an ASSIGNIN warning, but that can be downgraded to
            // a warning. (Also assigning to an input can has valid uses if
            // e.g. done via a hierarchical reference from outside to an input
            // unconnected on the instance, so we don't want ASSIGNIN fatal.)
            // Same applies when there is a static initialzier for an input.
            // To avoid having to special case malformed assignment, or worse
            // yet emiting code like 0 = 0, we instead substitute a placeholder
            // variable that will later be pruned (it will otherwise be unreferenced).
            if (!nodep->access().isReadOnly()) {
                AstVar* const varp = nodep->varp();
                const std::string name
                    = m_cellp->name() + "__vInlPlaceholder_" + std::to_string(++m_nPlaceholders);
                AstVar* const holdep = new AstVar{varp->fileline(), VVarType::VAR, name, varp};
                m_modp->addStmtsp(holdep);
                AstVarRef* const newp = new AstVarRef{nodep->fileline(), holdep, nodep->access()};
                nodep->replaceWith(newp);
            } else {
                nodep->replaceWith(constp->cloneTree(false));
            }
            VL_DO_DANGLING(nodep->deleteTree(), nodep);
            return;
        }

        // Handle VarRef: simple retarget
        if (const AstVarRef* const vrefp = VN_CAST(pinExpr, VarRef)) {
            nodep->varp(vrefp->varp());
            nodep->classOrPackagep(vrefp->classOrPackagep());
            return;
        }

        // Handle VarXRef: replace VarRef with VarXRef (e.g., nested interface port)
        const AstVarXRef* const xrefp = VN_AS(pinExpr, VarXRef);
        AstVarXRef* const newp
            = new AstVarXRef{nodep->fileline(), xrefp->name(), xrefp->dotted(), nodep->access()};
        newp->varp(xrefp->varp());
        // The pin expression came from m_modp (the parent we are inlining into), so its
        // dotted/inlinedDots already describe a path in m_modp's scope. Record this xref
        // so visit(AstVarXRef) leaves it alone on the immediate visit; later inline
        // passes will prepend their cell names normally.
        newp->inlinedDots(xrefp->inlinedDots());
        m_pinSubstitutedXRefs.insert(newp);
        nodep->replaceWith(newp);
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
    }
    void visit(AstVarXRef* nodep) override {
        // VarXRefs just created by pin substitution in this pass already describe a path
        // in m_modp's scope (the parent we are inlining into). Leave them untouched on
        // this immediate visit; subsequent inline passes will prepend their cell names.
        if (m_pinSubstitutedXRefs.erase(nodep)) {
            iterateChildren(nodep);
            return;
        }
        // Track what scope it was originally under so V3LinkDot can resolve it
        const string origInlinedDots = nodep->inlinedDots();
        nodep->inlinedDots(VString::dot(m_cellp->name(), ".", origInlinedDots));
        // If origInlinedDots starts with the name of a previously-inlined cell, this
        // VarXRef came from that cell's body and its dotted refers to that child's
        // local scope; renaming it against m_renamedInterfaces would wrongly alias it
        // to a coincidentally-named var in the current module (#5120). VarXRefs whose
        // inlinedDots was stamped by V3Begin generate-block unrolling are unaffected,
        // since V3Begin's CellInlines have origModName "__BEGIN__" and don't appear in
        // m_priorInlinedCells.
        const string::size_type firstDot = origInlinedDots.find('.');
        const string firstSeg
            = firstDot == string::npos ? origInlinedDots : origInlinedDots.substr(0, firstDot);
        const bool fromPriorInline = m_priorInlinedCells.count(firstSeg);
        for (string tryname = nodep->dotted(); true;) {
            if (m_renamedInterfaces.count(tryname)) {
                // matchIsRenamed: the matched name itself was created by a prior V3Inline
                // rename (contains "__DOT__"). When true, we are following the chain of
                // renames for the same var across nested inlines, so apply the rename
                // even if the VarXRef came from a prior-inlined child.
                const bool matchIsRenamed = tryname.find("__DOT__") != string::npos;
                if (!fromPriorInline || matchIsRenamed) {
                    nodep->dotted(m_cellp->name() + "__DOT__" + nodep->dotted());
                }
                break;
            }
            // If foo.bar, and foo is an interface, then need to search again for foo
            const string::size_type pos = tryname.rfind('.');
            if (pos == string::npos || pos == 0) {
                break;
            } else {
                tryname.resize(pos);
            }
        }
        iterateChildren(nodep);
    }
    void visit(AstNodeFTaskRef* nodep) override {
        // Track what scope it was originally under so V3LinkDot can resolve it
        nodep->inlinedDots(VString::dot(m_cellp->name(), ".", nodep->inlinedDots()));
        if (m_renamedInterfaces.count(nodep->dotted())) {
            nodep->dotted(m_cellp->name() + "__DOT__" + nodep->dotted());
        }
        UINFO(8, "   " << nodep);
        iterateChildren(nodep);
    }

    // Not needed, as V3LinkDot doesn't care about typedefs
    //  void visit(AstRefDType* nodep) override {}

    void visit(AstScopeName* nodep) override {
        // If there's a %m in the display text, we add a special node that will contain the name()
        // Similar code in V3Begin
        // To keep correct visual order, must add before exising
        nodep->scopeAttr("__DOT__" + m_cellp->name() + nodep->scopeAttr());
        nodep->scopeEntr("__DOT__" + m_cellp->name() + nodep->scopeEntr());
        iterateChildren(nodep);
    }
    void visit(AstNodeCoverDecl* nodep) override {
        // Fix path in coverage statements
        nodep->hier(VString::dot(m_cellp->prettyName(), ".", nodep->hier()));
        iterateChildren(nodep);
    }
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    InlineRelinkVisitor(AstNodeModule* cloneModp, AstNodeModule* oldModp, AstCell* cellp,
                        InlineModGraph& graph)
        : m_graph{graph}
        , m_modp{oldModp}
        , m_cellp{cellp} {
        // CellInlines added by V3Begin for generate/named blocks have origModName
        // "__BEGIN__"; only those added by prior V3Inline passes carry a real module
        // name. Track the latter so visit(AstVarXRef) can distinguish VarXRefs
        // originating from previously-inlined children.
        for (AstNode* nodep = cloneModp->inlinesp(); nodep; nodep = nodep->nextp()) {
            const AstCellInline* const cip = VN_CAST(nodep, CellInline);
            if (cip && cip->origModName() != "__BEGIN__") {
                m_priorInlinedCells.insert(cip->name());
            }
        }
        iterate(cloneModp);
    }
    ~InlineRelinkVisitor() override = default;
};

//######################################################################
// Module inliner

namespace ModuleInliner {

// A port variable in an inlined module can be connected 2 ways.
// Either add a continuous assignment between the pin expression from
// the instance and the port variable, or simply inline the pin expression
// in place of the port variable. We will prefer to do the later whenever
// possible (and sometimes required). When inlining, we need to create an
// alias for the inlined variable, in order to resovle hierarchical references
// against it later in V3Scope (and also for tracing, which is inserted
//later). Returns ture iff the given port variable should be inlined,
// and false if a continuous assignment should be used.
bool inlinePort(const AstVar* nodep) {
    // Interface references are always inlined
    if (nodep->isIfaceRef()) return true;
    // Ref ports must be always inlined
    if (nodep->direction() == VDirection::REF) return true;
    // Forced signals must not be inlined. The port signal can be
    // forced separately from the connected signals.
    if (nodep->isForced()) return false;

    // Note: For singls marked 'public' (and not 'public_flat') inlining
    // of their containing modules is disabled so they wont reach here.

    // TODO: For now, writable public signals inside the cell cannot be
    // eliminated as they are entered into the VerilatedScope, and
    // changes would not propagate to it when assigned. (The alias created
    // for them ensures they would be read correctly, but would not
    // propagate any changes.) This can be removed when the VerialtedScope
    // construction in V3EmitCSyms understands aliases.
    if (nodep->isSigUserRWPublic()) return false;

    // Otherwise we can repalce the variable
    return true;
}

// Connect the given port 'nodep' (being inlined into 'modp') to the given
// expression (from the Cell Pin)
void connectPort(AstNodeModule* modp, AstVar* nodep, AstNodeExpr* pinExprp) {
    UINFO(6, "Connecting " << pinExprp);
    UINFO(6, "        to " << nodep);

    // Decide whether to inline the port variable or use continuous assignments
    const bool inlineIt = inlinePort(nodep);

    // If we deccided to inline it, record the expression to substitute this variable with
    if (inlineIt) nodep->user2p(pinExprp);

    FileLine* const flp = nodep->fileline();

    // Helper to creates an AstVarRef reference to the port variable
    const auto portRef = [&](VAccess access) { return new AstVarRef{flp, nodep, access}; };

    // If the connected expression is a constant, add an assignment to set
    // the port variable. The constant can still be inlined, in which case
    // this is needed for tracing the inlined port variable.
    if (AstConst* const pinp = VN_CAST(pinExprp, Const)) {
        AstVarRef* const lhsp = portRef(VAccess::WRITE);
        lhsp->varp()->isContinuously(true);
        AstAssignW* const ap = new AstAssignW{flp, lhsp, pinp->cloneTree(false)};
        modp->addStmtsp(new AstAlways{ap});
        return;
    }

    // Otherwise it must be a variable reference due to having called pinReconnectSimple
    const AstNodeVarRef* const pinRefp = VN_AS(pinExprp, NodeVarRef);

    const auto pinRefAsVarRef = [&](VAccess access) -> AstVarRef* {
        const AstVarRef* const vrp = VN_AS(pinRefp, VarRef);
        AstVarRef* const newp = new AstVarRef{vrp->fileline(), vrp->varp(), access};
        newp->classOrPackagep(vrp->classOrPackagep());
        return newp;
    };

    const auto pinRefAsExpr = [&](VAccess access) -> AstNodeExpr* {
        if (const AstVarRef* const vrp = VN_CAST(pinRefp, VarRef)) {
            AstVarRef* const newp = new AstVarRef{vrp->fileline(), vrp->varp(), access};
            newp->classOrPackagep(vrp->classOrPackagep());
            return newp;
        } else {
            const AstVarXRef* const xrp = VN_AS(pinRefp, VarXRef);
            AstVarXRef* const newp
                = new AstVarXRef{xrp->fileline(), xrp->name(), xrp->dotted(), access};
            newp->varp(xrp->varp());
            newp->inlinedDots(xrp->inlinedDots());
            return newp;
        }
    };

    // If it is being inlined, create the alias for it
    if (inlineIt) {
        UINFO(6, "Inlining port variable: " << nodep);
        if (nodep->isIfaceRef()) {
            modp->addStmtsp(
                new AstAliasScope{flp, portRef(VAccess::WRITE), pinRefAsExpr(VAccess::READ)});
        } else {
            AstVarRef* const aliasArgsp = portRef(VAccess::WRITE);
            aliasArgsp->addNext(pinRefAsVarRef(VAccess::READ));
            modp->addStmtsp(new AstAlias{flp, aliasArgsp});
        }
        // They will become the same variable, so propagate file-line and variable attributes
        pinRefp->varp()->fileline()->modifyStateInherit(flp);
        flp->modifyStateInherit(pinRefp->varp()->fileline());
        pinRefp->varp()->propagateAttrFrom(nodep);
        nodep->propagateAttrFrom(pinRefp->varp());
        return;
    }

    // Otherwise create the continuous assignment between the port var and the pin expression
    UINFO(6, "Not inlining port variable: " << nodep);
    if (nodep->direction() == VDirection::INPUT) {
        AstVarRef* const lhsp = portRef(VAccess::WRITE);
        lhsp->varp()->isContinuously(true);
        AstAssignW* const ap = new AstAssignW{flp, lhsp, pinRefAsExpr(VAccess::READ)};
        modp->addStmtsp(new AstAlways{ap});
    } else if (nodep->direction() == VDirection::OUTPUT) {
        AstNodeVarRef* const lhsp = VN_AS(pinRefAsExpr(VAccess::WRITE), NodeVarRef);
        lhsp->varp()->isContinuously(true);
        AstAssignW* const ap = new AstAssignW{flp, lhsp, portRef(VAccess::READ)};
        modp->addStmtsp(new AstAlways{ap});
    } else {
        pinExprp->v3fatalSrc("V3Tristate left INOUT port");
    }
}

// Inline 'cellp' into 'modp'. 'last' indicatest this is tha last instance of the inlined module
void inlineCell(AstNodeModule* modp, AstCell* cellp, bool last, InlineModGraph& graph) {
    UINFO(5, " Inline Cell  " << cellp);
    UINFO(5, " into Module  " << modp);

    const VNUser2InUse user2InUse;

    // Important: If this is the last cell, then don't clone the instantiated module but
    // inline the original directly. While this requires some special casing, doing so
    // saves us having to temporarily clone the module for the last cell, which
    // significantly reduces Verilator memory usage. This is especially true as often the
    // top few levels of the hierarchy are singleton wrapper modules, which we always
    // inline. In this case this special casing saves us from having to clone essentially
    // the entire netlist, which would in effect double Verilator memory consumption, or
    // worse if we put off deleting the inlined modules until the end. Not having to clone
    // large trees also improves speed.

    // The module we will yank the contents out of and put into 'modp'
    AstNodeModule* const inlinedp = last ? cellp->modp()->unlinkFrBack()  //
                                         : cellp->modp()->cloneTree(false);

    // Compute map from original port variables and cells to their clones
    for (AstNode *ap = cellp->modp()->stmtsp(), *bp = inlinedp->stmtsp(); ap || bp;
         ap = ap->nextp(), bp = bp->nextp()) {
        UASSERT_OBJ(ap && bp, ap ? ap : bp, "Clone has different number of children");
        // We only care about AstVar and AstCell, but faster to just set them all
        ap->user3p(bp);
    }

    // Create data for resolving hierarchical references later.
    modp->addInlinesp(
        new AstCellInline{cellp->fileline(), cellp->name(), cellp->modp()->origName()});

    // Connect the pins on the instance
    for (AstPin* pinp = cellp->pinsp(); pinp; pinp = VN_AS(pinp->nextp(), Pin)) {
        if (!pinp->exprp()) continue;
        UINFO(6, "Connecting port " << pinp->modVarp());
        UINFO(6, "   of instance " << cellp);

        // Make sure the conneccted pin expression is always a VarRef or a Const
        V3Inst::pinReconnectSimple(pinp, cellp, false);

        // Warn
        V3Inst::checkOutputShort(pinp);
        if (!pinp->exprp()) continue;

        // Pick up the old and new port variables signal (new is the same on last instance)
        const AstVar* const oldModVarp = pinp->modVarp();
        AstVar* const newModVarp = VN_AS(oldModVarp->user3p(), Var);
        // Pick up the connected expression (a VarRef or Const due to pinReconnectSimple)
        AstNodeExpr* const pinExprp = VN_AS(pinp->exprp(), NodeExpr);

        // Connect up the port
        connectPort(modp, newModVarp, pinExprp);
    }

    // Cleanup var names, etc, to not conflict, relink replaced variables, adjust graph
    { InlineRelinkVisitor{inlinedp, modp, cellp, graph}; }
    // Move statements from the inlined module into the module we are inlining into
    if (AstNode* const stmtsp = inlinedp->stmtsp()) {
        modp->addStmtsp(stmtsp->unlinkFrBackWithNext());
    }
    // Delete the empty shell of the inlined module
    VL_DO_DANGLING(inlinedp->deleteTree(), inlinedp);
    // Remove the cell we just inlined
    VL_DO_DANGLING(cellp->unlinkFrBack()->deleteTree(), cellp);
}

// Apply all inlining decisions
void process(AstNetlist* netlistp, InlineModGraph& graph) {
    // NODE STATE
    // Cleared entire netlist
    //   AstIfaceRefDType::user1()  // Whether the cell pointed to by this
    //                              // AstIfaceRefDType has been inlined
    //   AstCell::user3p()      // AstCell*, the clone
    //   AstVar::user3p()       // AstVar*, the clone
    // Cleared each cell
    //   AstVar::user2p()       // AstVarRef*/AstConst* This port is connected to (AstPin::expr())
    const VNUser1InUse user1InUse;
    const VNUser3InUse user3InUse;

    // Number of inlined instances, for statistics
    VDouble0 m_nInlined;

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
        inlineCell(mVtx.modp(), cellp, last, graph);
        if (dumpGraphLevel() >= 9) graph.dumpDotFilePrefixed("inlinemod-cell");
    }

    V3Stats::addStat("Optimizations, Inlined instances", m_nInlined);

    // Clean up AstIfaceRefDType references
    // If the cell has been removed let's make sure we don't leave a
    // reference to it. This dtype may still be in use by the
    // AstAliasScope created earlier but that'll get cleared up later
    netlistp->typeTablep()->foreach([](AstIfaceRefDType* nodep) {
        if (nodep->user1()) nodep->cellp(nullptr);
    });
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

    // Inline the modles we decided to inline
    ModuleInliner::process(nodep, *graphp);
    if (dumpGraphLevel() >= 6) graphp->dumpDotFilePrefixed("inlinemod-inlined");

    V3Global::dumpCheckGlobalTree("inline", 0, dumpTreeEitherLevel() >= 3);
}
