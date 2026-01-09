// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Add temporaries, such as for inline nodes
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2026 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
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
#include "V3Inst.h"
#include "V3Stats.h"

#include <unordered_set>
#include <vector>

VL_DEFINE_DEBUG_FUNCTIONS;

// CONFIG
static const int INLINE_MODS_SMALLER = 100;  // If a mod is < this # nodes, can always inline it

//######################################################################
// Inlining state. Kept as AstNodeModule::user1p via AstUser1Allocator

namespace {

struct ModuleState final {
    bool m_inlined = false;  // Whether to inline this module
    unsigned m_cellRefs = 0;  // Number of AstCells instantiating this module
    std::vector<AstCell*> m_childCells;  // AstCells under this module (to speed up traversal)
};

using ModuleStateUser1Allocator = AstUser1Allocator<AstNodeModule, ModuleState>;

}  // namespace

//######################################################################
// Visitor that determines which modules will be inlined

class InlineMarkVisitor final : public VNVisitor {
    // NODE STATE
    // Output
    //  AstNodeModule::user1()  // OUTPUT: ModuleState instance (via m_moduleState)
    // Internal state (can be cleared after this visit completes)
    //  AstNodeModule::user2()  // CIL_*. Allowed to automatically inline module
    //  AstNodeModule::user4()  // int. Statements in module
    const VNUser2InUse m_inuser2;
    const VNUser4InUse m_inuser4;

    ModuleStateUser1Allocator& m_moduleState;

    // For the user2 field:
    enum : uint8_t {
        CIL_NOTHARD = 0,  // Inline not supported
        CIL_NOTSOFT,  // Don't inline unless user overrides
        CIL_MAYBE,  // Might inline
        CIL_USER
    };  // Pragma suggests inlining

    // STATE
    AstNodeModule* m_modp = nullptr;  // Current module
    VDouble0 m_statUnsup;  // Statistic tracking
    std::vector<AstNodeModule*> m_allMods;  // All modules, in top-down order.

    // Within the context of a given module, LocalInstanceMap maps
    // from child modules to the count of each child's local instantiations.
    using LocalInstanceMap = std::unordered_map<AstNodeModule*, unsigned>;

    // We keep a LocalInstanceMap for each module in the design
    std::unordered_map<AstNodeModule*, LocalInstanceMap> m_instances;

    // METHODS
    void cantInline(const char* reason, bool hard) {
        if (hard) {
            if (m_modp->user2() != CIL_NOTHARD) {
                UINFO(4, "  No inline hard: " << reason << " " << m_modp);
                m_modp->user2(CIL_NOTHARD);
                ++m_statUnsup;
            }
        } else {
            if (m_modp->user2() == CIL_MAYBE) {
                UINFO(4, "  No inline soft: " << reason << " " << m_modp);
                m_modp->user2(CIL_NOTSOFT);
            }
        }
    }

    // VISITORS
    void visit(AstNodeModule* nodep) override {
        UASSERT_OBJ(!m_modp, nodep, "Unsupported: Nested modules");
        VL_RESTORER(m_modp);
        m_modp = nodep;
        m_allMods.push_back(nodep);
        m_modp->user2(CIL_MAYBE);
        m_modp->user4(0);  // statement count
        if (VN_IS(m_modp, Iface)) {
            // Inlining an interface means we no longer have a cell handle to resolve to.
            // If inlining moves post-scope this can perhaps be relaxed.
            cantInline("modIface", true);
        }
        if (m_modp->modPublic() && (m_modp->isTop() || !v3Global.opt.flatten())) {
            cantInline("modPublic", false);
        }

        iterateChildren(nodep);
    }
    void visit(AstClass* nodep) override {
        // TODO allow inlining of modules that have classes
        // (Probably wait for new inliner scheme)
        cantInline("class", true);
        iterateChildren(nodep);
    }
    void visit(AstCell* nodep) override {
        m_moduleState(nodep->modp()).m_cellRefs++;
        m_moduleState(m_modp).m_childCells.push_back(nodep);
        m_instances[m_modp][nodep->modp()]++;
        iterateChildren(nodep);
    }
    void visit(AstPragma* nodep) override {
        if (nodep->pragType() == VPragmaType::INLINE_MODULE) {
            if (!m_modp) {
                nodep->v3error("Inline pragma not under a module");  // LCOV_EXCL_LINE
            } else if (m_modp->user2() == CIL_MAYBE || m_modp->user2() == CIL_NOTSOFT) {
                m_modp->user2(CIL_USER);
            }
            // Remove so it does not propagate to upper cell
            VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
        } else if (nodep->pragType() == VPragmaType::NO_INLINE_MODULE) {
            if (!m_modp) {
                nodep->v3error("Inline pragma not under a module");  // LCOV_EXCL_LINE
            } else if (!v3Global.opt.flatten()) {
                cantInline("Pragma NO_INLINE_MODULE", false);
            }
            // Remove so it does not propagate to upper cell
            // Remove so don't propagate to upper cell...
            VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
        }
    }
    void visit(AstVarXRef* nodep) override {
        // Remove link. V3LinkDot will reestablish it after inlining.
        nodep->varp(nullptr);
    }
    void visit(AstNodeFTaskRef* nodep) override {
        // Remove link. V3LinkDot will reestablish it after inlining.
        // MethodCalls not currently supported by inliner, so keep linked
        if (!nodep->classOrPackagep() && !VN_IS(nodep, MethodCall)) {
            nodep->taskp(nullptr);
            VIsCached::clearCacheTree();
        }
        iterateChildren(nodep);
    }
    void visit(AstAlways* nodep) override {
        if (nodep->keyword() != VAlwaysKwd::CONT_ASSIGN) nodep->user4Inc();  // statement count
        iterateChildren(nodep);
    }
    void visit(AstNodeAssign* nodep) override {
        // Don't count assignments, as they'll likely flatten out
        // Still need to iterate though to nullify VarXRefs
        const int oldcnt = m_modp->user4();
        iterateChildren(nodep);
        m_modp->user4(oldcnt);
    }
    void visit(AstNetlist* nodep) override {
        // Build ModuleState, user2, and user4 for all modules.
        // Also build m_allMods and m_instances.
        iterateChildren(nodep);

        // Iterate through all modules in bottom-up order.
        // Make a final inlining decision for each.
        for (AstNodeModule* const modp : vlstd::reverse_view(m_allMods)) {

            // If we're going to inline some modules into this one,
            // update user4 (statement count) to reflect that:
            int statements = modp->user4();
            for (const auto& pair : m_instances[modp]) {
                const AstNodeModule* const childp = pair.first;
                if (m_moduleState(childp).m_inlined) {  // inlining child
                    statements += childp->user4() * pair.second;
                }
            }
            modp->user4(statements);

            const int allowed = modp->user2();
            const int refs = m_moduleState(modp).m_cellRefs;

            // Should we automatically inline this module?
            // If --flatten is specified, then force everything to be inlined that can be.
            // inlineMult = 2000 by default.
            // If a mod*#refs is < this # nodes, can inline it
            // Packages aren't really "under" anything so they confuse this algorithm
            const bool doit = !VN_IS(modp, Package)  //
                              && allowed != CIL_NOTHARD  //
                              && allowed != CIL_NOTSOFT  //
                              && (allowed == CIL_USER  //
                                  || v3Global.opt.flatten()  //
                                  || refs == 1  //
                                  || statements < INLINE_MODS_SMALLER  //
                                  || v3Global.opt.inlineMult() < 1  //
                                  || refs * statements < v3Global.opt.inlineMult());
            m_moduleState(modp).m_inlined = doit;
            UINFO(4, " Inline=" << doit << " Possible=" << allowed << " Refs=" << refs
                                << " Stmts=" << statements << "  " << modp);
        }
    }
    //--------------------
    void visit(AstNode* nodep) override {
        if (m_modp) m_modp->user4Inc();  // Inc statement count
        iterateChildren(nodep);
    }

public:
    // CONSTRUCTORS
    explicit InlineMarkVisitor(AstNode* nodep, ModuleStateUser1Allocator& moduleState)
        : m_moduleState{moduleState} {
        iterate(nodep);
    }
    ~InlineMarkVisitor() override {
        V3Stats::addStat("Optimizations, Inline unsupported", m_statUnsup);
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
    AstNodeModule* const m_modp;  // The module we are inlining into
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
        // connected expression (always a Const of a VarRef).
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
                const std::string name = "__vInlPlaceholder_" + std::to_string(++m_nPlaceholders);
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

        // Otherwise it must be a variable reference, retarget this ref
        const AstVarRef* const vrefp = VN_AS(pinExpr, VarRef);
        nodep->varp(vrefp->varp());
        nodep->classOrPackagep(vrefp->classOrPackagep());
    }
    void visit(AstVarXRef* nodep) override {
        // Track what scope it was originally under so V3LinkDot can resolve it
        nodep->inlinedDots(VString::dot(m_cellp->name(), ".", nodep->inlinedDots()));
        for (string tryname = nodep->dotted(); true;) {
            if (m_renamedInterfaces.count(tryname)) {
                nodep->dotted(m_cellp->name() + "__DOT__" + nodep->dotted());
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
    InlineRelinkVisitor(AstNodeModule* cloneModp, AstNodeModule* oldModp, AstCell* cellp)
        : m_modp{oldModp}
        , m_cellp{cellp} {
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
        AstAssignW* const ap
            = new AstAssignW{flp, portRef(VAccess::WRITE), pinp->cloneTree(false)};
        modp->addStmtsp(new AstAlways{ap});
        return;
    }

    // Otherwise it must be a variable reference due to having called pinReconnectSimple
    const AstVarRef* const pinRefp = VN_AS(pinExprp, VarRef);

    // Helper to create an AstVarRef reference to the pin variable
    const auto pinRef = [&](VAccess access) {
        AstVarRef* const p = new AstVarRef{pinRefp->fileline(), pinRefp->varp(), access};
        p->classOrPackagep(pinRefp->classOrPackagep());
        return p;
    };

    // If it is being inlined, create the alias for it
    if (inlineIt) {
        UINFO(6, "Inlining port variable: " << nodep);
        if (nodep->isIfaceRef()) {
            modp->addStmtsp(
                new AstAliasScope{flp, portRef(VAccess::WRITE), pinRef(VAccess::READ)});
        } else {
            AstVarRef* const aliasArgsp = portRef(VAccess::WRITE);
            aliasArgsp->addNext(pinRef(VAccess::READ));
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
        AstAssignW* const ap = new AstAssignW{flp, portRef(VAccess::WRITE), pinRef(VAccess::READ)};
        modp->addStmtsp(new AstAlways{ap});
    } else if (nodep->direction() == VDirection::OUTPUT) {
        AstAssignW* const ap = new AstAssignW{flp, pinRef(VAccess::WRITE), portRef(VAccess::READ)};
        modp->addStmtsp(new AstAlways{ap});
    } else {
        pinExprp->v3fatalSrc("V3Tristate left INOUT port");
    }
}

// Inline 'cellp' into 'modp'. 'last' indicatest this is tha last instance of the inlined module
void inlineCell(AstNodeModule* modp, AstCell* cellp, bool last) {
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
        UINFO(6, "Conecting port " << pinp->modVarp());
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

    // Cleanup var names, etc, to not conflict, relink replaced variables
    { InlineRelinkVisitor{inlinedp, modp, cellp}; }
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
void process(AstNetlist* netlistp, ModuleStateUser1Allocator& moduleStates) {
    // NODE STATE
    // Input:
    //   AstNodeModule::user1p()    // ModuleState instance (via moduleState)
    //
    // Cleared entire netlist
    //   AstIfaceRefDType::user1()  // Whether the cell pointed to by this
    //                              // AstIfaceRefDType has been inlined
    //   AstCell::user3p()      // AstCell*, the clone
    //   AstVar::user3p()       // AstVar*, the clone clone
    // Cleared each cell
    //   AstVar::user2p()       // AstVarRef*/AstConst* This port is connected to (AstPin::expr())
    const VNUser3InUse m_user3InUse;

    // Number of inlined instances, for statistics
    VDouble0 m_nInlined;

    // We want to inline bottom up. The modules under the netlist are in
    // dependency order (top first, leaves last), so find the end of the list.
    AstNode* nodep = netlistp->modulesp();
    while (nodep->nextp()) nodep = nodep->nextp();

    // Iterate module list backwards (stop when we get back to the Netlist)
    while (AstNodeModule* const modp = VN_CAST(nodep, NodeModule)) {
        nodep = nodep->backp();

        // Consider each cell inside the current module for inlining
        for (AstCell* const cellp : moduleStates(modp).m_childCells) {
            ModuleState& childState = moduleStates(cellp->modp());
            if (!childState.m_inlined) continue;
            ++m_nInlined;
            inlineCell(modp, cellp, --childState.m_cellRefs == 0);
        }
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

    {
        const VNUser1InUse m_inuser1;  // output of InlineMarkVisitor, input to InlineVisitor.
        ModuleStateUser1Allocator moduleState;  // AstUser1Allocator

        // Scoped to clean up temp userN's
        { InlineMarkVisitor{nodep, moduleState}; }

        // Inline the modles we decided to inline
        ModuleInliner::process(nodep, moduleState);

        // Check inlined modules have been removed during traversal. Otherwise we might have blown
        // up Verilator memory consumption.
        for (AstNodeModule* modp = v3Global.rootp()->modulesp(); modp;
             modp = VN_AS(modp->nextp(), NodeModule)) {
            UASSERT_OBJ(!moduleState(modp).m_inlined, modp,
                        "Inlined module should have been deleted when the last instance "
                        "referencing it was inlined");
        }
    }

    V3Global::dumpCheckGlobalTree("inline", 0, dumpTreeEitherLevel() >= 3);
}
