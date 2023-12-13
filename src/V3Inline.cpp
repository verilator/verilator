// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Add temporaries, such as for inline nodes
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2023 by Wilson Snyder. This program is free software; you
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

struct ModuleState {
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
                UINFO(4, "  No inline hard: " << reason << " " << m_modp << endl);
                m_modp->user2(CIL_NOTHARD);
                ++m_statUnsup;
            }
        } else {
            if (m_modp->user2() == CIL_MAYBE) {
                UINFO(4, "  No inline soft: " << reason << " " << m_modp << endl);
                m_modp->user2(CIL_NOTSOFT);
            }
        }
    }

    // VISITORS
    void visit(AstNodeModule* nodep) override {
        UASSERT_OBJ(!m_modp, nodep, "Unsupported: Nested modules");
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
        m_modp = nullptr;
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
        m_modp->user4Inc();  // statement count
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
                                << " Stmts=" << statements << "  " << modp << endl);
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
    AstNodeModule* const m_modp;  // Current module
    const AstCell* const m_cellp;  // Cell being cloned

    // VISITORS
    void visit(AstCellInline* nodep) override {
        // Inlined cell under the inline cell, need to move to avoid conflicts
        nodep->unlinkFrBack();
        m_modp->addInlinesp(nodep);
        // Rename
        nodep->name(m_cellp->name() + "__DOT__" + nodep->name());
        UINFO(6, "    Inline " << nodep << endl);
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
        if (nodep->user2p()) {
            // Make an assignment, so we'll trace it properly
            // user2p is either a const or a var.
            FileLine* const flp = nodep->fileline();
            AstConst* const exprconstp = VN_CAST(nodep->user2p(), Const);
            const AstVarRef* const exprvarrefp = VN_CAST(nodep->user2p(), VarRef);
            UINFO(8, "connectto: " << nodep->user2p() << endl);
            UASSERT_OBJ(exprconstp || exprvarrefp, nodep,
                        "Unknown interconnect type; pinReconnectSimple should have cleared up");
            if (exprconstp) {
                m_modp->addStmtsp(new AstAssignW{flp, new AstVarRef{flp, nodep, VAccess::WRITE},
                                                 exprconstp->cloneTree(false)});
            } else if (nodep->user3()) {
                // Public variable at the lower module end - we need to make sure we propagate
                // the logic changes up and down; if we aliased, we might
                // remove the change detection on the output variable.
                UINFO(9, "public pin assign: " << exprvarrefp << endl);
                UASSERT_OBJ(!nodep->isNonOutput(), nodep, "Outputs only - inputs use AssignAlias");
                m_modp->addStmtsp(
                    new AstAssignW{flp, new AstVarRef{flp, exprvarrefp->varp(), VAccess::WRITE},
                                   new AstVarRef{flp, nodep, VAccess::READ}});
            } else if (nodep->isSigPublic() && VN_IS(nodep->dtypep(), UnpackArrayDType)) {
                // Public variable at this end and it is an unpacked array. We need to assign
                // instead of aliased, because otherwise it will pass V3Slice and invalid
                // code will be emitted.
                UINFO(9, "assign to public and unpacked: " << nodep << endl);
                m_modp->addStmtsp(
                    new AstAssignW{flp, new AstVarRef{flp, nodep, VAccess::WRITE},
                                   new AstVarRef{flp, exprvarrefp->varp(), VAccess::READ}});
            } else if (nodep->isIfaceRef()) {
                m_modp->addStmtsp(
                    new AstAssignVarScope{flp, new AstVarRef{flp, nodep, VAccess::WRITE},
                                          new AstVarRef{flp, exprvarrefp->varp(), VAccess::READ}});
                FileLine* const flbp = exprvarrefp->varp()->fileline();
                flp->modifyStateInherit(flbp);
                flbp->modifyStateInherit(flp);
            } else {
                // Do to inlining child's variable now within the same
                // module, so a AstVarRef not AstVarXRef below
                m_modp->addStmtsp(
                    new AstAssignAlias{flp, new AstVarRef{flp, nodep, VAccess::WRITE},
                                       new AstVarRef{flp, exprvarrefp->varp(), VAccess::READ}});
                FileLine* const flbp = exprvarrefp->varp()->fileline();
                flp->modifyStateInherit(flbp);
                flbp->modifyStateInherit(flp);
            }
        }
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
                if (AstCell* const newcellp = VN_CAST(newdp->cellp()->user4p(), Cell)) {
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
        if (debug() >= 9) nodep->dumpTree("-  varchanged: ");
        if (debug() >= 9 && nodep->valuep()) nodep->valuep()->dumpTree("-  varchangei: ");
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
    void visit(AstVarRef* nodep) override {
        if (nodep->varp()->user2p()  // It's being converted to an alias.
            && !nodep->varp()->user3()
            // Don't constant propagate aliases (we just made)
            && !VN_IS(nodep->backp(), AssignAlias)) {
            AstVar* const varp = nodep->varp();
            if (AstConst* const constp = VN_CAST(varp->user2p(), Const)) {
                nodep->replaceWith(constp->cloneTree(false));
                VL_DO_DANGLING(nodep->deleteTree(), nodep);
                return;
            } else if (const AstVarRef* const vrefp = VN_CAST(varp->user2p(), VarRef)) {
                nodep->varp(vrefp->varp());
            } else {
                nodep->v3fatalSrc("Null connection?");
            }
        }
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
                tryname = tryname.substr(0, pos);
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
        UINFO(8, "   " << nodep << endl);
        iterateChildren(nodep);
    }

    // Not needed, as V3LinkDot doesn't care about typedefs
    //  void visit(AstRefDType* nodep) override {}

    void visit(AstScopeName* nodep) override {
        // If there's a %m in the display text, we add a special node that will contain the name()
        // Similar code in V3Begin
        // To keep correct visual order, must add before other Text's
        AstText* afterp = nodep->scopeAttrp();
        if (afterp) afterp->unlinkFrBackWithNext();
        nodep->addScopeAttrp(
            new AstText{nodep->fileline(), std::string{"__DOT__"} + m_cellp->name()});
        if (afterp) nodep->addScopeAttrp(afterp);
        afterp = nodep->scopeEntrp();
        if (afterp) afterp->unlinkFrBackWithNext();
        nodep->addScopeEntrp(
            new AstText{nodep->fileline(), std::string{"__DOT__"} + m_cellp->name()});
        if (afterp) nodep->addScopeEntrp(afterp);
        iterateChildren(nodep);
    }
    void visit(AstCoverDecl* nodep) override {
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
// Inline state, as a visitor of each AstNode

class InlineVisitor final : public VNVisitor {
    // NODE STATE
    // Cleared entire netlist
    //  AstIfaceRefDType::user1()  // Whether the cell pointed to by this
    //                             // AstIfaceRefDType has been inlined
    //  Input:
    //   AstNodeModule::user1p()    // ModuleState instance (via m_moduleState)
    // Cleared each cell
    //   AstVar::user2p()       // AstVarRef*/AstConst*  Points to signal this
    //                          // is a direct connect to
    //   AstVar::user3()        // bool    Don't alias the user2, keep it as signal
    //   AstCell::user4         // AstCell* of the created clone
    const VNUser4InUse m_inuser4;

    ModuleStateUser1Allocator& m_moduleState;

    // STATE
    AstNodeModule* m_modp = nullptr;  // Current module
    VDouble0 m_statCells;  // Statistic tracking

    // METHODS
    void inlineCell(AstCell* nodep) {
        UINFO(5, " Inline CELL   " << nodep << endl);

        const VNUser2InUse user2InUse;
        const VNUser3InUse user3InUse;

        ++m_statCells;

        // Before cloning simplify pin assignments. Better off before, as if the module has
        // multiple instantiations we will save work, and we can't call pinReconnectSimple in this
        // loop as it clone()s itself.
        for (AstPin* pinp = nodep->pinsp(); pinp; pinp = VN_AS(pinp->nextp(), Pin)) {
            V3Inst::pinReconnectSimple(pinp, nodep, false);
        }

        // Is this the last cell referencing this module?
        const bool lastCell = --m_moduleState(nodep->modp()).m_cellRefs == 0;

        // Important: If this is the last cell, then don't clone the instantiated module but
        // inline the original directly. While this requires some special casing, doing so
        // saves us having to temporarily clone the module for the last cell, which
        // significantly reduces Verilator memory usage. This is especially true as often the
        // top few levels of the hierarchy are singleton wrapper modules, which we always
        // inline. In this case this special casing saves us from having to clone essentially
        // the entire netlist, which would in effect double Verilator memory consumption, or
        // worse if we put off deleting the inlined modules until the end. Not having to clone
        // large trees also improves speed.
        AstNodeModule* newmodp = nullptr;
        if (!lastCell) {
            // Clone original module
            newmodp = nodep->modp()->cloneTree(false);
        } else {
            // For the last cell, reuse the original module
            nodep->modp()->unlinkFrBack();
            newmodp = nodep->modp();
        }
        // Find cell cross-references
        nodep->modp()->foreach([](AstCell* cellp) {
            // clonep is nullptr when inlining the last instance, if so the use original node
            cellp->user4p(cellp->clonep() ? cellp->clonep() : cellp);
        });
        // Create data for dotted variable resolution
        AstCellInline* const inlinep
            = new AstCellInline{nodep->fileline(), nodep->name(), nodep->modp()->origName(),
                                nodep->modp()->timeunit()};
        m_modp->addInlinesp(inlinep);  // Must be parsed before any AstCells
        // Create assignments to the pins
        for (AstPin* pinp = nodep->pinsp(); pinp; pinp = VN_AS(pinp->nextp(), Pin)) {
            if (!pinp->exprp()) continue;
            UINFO(6, "     Pin change from " << pinp->modVarp() << endl);

            AstNode* const connectRefp = pinp->exprp();
            UASSERT_OBJ(VN_IS(connectRefp, Const) || VN_IS(connectRefp, VarRef), pinp,
                        "Unknown interconnect type; pinReconnectSimple should have cleared up");
            V3Inst::checkOutputShort(pinp);

            // Make new signal; even though we'll optimize the interconnect, we
            // need an alias to trace correctly.  If tracing is disabled, we'll
            // delete it in later optimizations.
            AstVar* const pinOldVarp = pinp->modVarp();
            AstVar* const pinNewVarp = lastCell ? pinOldVarp : pinOldVarp->clonep();
            UASSERT_OBJ(pinNewVarp, pinOldVarp, "Cloning failed");
            // Propagate any attributes across the interconnect
            pinNewVarp->propagateAttrFrom(pinOldVarp);
            if (const AstVarRef* const vrefp = VN_CAST(connectRefp, VarRef)) {
                vrefp->varp()->propagateAttrFrom(pinOldVarp);
            }

            // One to one interconnect won't make a temporary variable.
            // This prevents creating a lot of extra wires for clock signals.
            // It will become a tracing alias.
            UINFO(6, "One-to-one " << connectRefp << endl);
            UINFO(6, "       -to " << pinNewVarp << endl);
            pinNewVarp->user2p(connectRefp);
            // Public output inside the cell must go via an assign rather
            // than alias.  Else the public logic will set the alias, losing
            // the value to be propagated up (InOnly isn't a problem as the
            // AssignAlias will create the assignment for us)
            pinNewVarp->user3(pinNewVarp->isSigUserRWPublic()
                              && pinNewVarp->direction() == VDirection::OUTPUT);
        }
        // Cleanup var names, etc, to not conflict
        { InlineRelinkVisitor{newmodp, m_modp, nodep}; }
        // Move statements under the module we are inlining into
        if (AstNode* const stmtsp = newmodp->stmtsp()) {
            stmtsp->unlinkFrBackWithNext();
            m_modp->addStmtsp(stmtsp);
        }
        // Clear any leftover ports, etc
        VL_DO_DANGLING(newmodp->deleteTree(), newmodp);
        // Remove the cell we just inlined
        nodep->unlinkFrBack();
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }

    // VISITORS
    void visit(AstNetlist* nodep) override {
        // Iterate modules backwards, in bottom-up order.  Required!
        iterateAndNextConstNullBackwards(nodep->modulesp());
        // Clean up AstIfaceRefDType references
        iterateChildren(nodep->typeTablep());
    }
    void visit(AstNodeModule* nodep) override {
        UASSERT_OBJ(!m_modp, nodep, "Unsupported: Nested modules");
        m_modp = nodep;
        // Iterate the stored cells directly to reduce traversal
        for (AstCell* const cellp : m_moduleState(nodep).m_childCells) {
            if (m_moduleState(cellp->modp()).m_inlined) inlineCell(cellp);
        }
        m_moduleState(nodep).m_childCells.clear();
        m_modp = nullptr;
    }
    void visit(AstIfaceRefDType* nodep) override {
        if (nodep->user1()) {
            // The cell has been removed so let's make sure we don't leave a reference to it
            // This dtype may still be in use by the AstAssignVarScope created earlier
            // but that'll get cleared up later
            nodep->cellp(nullptr);
        }
    }

    //--------------------
    void visit(AstCell* nodep) override {  // LCOV_EXCL_START
        nodep->v3fatal("Traversal should have been short circuited");
    }
    void visit(AstNodeStmt* nodep) override {
        nodep->v3fatal("Traversal should have been short circuited");
    }  // LCOV_EXCL_STOP
    void visit(AstNodeFile*) override {}  // Accelerate
    void visit(AstNodeDType*) override {}  // Accelerate
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit InlineVisitor(AstNode* nodep, ModuleStateUser1Allocator& moduleState)
        : m_moduleState{moduleState} {
        iterate(nodep);
    }
    ~InlineVisitor() override {
        V3Stats::addStat("Optimizations, Inlined instances", m_statCells);
    }
};

//######################################################################
// Inline class functions

void V3Inline::inlineAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);

    {
        const VNUser1InUse m_inuser1;  // output of InlineMarkVisitor, input to InlineVisitor.
        ModuleStateUser1Allocator moduleState;  // AstUser1Allocator

        // Scoped to clean up temp userN's
        { InlineMarkVisitor{nodep, moduleState}; }

        { InlineVisitor{nodep, moduleState}; }

        // Check inlined modules have been removed during traversal. Otherwise we might have blown
        // up Verilator memory consumption.
        for (AstNodeModule* modp = v3Global.rootp()->modulesp(); modp;
             modp = VN_AS(modp->nextp(), NodeModule)) {
            UASSERT_OBJ(!moduleState(modp).m_inlined, modp,
                        "Inlined module should have been deleted when the last cell referencing "
                        "it was inlined");
        }
    }

    V3Global::dumpCheckGlobalTree("inline", 0, dumpTreeLevel() >= 3);
}
