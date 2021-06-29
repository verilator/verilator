// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Add temporaries, such as for inline nodes
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2021 by Wilson Snyder. This program is free software; you
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

#include "config_build.h"
#include "verilatedos.h"

#include "V3Global.h"
#include "V3Inline.h"
#include "V3Inst.h"
#include "V3Stats.h"
#include "V3Ast.h"
#include "V3String.h"

#include <algorithm>
#include <vector>
#include <unordered_set>

// CONFIG
static const int INLINE_MODS_SMALLER = 100;  // If a mod is < this # nodes, can always inline it

//######################################################################
// Inline state, as a visitor of each AstNode

class InlineMarkVisitor final : public AstNVisitor {
private:
    // NODE STATE
    // Output
    //  AstNodeModule::user1()  // OUTPUT: bool. User request to inline this module
    // Internal state (can be cleared after this visit completes)
    //  AstNodeModule::user2()  // CIL_*. Allowed to automatically inline module
    //  AstNodeModule::user3()  // int. Number of cells referencing this module
    //  AstNodeModule::user4()  // int. Statements in module
    AstUser2InUse m_inuser2;
    AstUser3InUse m_inuser3;
    AstUser4InUse m_inuser4;

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

    using ModVec = std::vector<AstNodeModule*>;
    ModVec m_allMods;  // All modules, in top-down order.

    // Within the context of a given module, LocalInstanceMap maps
    // from child modules to the count of each child's local instantiations.
    using LocalInstanceMap = std::unordered_map<AstNodeModule*, int>;

    // We keep a LocalInstanceMap for each module in the design
    std::unordered_map<AstNodeModule*, LocalInstanceMap> m_instances;

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()
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
    virtual void visit(AstNodeModule* nodep) override {
        UASSERT_OBJ(!m_modp, nodep, "Unsupported: Recursive modules");
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
    virtual void visit(AstClass* nodep) override {
        // TODO allow inlining of modules that have classes
        // (Probably wait for new inliner scheme)
        cantInline("class", true);
        iterateChildren(nodep);
    }
    virtual void visit(AstCell* nodep) override {
        nodep->modp()->user3Inc();  // Inc refs
        m_instances[m_modp][nodep->modp()]++;
        iterateChildren(nodep);
    }
    virtual void visit(AstPragma* nodep) override {
        if (nodep->pragType() == AstPragmaType::INLINE_MODULE) {
            // UINFO(0, "PRAG MARK " << m_modp << endl);
            if (!m_modp) {
                nodep->v3error("Inline pragma not under a module");  // LCOV_EXCL_LINE
            } else if (m_modp->user2() == CIL_MAYBE || m_modp->user2() == CIL_NOTSOFT) {
                m_modp->user2(CIL_USER);
            }
            // Remove so don't propagate to upper cell...
            VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
        } else if (nodep->pragType() == AstPragmaType::NO_INLINE_MODULE) {
            if (!m_modp) {
                nodep->v3error("Inline pragma not under a module");  // LCOV_EXCL_LINE
            } else if (!v3Global.opt.flatten()) {
                cantInline("Pragma NO_INLINE_MODULE", false);
            }
            // Remove so don't propagate to upper cell...
            VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
        } else {
            iterateChildren(nodep);
        }
    }
    virtual void visit(AstVarXRef* nodep) override {
        // Cleanup link until V3LinkDot can correct it
        nodep->varp(nullptr);
    }
    virtual void visit(AstNodeFTaskRef* nodep) override {
        // Cleanup link until V3LinkDot can correct it
        // MethodCalls not currently supported by inliner, so keep linked
        if (!nodep->classOrPackagep() && !VN_IS(nodep, MethodCall)) nodep->taskp(nullptr);
        iterateChildren(nodep);
    }
    virtual void visit(AstAlways* nodep) override {
        iterateChildren(nodep);
        m_modp->user4Inc();  // statement count
    }
    virtual void visit(AstNodeAssign* nodep) override {
        // Don't count assignments, as they'll likely flatten out
        // Still need to iterate though to nullify VarXRefs
        const int oldcnt = m_modp->user4();
        iterateChildren(nodep);
        m_modp->user4(oldcnt);
    }
    virtual void visit(AstNetlist* nodep) override {
        // Build user2, user3, and user4 for all modules.
        // Also build m_allMods and m_instances.
        iterateChildren(nodep);

        // Iterate through all modules in bottom-up order.
        // Make a final inlining decision for each.
        for (auto it = m_allMods.rbegin(); it != m_allMods.rend(); ++it) {
            AstNodeModule* modp = *it;

            // If we're going to inline some modules into this one,
            // update user4 (statement count) to reflect that:
            int statements = modp->user4();
            LocalInstanceMap& localsr = m_instances[modp];
            for (LocalInstanceMap::iterator iti = localsr.begin(); iti != localsr.end(); ++iti) {
                AstNodeModule* childp = iti->first;
                if (childp->user1()) {  // inlining child
                    statements += (childp->user4() * iti->second);
                }
            }
            modp->user4(statements);

            const int allowed = modp->user2();
            const int refs = modp->user3();

            // Should we automatically inline this module?
            // If --flatten is specified, then force everything to be inlined that can be.
            // inlineMult = 2000 by default.
            // If a mod*#refs is < this # nodes, can inline it
            bool doit = ((allowed == CIL_USER)
                         || ((allowed == CIL_MAYBE)
                             && (v3Global.opt.flatten()
                                 || (refs == 1 || statements < INLINE_MODS_SMALLER
                                     || v3Global.opt.inlineMult() < 1
                                     || refs * statements < v3Global.opt.inlineMult()))));
            // Packages aren't really "under" anything so they confuse this algorithm
            if (VN_IS(modp, Package)) doit = false;
            UINFO(4, " Inline=" << doit << " Possible=" << allowed << " Refs=" << refs
                                << " Stmts=" << statements << "  " << modp << endl);
            modp->user1(doit);
        }
    }
    //--------------------
    virtual void visit(AstNode* nodep) override {
        iterateChildren(nodep);
        if (m_modp) {
            m_modp->user4Inc();  // Inc statement count
        }
    }

public:
    // CONSTRUCTORS
    explicit InlineMarkVisitor(AstNode* nodep) { iterate(nodep); }
    virtual ~InlineMarkVisitor() override {
        V3Stats::addStat("Optimizations, Inline unsupported", m_statUnsup);
        // Done with these, are not outputs
        AstNode::user2ClearTree();
        AstNode::user3ClearTree();
        AstNode::user4ClearTree();
    }
};

//######################################################################
// Using clonep(), find cell cross references.
// clone() must not be called inside this visitor

class InlineCollectVisitor final : public AstNVisitor {
private:
    // NODE STATE
    //  Output:
    //   AstCell::user4p()      // AstCell* of the created clone

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    // VISITORS
    virtual void visit(AstCell* nodep) override { nodep->user4p(nodep->clonep()); }
    //--------------------
    virtual void visit(AstNodeStmt*) override {}  // Accelerate
    virtual void visit(AstNodeMath*) override {}  // Accelerate
    virtual void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit InlineCollectVisitor(AstNodeModule* nodep) {  // passed OLD module, not new one
        iterate(nodep);
    }
    virtual ~InlineCollectVisitor() override = default;
};

//######################################################################
// After cell is cloned, relink the new module's contents

class InlineRelinkVisitor final : public AstNVisitor {
private:
    // NODE STATE
    //  Input:
    //   See InlineVisitor

    // STATE
    std::unordered_set<std::string> m_renamedInterfaces;  // Name of renamed interface variables
    AstNodeModule* m_modp;  // Current module
    AstCell* m_cellp;  // Cell being cloned

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    // VISITORS
    virtual void visit(AstCellInline* nodep) override {
        // Inlined cell under the inline cell, need to move to avoid conflicts
        nodep->unlinkFrBack();
        m_modp->addInlinesp(nodep);
        // Rename
        const string name = m_cellp->name() + "__DOT__" + nodep->name();
        nodep->name(name);
        UINFO(6, "    Inline " << nodep << endl);
        // Do CellInlines under this, but don't move them
        iterateChildren(nodep);
    }
    virtual void visit(AstCell* nodep) override {
        // Cell under the inline cell, need to rename to avoid conflicts
        const string name = m_cellp->name() + "__DOT__" + nodep->name();
        nodep->name(name);
        iterateChildren(nodep);
    }
    virtual void visit(AstClass* nodep) override {
        const string name = m_cellp->name() + "__DOT__" + nodep->name();
        nodep->name(name);
        iterateChildren(nodep);
    }
    virtual void visit(AstModule* nodep) override {
        m_renamedInterfaces.clear();
        iterateChildren(nodep);
    }
    virtual void visit(AstVar* nodep) override {
        if (nodep->user2p()) {
            // Make an assignment, so we'll trace it properly
            // user2p is either a const or a var.
            AstConst* exprconstp = VN_CAST(nodep->user2p(), Const);
            AstVarRef* exprvarrefp = VN_CAST(nodep->user2p(), VarRef);
            UINFO(8, "connectto: " << nodep->user2p() << endl);
            UASSERT_OBJ(exprconstp || exprvarrefp, nodep,
                        "Unknown interconnect type; pinReconnectSimple should have cleared up");
            if (exprconstp) {
                m_modp->addStmtp(new AstAssignW(
                    nodep->fileline(), new AstVarRef(nodep->fileline(), nodep, VAccess::WRITE),
                    exprconstp->cloneTree(true)));
            } else if (nodep->user3()) {
                // Public variable at the lower module end - we need to make sure we propagate
                // the logic changes up and down; if we aliased, we might
                // remove the change detection on the output variable.
                UINFO(9, "public pin assign: " << exprvarrefp << endl);
                UASSERT_OBJ(!nodep->isNonOutput(), nodep, "Outputs only - inputs use AssignAlias");
                m_modp->addStmtp(new AstAssignW(
                    nodep->fileline(),
                    new AstVarRef(nodep->fileline(), exprvarrefp->varp(), VAccess::WRITE),
                    new AstVarRef(nodep->fileline(), nodep, VAccess::READ)));
            } else if (nodep->isSigPublic() && VN_IS(nodep->dtypep(), UnpackArrayDType)) {
                // Public variable at this end and it is an unpacked array. We need to assign
                // instead of aliased, because otherwise it will pass V3Slice and invalid
                // code will be emitted.
                UINFO(9, "assign to public and unpacked: " << nodep << endl);
                m_modp->addStmtp(new AstAssignW(
                    nodep->fileline(),
                    new AstVarRef(nodep->fileline(), exprvarrefp->varp(), VAccess::WRITE),
                    new AstVarRef(nodep->fileline(), nodep, VAccess::READ)));
            } else if (nodep->isIfaceRef()) {
                m_modp->addStmtp(new AstAssignVarScope(
                    nodep->fileline(), new AstVarRef(nodep->fileline(), nodep, VAccess::WRITE),
                    new AstVarRef(nodep->fileline(), exprvarrefp->varp(), VAccess::READ)));
                AstNode* nodebp = exprvarrefp->varp();
                nodep->fileline()->modifyStateInherit(nodebp->fileline());
                nodebp->fileline()->modifyStateInherit(nodep->fileline());
            } else {
                // Do to inlining child's variable now within the same
                // module, so a AstVarRef not AstVarXRef below
                m_modp->addStmtp(new AstAssignAlias(
                    nodep->fileline(), new AstVarRef(nodep->fileline(), nodep, VAccess::WRITE),
                    new AstVarRef(nodep->fileline(), exprvarrefp->varp(), VAccess::READ)));
                AstNode* nodebp = exprvarrefp->varp();
                nodep->fileline()->modifyStateInherit(nodebp->fileline());
                nodebp->fileline()->modifyStateInherit(nodep->fileline());
            }
        }
        // Iterate won't hit AstIfaceRefDType directly as it is no longer underneath the module
        if (AstIfaceRefDType* ifacerefp = VN_CAST(nodep->dtypep(), IfaceRefDType)) {
            m_renamedInterfaces.insert(nodep->name());
            // Each inlined cell that contain an interface variable need to
            // copy the IfaceRefDType and point it to the newly cloned
            // interface cell.
            AstIfaceRefDType* newdp = VN_CAST(ifacerefp->cloneTree(false), IfaceRefDType);
            nodep->dtypep(newdp);
            ifacerefp->addNextHere(newdp);
            // Relink to point to newly cloned cell
            if (newdp->cellp()) {
                if (AstCell* newcellp = VN_CAST(newdp->cellp()->user4p(), Cell)) {
                    newdp->cellp(newcellp);
                    newdp->cellName(newcellp->name());
                    // Tag the old ifacerefp to ensure it leaves no stale
                    // reference to the inlined cell.
                    newdp->user5(false);
                    ifacerefp->user5(true);
                }
            }
        }
        // Variable under the inline cell, need to rename to avoid conflicts
        // Also clear I/O bits, as it is now local.
        const string name = m_cellp->name() + "__DOT__" + nodep->name();
        if (!nodep->isFuncLocal() && !nodep->isClassMember()) nodep->inlineAttrReset(name);
        if (!m_cellp->isTrace()) nodep->trace(false);
        if (debug() >= 9) nodep->dumpTree(cout, "varchanged:");
        if (debug() >= 9 && nodep->valuep()) nodep->valuep()->dumpTree(cout, "varchangei:");
        iterateChildren(nodep);
    }
    virtual void visit(AstNodeFTask* nodep) override {
        // Function under the inline cell, need to rename to avoid conflicts
        nodep->name(m_cellp->name() + "__DOT__" + nodep->name());
        iterateChildren(nodep);
    }
    virtual void visit(AstTypedef* nodep) override {
        // Typedef under the inline cell, need to rename to avoid conflicts
        nodep->name(m_cellp->name() + "__DOT__" + nodep->name());
        iterateChildren(nodep);
    }
    virtual void visit(AstVarRef* nodep) override {
        if (nodep->varp()->user2p()  // It's being converted to an alias.
            && !nodep->varp()->user3()
            // Don't constant propagate aliases (we just made)
            && !VN_IS(nodep->backp(), AssignAlias)) {
            AstConst* exprconstp = VN_CAST(nodep->varp()->user2p(), Const);
            AstVarRef* exprvarrefp = VN_CAST(nodep->varp()->user2p(), VarRef);
            if (exprconstp) {
                nodep->replaceWith(exprconstp->cloneTree(true));
                VL_DO_DANGLING(nodep->deleteTree(), nodep);
                return;
            } else if (exprvarrefp) {
                nodep->varp(exprvarrefp->varp());
            } else {
                nodep->v3fatalSrc("Null connection?");
            }
        }
        nodep->name(nodep->varp()->name());
        iterateChildren(nodep);
    }
    virtual void visit(AstVarXRef* nodep) override {
        // Track what scope it was originally under so V3LinkDot can resolve it
        const string newdots = VString::dot(m_cellp->name(), ".", nodep->inlinedDots());
        nodep->inlinedDots(newdots);
        for (string tryname = nodep->dotted(); true;) {
            if (m_renamedInterfaces.count(tryname)) {
                nodep->dotted(m_cellp->name() + "__DOT__" + nodep->dotted());
                break;
            }
            // If foo.bar, and foo is an interface, then need to search again for foo
            string::size_type pos = tryname.rfind('.');
            if (pos == string::npos || pos == 0) {
                break;
            } else {
                tryname = tryname.substr(0, pos);
            }
        }
        iterateChildren(nodep);
    }
    virtual void visit(AstNodeFTaskRef* nodep) override {
        // Track what scope it was originally under so V3LinkDot can resolve it
        const string newdots = VString::dot(m_cellp->name(), ".", nodep->inlinedDots());
        nodep->inlinedDots(newdots);
        if (m_renamedInterfaces.count(nodep->dotted())) {
            nodep->dotted(m_cellp->name() + "__DOT__" + nodep->dotted());
        }
        UINFO(8, "   " << nodep << endl);
        iterateChildren(nodep);
    }

    // Not needed, as V3LinkDot doesn't care about typedefs
    // virtual void visit(AstRefDType* nodep) override {}

    virtual void visit(AstScopeName* nodep) override {
        // If there's a %m in the display text, we add a special node that will contain the name()
        // Similar code in V3Begin
        // To keep correct visual order, must add before other Text's
        AstNode* afterp = nodep->scopeAttrp();
        if (afterp) afterp->unlinkFrBackWithNext();
        nodep->scopeAttrp(new AstText(nodep->fileline(), string("__DOT__") + m_cellp->name()));
        if (afterp) nodep->scopeAttrp(afterp);
        afterp = nodep->scopeEntrp();
        if (afterp) afterp->unlinkFrBackWithNext();
        nodep->scopeEntrp(new AstText(nodep->fileline(), string("__DOT__") + m_cellp->name()));
        if (afterp) nodep->scopeEntrp(afterp);
        iterateChildren(nodep);
    }
    virtual void visit(AstCoverDecl* nodep) override {
        // Fix path in coverage statements
        nodep->hier(VString::dot(m_cellp->prettyName(), ".", nodep->hier()));
        iterateChildren(nodep);
    }
    virtual void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    InlineRelinkVisitor(AstNodeModule* cloneModp, AstNodeModule* oldModp, AstCell* cellp)
        : m_modp{oldModp}
        , m_cellp{cellp} {
        iterate(cloneModp);
    }
    virtual ~InlineRelinkVisitor() override = default;
};

//######################################################################
// Inline state, as a visitor of each AstNode

class InlineVisitor final : public AstNVisitor {
private:
    // NODE STATE
    // Cleared entire netlist
    //  AstIfaceRefDType::user5p()  // Whether the cell pointed to by this
    //                              // AstIfaceRefDType has been inlined
    //  Input:
    //   AstNodeModule::user1p()    // bool. True to inline this module (from InlineMarkVisitor)
    // Cleared each cell
    //   AstVar::user2p()       // AstVarRef*/AstConst*  Points to signal this
    //                          // is a direct connect to
    //   AstVar::user3()        // bool    Don't alias the user2, keep it as signal
    //   AstCell::user4         // AstCell* of the created clone

    AstUser2InUse m_inuser2;
    AstUser3InUse m_inuser3;
    AstUser4InUse m_inuser4;
    AstUser5InUse m_inuser5;

    // STATE
    AstNodeModule* m_modp = nullptr;  // Current module
    VDouble0 m_statCells;  // Statistic tracking

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    // VISITORS
    virtual void visit(AstNetlist* nodep) override {
        // Iterate modules backwards, in bottom-up order.  Required!
        iterateChildrenBackwards(nodep);
    }
    virtual void visit(AstIfaceRefDType* nodep) override {
        if (nodep->user5()) {
            // The cell has been removed so let's make sure we don't leave a reference to it
            // This dtype may still be in use by the AstAssignVarScope created earlier
            // but that'll get cleared up later
            nodep->cellp(nullptr);
        }
    }
    virtual void visit(AstNodeModule* nodep) override {
        VL_RESTORER(m_modp);
        {
            m_modp = nodep;
            iterateChildren(nodep);
        }
    }
    virtual void visit(AstCell* nodep) override {
        if (nodep->modp()->user1()) {  // Marked with inline request
            UINFO(5, " Inline CELL   " << nodep << endl);
            UINFO(5, "   To MOD      " << m_modp << endl);
            ++m_statCells;

            // Before cloning simplify pin assignments
            // Better off before, as if module has multiple instantiations
            // we'll save work, and we can't call pinReconnectSimple in
            // this loop as it clone()s itself.
            for (AstPin* pinp = nodep->pinsp(); pinp; pinp = VN_CAST(pinp->nextp(), Pin)) {
                V3Inst::pinReconnectSimple(pinp, nodep, false);
            }

            // Clone original module
            if (debug() >= 9) nodep->dumpTree(cout, "inlcell:");
            // if (debug() >= 9) nodep->modp()->dumpTree(cout, "oldmod:");
            AstNodeModule* newmodp = nodep->modp()->cloneTree(false);
            if (debug() >= 9) newmodp->dumpTree(cout, "newmod:");
            // Clear var markings and find cell cross references
            AstNode::user2ClearTree();
            AstNode::user4ClearTree();
            { InlineCollectVisitor(nodep->modp()); }  // {} to destroy visitor immediately
            // Create data for dotted variable resolution
            AstCellInline* inlinep
                = new AstCellInline(nodep->fileline(), nodep->name(), nodep->modp()->origName(),
                                    nodep->modp()->timeunit());
            m_modp->addInlinesp(inlinep);  // Must be parsed before any AstCells
            // Create assignments to the pins
            for (AstPin* pinp = nodep->pinsp(); pinp; pinp = VN_CAST(pinp->nextp(), Pin)) {
                if (!pinp->exprp()) continue;
                UINFO(6, "     Pin change from " << pinp->modVarp() << endl);
                // Make new signal; even though we'll optimize the interconnect, we
                // need an alias to trace correctly.  If tracing is disabled, we'll
                // delete it in later optimizations.
                AstVar* pinOldVarp = pinp->modVarp();
                AstVar* pinNewVarp = pinOldVarp->clonep();
                UASSERT_OBJ(pinNewVarp, pinOldVarp, "Cloning failed");

                AstNode* connectRefp = pinp->exprp();
                UASSERT_OBJ(
                    VN_IS(connectRefp, Const) || VN_IS(connectRefp, VarRef), pinp,
                    "Unknown interconnect type; pinReconnectSimple should have cleared up");
                V3Inst::checkOutputShort(pinp);

                // Propagate any attributes across the interconnect
                pinNewVarp->propagateAttrFrom(pinOldVarp);
                if (VN_IS(connectRefp, VarRef)) {
                    VN_CAST(connectRefp, VarRef)->varp()->propagateAttrFrom(pinOldVarp);
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
            { InlineRelinkVisitor(newmodp, m_modp, nodep); }
            // Move statements to top module
            if (debug() >= 9) newmodp->dumpTree(cout, "fixmod:");
            AstNode* stmtsp = newmodp->stmtsp();
            if (stmtsp) stmtsp->unlinkFrBackWithNext();
            if (stmtsp) m_modp->addStmtp(stmtsp);
            // Remove the cell
            VL_DO_DANGLING(newmodp->deleteTree(), newmodp);  // Clear any leftover ports, etc
            nodep->unlinkFrBack();
            VL_DO_DANGLING(pushDeletep(nodep), nodep);
            if (debug() >= 9) m_modp->dumpTree(cout, "donemod:");
        }
    }

    //--------------------
    virtual void visit(AstNodeMath*) override {}  // Accelerate
    virtual void visit(AstNodeStmt*) override {}  // Accelerate
    virtual void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit InlineVisitor(AstNode* nodep) { iterate(nodep); }
    virtual ~InlineVisitor() override {  //
        V3Stats::addStat("Optimizations, Inlined instances", m_statCells);
    }
};

//######################################################################
// Track interface references under the Cell they reference

class InlineIntfRefVisitor final : public AstNVisitor {
private:
    // NODE STATE
    //   AstVar::user1p()   // AstCell which this Var points to

    AstUser2InUse m_inuser2;

    string m_scope;  // Scope name

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    // VISITORS
    virtual void visit(AstNetlist* nodep) override { iterateChildren(nodep); }
    virtual void visit(AstModule* nodep) override {
        if (nodep->isTop()) iterateChildren(nodep);
    }
    virtual void visit(AstCell* nodep) override {
        VL_RESTORER(m_scope);
        if (m_scope.empty()) {
            m_scope = nodep->name();
        } else {
            m_scope += "__DOT__" + nodep->name();
        }

        if (AstModule* modp = VN_CAST(nodep->modp(), Module)) {
            // Pass Cell pointers down to the next module
            for (AstPin* pinp = nodep->pinsp(); pinp; pinp = VN_CAST(pinp->nextp(), Pin)) {
                AstVar* varp = pinp->modVarp();
                AstVarRef* varrefp = VN_CAST(pinp->exprp(), VarRef);
                if (!varrefp) continue;
                AstVar* fromVarp = varrefp->varp();
                AstIfaceRefDType* irdtp = VN_CAST(fromVarp->dtypep(), IfaceRefDType);
                if (!irdtp) continue;

                AstCell* cellp;
                if ((cellp = VN_CAST(fromVarp->user1p(), Cell)) || (cellp = irdtp->cellp())) {
                    varp->user1p(cellp);
                    const string alias = m_scope + "__DOT__" + pinp->name();
                    cellp->addIntfRefp(new AstIntfRef(pinp->fileline(), alias));
                }
            }

            iterateChildren(modp);
        } else if (VN_IS(nodep->modp(), Iface)) {
            nodep->addIntfRefp(new AstIntfRef(nodep->fileline(), m_scope));
            // No need to iterate on interface cells
        }
    }
    virtual void visit(AstAssignVarScope* nodep) override {
        // Reference
        AstVarRef* reflp = VN_CAST(nodep->lhsp(), VarRef);
        // What the reference refers to
        AstVarRef* refrp = VN_CAST(nodep->rhsp(), VarRef);
        if (!(reflp && refrp)) return;

        AstVar* varlp = reflp->varp();
        AstVar* varrp = refrp->varp();
        if (!(varlp && varrp)) return;

        AstCell* cellp = VN_CAST(varrp->user1p(), Cell);
        if (!cellp) {
            AstIfaceRefDType* irdtp = VN_CAST(varrp->dtypep(), IfaceRefDType);
            if (!irdtp) return;

            cellp = irdtp->cellp();
        }
        if (!cellp) return;
        string alias;
        if (!m_scope.empty()) alias = m_scope + "__DOT__";
        alias += varlp->name();
        cellp->addIntfRefp(new AstIntfRef(varlp->fileline(), alias));
    }
    //--------------------
    virtual void visit(AstNodeMath*) override {}  // Accelerate
    virtual void visit(AstNodeStmt*) override {}  // Accelerate
    virtual void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit InlineIntfRefVisitor(AstNode* nodep) { iterate(nodep); }
    virtual ~InlineIntfRefVisitor() override = default;
};

//######################################################################
// Inline class functions

void V3Inline::inlineAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    AstUser1InUse m_inuser1;  // output of InlineMarkVisitor,
                              // input to InlineVisitor.
    // Scoped to clean up temp userN's
    { InlineMarkVisitor mvisitor(nodep); }
    { InlineVisitor visitor(nodep); }
    // Remove all modules that were inlined
    // V3Dead will also clean them up, but if we have debug on, it's a good
    // idea to avoid dumping the hugely exploded tree.
    AstNodeModule* nextmodp;
    for (AstNodeModule* modp = v3Global.rootp()->modulesp(); modp; modp = nextmodp) {
        nextmodp = VN_CAST(modp->nextp(), NodeModule);
        if (modp->user1()) {  // Was inlined
            VL_DO_DANGLING(modp->unlinkFrBack()->deleteTree(), modp);
        }
    }
    { InlineIntfRefVisitor crvisitor(nodep); }
    V3Global::dumpCheckGlobalTree("inline", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}
