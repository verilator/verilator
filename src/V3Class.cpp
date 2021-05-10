// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Handle SV classes
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
// V3Class's Transformations:
//
// Each class:
//      Move to be modules under AstNetlist
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3Global.h"
#include "V3Class.h"
#include "V3Ast.h"

//######################################################################

class ClassVisitor final : public AstNVisitor {
private:
    // MEMBERS
    AstUser1InUse m_inuser1;
    string m_prefix;  // String prefix to add to name based on hier
    AstScope* m_classScopep = nullptr;  // Package moving scopes into
    AstScope* m_packageScopep = nullptr;  // Class package scope
    AstNodeFTask* m_ftaskp = nullptr;  // Current task
    std::vector<std::pair<AstNode*, AstScope*>> m_moves;

    // NODE STATE
    //  AstClass::user1()       -> bool.  True if iterated already

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    virtual void visit(AstClass* nodep) override {
        if (nodep->user1SetOnce()) return;
        // Move this class
        nodep->name(m_prefix + nodep->name());
        nodep->unlinkFrBack();
        v3Global.rootp()->addModulep(nodep);
        // Make containing package
        // Note origName is the same as the class origName so errors look correct
        AstClassPackage* packagep = new AstClassPackage(nodep->fileline(), nodep->origName());
        packagep->name(nodep->name() + "__Vclpkg");
        nodep->classOrPackagep(packagep);
        packagep->classp(nodep);
        v3Global.rootp()->addModulep(packagep);
        // Add package to hierarchy
        AstCell* cellp = new AstCell(packagep->fileline(), packagep->fileline(), packagep->name(),
                                     packagep->name(), nullptr, nullptr, nullptr);
        cellp->modp(packagep);
        v3Global.rootp()->topModulep()->addStmtp(cellp);
        // Find class's scope
        // Alternative would be to move this and related to V3Scope
        AstScope* classScopep = nullptr;
        for (AstNode* itp = nodep->stmtsp(); itp; itp = itp->nextp()) {
            if ((classScopep = VN_CAST(itp, Scope))) break;
        }
        UASSERT_OBJ(classScopep, nodep, "No scope under class");

        // Add scope
        AstScope* scopep = new AstScope(nodep->fileline(), packagep, classScopep->name(),
                                        classScopep->aboveScopep(), classScopep->aboveCellp());
        packagep->addStmtp(scopep);
        // Iterate
        VL_RESTORER(m_prefix);
        VL_RESTORER(m_classScopep);
        VL_RESTORER(m_packageScopep);
        {
            m_classScopep = classScopep;
            m_packageScopep = scopep;
            m_prefix = nodep->name() + "__02e";  // .
            iterateChildren(nodep);
        }
    }
    virtual void visit(AstNodeModule* nodep) override {
        // Visit for NodeModules that are not AstClass (AstClass is-a AstNodeModule)
        VL_RESTORER(m_prefix);
        {
            m_prefix = nodep->name() + "__03a__03a";  // ::
            iterateChildren(nodep);
        }
    }

    virtual void visit(AstVar* nodep) override {
        iterateChildren(nodep);
        // Don't move now, or wouldn't keep interating the class
        // TODO move class statics too
        if (m_packageScopep && m_ftaskp && m_ftaskp->lifetime().isStatic()) {
            m_moves.push_back(std::make_pair(nodep, m_packageScopep));
        }
    }

    virtual void visit(AstVarScope* nodep) override {
        iterateChildren(nodep);
        nodep->varp()->user1p(nodep);
    }

    virtual void visit(AstNodeFTask* nodep) override {
        VL_RESTORER(m_ftaskp);
        {
            m_ftaskp = nodep;
            iterateChildren(nodep);
            if (m_packageScopep && nodep->lifetime().isStatic()) {
                m_moves.push_back(std::make_pair(nodep, m_packageScopep));
            }
        }
    }

    virtual void visit(AstCFunc* nodep) override {
        iterateChildren(nodep);
        // Don't move now, or wouldn't keep interating the class
        // TODO move function statics only
        // if (m_classScopep) {
        //    m_moves.push_back(std::make_pair(nodep, m_classScopep));
        //}
    }

    virtual void visit(AstNodeMath* nodep) override {}  // Short circuit
    virtual void visit(AstNodeStmt* nodep) override {}  // Short circuit
    virtual void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit ClassVisitor(AstNetlist* nodep) { iterate(nodep); }
    virtual ~ClassVisitor() override {
        for (auto moved : m_moves) {
            if (VN_IS(moved.first, NodeFTask)) {
                moved.second->addActivep(moved.first->unlinkFrBack());
            } else if (VN_IS(moved.first, Var)) {
                AstVarScope* scopep = VN_CAST(moved.first->user1p(), VarScope);
                moved.second->addVarp(scopep->unlinkFrBack());
            }
        }
    }
};

//######################################################################
// Class class functions

void V3Class::classAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    { ClassVisitor visitor(nodep); }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("class", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}
