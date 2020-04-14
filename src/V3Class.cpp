// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Handle SV classes
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2020 by Wilson Snyder. This program is free software; you
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

class ClassVisitor : public AstNVisitor {
private:
    // MEMBERS
    AstUser1InUse m_inuser1;
    string m_prefix;  // String prefix to add to name based on hier
    AstScope* m_classScopep;  // Package moving scopes into
    typedef std::vector<std::pair<AstNode*, AstScope*> > MoveVector;
    MoveVector m_moves;

    // NODE STATE
    //  AstClass::user1()       -> bool.  True if iterated already

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    virtual void visit(AstClass* nodep) VL_OVERRIDE {
        if (nodep->user1SetOnce()) return;
        // Move this class
        nodep->name(m_prefix + nodep->name());
        nodep->unlinkFrBack();
        v3Global.rootp()->addModulep(nodep);
        // Make containing package
        // Note origName is the same as the class origName so errors look correct
        AstClassPackage* packagep = new AstClassPackage(nodep->fileline(), nodep->origName());
        packagep->name(nodep->name() + "__Vclpkg");
        nodep->packagep(packagep);
        packagep->classp(nodep);
        v3Global.rootp()->addModulep(packagep);
        // Add package to hierarchy
        AstCell* cellp = new AstCell(packagep->fileline(), packagep->fileline(), packagep->name(),
                                     packagep->name(), NULL, NULL, NULL);
        cellp->modp(packagep);
        v3Global.rootp()->topModulep()->addStmtp(cellp);
        // Find class's scope
        // Alternative would be to move this and related to V3Scope
        AstScope* classScopep = NULL;
        for (AstNode* itp = nodep->stmtsp(); itp; itp = itp->nextp()) {
            if ((classScopep = VN_CAST(itp, Scope))) break;
        }
        UASSERT_OBJ(classScopep, nodep, "No scope under class");

        // Add scope
        AstScope* scopep = new AstScope(nodep->fileline(), packagep, classScopep->name(),
                                        classScopep->aboveScopep(), classScopep->aboveCellp());
        packagep->addStmtp(scopep);
        // Iterate
        string prevPrefix = m_prefix;
        {
            m_classScopep = classScopep;
            m_prefix = nodep->name() + "__02e";  // .
            iterateChildren(nodep);
        }
        m_prefix = prevPrefix;
        m_classScopep = NULL;
    }
    virtual void visit(AstPackage* nodep) VL_OVERRIDE {
        string prevPrefix = m_prefix;
        {
            m_prefix = nodep->name() + "__03a__03a";  // ::
            iterateChildren(nodep);
        }
        m_prefix = prevPrefix;
    }

    virtual void visit(AstVar* nodep) VL_OVERRIDE {
        iterateChildren(nodep);
        // Don't move now, or wouldn't keep interating the class
        // TODO move class statics only
        // if (m_classScopep) {
        //    m_moves.push_back(make_pair(nodep, m_classScopep));
        //}
    }
    virtual void visit(AstCFunc* nodep) VL_OVERRIDE {
        iterateChildren(nodep);
        // Don't move now, or wouldn't keep interating the class
        // TODO move function statics only
        // if (m_classScopep) {
        //    m_moves.push_back(make_pair(nodep, m_classScopep));
        //}
    }

    virtual void visit(AstNodeMath* nodep) VL_OVERRIDE {}  // Short circuit
    virtual void visit(AstNodeStmt* nodep) VL_OVERRIDE {}  // Short circuit
    virtual void visit(AstNode* nodep) VL_OVERRIDE { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit ClassVisitor(AstNetlist* nodep)
        : m_classScopep(NULL) {
        iterate(nodep);
    }
    virtual ~ClassVisitor() {
        for (MoveVector::iterator it = m_moves.begin(); it != m_moves.end(); ++it) {
            it->second->addVarp(it->first->unlinkFrBack());
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
