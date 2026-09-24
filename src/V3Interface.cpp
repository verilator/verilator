// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Interface references for tracing and VPI
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
// V3Interface's Transformations:
//
// Each module:
//      Look for CELL...
//          Keep track of scope and concrete interface along the way
//          Find all interface references
//              Add INTFREF to concrete interface's list of references
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Interface.h"

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// Track interface references under the Cell they reference

class InlineIntfRefVisitor final : public VNVisitor {
    // NODE STATE
    //   AstVar::user1p()   // AstCell which this Var points to
    const VNUser1InUse m_inuser1;

    string m_scope;  // Scope name

    // VISITORS
    void visit(AstNetlist* nodep) override { iterateChildrenConst(nodep->topModulep()); }
    void visit(AstCell* nodep) override {
        VL_RESTORER_COPY(m_scope);
        if (m_scope.empty()) {
            m_scope = nodep->name();
        } else {
            m_scope += "__DOT__" + nodep->name();
        }

        AstNodeModule* const modp = nodep->modp();
        // Pass Cell pointers down to the next module
        for (AstPin* pinp = nodep->pinsp(); pinp; pinp = VN_AS(pinp->nextp(), Pin)) {
            AstVar* const varp = pinp->modVarp();
            const AstVarRef* const varrefp = VN_CAST(pinp->exprp(), VarRef);
            if (!varrefp) continue;

            const AstVar* const fromVarp = varrefp->varp();
            const AstIfaceRefDType* const irdtp = VN_CAST(fromVarp->dtypep(), IfaceRefDType);
            if (!irdtp) continue;

            AstCell* cellp = VN_CAST(fromVarp->user1p(), Cell);
            if (!cellp) cellp = irdtp->cellp();
            if (!cellp) continue;
            varp->user1p(cellp);
            const string alias = m_scope + "__DOT__" + pinp->name();
            // Prefer the port's own dtype; the source may have no modport
            const AstIfaceRefDType* const portIrdtp = VN_CAST(varp->dtypep(), IfaceRefDType);
            const string modportName = portIrdtp ? portIrdtp->modportName() : irdtp->modportName();
            FileLine* const flp = pinp->fileline();
            cellp->addIntfRefsp(new AstIntfRef{flp, alias, pinp->name(), modportName});
        }

        iterateChildrenConst(modp);
    }
    //--------------------
    void visit(AstNodeExpr*) override {}  // Accelerate
    void visit(AstNodeStmt*) override {}  // Accelerate
    void visit(AstNode* nodep) override { iterateChildrenConst(nodep); }

public:
    // CONSTRUCTORS
    explicit InlineIntfRefVisitor(AstNode* nodep) { iterateConst(nodep); }
    ~InlineIntfRefVisitor() override = default;
};

//######################################################################
// Interface class functions

void V3Interface::interfaceAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ":");

    { InlineIntfRefVisitor{nodep}; }

    V3Global::dumpCheckGlobalTree("interface", 0, dumpTreeEitherLevel() >= 3);
}
