// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Interface references for tracing
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
private:
    // NODE STATE
    //   AstVar::user1p()   // AstCell which this Var points to
    const VNUser1InUse m_inuser1;
    const VNUser2InUse m_inuser2;

    string m_scope;  // Scope name

    // VISITORS
    void visit(AstNetlist* nodep) override { iterateChildren(nodep->topModulep()); }
    void visit(AstCell* nodep) override {
        VL_RESTORER(m_scope);
        if (m_scope.empty()) {
            m_scope = nodep->name();
        } else {
            m_scope += "__DOT__" + nodep->name();
        }

        if (VN_IS(nodep->modp(), Iface)) {
            nodep->addIntfRefsp(new AstIntfRef{nodep->fileline(), m_scope});
        }
        {
            AstNodeModule* const modp = nodep->modp();
            // Pass Cell pointers down to the next module
            for (AstPin* pinp = nodep->pinsp(); pinp; pinp = VN_AS(pinp->nextp(), Pin)) {
                AstVar* const varp = pinp->modVarp();
                const AstVarRef* const varrefp = VN_CAST(pinp->exprp(), VarRef);
                if (!varrefp) continue;
                const AstVar* const fromVarp = varrefp->varp();
                const AstIfaceRefDType* const irdtp = VN_CAST(fromVarp->dtypep(), IfaceRefDType);
                if (!irdtp) continue;

                AstCell* cellp;
                if ((cellp = VN_CAST(fromVarp->user1p(), Cell)) || (cellp = irdtp->cellp())) {
                    varp->user1p(cellp);
                    const string alias = m_scope + "__DOT__" + pinp->name();
                    cellp->addIntfRefsp(new AstIntfRef{pinp->fileline(), alias});
                }
            }

            iterateChildren(modp);
        }
    }
    void visit(AstAssignVarScope* nodep) override {
        // Reference
        const AstVarRef* const reflp = VN_CAST(nodep->lhsp(), VarRef);
        // What the reference refers to
        const AstVarRef* const refrp = VN_CAST(nodep->rhsp(), VarRef);
        if (!(reflp && refrp)) return;

        const AstVar* const varlp = reflp->varp();
        const AstVar* const varrp = refrp->varp();
        if (!(varlp && varrp)) return;

        AstCell* cellp = VN_CAST(varrp->user1p(), Cell);
        if (!cellp) {
            const AstIfaceRefDType* const irdtp = VN_CAST(varrp->dtypep(), IfaceRefDType);
            if (!irdtp) return;

            cellp = irdtp->cellp();
        }
        if (!cellp) return;
        string alias;
        if (!m_scope.empty()) alias = m_scope + "__DOT__";
        alias += varlp->name();
        cellp->addIntfRefsp(new AstIntfRef{varlp->fileline(), alias});
    }
    //--------------------
    void visit(AstNodeExpr*) override {}  // Accelerate
    void visit(AstNodeStmt*) override {}  // Accelerate
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit InlineIntfRefVisitor(AstNode* nodep) { iterate(nodep); }
    ~InlineIntfRefVisitor() override = default;
};

//######################################################################
// Interface class functions

void V3Interface::interfaceAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);

    { InlineIntfRefVisitor{nodep}; }

    V3Global::dumpCheckGlobalTree("interface", 0, dumpTreeLevel() >= 3);
}
