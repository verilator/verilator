// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Addressable $fscanf/$sscanf destinations
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
// V3ScanfDest's Transformations:
//
// Top Scope:
//   Replace each non-addressable $fscanf/$sscanf destination (part-select or
//   packed struct member) with a write to a temporary variable, and add a
//   write-back assignment of that temporary to the destination right after
//   the statement containing the call. The generated VL_FSCANF/VL_SSCANF
//   macros take the address of the destination, and a part-select has no
//   address. Calls in other contexts (e.g. a continuous assignment) are
//   rejected, as no write-back can be placed after them.
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3ScanfDest.h"

#include "V3SharedTmps.h"
#include "V3Stats.h"

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// $fscanf/$sscanf destinations, as a visitor of each AstNode

class ScanfDestVisitor final : public VNVisitor {
    // STATE - across all visitors
    V3SharedTmps m_tmps{"__Vscanf", VVarType::BLOCKTEMP};  // Temp results
    int m_nRewritten = 0;  // Number of destinations rewritten

    // STATE - for current visit position (use VL_RESTORER)
    AstScope* m_scopep = nullptr;  // Current scope

    // METHODS

    // True if 'nodep' can be the destination of a $fscanf/$sscanf call, i.e.
    // a lvalue for which C++ can take the address
    static bool addressable(AstNode* nodep) {
        if (VN_CAST(nodep, VarRef)) return true;
        if (VN_CAST(nodep, Sel)) return false;
        if (const AstArraySel* const arrayp = VN_CAST(nodep, ArraySel))
            return addressable(arrayp->fromp());
        if (const AstStructSel* const structp = VN_CAST(nodep, StructSel))
            return addressable(structp->fromp());
        return false;
    }

    // Rewrite each non-addressable destination of a $fscanf/$sscanf call.
    // Each is redirected to a temporary variable, written back to the
    // destination by an assignment placed after the statement containing the
    // call, in destination order.
    void scanfDest(AstNode* scanfp, AstNodeExpr* firstp) {
        // The call is an expression, so find the statement containing it
        AstNode* stmtp = scanfp;
        while (stmtp && !VN_IS(stmtp, NodeStmt)) stmtp = stmtp->backp();
        // Only a sequential statement can be followed by the write-back;
        // the call has usually already been lifted into its own assignment
        if (!stmtp || VN_IS(stmtp, AssignCont)
            || !(VN_IS(stmtp, StmtExpr) || VN_IS(stmtp, NodeAssign))) {
            scanfp->v3error("Unsupported: $fscanf/$sscanf in this context; "
                            "the destination cannot be written back.");
            return;
        }
        UASSERT_OBJ(m_scopep, scanfp, "$fscanf/$sscanf outside a scope");
        AstNode* insertp = stmtp;  // Write-backs are added after this
        for (AstNode* nextp = firstp; nextp;) {
            AstNode* const nextDestp = nextp->nextp();
            AstNodeExpr* const destp = VN_CAST(nextp, NodeExpr);
            UASSERT_OBJ(destp, nextp, "Non-expression in $fscanf/$sscanf destination list");
            if (addressable(destp)) {
                nextp = nextDestp;
                continue;
            }
            FileLine* const flp = destp->fileline();
            // The generated call takes &destination, so store the result in a
            // temporary variable and write it back to the destination after
            AstVarScope* const vscp = m_tmps.make(flp, m_scopep, destp->widthMin());
            destp->replaceWith(new AstVarRef{flp, vscp, VAccess::WRITE});
            AstAssign* const wbp
                = new AstAssign{flp, destp, new AstVarRef{flp, vscp, VAccess::READ}};
            insertp->addNextHere(wbp);
            insertp = wbp;
            ++m_nRewritten;
            nextp = nextDestp;
        }
    }

    // VISITORS

    void visit(AstScope* nodep) override {
        VL_RESTORER(m_scopep);
        m_scopep = nodep;
        iterateChildren(nodep);
    }
    void visit(AstFScanF* nodep) override {
        scanfDest(nodep, nodep->exprsp());
        iterateChildren(nodep);
    }
    void visit(AstSScanF* nodep) override {
        scanfDest(nodep, nodep->exprsp());
        iterateChildren(nodep);
    }

    //--------------------
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit ScanfDestVisitor(AstNetlist* netlistp) { iterate(netlistp); }
    ~ScanfDestVisitor() override = default;

    int nRewritten() const { return m_nRewritten; }
};

//######################################################################
// Top Scope

void V3ScanfDest::scanfDestAll(AstNetlist* netlistp) {
    // Locals
    ScanfDestVisitor visitor{netlistp};
    // Actions
    V3Global::dumpCheckGlobalTree("scanfDest", 0, dumpTreeEitherLevel() >= 3);
    if (visitor.nRewritten())
        V3Stats::addStat("Optimizations, ScanfDest, lvalues rewritten", visitor.nRewritten());
}
