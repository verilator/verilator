// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Generate C language constructors and AstCReset nodes.
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
// V3CCtors's Transformations:
//      Iterates over all modules and
//      for all AstVar, create a creates a AstCReset node in an _ctor_var_reset AstCFunc.
//      for all AstCoverDecl, move the declaration into a _configure_coverage AstCFunc.
//      For each variable that needs reset, add a AstCReset node.
//
//      For primary inputs, add _eval_debug_assertions.
//
//      This transformation honors outputSplitCFuncs.
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3Global.h"
#include "V3EmitCBase.h"
#include "V3CCtors.h"

#include <algorithm>
#include <cmath>
#include <cstdarg>
#include <map>
#include <vector>

class V3CCtorsVisitor {
private:
    string              m_basename;
    string              m_argsp;
    string              m_callargsp;
    AstNodeModule*      m_modp;         // Current module
    AstCFunc*           m_tlFuncp;      // Top level function being built
    AstCFunc*           m_funcp;        // Current function
    int                 m_numStmts;     // Number of statements output
    int                 m_funcNum;      // Function number being built

public:
    AstCFunc* builtFuncp() const { return m_tlFuncp; }
    void add(AstNode* nodep) {
        if (v3Global.opt.outputSplitCFuncs()
            && v3Global.opt.outputSplitCFuncs() < m_numStmts) {
            m_funcp = NULL;
        }
        if (!m_funcp) {
            m_funcp = new AstCFunc(m_modp->fileline(),
                                   m_basename+"_"+cvtToStr(++m_funcNum), NULL, "void");
            m_funcp->isStatic(false);
            m_funcp->declPrivate(true);
            m_funcp->slow(!VN_IS(m_modp, Class));  // Only classes construct on fast path
            m_funcp->argTypes(m_argsp);
            m_modp->addStmtp(m_funcp);

            // Add a top call to it
            AstCCall* callp = new AstCCall(m_modp->fileline(), m_funcp);
            callp->argTypes(m_callargsp);

            m_tlFuncp->addStmtsp(callp);
            m_numStmts = 0;
        }
        m_funcp->addStmtsp(nodep);
        m_numStmts += 1;
    }

    V3CCtorsVisitor(AstNodeModule* nodep, const string& basename,
                    const string& argsp="", const string& callargsp="",
                    const string& stmt="") {
        m_basename = basename;
        m_argsp = argsp;
        m_callargsp = callargsp;
        m_modp = nodep;
        m_numStmts = 0;
        m_funcNum = 0;
        m_tlFuncp = new AstCFunc(nodep->fileline(), basename, NULL, "void");
        m_tlFuncp->declPrivate(true);
        m_tlFuncp->isStatic(false);
        m_tlFuncp->slow(!VN_IS(m_modp, Class));  // Only classes construct on fast path
        m_tlFuncp->argTypes(m_argsp);
        if (stmt != "") {
            m_tlFuncp->addStmtsp(new AstCStmt(nodep->fileline(), stmt));
        }
        m_funcp = m_tlFuncp;
        m_modp->addStmtp(m_tlFuncp);
    }
    ~V3CCtorsVisitor() {}
private:
    VL_UNCOPYABLE(V3CCtorsVisitor);
};

//######################################################################

void V3CCtors::evalAsserts() {
    AstNodeModule* modp = v3Global.rootp()->modulesp();  // Top module wrapper
    AstCFunc* funcp = new AstCFunc(modp->fileline(), "_eval_debug_assertions", NULL, "void");
    funcp->declPrivate(true);
    funcp->isStatic(false);
    funcp->slow(false);
    funcp->ifdef("VL_DEBUG");
    modp->addStmtp(funcp);
    for (AstNode* np = modp->stmtsp(); np; np = np->nextp()) {
        if (AstVar* varp = VN_CAST(np, Var)) {
            if (varp->isPrimaryInish() && !varp->isSc()) {
                if (AstBasicDType* basicp = VN_CAST(varp->dtypeSkipRefp(), BasicDType)) {
                    int storedWidth = basicp->widthAlignBytes() * 8;
                    int lastWordWidth = varp->width() % storedWidth;
                    if (lastWordWidth != 0) {
                        // if (signal & CONST(upper_non_clean_mask)) { fail; }
                        AstNode* newp = new AstVarRef(varp->fileline(), varp, false);
                        if (varp->isWide()) {
                            newp = new AstWordSel(
                                varp->fileline(), newp,
                                new AstConst(varp->fileline(), varp->widthWords()-1));
                        }
                        uint64_t value = VL_MASK_Q(storedWidth) & ~VL_MASK_Q(lastWordWidth);
                        newp = new AstAnd(varp->fileline(), newp,
                                          new AstConst(varp->fileline(), AstConst::WidthedValue(),
                                                       storedWidth, value));
                        AstNodeIf* ifp = new AstIf(varp->fileline(), newp,
                                                   new AstCStmt(varp->fileline(),
                                                                "Verilated::overWidthError(\""+varp->prettyName()+"\");"));
                        ifp->branchPred(VBranchPred::BP_UNLIKELY);
                        newp = ifp;
                        funcp->addStmtsp(newp);
                    }
                }
            }
        }
    }
}

void V3CCtors::cctorsAll() {
    UINFO(2,__FUNCTION__<<": "<<endl);
    evalAsserts();
    for (AstNodeModule* modp = v3Global.rootp()->modulesp();
         modp; modp = VN_CAST(modp->nextp(), NodeModule)) {
        // Process each module in turn
        AstCFunc* varResetFuncp;
        {
            V3CCtorsVisitor var_reset (modp, "_ctor_var_reset");
            varResetFuncp = var_reset.builtFuncp();
            for (AstNode* np = modp->stmtsp(); np; np = np->nextp()) {
                if (AstVar* varp = VN_CAST(np, Var)) {
                    if (!varp->isIfaceParent() && !varp->isIfaceRef()
                        && !varp->noReset()) {
                        var_reset.add(new AstCReset(varp->fileline(),
                                                    new AstVarRef(varp->fileline(), varp, true)));
                    }
                }
            }
        }
        if (v3Global.opt.coverage()) {
            V3CCtorsVisitor configure_coverage
                (modp, "_configure_coverage",
                 EmitCBaseVisitor::symClassVar()+ ", bool first", "vlSymsp, first",
                 "if (0 && vlSymsp && first) {}  // Prevent unused\n");
            for (AstNode* np = modp->stmtsp(); np; np = np->nextp()) {
                if (AstCoverDecl* coverp = VN_CAST(np, CoverDecl)) {
                    AstNode* backp = coverp->backp();
                    coverp->unlinkFrBack();
                    configure_coverage.add(coverp);
                    np = backp;
                }
            }
        }
        if (VN_IS(modp, Class)) {
            AstCFunc* funcp = new AstCFunc(modp->fileline(), "new", NULL, "");
            funcp->isConstructor(true);
            funcp->isStatic(false);
            funcp->slow(false);
            modp->addStmtp(funcp);
            funcp->addStmtsp(new AstCCall(varResetFuncp->fileline(), varResetFuncp));
        }
        if (VN_IS(modp, Class)) {
            AstCFunc* funcp = new AstCFunc(modp->fileline(), "~", NULL, "");
            funcp->isDestructor(true);
            funcp->isStatic(false);
            funcp->slow(false);
            modp->addStmtp(funcp);
        }
    }
}
