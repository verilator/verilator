// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Generate C language constructors and AstCReset nodes.
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
#include <map>

class VCtorType final {
public:
    enum en : uint8_t { MODULE, CLASS, COVERAGE };

private:
    enum en m_e;

public:
    // cppcheck-suppress noExplicitConstructor
    inline VCtorType(en _e)
        : m_e{_e} {}
    bool isClass() const { return m_e == CLASS; }
    bool isCoverage() const { return m_e == COVERAGE; }
};

class V3CCtorsVisitor final {
private:
    AstNodeModule* const m_modp;  // Current module/class
    const string m_basename;
    const VCtorType m_type;  // What kind of constructor are we creating
    AstCFunc* m_funcp = nullptr;  // Current function
    int m_numStmts = 0;  // Number of statements output

    void makeNewFunc() {
        const int funcNum = m_type.isCoverage() ? m_modp->configureCoverageFuncsInc()
                                                : m_modp->ctorVarResetFuncsInc();
        const string funcName
            = m_type.isClass() ? m_basename : m_basename + "_" + cvtToStr(funcNum);
        m_funcp = new AstCFunc(m_modp->fileline(), funcName, nullptr, "void");
        m_funcp->isStatic(!m_type.isClass());  // Class constructors are non static
        m_funcp->declPrivate(true);
        m_funcp->slow(!m_type.isClass());  // Only classes construct on fast path
        string preventUnusedStmt;
        if (m_type.isClass()) {
            m_funcp->argTypes(EmitCBaseVisitor::symClassVar());
            preventUnusedStmt = "if (false && vlSymsp) {}";
        } else if (m_type.isCoverage()) {
            m_funcp->argTypes(EmitCBaseVisitor::prefixNameProtect(m_modp) + "* self, "
                              + EmitCBaseVisitor::symClassVar() + ", bool first");
            preventUnusedStmt = "if (false && self && vlSymsp && first) {}";
        } else {  // Module
            m_funcp->argTypes(EmitCBaseVisitor::prefixNameProtect(m_modp) + "* self");
            preventUnusedStmt = "if (false && self) {}";
        }
        preventUnusedStmt += "  // Prevent unused\n";
        m_funcp->addStmtsp(new AstCStmt(m_modp->fileline(), preventUnusedStmt));
        m_modp->addStmtp(m_funcp);
        m_numStmts = 0;
    }

public:
    void add(AstNode* nodep) {
        // Don't split the function for classes yet, as it is called via a text AstCStmt added in
        // V3Task, which does not handle split functions. This should not be a problem as we don't
        // inline classes like we do modules, and hopefully the user didn't write enormous classes.
        if (!m_type.isClass() &&  // Don't split for classes
            v3Global.opt.outputSplitCFuncs() && m_numStmts > v3Global.opt.outputSplitCFuncs()) {
            m_funcp = nullptr;
        }
        if (!m_funcp) makeNewFunc();
        m_funcp->addStmtsp(nodep);
        m_numStmts += 1;
    }

    V3CCtorsVisitor(AstNodeModule* nodep, const string& basename, VCtorType type)
        : m_modp(nodep)
        , m_basename{basename}
        , m_type(type) {
        // Note: The constructor for classes is always called, even if empty,
        // so we must always create at least one.
        if (m_type.isClass()) makeNewFunc();
    }
    ~V3CCtorsVisitor() = default;

private:
    VL_UNCOPYABLE(V3CCtorsVisitor);
};

//######################################################################

void V3CCtors::evalAsserts() {
    AstNodeModule* modp = v3Global.rootp()->modulesp();  // Top module wrapper
    AstCFunc* funcp = new AstCFunc(modp->fileline(), "_eval_debug_assertions", nullptr, "void");
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
                        AstNode* newp = new AstVarRef(varp->fileline(), varp, VAccess::READ);
                        if (varp->isWide()) {
                            newp = new AstWordSel(
                                varp->fileline(), newp,
                                new AstConst(varp->fileline(), varp->widthWords() - 1));
                        }
                        uint64_t value = VL_MASK_Q(storedWidth) & ~VL_MASK_Q(lastWordWidth);
                        newp = new AstAnd(varp->fileline(), newp,
                                          new AstConst(varp->fileline(), AstConst::WidthedValue(),
                                                       storedWidth, value));
                        AstNodeIf* ifp = new AstIf(
                            varp->fileline(), newp,
                            new AstCStmt(varp->fileline(), "Verilated::overWidthError(\""
                                                               + varp->prettyName() + "\");"));
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
    UINFO(2, __FUNCTION__ << ": " << endl);
    evalAsserts();
    for (AstNodeModule* modp = v3Global.rootp()->modulesp(); modp;
         modp = VN_CAST(modp->nextp(), NodeModule)) {
        // Process each module in turn
        {
            V3CCtorsVisitor var_reset(modp, "_ctor_var_reset",
                                      VN_IS(modp, Class) ? VCtorType::CLASS : VCtorType::MODULE);

            for (AstNode* np = modp->stmtsp(); np; np = np->nextp()) {
                if (AstVar* const varp = VN_CAST(np, Var)) {
                    if (!varp->isIfaceParent() && !varp->isIfaceRef() && !varp->noReset()) {
                        const auto vrefp = new AstVarRef(varp->fileline(), varp, VAccess::WRITE);
                        var_reset.add(new AstCReset(varp->fileline(), vrefp));
                    }
                }
            }
        }
        if (v3Global.opt.coverage()) {
            V3CCtorsVisitor configure_coverage(modp, "_configure_coverage", VCtorType::COVERAGE);
            for (AstNode* np = modp->stmtsp(); np; np = np->nextp()) {
                if (AstCoverDecl* const coverp = VN_CAST(np, CoverDecl)) {
                    np = coverp->backp();
                    configure_coverage.add(coverp->unlinkFrBack());
                }
            }
        }
        if (AstClass* classp = VN_CAST(modp, Class)) {
            AstCFunc* funcp = new AstCFunc(modp->fileline(), "~", nullptr, "");
            funcp->isDestructor(true);
            funcp->isStatic(false);
            // If can be referred to by base pointer, need virtual delete
            funcp->isVirtual(classp->isExtended());
            funcp->slow(false);
            modp->addStmtp(funcp);
        }
    }
}
