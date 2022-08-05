// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Generate C language constructors and AstCReset nodes.
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2022 by Wilson Snyder. This program is free software; you
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

#include "V3CCtors.h"

#include "V3EmitCBase.h"
#include "V3Global.h"

#include <algorithm>
#include <list>

class VCtorType final {
public:
    enum en : uint8_t { MODULE, CLASS, COVERAGE };

private:
    const enum en m_e;

public:
    // cppcheck-suppress noExplicitConstructor
    inline VCtorType(en _e)
        : m_e{_e} {}
    bool isClass() const { return m_e == CLASS; }
    bool isCoverage() const { return m_e == COVERAGE; }
};

class V3CCtorsBuilder final {
private:
    AstNodeModule* const m_modp;  // Current module/class
    const string m_basename;
    const VCtorType m_type;  // What kind of constructor are we creating
    std::list<AstCFunc*> m_newFunctions;  // Created functions, latest is at back
    int m_numStmts = 0;  // Number of statements output

    AstCFunc* makeNewFunc() {
        const int funcNum = m_newFunctions.size();
        const string funcName = m_basename + "_" + cvtToStr(funcNum);
        AstCFunc* const funcp = new AstCFunc{m_modp->fileline(), funcName, nullptr, "void"};
        funcp->isStatic(false);
        funcp->isLoose(!m_type.isClass());
        funcp->declPrivate(true);
        funcp->slow(!m_type.isClass());  // Only classes construct on fast path
        string preventUnusedStmt;
        if (m_type.isClass()) {
            funcp->argTypes(EmitCBaseVisitor::symClassVar());
            preventUnusedStmt = "if (false && vlSymsp) {}  // Prevent unused\n";
        } else if (m_type.isCoverage()) {
            funcp->argTypes("bool first");
            preventUnusedStmt = "if (false && first) {}  // Prevent unused\n";
        }
        if (!preventUnusedStmt.empty()) {
            funcp->addStmtsp(new AstCStmt{m_modp->fileline(), preventUnusedStmt});
        }
        m_modp->addStmtp(funcp);
        m_numStmts = 0;
        return funcp;
    }

public:
    void add(AstNode* nodep) {
        if (v3Global.opt.outputSplitCFuncs() && m_numStmts > v3Global.opt.outputSplitCFuncs()) {
            m_newFunctions.push_back(makeNewFunc());
        }
        m_newFunctions.back()->addStmtsp(nodep);
        m_numStmts += 1;
    }

    V3CCtorsBuilder(AstNodeModule* nodep, const string& basename, VCtorType type)
        : m_modp{nodep}
        , m_basename{basename}
        , m_type{type} {
        // Note: The constructor is always called, even if empty, so we must always create at least
        // one.
        m_newFunctions.push_back(makeNewFunc());
    }

    ~V3CCtorsBuilder() {
        if (m_newFunctions.size() == 1) {
            // No split was necessary, rename the one function to the basename
            m_newFunctions.front()->name(m_basename);
        } else {
            // Split was necessary, create root function and call all others from that
            AstCFunc* const rootFuncp = makeNewFunc();
            rootFuncp->name(m_basename);
            for (AstCFunc* const funcp : m_newFunctions) {
                AstCCall* const callp = new AstCCall{m_modp->fileline(), funcp};
                if (m_type.isClass()) {
                    callp->argTypes("vlSymsp");
                } else {
                    if (m_type.isCoverage()) callp->argTypes("first");
                    callp->selfPointer("this");
                }
                rootFuncp->addStmtsp(callp);
            }
        }
    }

private:
    VL_UNCOPYABLE(V3CCtorsBuilder);
};

//######################################################################

void V3CCtors::evalAsserts() {
    AstNodeModule* const modp = v3Global.rootp()->modulesp();  // Top module wrapper
    AstCFunc* const funcp
        = new AstCFunc{modp->fileline(), "_eval_debug_assertions", nullptr, "void"};
    funcp->declPrivate(true);
    funcp->isStatic(false);
    funcp->isLoose(true);
    funcp->slow(false);
    funcp->ifdef("VL_DEBUG");
    modp->addStmtp(funcp);
    for (AstNode* np = modp->stmtsp(); np; np = np->nextp()) {
        if (AstVar* const varp = VN_CAST(np, Var)) {
            if (varp->isPrimaryInish() && !varp->isSc()) {
                if (const AstBasicDType* const basicp
                    = VN_CAST(varp->dtypeSkipRefp(), BasicDType)) {
                    const int storedWidth = basicp->widthAlignBytes() * 8;
                    const int lastWordWidth = varp->width() % storedWidth;
                    if (lastWordWidth != 0) {
                        // if (signal & CONST(upper_non_clean_mask)) { fail; }
                        AstVarRef* const vrefp
                            = new AstVarRef{varp->fileline(), varp, VAccess::READ};
                        vrefp->selfPointer("this");
                        AstNode* newp = vrefp;
                        if (varp->isWide()) {
                            newp = new AstWordSel{
                                varp->fileline(), newp,
                                new AstConst(varp->fileline(), varp->widthWords() - 1)};
                        }
                        const uint64_t value = VL_MASK_Q(storedWidth) & ~VL_MASK_Q(lastWordWidth);
                        newp = new AstAnd{varp->fileline(), newp,
                                          new AstConst(varp->fileline(), AstConst::WidthedValue(),
                                                       storedWidth, value)};
                        AstNodeIf* const ifp = new AstIf{
                            varp->fileline(), newp,
                            new AstCStmt{varp->fileline(), "Verilated::overWidthError(\""
                                                               + varp->prettyName() + "\");"}};
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
         modp = VN_AS(modp->nextp(), NodeModule)) {
        // Process each module in turn
        {
            V3CCtorsBuilder var_reset{modp, "_ctor_var_reset",
                                      VN_IS(modp, Class) ? VCtorType::CLASS : VCtorType::MODULE};

            for (AstNode* np = modp->stmtsp(); np; np = np->nextp()) {
                if (AstVar* const varp = VN_CAST(np, Var)) {
                    if (!varp->isIfaceParent() && !varp->isIfaceRef() && !varp->noReset()
                        && !varp->isParam()) {
                        const auto vrefp = new AstVarRef{varp->fileline(), varp, VAccess::WRITE};
                        var_reset.add(new AstCReset{varp->fileline(), vrefp});
                    }
                }
            }
        }
        if (v3Global.opt.coverage()) {
            V3CCtorsBuilder configure_coverage{modp, "_configure_coverage", VCtorType::COVERAGE};
            for (AstNode* np = modp->stmtsp(); np; np = np->nextp()) {
                if (AstCoverDecl* const coverp = VN_CAST(np, CoverDecl)) {
                    np = coverp->backp();
                    configure_coverage.add(coverp->unlinkFrBack());
                }
            }
        }
        if (const AstClass* const classp = VN_CAST(modp, Class)) {
            AstCFunc* const funcp = new AstCFunc{modp->fileline(), "~", nullptr, ""};
            funcp->isDestructor(true);
            funcp->isStatic(false);
            // If can be referred to by base pointer, need virtual delete
            funcp->isVirtual(classp->isExtended());
            funcp->slow(false);
            modp->addStmtp(funcp);
        }
    }
}
