// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Generate C language constructors and AstCReset nodes.
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

VL_DEFINE_DEBUG_FUNCTIONS;

class VCtorType final {
public:
    enum en : uint8_t { MODULE, CLASS, COVERAGE };

private:
    const enum en m_e;

public:
    // cppcheck-suppress noExplicitConstructor
    constexpr VCtorType(en _e)
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
            funcp->argTypes(EmitCBase::symClassVar());
            preventUnusedStmt = "if (false && vlSymsp) {}  // Prevent unused\n";
        } else if (m_type.isCoverage()) {
            funcp->argTypes("bool first");
            preventUnusedStmt = "if (false && first) {}  // Prevent unused\n";
        }
        if (!preventUnusedStmt.empty()) {
            funcp->addStmtsp(new AstCStmt{m_modp->fileline(), preventUnusedStmt});
        }
        m_modp->addStmtsp(funcp);
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
                callp->dtypeSetVoid();
                if (m_type.isClass()) {
                    callp->argTypes("vlSymsp");
                } else {
                    if (m_type.isCoverage()) callp->argTypes("first");
                    callp->selfPointer(VSelfPointerText{VSelfPointerText::This()});
                }
                rootFuncp->addStmtsp(callp->makeStmt());
            }
        }
    }

private:
    VL_UNCOPYABLE(V3CCtorsBuilder);
};

//######################################################################

// Link state, as a visitor of each AstNode

class CCtorsVisitor final : public VNVisitor {
private:
    // NODE STATE

    // STATE
    AstNodeModule* m_modp = nullptr;  // Current module
    AstCFunc* m_cfuncp = nullptr;  // Current function
    V3CCtorsBuilder* m_varResetp = nullptr;  // Builder of _ctor_var_reset

    // VISITs
    void visit(AstNodeModule* nodep) override {
        VL_RESTORER(m_modp);
        VL_RESTORER(m_varResetp);
        m_modp = nodep;
        V3CCtorsBuilder var_reset{nodep, "_ctor_var_reset",
                                  VN_IS(nodep, Class) ? VCtorType::CLASS : VCtorType::MODULE};
        // cppcheck-suppress danglingLifetime
        m_varResetp = &var_reset;
        iterateChildren(nodep);

        if (v3Global.opt.coverage()) {
            V3CCtorsBuilder configure_coverage{nodep, "_configure_coverage", VCtorType::COVERAGE};
            for (AstNode* np = nodep->stmtsp(); np; np = np->nextp()) {
                if (AstCoverDecl* const coverp = VN_CAST(np, CoverDecl)) {
                    // ... else we don't have a static VlSym to be able to coverage insert
                    UASSERT_OBJ(!VN_IS(nodep, Class), coverp,
                                "CoverDecl should be in class's package, not class itself");
                    np = coverp->backp();
                    configure_coverage.add(coverp->unlinkFrBack());
                }
            }
        }
        if (AstClass* const classp = VN_CAST(nodep, Class)) {
            AstCFunc* const funcp = new AstCFunc{classp->fileline(), "~", nullptr, ""};
            funcp->isDestructor(true);
            funcp->isStatic(false);
            // If can be referred to by base pointer, need virtual delete
            funcp->isVirtual(classp->isExtended());
            funcp->slow(false);
            classp->addStmtsp(funcp);
        }
    }

    void visit(AstCFunc* nodep) override {
        VL_RESTORER(m_varResetp);
        VL_RESTORER(m_cfuncp);
        m_varResetp = nullptr;
        m_cfuncp = nodep;
        iterateChildren(nodep);
    }
    void visit(AstVar* nodep) override {
        if (!nodep->isIfaceParent() && !nodep->isIfaceRef() && !nodep->noReset()
            && !nodep->isParam() && !nodep->isStatementTemp()
            && !(nodep->basicp()
                 && (nodep->basicp()->isEvent() || nodep->basicp()->isTriggerVec()))) {
            if (m_varResetp) {
                const auto vrefp = new AstVarRef{nodep->fileline(), nodep, VAccess::WRITE};
                m_varResetp->add(new AstCReset{nodep->fileline(), vrefp});
            } else if (m_cfuncp) {
                const auto vrefp = new AstVarRef{nodep->fileline(), nodep, VAccess::WRITE};
                nodep->addNextHere(new AstCReset{nodep->fileline(), vrefp});
            }
        }
    }

    void visit(AstConstPool*) override {}
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit CCtorsVisitor(AstNode* nodep) { iterate(nodep); }
    ~CCtorsVisitor() override = default;
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
    modp->addStmtsp(funcp);
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
                        vrefp->selfPointer(VSelfPointerText{VSelfPointerText::This()});
                        AstNodeExpr* newp = vrefp;
                        if (varp->isWide()) {
                            newp = new AstWordSel{
                                varp->fileline(), newp,
                                new AstConst(varp->fileline(), varp->widthWords() - 1)};
                        }
                        const uint64_t value = VL_MASK_Q(storedWidth) & ~VL_MASK_Q(lastWordWidth);
                        newp = new AstAnd{varp->fileline(), newp,
                                          new AstConst(varp->fileline(), AstConst::WidthedValue{},
                                                       storedWidth, value)};
                        AstNodeIf* const ifp = new AstIf{
                            varp->fileline(), newp,
                            new AstCStmt{varp->fileline(), "Verilated::overWidthError(\""
                                                               + varp->prettyName() + "\");"}};
                        ifp->branchPred(VBranchPred::BP_UNLIKELY);
                        funcp->addStmtsp(ifp);
                    }
                }
            }
        }
    }
}

void V3CCtors::cctorsAll() {
    UINFO(2, __FUNCTION__ << ": " << endl);
    evalAsserts();
    { CCtorsVisitor{v3Global.rootp()}; }
    V3Global::dumpCheckGlobalTree("cctors", 0, dumpTreeLevel() >= 3);
}
