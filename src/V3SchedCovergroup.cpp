// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Resolve covergroup reference formal arguments for
//                         scheduling
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
// V3SchedCovergroup's Transformations:
//
// None - this only gathers information.
//
// A covergroup 'ref'/'const ref' formal argument becomes a pointer member of the covergroup
// class, bound when the covergroup is constructed. A sample() reading through it therefore
// holds no AstVarRef naming the design variable it reads, and V3Order would see the sampling
// block as reading nothing. Record what each construction binds, so V3Order can attribute
// those reads to the blocks that call sample().
//
// Bindings are keyed by the constructed handle where that is exact, which it is when every
// write of the handle is a construction of the recognized shape 'handle = new(...)'. Any other
// way for a covergroup object to reach a handle - an aliasing assignment, a temporary
// introduced by V3Task, an array element, passing the handle to a function by reference - is
// itself a write of that handle, and taints it. A tainted handle falls back to the union over
// all constructions of its class, which is an over-approximation, but safe.
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3AstNodeExpr.h"
#include "V3Sched.h"

#include <unordered_set>

VL_DEFINE_DEBUG_FUNCTIONS;

namespace V3Sched {

const CovergroupRefBindings::Bindings CovergroupRefBindings::s_none;

void CovergroupRefBindings::addConstruction(const AstClass* classp, const AstVarScope* instp,
                                            const Bindings& bindings) {
    Bindings& classBindings = m_byClass[classp];
    classBindings.insert(classBindings.end(), bindings.begin(), bindings.end());
    // Note this creates an entry even when 'bindings' is empty, so that a handle binding
    // nothing stays distinguishable from a handle we know nothing about
    if (instp) {
        Bindings& instBindings = m_byInstance[instp];
        instBindings.insert(instBindings.end(), bindings.begin(), bindings.end());
    }
}

const CovergroupRefBindings::Bindings&
CovergroupRefBindings::forSample(const AstVarScope* instp, const AstClass* classp) const {
    if (instp) {
        const auto it = m_byInstance.find(instp);
        if (it != m_byInstance.end()) {
            ++m_numExactCalls;
            return it->second;
        }
    }
    const auto it = m_byClass.find(classp);
    if (it != m_byClass.end()) {
        ++m_numUnionCalls;
        return it->second;
    }
    // A covergroup with no reference formal at all
    return s_none;
}

namespace {

// The covergroup class this call constructs, or nullptr if it is not a covergroup construction
AstClass* constructedCovergroup(const AstNodeCCall* nodep) {
    const AstCFunc* const funcp = nodep->funcp();
    if (!funcp->isConstructor()) return nullptr;
    // A constructor is a class method, so it is scoped and its scope is that of a class
    AstClass* const classp = VN_AS(funcp->scopep()->modp(), Class);
    return classp->isCovergroup() ? classp : nullptr;
}

// True if this variable holds a handle to a covergroup object
bool isCovergroupHandle(const AstVar* varp) {
    const AstClassRefDType* const dtypep = VN_CAST(varp->dtypep()->skipRefp(), ClassRefDType);
    return dtypep && dtypep->classp()->isCovergroup();
}

// True if this constructor takes a reference formal, and so has anything to bind
bool hasRefFormal(const AstCFunc* funcp) {
    for (AstNode* portp = funcp->argsp(); portp; portp = portp->nextp()) {
        const AstVar* const varp = VN_AS(portp, Var);
        if (varp->declDirection().isRef() || varp->declDirection().isConstRef()) return true;
    }
    return false;
}

class CovergroupRefBindVisitor final : public VNVisitor {
    // STATE
    CovergroupRefBindings m_bindings;  // Result
    // Covergroup handles written by something other than a construction we recognized
    std::unordered_set<const AstVarScope*> m_tainted;

    // METHODS

    // Record one construction of 'classp' assigning to 'instp' (nullptr if not identified).
    // A covergroup with no reference formal has nothing to bind, and is left out entirely, so
    // that an entry with no bindings means only 'this handle binds nothing a sample() reads'.
    void recordConstruction(AstNodeCCall* nodep, const AstClass* classp,
                            const AstVarScope* instp) {
        if (!hasRefFormal(nodep->funcp())) return;
        m_bindings.addConstruction(classp, instp, refBindingsOf(nodep));
    }

    // The design variables this construction binds to reference formals
    CovergroupRefBindings::Bindings refBindingsOf(AstNodeCCall* nodep) {
        CovergroupRefBindings::Bindings bindings;
        // Actuals correspond one to one, in order, with the function's argument variables.
        // A constructor returns void, so none of them is a return value variable.
        AstNode* actualp = nodep->argsp();
        for (AstNode* portp = nodep->funcp()->argsp(); portp; portp = portp->nextp()) {
            UASSERT_OBJ(actualp, nodep, "Constructor call has fewer arguments than formals");
            AstNode* const thisActualp = actualp;
            actualp = actualp->nextp();
            const AstVar* const varp = VN_AS(portp, Var);
            if (!varp->declDirection().isRef() && !varp->declDirection().isConstRef()) continue;
            // A 'ref' actual is an lvalue expression, so it need not be a plain variable
            // reference. Bind every variable it names: for 'sigs[0]' that is 'sigs', which is
            // exact rather than approximate, as V3Order models the whole array as one
            // VarScope. An index expression contributes its own variables as well, which is an
            // over-approximation, and so safe.
            thisActualp->foreach([&](AstVarRef* refp) {
                AstVarScope* const vscp = refp->varScopep();
                UASSERT_OBJ(vscp, refp, "Var didn't get varscoped in V3Scope.cpp");
                bindings.push_back(vscp);
            });
        }
        return bindings;
    }

    // VISITORS
    void visit(AstNodeAssign* nodep) override {
        AstCNew* const cnewp = VN_CAST(nodep->rhsp(), CNew);
        AstVarRef* const lhsRefp = VN_CAST(nodep->lhsp(), VarRef);
        AstClass* const classp = cnewp && lhsRefp ? constructedCovergroup(cnewp) : nullptr;
        if (!classp) {
            iterateChildren(nodep);
            return;
        }
        recordConstruction(cnewp, classp, lhsRefp->varScopep());
        // Deliberately not iterating the destination: this write is the one shape that does not
        // taint the handle. Do iterate the arguments, which may write handles of their own.
        iterateChildren(cnewp);
    }

    void visit(AstNodeCCall* nodep) override {
        iterateChildren(nodep);
        // A construction reached only here is one whose destination we could not identify, so
        // every handle of the class must assume it
        if (const AstClass* const classp = constructedCovergroup(nodep)) {
            recordConstruction(nodep, classp, nullptr);
        }
    }

    void visit(AstVarRef* nodep) override {
        if (!nodep->access().isWriteOrRW()) return;
        if (!isCovergroupHandle(nodep->varp())) return;
        m_tainted.emplace(nodep->varScopep());
    }

    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit CovergroupRefBindVisitor(AstNetlist* nodep) {
        iterate(nodep);
        for (const AstVarScope* const vscp : m_tainted) m_bindings.dropInstance(vscp);
    }
    ~CovergroupRefBindVisitor() override = default;

    // METHODS
    CovergroupRefBindings take_bindings() { return std::move(m_bindings); }
};

}  // namespace

CovergroupRefBindings makeCovergroupRefBindings(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ":");
    CovergroupRefBindings bindings{};
    if (v3Global.useCovergroup()) bindings = CovergroupRefBindVisitor{nodep}.take_bindings();
    return bindings;
}

}  // namespace V3Sched
