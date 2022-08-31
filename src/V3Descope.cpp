// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Rename scope references to module-local references
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
// DESCOPE TRANSFORMATIONS:
//      All modules:
//          Each VARREF/FUNCCALL
//              Change varref name() to be relative to current module
//              Remove varScopep()
//          This allows for better V3Combine'ing.
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3Descope.h"

#include "V3Ast.h"
#include "V3EmitCBase.h"
#include "V3Global.h"

#include <map>

//######################################################################

class DescopeVisitor final : public VNVisitor {
private:
    // NODE STATE
    //  Cleared entire netlist
    //   AstCFunc::user()               // bool.  Indicates processing completed
    const VNUser1InUse m_inuser1;

    // TYPES
    using FuncMmap = std::multimap<std::string, AstCFunc*>;

    // STATE
    AstNodeModule* m_modp = nullptr;  // Current module
    const AstScope* m_scopep = nullptr;  // Current scope
    const AstCFunc* m_funcp = nullptr;  // Current function
    bool m_modSingleton = false;  // m_modp is only instantiated once
    FuncMmap m_modFuncs;  // Name of public functions added

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    static bool modIsSingleton(AstNodeModule* modp) {
        // True iff there's exactly one instance of this module in the design (including top).
        if (modp->isTop()) return true;
        int instances = 0;
        for (AstNode* stmtp = modp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
            if (VN_IS(stmtp, Scope)) {
                if (++instances > 1) return false;
            }
        }
        return (instances == 1);
    }

    // Construct the best self pointer to reference an object in 'scopep'  from a CFunc in
    // 'm_scopep'. Result may be relative ("this->[...]") or absolute ("vlSyms->[...]").
    //
    // Using relative references allows V3Combine'ing code across multiple instances of the same
    // module.
    string descopedSelfPointer(const AstScope* scopep) {
        UASSERT(scopep, "Var/Func not scoped");
        // Static functions can't use relative references via 'this->'
        const bool relativeRefOk = !m_funcp->isStatic();

        UINFO(8, "      Descope ref under " << m_scopep << endl);
        UINFO(8, "              ref to    " << scopep << endl);
        UINFO(8, "             aboveScope " << scopep->aboveScopep() << endl);

        if (VN_IS(scopep->modp(), Class)) {
            // Direct reference to class members are from within the class itself, references from
            // outside the class must go via AstMemberSel
            return "this";
        } else if (relativeRefOk && scopep == m_scopep) {
            return "this";
        } else if (relativeRefOk && !m_modSingleton && scopep->aboveScopep() == m_scopep
                   && VN_IS(scopep->modp(), Module)) {
            // Reference to scope of instance directly under this module, can just "this->cell",
            // which can potentially be V3Combined, but note this requires one extra pointer
            // dereference which is slower, so we only use it if the source scope is not a
            // singleton.
            string name = scopep->name();
            string::size_type pos;
            if ((pos = name.rfind('.')) != string::npos) name.erase(0, pos + 1);
            return "this->" + name;
        } else {
            // Reference to something elsewhere, or relative references are disabled. Use global
            // variable
            return "(&" + scopep->nameVlSym() + ")";
        }
    }

    void makePublicFuncWrappers() {
        // We recorded all public functions in m_modFuncs.
        // If for any given name only one function exists, we can use that function directly.
        // If multiple functions exist, we need to select the appropriate scope.
        for (FuncMmap::iterator it = m_modFuncs.begin(); it != m_modFuncs.end(); ++it) {
            const string name = it->first;
            AstCFunc* const topFuncp = it->second;
            auto nextIt1 = it;
            ++nextIt1;
            const bool moreOfSame1 = (nextIt1 != m_modFuncs.end() && nextIt1->first == name);
            if (moreOfSame1) {
                // Multiple functions under this name, need a wrapper function
                UINFO(6, "  Wrapping " << name << " multifuncs\n");
                AstCFunc* const newfuncp = topFuncp->cloneTree(false);
                if (newfuncp->initsp()) newfuncp->initsp()->unlinkFrBackWithNext()->deleteTree();
                if (newfuncp->stmtsp()) newfuncp->stmtsp()->unlinkFrBackWithNext()->deleteTree();
                if (newfuncp->finalsp()) newfuncp->finalsp()->unlinkFrBackWithNext()->deleteTree();
                newfuncp->name(name);
                newfuncp->isStatic(false);
                topFuncp->addNextHere(newfuncp);
                // In the body, call each function if it matches the given scope
                for (FuncMmap::iterator eachIt = it;
                     eachIt != m_modFuncs.end() && eachIt->first == name; ++eachIt) {
                    it = eachIt;
                    AstCFunc* const funcp = eachIt->second;
                    auto nextIt2 = eachIt;
                    ++nextIt2;
                    const bool moreOfSame
                        = (nextIt2 != m_modFuncs.end() && nextIt2->first == name);
                    UASSERT_OBJ(funcp->scopep(), funcp, "Not scoped");

                    UINFO(6, "     Wrapping " << name << " " << funcp << endl);
                    UINFO(6,
                          "  at " << newfuncp->argTypes() << " und " << funcp->argTypes() << endl);
                    funcp->declPrivate(true);
                    AstNode* argsp = nullptr;
                    for (AstNode* stmtp = newfuncp->argsp(); stmtp; stmtp = stmtp->nextp()) {
                        if (AstVar* const portp = VN_CAST(stmtp, Var)) {
                            if (portp->isIO() && !portp->isFuncReturn()) {
                                AstNode* const newp = new AstVarRef(
                                    portp->fileline(), portp,
                                    portp->isWritable() ? VAccess::WRITE : VAccess::READ);
                                argsp = argsp ? argsp->addNextNull(newp) : newp;
                            }
                        }
                    }

                    AstNode* const returnp = new AstCReturn(
                        funcp->fileline(), new AstCCall(funcp->fileline(), funcp, argsp));

                    if (moreOfSame) {
                        AstIf* const ifp = new AstIf(
                            funcp->fileline(),
                            new AstEq(
                                funcp->fileline(), new AstCMath(funcp->fileline(), "this", 64),
                                new AstCMath(funcp->fileline(),
                                             string("&(") + funcp->scopep()->nameVlSym() + ")",
                                             64)),
                            returnp);
                        newfuncp->addStmtsp(ifp);
                    } else {
                        newfuncp->addStmtsp(returnp);
                    }
                }
                // Not really any way the user could do this, and we'd need
                // to come up with some return value
                // newfuncp->addStmtsp(new AstDisplay(newfuncp->fileline(),
                //                                   VDisplayType::DT_WARNING,
                //                                   string("%%Error: ")+name+"() called with bad
                //                                   scope", nullptr));
                // newfuncp->addStmtsp(new AstStop(newfuncp->fileline()));
                if (debug() >= 9) newfuncp->dumpTree(cout, "   newfunc: ");
            } else {
                // Only a single function under this name, we can rename it
                UINFO(6, "  Wrapping " << name << " just one " << topFuncp << endl);
                topFuncp->name(name);
            }
        }
    }

    // VISITORS
    virtual void visit(AstNetlist* nodep) override {
        nodep->dpiExportTriggerp(nullptr);
        iterateChildren(nodep);
    }
    virtual void visit(AstNodeModule* nodep) override {
        VL_RESTORER(m_modp);
        {
            m_modp = nodep;
            m_modFuncs.clear();
            m_modSingleton = modIsSingleton(m_modp);
            iterateChildren(nodep);
            makePublicFuncWrappers();
        }
    }
    virtual void visit(AstScope* nodep) override {
        m_scopep = nodep;
        iterateChildren(nodep);
        m_scopep = nullptr;
    }
    virtual void visit(AstVarScope* nodep) override {
        // Delete the varscope when we're finished
        nodep->unlinkFrBack();
        pushDeletep(nodep);
    }
    virtual void visit(AstNodeVarRef* nodep) override {
        iterateChildren(nodep);
        if (!nodep->varScopep()) {
            UASSERT_OBJ(nodep->varp()->isFuncLocal(), nodep,
                        "unscoped reference can only appear to function locals at this point");
            return;
        }
        // Convert the hierch name
        UINFO(9, "  ref-in " << nodep << endl);
        UASSERT_OBJ(m_scopep, nodep, "Node not under scope");
        const AstVar* const varp = nodep->varScopep()->varp();
        const AstScope* const scopep = nodep->varScopep()->scopep();
        if (varp->isFuncLocal()) {
            // Reference to function locals need no self pointer
            nodep->selfPointer("");
        } else if (scopep->modp() == v3Global.rootp()->constPoolp()->modp()) {
            // Reference to constant pool value need no self pointer
            nodep->selfPointer("");
        } else {
            nodep->selfPointer(descopedSelfPointer(scopep));
        }
        nodep->varScopep(nullptr);
        UINFO(9, "  refout " << nodep << " selfPtr=" << nodep->selfPointer() << endl);
    }
    virtual void visit(AstCCall* nodep) override {
        // UINFO(9, "       " << nodep << endl);
        iterateChildren(nodep);
        // Convert the hierch name
        UASSERT_OBJ(m_scopep, nodep, "Node not under scope");
        const AstScope* const scopep = nodep->funcp()->scopep();
        nodep->selfPointer(descopedSelfPointer(scopep));
        // Can't do this, as we may have more calls later
        // nodep->funcp()->scopep(nullptr);
    }
    virtual void visit(AstCMethodCall* nodep) override { iterateChildren(nodep); }
    virtual void visit(AstCNew* nodep) override { iterateChildren(nodep); }
    virtual void visit(AstCFunc* nodep) override {
        VL_RESTORER(m_funcp);
        if (!nodep->user1()) {
            // Static functions should have been moved under the corresponding AstClassPackage
            UASSERT_OBJ(!(nodep->isStatic() && VN_IS(m_modp, Class)), nodep,
                        "Static function under AstClass");
            m_funcp = nodep;
            iterateChildren(nodep);
            nodep->user1(true);
            // If it's under a scope, move it up to the top
            if (m_scopep) {
                nodep->unlinkFrBack();
                m_modp->addStmtp(nodep);

                if (nodep->funcPublic()) {
                    // There may be multiple public functions by the same name;
                    // record for later correction or making of shells
                    m_modFuncs.emplace(nodep->name(), nodep);
                    nodep->name(m_scopep->nameDotless() + "__" + nodep->name());
                }
            }
        }
    }
    virtual void visit(AstVar*) override {}
    virtual void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit DescopeVisitor(AstNetlist* nodep) { iterate(nodep); }
    virtual ~DescopeVisitor() override = default;
};

//######################################################################
// Descope class functions

void V3Descope::descopeAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    { DescopeVisitor{nodep}; }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("descope", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}
