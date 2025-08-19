// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Handle SV classes
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2025 by Wilson Snyder. This program is free software; you
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

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Class.h"

#include "V3UniqueNames.h"

#include <queue>
#include <set>

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################

class ClassVisitor final : public VNVisitor {
    // NODE STATE
    //  AstClass::user1()       -> bool.  True if iterated already
    //  AstVar::user1p()        -> AstVarScope*  Scope used with this var
    const VNUser1InUse m_inuser1;

    // MEMBERS
    string m_prefix;  // String prefix to add to class name based on hier
    V3UniqueNames m_names;  // For unique naming of structs and unions
    AstNodeModule* m_modp = nullptr;  // Current module
    AstNodeModule* m_classPackagep = nullptr;  // Package moving into
    const AstScope* m_classScopep = nullptr;  // Package moving scopes into
    AstScope* m_packageScopep = nullptr;  // Class package scope
    const AstNodeFTask* m_ftaskp = nullptr;  // Current task
    std::vector<std::pair<AstNode*, AstScope*>> m_toScopeMoves;
    std::vector<std::pair<AstNode*, AstNodeModule*>> m_toPackageMoves;
    std::set<AstTypedef*> m_typedefps;  // Contains all typedef nodes
    std::set<AstNodeUOrStructDType*> m_strDtypeps;  // Contains all packed structs and unions
    // Contains all public packed structs and unions, using a queue to
    // mark embedded struct / union public by BFS
    std::queue<AstNodeUOrStructDType*> m_pubStrDtypeps;

    // METHODS

    void recurseImplements(AstClass* nodep) {
        // In SystemVerilog, we have two inheritance chains:
        // - extends of concrete clasess: mapped to non-virtual C++ inheritance
        //   as there is only single ancestor allowed
        // - implements of concrete classes / extends of interface classes: mapped
        //   to virtual inheritance to allow diamond patterns with multiple ancestors
        if (nodep->useVirtualPublic()) return;  // Short-circuit to exit diamond cycles
        if (nodep->isInterfaceClass()) { nodep->useVirtualPublic(true); }
        for (const AstClassExtends* extp = nodep->extendsp(); extp;
             extp = VN_AS(extp->nextp(), ClassExtends)) {
            recurseImplements(extp->classp());
        }
    }

    // VISITORS

    void visit(AstClass* nodep) override {
        if (nodep->user1SetOnce()) return;
        // Move this class
        nodep->name(m_prefix + nodep->name());
        nodep->unlinkFrBack();
        v3Global.rootp()->addModulesp(nodep);
        recurseImplements(nodep);
        // Make containing package
        // Note origName is the same as the class origName so errors look correct
        AstClassPackage* const packagep
            = new AstClassPackage{nodep->fileline(), nodep->origName(), nodep->libname()};
        packagep->name(nodep->name() + "__Vclpkg");
        nodep->editCountInc();
        nodep->classOrPackagep(packagep);
        packagep->classp(nodep);
        packagep->timeunit(nodep->timeunit());
        v3Global.rootp()->addModulesp(packagep);
        // Add package to hierarchy
        AstCell* const cellp = new AstCell{packagep->fileline(),
                                           packagep->fileline(),
                                           packagep->name(),
                                           packagep->name(),
                                           nullptr,
                                           nullptr,
                                           nullptr};
        cellp->modp(packagep);
        v3Global.rootp()->topModulep()->addStmtsp(cellp);
        // Find class's scope
        // Alternative would be to move this and related to V3Scope
        const AstScope* classScopep = nullptr;
        for (AstNode* itp = nodep->stmtsp(); itp; itp = itp->nextp()) {
            if ((classScopep = VN_CAST(itp, Scope))) break;
        }
        UASSERT_OBJ(classScopep, nodep, "No scope under class");

        // Add scope
        AstScope* const scopep
            = new AstScope{nodep->fileline(), packagep, classScopep->name(),
                           classScopep->aboveScopep(), classScopep->aboveCellp()};
        packagep->addStmtsp(scopep);
        // Iterate
        VL_RESTORER(m_prefix);
        VL_RESTORER(m_classPackagep);
        VL_RESTORER(m_classScopep);
        VL_RESTORER(m_packageScopep);
        VL_RESTORER(m_modp);
        m_modp = nodep;
        m_classPackagep = packagep;
        m_classScopep = classScopep;
        m_packageScopep = scopep;
        m_prefix = nodep->name() + "__02e";  // .
        iterateChildren(nodep);
    }
    void visit(AstNodeModule* nodep) override {
        // Visit for NodeModules that are not AstClass (AstClass is-a AstNodeModule)
        // Classes are always under a Package (perhaps $unit) or a module
        VL_RESTORER(m_prefix);
        VL_RESTORER(m_modp);
        m_modp = nodep;
        m_prefix = nodep->name() + "__03a__03a";  // ::
        iterateChildren(nodep);
    }

    void visit(AstVar* nodep) override {
        iterateChildren(nodep);
        if (m_packageScopep) {
            if (m_ftaskp && m_ftaskp->isStatic()) {
                // Move later, or we wouldn't keep iterating the class
                // We're really moving the VarScope but we might not
                // have a pointer to it yet
                m_toScopeMoves.emplace_back(nodep, m_packageScopep);
            }
            if (!m_ftaskp && (nodep->lifetime().isStatic() || nodep->isParam())) {
                m_toPackageMoves.emplace_back(nodep, m_classPackagep);
                // We're really moving the VarScope but we might not
                // have a pointer to it yet
                m_toScopeMoves.emplace_back(nodep, m_packageScopep);
            }
        }
    }

    void visit(AstVarScope* nodep) override {
        iterateChildren(nodep);
        nodep->varp()->user1p(nodep);
    }

    void visit(AstNodeFTask* nodep) override {
        VL_RESTORER(m_ftaskp);
        m_ftaskp = nodep;
        iterateChildren(nodep);
        if (m_packageScopep && nodep->isStatic()) {
            m_toScopeMoves.emplace_back(nodep, m_packageScopep);
        }
    }
    void visit(AstCFunc* nodep) override {
        iterateChildren(nodep);
        // Don't move now, or wouldn't keep iterating the class
        // TODO move function statics only
        // if (m_classScopep) {
        //    m_toScopeMoves.emplace_back(nodep, m_classScopep);
        //}
    }
    void visit(AstNodeCoverDecl* nodep) override {
        // Need to declare coverage in package, where we have access to symbol table
        iterateChildren(nodep);
        if (m_classPackagep) m_classPackagep->addStmtsp(nodep->unlinkFrBack());
    }
    void visit(AstInitial* nodep) override {
        // But not AstInitialAutomatic, which remains under the class
        iterateChildren(nodep);
        if (m_packageScopep) m_toScopeMoves.emplace_back(nodep, m_packageScopep);
    }
    void visit(AstInitialStatic* nodep) override {
        // But not AstInitialAutomatic, which remains under the class
        iterateChildren(nodep);
        if (m_packageScopep) m_toScopeMoves.emplace_back(nodep, m_packageScopep);
    }

    void setStructModulep(AstNodeUOrStructDType* const dtypep) {
        // Give struct a pointer to its package and a final name
        dtypep->editCountInc();
        dtypep->classOrPackagep(m_classPackagep ? m_classPackagep : m_modp);
        dtypep->name(
            m_names.get(dtypep->name() + (VN_IS(dtypep, UnionDType) ? "__union" : "__struct")));
        if (dtypep->packed()) m_strDtypeps.insert(dtypep);

        for (AstMemberDType* itemp = dtypep->membersp(); itemp;
             itemp = VN_AS(itemp->nextp(), MemberDType)) {
            AstNodeUOrStructDType* const subp = itemp->getChildStructp();
            // Recurse only into anonymous structs inside this definition,
            // other structs will be reached from another typedefs
            if (subp && subp->name().empty()) setStructModulep(subp);
        }
    }
    void visit(AstTypedef* nodep) override {
        if (nodep->user1SetOnce()) return;
        AstNodeUOrStructDType* const dtypep = VN_CAST(nodep->dtypep(), NodeUOrStructDType);
        if (dtypep && dtypep->packed()) {
            m_typedefps.insert(nodep);
            if (nodep->attrPublic()) m_pubStrDtypeps.push(dtypep);
        }
        iterateChildren(nodep);
        if (m_classPackagep) m_classPackagep->addStmtsp(nodep->unlinkFrBack());

        if (dtypep) {
            dtypep->name(nodep->name());
            setStructModulep(dtypep);
        }
    }

    void visit(AstNodeExpr* nodep) override {}  // Short circuit
    void visit(AstNodeStmt* nodep) override {}  // Short circuit
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit ClassVisitor(AstNetlist* nodep) { iterate(nodep); }
    ~ClassVisitor() override {
        for (auto moved : m_toScopeMoves) {
            AstNode* const nodep = moved.first;
            AstScope* const scopep = moved.second;
            UINFO(9, "moving " << nodep << " to " << scopep);
            if (VN_IS(nodep, NodeFTask)) {
                scopep->addBlocksp(nodep->unlinkFrBack());
            } else if (VN_IS(nodep, Var)) {
                AstVarScope* const vscp = VN_AS(nodep->user1p(), VarScope);
                vscp->scopep(scopep);
                vscp->unlinkFrBack();
                scopep->addVarsp(vscp);
            } else if (VN_IS(nodep, Initial) || VN_IS(nodep, InitialStatic)) {
                nodep->unlinkFrBack();
                scopep->addBlocksp(nodep);
            } else {
                nodep->v3fatalSrc("Bad case");
            }
        }
        for (auto moved : m_toPackageMoves) {
            AstNode* const nodep = moved.first;
            AstNodeModule* const modp = moved.second;
            UINFO(9, "moving " << nodep << " to " << modp);
            nodep->unlinkFrBack();
            modp->addStmtsp(nodep);
        }
        // BFS to mark public typedefs.
        std::set<const AstNodeUOrStructDType*> pubStrDtypeps;
        while (!m_pubStrDtypeps.empty()) {
            AstNodeUOrStructDType* const dtypep = m_pubStrDtypeps.front();
            m_pubStrDtypeps.pop();
            if (pubStrDtypeps.insert(dtypep).second) {
                for (AstMemberDType* itemp = dtypep->membersp(); itemp;
                     itemp = VN_AS(itemp->nextp(), MemberDType)) {
                    if (AstNodeUOrStructDType* const subp = itemp->getChildStructp())
                        m_pubStrDtypeps.push(subp);
                }
            }
        }
        for (AstTypedef* typedefp : m_typedefps) {
            const AstNodeUOrStructDType* const sdtypep
                = VN_AS(typedefp->dtypep(), NodeUOrStructDType);
            if (pubStrDtypeps.count(sdtypep)) typedefp->attrPublic(true);
        }
        // Clear package pointer of non-public packed struct / union type, which will never be
        // exported.
        for (AstNodeUOrStructDType* sdtypep : m_strDtypeps) {
            if (!pubStrDtypeps.count(sdtypep)) sdtypep->classOrPackagep(nullptr);
        }
    }
};

//######################################################################
// Class class functions

void V3Class::classAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ":");
    { ClassVisitor{nodep}; }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("class", 0, dumpTreeEitherLevel() >= 3);
}
