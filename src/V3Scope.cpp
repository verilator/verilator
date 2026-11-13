// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Break always into sensitivity block domains
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
// V3Scope's Transformations:
//
//      For every CELL that references this module, create a
//              SCOPE
//                      {all blocked statements}
//
//      A class declared under a module has its methods moved under the single class scope of one
//      instantiation of that module, so a method that uses the declaring module's own state can
//      only ever bind to that instantiation.  Each other instantiation therefore gets a copy: a
//      class derived from the original, overriding the methods that use that state, including the
//      constructor's body, which moves into a virtual method the constructor calls.  A class that
//      does not use the declaring module's state is never copied.
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Scope.h"

#include "V3ConstPool.h"
#include "V3Control.h"
#include "V3UniqueNames.h"

#include <unordered_map>
#include <unordered_set>

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// Scope class functions

class ScopeVisitor final : public VNVisitor {
    // NODE STATE
    // AstVar::user1p           -> AstVarScope*.  Replacement for this variable
    // AstCell::user2p          -> AstScope*.  The scope created inside the cell
    // AstTask::user2p          -> AstTask*.  Replacement task
    // AstNodeModule::user3()   -> uint64_t.  Pending instantiations of this module
    const VNUser1InUse m_inuser1;
    const VNUser2InUse m_inuser2;
    const VNUser3InUse m_inuser3;

    // TYPES
    // These cannot be unordered unless make a specialized hashing pair (gcc-8)
    using VarScopeMap = std::map<std::pair<AstVar*, AstScope*>, AstVarScope*>;

    // STATE, inside processing a single module
    AstNodeModule* m_modp = nullptr;  // Current module
    AstNodeProcedure* m_procedurep = nullptr;  // Current procedure
    AstScope* m_scopep = nullptr;  // Current scope we are building
    // STATE, for passing down one level of hierarchy (may need save/restore)
    AstCell* m_aboveCellp = nullptr;  // Cell that instantiates this module
    AstScope* m_aboveScopep = nullptr;  // Scope that instantiates this scope
    bool m_last = false;  // Scoping the last instantiation of the current module

    std::unordered_map<AstNodeModule*, AstScope*>
        m_classOrPackageScopes;  // Scopes for each class or package
    VarScopeMap m_varScopes;  // Varscopes created for each scope and var
    // Varrefs-in-scopes needing fixup when done
    std::vector<std::pair<AstVarRef*, AstScope*>> m_varRefScopes;
    std::vector<AstScope*> m_scopes;  // Scopes awaiting attachment to their modules
    // STATE, for classes declared directly under a module or interface.  A class's methods move
    // under the class scope of one instantiation of the module declaring it, so a method using
    // that module's own state cannot work for any other instantiation.  Each other instantiation
    // gets a copy: a class derived from the original, overriding those methods.
    struct ClassCopy final {
        AstClass* classp;  // The copy
        AstNodeFTask* newp;  // The copy's constructor
        AstClassRefDType* dtypep;  // Handle type naming the copy
    };
    std::unordered_map<AstNodeFTask*, ClassCopy> m_classCopies;  // By original constructor, for
                                                                 // the instance being scoped
    std::unordered_set<const AstClass*> m_classCopiesMade;  // Every copy made, all instances
    V3UniqueNames m_classCopyNames;  // For unique naming of class copies
    int m_ctorBodies = 0;  // Count of virtual constructor bodies, for unique naming

    // METHODS

    // Return the items declared directly in 'modp', whose use binds a class declared in it to one
    // instantiation of 'modp'.
    static std::unordered_set<const AstNode*> declaredMembers(const AstNodeModule* const modp) {
        std::unordered_set<const AstNode*> memberps;
        for (const AstNode* itemp = modp->stmtsp(); itemp; itemp = itemp->nextp())
            memberps.insert(itemp);
        return memberps;
    }

    // Return whether 'nodep' uses one of 'memberps', and therefore only works with the one
    // instantiation of the module that declares the class 'nodep' belongs to.
    static bool usesMembers(const AstNode* const nodep,
                            const std::unordered_set<const AstNode*>& memberps) {
        return nodep->exists([&memberps](const AstNodeVarRef* const refp) {
            return refp->varp() && memberps.count(refp->varp());
        });
    }

    // Return whether 'nodep' is the statement by which a derived class's constructor calls its
    // base class's constructor.  V3EmitCFunc recognizes the same node by its void dtype.
    static bool isSuperNew(const AstNode* const nodep) {
        const AstStmtExpr* const stmtp = VN_CAST(nodep, StmtExpr);
        const AstNew* const newp = stmtp ? VN_CAST(stmtp->exprp(), New) : nullptr;
        return newp && VN_IS(newp->dtypep(), VoidDType);
    }

    // Move the statements of 'ctorp', a constructor of class 'nodep', into a new virtual method
    // that the constructor calls, so that a class derived from 'nodep' can replace them.  The
    // constructor keeps its ports, as its callers pass arguments to it, and the new method gets a
    // port of its own for each, which the constructor passes along.  Only the local variables that
    // just the body used move to it.  A 'super.new' stays in the constructor: the body method
    // cannot call it, as the base class's constructor has run already by the time it does.
    void makeCtorBodyMethod(AstClass* const nodep, AstNodeFTask* const ctorp) {
        FileLine* const flp = ctorp->fileline();
        // Named uniquely per class, as a copy overriding both its own constructor's body and an
        // extended class's would otherwise declare one method name twice
        AstTask* const bodyp = new AstTask{flp, "__VctorBody"s + std::to_string(++m_ctorBodies)};
        bodyp->classMethod(true);
        bodyp->isVirtual(true);
        nodep->addMembersp(bodyp);
        AstArg* argsp = nullptr;
        std::unordered_map<const AstVar*, AstVar*> portMap;
        for (AstNode *itemp = ctorp->declsp(), *nextp; itemp; itemp = nextp) {
            nextp = itemp->nextp();
            AstVar* const varp = VN_CAST(itemp, Var);
            if (!varp) continue;
            if (varp->isIO()) {  // The constructor keeps its ports, the body method gets its own
                AstVar* const fromp = varp->cloneTree(false);
                bodyp->addDeclsp(fromp);
                portMap.emplace(varp, fromp);
                argsp = AstNode::addNext(
                    argsp, new AstArg{flp, "", new AstVarRef{flp, varp, VAccess::READ}});
            } else if (varp->isFuncLocal()) {  // Only the moved body used it
                bodyp->addDeclsp(varp->unlinkFrBack());
            }
        }
        AstNode* stmtp = ctorp->stmtsp();
        while (stmtp && isSuperNew(stmtp)) stmtp = stmtp->nextp();
        if (stmtp) {
            bodyp->addStmtsp(VN_AS(stmtp->unlinkFrBackWithNext(), NodeStmt));
            // A use of a constructor's port is now a use of the body method's own
            bodyp->foreach([&portMap](AstVarRef* const refp) {
                const auto it = portMap.find(refp->varp());
                if (it != portMap.end()) refp->varp(it->second);
            });
        }
        AstClassRefDType* const refDTypep = new AstClassRefDType{flp, nodep, nullptr};
        v3Global.rootp()->typeTablep()->addTypesp(refDTypep);
        AstMethodCall* const callp
            = new AstMethodCall{flp, new AstThisRef{flp, refDTypep}, bodyp->name(), argsp};
        callp->taskp(bodyp);
        callp->dtypeSetVoid();
        ctorp->addStmtsp(callp->makeStmt());
    }

    // Return the class 'classp' extends, or nullptr.  Interface classes are implemented rather
    // than extended, and have nothing to inherit.
    static AstClass* extendedClassp(AstClass* const classp) {
        for (AstClassExtends* const extp : classp->extendspList()) {
            if (extp->classp() && !extp->classp()->isInterfaceClass()) return extp->classp();
        }
        return nullptr;
    }

    // Return the member functions of 'classp', and of the classes it extends, that use one of
    // 'memberps' and so only work with the one instantiation of the module that declares them.
    // Only the most derived declaration of a name is kept, as that is the one a call would run.
    static std::vector<AstNodeFTask*>
    boundMethods(AstClass* const classp, const std::unordered_set<const AstNode*>& memberps) {
        std::vector<AstNodeFTask*> methodps;
        std::unordered_set<std::string> names;
        for (AstClass* clp = classp; clp; clp = extendedClassp(clp)) {
            for (AstNode* itemp = clp->membersp(); itemp; itemp = itemp->nextp()) {
                AstNodeFTask* const methodp = VN_CAST(itemp, NodeFTask);
                if (!methodp || methodp->name() == "new") continue;
                if (!names.insert(methodp->name()).second) continue;
                if (usesMembers(methodp, memberps)) methodps.push_back(methodp);
            }
        }
        return methodps;
    }

    // Give the instantiation being scoped a class derived from 'nodep', overriding each method
    // that binds 'nodep' to a single instantiation of the declaring module 'declModp', and return
    // it.  The overrides are C++ virtual, so a handle of the original class type calls the body
    // bound to the object's own instantiation.  Returns nullptr when nothing needs overriding.
    AstClass* makeClassCopy(AstClass* const nodep, AstNodeModule* const declModp) {
        const std::unordered_set<const AstNode*> memberps = declaredMembers(declModp);
        AstNodeFTask* origNewp = nullptr;
        for (AstNode* itemp = nodep->membersp(); itemp; itemp = itemp->nextp()) {
            AstNodeFTask* const ctorp = VN_CAST(itemp, NodeFTask);
            if (ctorp && ctorp->name() == "new") origNewp = ctorp;
        }
        // Only done once: what the constructor body leaves behind, the virtual method the copy
        // overrides, is itself found by the search below on every later instantiation
        if (origNewp && usesMembers(origNewp, memberps)) makeCtorBodyMethod(nodep, origNewp);
        const std::vector<AstNodeFTask*> methodps = boundMethods(nodep, memberps);
        if (methodps.empty()) return nullptr;
        // Nothing was moved out of the class before now, as that only happens when the class is
        // scoped, and a class needing a copy is only ever scoped as that copy
        UASSERT_OBJ(origNewp, nodep, "Class has no constructor");
        FileLine* const flp = nodep->fileline();
        AstClass* const newp
            = new AstClass{flp,  //
                           m_classCopyNames.get(nodep->name() + "__Vclscopy"), nodep->libname()};
        newp->timeunit(nodep->timeunit());
        // V3LinkDot requires a class to be under a module, so the copy stays beside the original
        // until V3Class makes it a top-level class of its own.
        AstClassRefDType* const baseDTypep = new AstClassRefDType{flp, nodep, nullptr};
        AstClassExtends* const extendsp = new AstClassExtends{flp, nullptr, false};
        extendsp->childDTypep(baseDTypep);
        extendsp->dtypep(baseDTypep);
        newp->addExtendsp(extendsp);
        nodep->isExtended(true);
        newp->isExtended(true);
        declModp->addStmtsp(newp);
        // The copy's constructor does no work of its own: the original class's constructor runs as
        // the base class's, and does that work through the virtual body method the copy overrides.
        // What it does pass on are its own ports, for the base class's constructor takes them.
        // Naming the base class's constructor is also what makes this constructor get emitted at
        // all, as an empty constructor body is not.
        AstFunc* const copyNewp = VN_AS(origNewp->cloneTree(false), Func);
        for (AstNode *itemp = copyNewp->declsp(), *nextp; itemp; itemp = nextp) {
            nextp = itemp->nextp();
            AstVar* const varp = VN_CAST(itemp, Var);
            // Ports stay, as the callers of 'new' pass arguments to this constructor
            if (!varp || varp->isIO() || !varp->isFuncLocal()) continue;
            VL_DO_DANGLING(pushDeletep(varp->unlinkFrBack()), varp);
        }
        if (AstNode* const stmtp = copyNewp->stmtsp())
            VL_DO_DANGLING(pushDeletep(stmtp->unlinkFrBackWithNext()), stmtp);
        AstArg* argsp = nullptr;
        for (AstNode* itemp = copyNewp->declsp(); itemp; itemp = itemp->nextp()) {
            AstVar* const varp = VN_CAST(itemp, Var);
            if (!varp || !varp->isIO()) continue;
            argsp = AstNode::addNext(argsp,
                                     new AstArg{flp, "", new AstVarRef{flp, varp, VAccess::READ}});
        }
        AstNew* const superNewp = new AstNew{flp, argsp};
        superNewp->isImplicit(true);
        superNewp->classOrPackagep(nodep);
        superNewp->taskp(origNewp);
        superNewp->dtypeSetVoid();
        copyNewp->addStmtsp(superNewp->makeStmt());
        newp->addMembersp(copyNewp);
        AstClassRefDType* const copyDTypep = new AstClassRefDType{flp, newp, nullptr};
        v3Global.rootp()->typeTablep()->addTypesp(copyDTypep);
        for (AstNodeFTask* const methodp : methodps) {
            methodp->isVirtual(true);
            AstNodeFTask* const overridep = methodp->cloneTree(false);
            overridep->isVirtual(true);
            relabelCloneVars(overridep);
            newp->addMembersp(overridep);
        }
        m_classCopiesMade.insert(newp);
        m_classCopies.emplace(origNewp, ClassCopy{newp, copyNewp, copyDTypep});
        retargetNews(newp);
        UINFO(4, " CLASS COPY " << newp);
        return newp;
    }

    // Objects created within 'nodep' must use the copy made for the instantiation being scoped,
    // so that their methods are the ones bound to that instantiation.  'nodep' must have just
    // been added to the tree, so that only its own subtree is rewritten.
    void retargetNews(AstNode* const nodep) {
        if (m_classCopies.empty()) return;
        nodep->foreach([this](AstNew* const newp) {
            // A 'super.new' names the base class's constructor, it creates no object
            if (VN_IS(newp->dtypep(), VoidDType)) return;
            const auto it = m_classCopies.find(newp->taskp());
            if (it == m_classCopies.end()) return;
            const ClassCopy& copy = it->second;
            newp->classOrPackagep(copy.classp);
            newp->taskp(copy.newp);
            newp->dtypep(copy.dtypep);
            UINFO(6, "   New in " << copy.classp);
        });
    }

    // A cloned method owns its own ports and local variables, but a reference to one of them
    // still names the class the method was cloned from as its owner, which is the wrong class to
    // look the variable's scope up in.
    static void relabelCloneVars(AstNode* const clonemp) {
        std::unordered_set<const AstNode*> ownps;
        clonemp->foreach([&ownps](const AstVar* const varp) { ownps.insert(varp); });
        clonemp->foreach([&ownps](AstNodeVarRef* const refp) {
            if (ownps.count(refp->varp())) refp->classOrPackagep(nullptr);
        });
    }

    // Count module instantiations, visiting cells the same way the traversal below does
    static void countInstantiations(AstNodeModule* modp) {
        modp->user3Inc();
        for (AstNode* const stmtp : modp->stmtspList()) {
            if (const AstCell* const cellp = VN_CAST(stmtp, Cell)) {
                countInstantiations(cellp->modp());
            }
        }
    }

    // Copy, or move (on the last instantiation), the given node under
    // the current scope, and return the version now under the scope
    template <typename T_Node>
    T_Node* cloneOrMove(T_Node* nodep) {
        T_Node* clonep;
        if (m_last) {
            nodep->unlinkFrBack();
            clonep = nodep;
        } else {
            clonep = nodep->cloneTree(false);
        }
        nodep->user2p(clonep);
        m_scopep->addBlocksp(clonep);
        return clonep;
    }

    void cleanupVarRefs() {
        for (const auto& itr : m_varRefScopes) {
            AstVarRef* const nodep = itr.first;
            AstScope* scopep = itr.second;
            if (nodep->classOrPackagep()
                && !VN_IS(nodep->classOrPackagep(),
                          Module)) {  // Module scopes are not in m_classOrPackageScopes
                const auto it2 = m_classOrPackageScopes.find(nodep->classOrPackagep());
                UASSERT_OBJ(it2 != m_classOrPackageScopes.end(), nodep,
                            "Can't locate class or package scope");
                scopep = it2->second;
            }
            nodep->classOrPackagep(nullptr);  // No longer needed after V3Scope
            // Search up the scope hierarchy for the variable
            AstVarScope* varscp = nullptr;
            AstScope* searchScopep = scopep;
            while (searchScopep) {
                const auto it3 = m_varScopes.find(std::make_pair(nodep->varp(), searchScopep));
                if (it3 != m_varScopes.end()) {
                    varscp = it3->second;
                    break;
                }
                searchScopep = searchScopep->aboveScopep();
            }
            UASSERT_OBJ(varscp, nodep, "Can't locate varref scope");
            nodep->varScopep(varscp);
        }
    }

    // VISITORS
    void visit(AstNetlist* nodep) override {
        AstNodeModule* const modp = nodep->topModulep();
        if (!modp) {
            nodep->v3error("No top level module found");
            return;
        }
        // Operate starting at the top of the hierarchy
        m_aboveCellp = nullptr;
        m_aboveScopep = nullptr;
        countInstantiations(modp);
        iterate(modp);
        // Defer attachment until all instances are visited so cell collection and child
        // iteration do not rescan a growing list of completed scopes.
        for (AstScope* const scopep : m_scopes) scopep->modp()->addStmtsp(scopep);
        if (v3Global.opt.mtasks()) V3Control::applyThreadsGroupWorkers(m_scopes);
        cleanupVarRefs();
    }
    void visit(AstNodeModule* nodep) override {
        // Create required blocks and add to module
        string scopename;
        if (!m_aboveScopep) {
            scopename = "TOP";
        } else {
            scopename = m_aboveScopep->name() + "." + m_aboveCellp->name();
            // The top modules are directly under 'TOP'
            if (m_aboveScopep->isTop() && VN_IS(nodep, Module)) {
                v3Global.rootp()->addL2Name(AstNode::prettyName(m_aboveCellp->name()));
            }
        }

        UINFO(4, " MOD AT " << scopename << "  " << nodep);
        AstNode::user1ClearTree();

        m_scopep = new AstScope{
            (m_aboveCellp ? static_cast<AstNode*>(m_aboveCellp) : static_cast<AstNode*>(nodep))
                ->fileline(),
            nodep, scopename, m_aboveScopep, m_aboveCellp};
        if (VN_IS(nodep, Package)) m_classOrPackageScopes.emplace(nodep, m_scopep);

        // Get list of cells before we edit, to avoid excess visits (issue #6059)
        std::deque<AstCell*> cells;
        for (AstNode* const cellnextp : nodep->stmtspList()) {
            if (AstCell* const cellp = VN_CAST(cellnextp, Cell)) cells.push_back(cellp);
        }

        // Now for each child cell, iterate the module this cell points to
        for (AstCell* const cellp : cells) {
            VL_RESTORER(m_scopep);  // Protects m_scopep set in called module
            // which is "above" in this code, but later in code execution order
            VL_RESTORER(m_aboveCellp);
            VL_RESTORER(m_aboveScopep);
            {
                m_aboveCellp = cellp;
                m_aboveScopep = m_scopep;
                AstNodeModule* const modp = cellp->modp();
                UASSERT_OBJ(modp, cellp, "Unlinked mod");
                iterate(modp);  // Recursive call to visit(AstNodeModule)
                if (VN_IS(modp, Iface)) {
                    // Remember newly created scope
                    cellp->user2p(m_scopep);
                }
            }
        }

        // Create scope for the current usage of this module
        UINFO(4, " back AT " << scopename << "  " << nodep);
        AstNode::user1ClearTree();
        m_modp = nodep;
        if (m_modp->isTop()) {
            v3Global.rootp()->createTopScope(m_scopep);
        } else {
            m_scopes.push_back(m_scopep);
        }

        // Copy blocks into this scope
        {
            VL_RESTORER(m_last);
            const uint64_t nInsts = nodep->user3();
            UASSERT_OBJ(nInsts, nodep, "Module scoped more times than instantiated");
            nodep->user3(nInsts - 1);
            m_last = nInsts == 1;
            // Copies made for a previous instantiation no longer apply to this one
            m_classCopies.clear();
            iterateChildren(nodep);
            // Objects created in this instantiation use the copies made for it, so their methods
            // are the ones bound to this instantiation.
            retargetNews(m_scopep);
        }

        // ***Note m_scopep is passed back to the caller of the routine (above)
    }
    void visit(AstClass* nodep) override {
        // A copy is scoped for the instantiation it was made for, as soon as it is made
        if (m_classCopiesMade.count(nodep)) return;
        // Create required blocks and add to module
        VL_RESTORER(m_scopep);
        VL_RESTORER(m_aboveCellp);
        VL_RESTORER(m_aboveScopep);
        VL_RESTORER(m_modp);
        AstNodeModule* const declModp = m_modp;
        // The methods of a class declared under a module move under one class scope, so they can
        // only ever bind to one instantiation of that module.  Give every other instantiation a
        // derived class overriding the methods that use the module's own state.
        if (!m_last && !VN_IS(declModp, Class) && !VN_IS(declModp, Package)) {
            if (AstClass* const copyp = makeClassCopy(nodep, declModp)) nodep = copyp;
        }
        m_aboveScopep = m_scopep;
        m_modp = nodep;

        string scopename;
        if (!m_aboveScopep) {
            scopename = "TOP";
        } else {
            scopename = m_aboveScopep->name() + "." + nodep->name();
        }

        UINFO(4, " CLASS AT " << scopename << "  " << nodep);
        AstNode::user1ClearTree();

        const AstNode* const abovep
            = (m_aboveCellp ? static_cast<AstNode*>(m_aboveCellp) : static_cast<AstNode*>(nodep));
        m_scopep
            = new AstScope{abovep->fileline(), m_modp, scopename, m_aboveScopep, m_aboveCellp};
        m_classOrPackageScopes.emplace(nodep, m_scopep);

        // Create scope for the current usage of this cell
        AstNode::user1ClearTree();
        m_scopes.push_back(m_scopep);

        iterateChildren(nodep);
    }
    void visit(AstCellInline* nodep) override {  //
        if (!v3Global.opt.vpi()) return;
        m_scopep->addInlinesp(
            new AstCellInlineScope{nodep->fileline(), nodep->name(), nodep->origModName()});
    }
    void visit(AstActive* nodep) override {  // LCOV_EXCL_LINE
        nodep->v3fatalSrc("Actives now made after scoping");
    }
    void visit(AstNodeProcedure* nodep) override {
        // Add to list of blocks under this scope
        // Check don't miss varref scope assignments
        UASSERT_OBJ(!m_procedurep, nodep, "prodedure in procedure");
        VL_RESTORER(m_procedurep);
        m_procedurep = nodep;
        UINFO(4, "    Move " << nodep);
        // We iterate under the *clone*
        iterateChildren(cloneOrMove(nodep));
    }
    void visit(AstAlias* nodep) override {
        // Add to list of blocks under this scope
        UINFO(4, "    Move " << nodep);
        // We iterate under the *clone*
        iterateChildren(cloneOrMove(nodep));
    }
    void visit(AstAliasScope* nodep) override {
        // Copy under the scope but don't recurse
        UINFO(4, "    Move " << nodep);
        // We iterate under the *clone*
        iterateChildren(cloneOrMove(nodep));
    }
    void visit(AstCFunc* nodep) override {
        // Add to list of blocks under this scope
        UINFO(4, "    CFUNC " << nodep);
        AstCFunc* const clonep = cloneOrMove(nodep);
        clonep->scopep(m_scopep);
        // We iterate under the *clone*
        iterateChildren(clonep);
    }
    void visit(AstNodeFTask* nodep) override {
        // Add to list of blocks under this scope
        UINFO(4, "    FTASK " << nodep);
        AstNodeFTask* const clonep = [&]() {
            VL_RESTORER(m_last);
            // Only one scope will be created, so avoid pointless cloning
            if (nodep->classMethod()) m_last = true;
            return cloneOrMove(nodep);
        }();
        clonep->user2p(clonep);  // For recursive self-references after cloneTree
        // We iterate under the *clone*
        iterateChildren(clonep);
    }
    void visit(AstVar* nodep) override {
        // Make new scope variable
        if (!nodep->user1p()) {
            AstScope* scopep = m_scopep;
            if (const AstIfaceRefDType* const ifrefp = VN_CAST(nodep->dtypep(), IfaceRefDType)) {
                // Attach every non-virtual interface variable its inner scope
                if (ifrefp->cellp()) scopep = VN_AS(ifrefp->cellp()->user2p(), Scope);
            }
            AstVarScope* const varscp = new AstVarScope{nodep->fileline(), scopep, nodep};
            UINFO(6, "   New scope " << varscp);
            if (m_aboveCellp && !m_aboveCellp->isTrace()) varscp->trace(false);
            nodep->user1p(varscp);
            UASSERT_OBJ(m_scopep, nodep, "No scope for var");
            m_varScopes.emplace(std::make_pair(nodep, m_scopep), varscp);
            m_scopep->addVarsp(varscp);
        }
        iterateChildren(nodep);
    }
    void visit(AstVarRef* nodep) override {
        // VarRef needs to point to VarScope
        // Make sure variable has made user1p.
        UASSERT_OBJ(nodep->varp(), nodep, "Unlinked");
        // We may have not made the variable yet, and we can't make it now as
        // the var's referenced package etc might not be created yet.
        // So push to a list and post-correct.
        // No check here for nodep->classOrPackagep(), will check when walk list.
        m_varRefScopes.emplace_back(nodep, m_scopep);
    }
    void visit(AstScopeName* nodep) override {
        // If there's a %m in the display text, we add a special node that will contain the name()
        const string prefix = "__DOT__"s + m_scopep->name();
        // TOP and above will be the user's name().
        // Note 'TOP.' is stripped by scopePrettyName
        // To keep correct visual order, must add before existing
        nodep->scopeAttr(prefix + nodep->scopeAttr());
        nodep->scopeEntr(prefix + nodep->scopeEntr());
        iterateChildren(nodep);
    }
    void visit(AstScope* nodep) override {
        UASSERT_OBJ(nodep->isTop(), nodep,
                    "Non-top scopes must remain detached until all instances are scoped");
    }
    //--------------------
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit ScopeVisitor(AstNetlist* nodep) { iterate(nodep); }
    ~ScopeVisitor() override = default;
};

//######################################################################
// Scope cleanup -- remove unused activates

class ScopeCleanupVisitor final : public VNVisitor {
    // STATE
    AstScope* m_scopep = nullptr;  // Current scope we are building

    // METHODS

    // VISITORS
    void visit(AstScope* nodep) override {
        // Want to ignore blocks under it
        VL_RESTORER(m_scopep);
        m_scopep = nodep;
        iterateChildren(nodep);
    }

    virtual void movedDeleteOrIterate(AstNode* nodep) {
        if (m_scopep) {
            // The new block; repair varrefs
            iterateChildren(nodep);
        } else {
            // A block that was just moved under a scope, Kill it.
            // Certain nodes can be referenced later in this pass, notably
            // an FTaskRef needs to access the FTask to find the cloned task
            VL_DO_DANGLING(pushDeletep(nodep->unlinkFrBack()), nodep);
        }
    }

    void visit(AstNodeProcedure* nodep) override { movedDeleteOrIterate(nodep); }
    void visit(AstAlias* nodep) override { movedDeleteOrIterate(nodep); }
    void visit(AstAliasScope* nodep) override { movedDeleteOrIterate(nodep); }
    void visit(AstNodeFTask* nodep) override { movedDeleteOrIterate(nodep); }
    void visit(AstCFunc* nodep) override { movedDeleteOrIterate(nodep); }

    void visit(AstVarXRef* nodep) override {
        // The crossrefs are dealt with in V3LinkDot
        nodep->varp(nullptr);
    }
    void visit(AstNodeFTaskRef* nodep) override {
        // The crossrefs are dealt with in V3LinkDot
        UINFO(9, "   Old pkg-taskref " << nodep);
        if (nodep->classOrPackagep()) {
            // Point to the clone
            UASSERT_OBJ(nodep->taskp(), nodep, "Unlinked");
            AstNodeFTask* const newp = VN_AS(nodep->taskp()->user2p(), NodeFTask);
            UASSERT_OBJ(newp, nodep, "No clone for package function");
            nodep->taskp(newp);
            UINFO(9, "   New pkg-taskref " << nodep);
        } else if (!VN_IS(nodep, MethodCall)) {
            nodep->taskp(nullptr);
            VIsCached::clearCacheTree();
            UINFO(9, "   New pkg-taskref " << nodep);
        }
        iterateChildren(nodep);
    }
    void visit(AstModportFTaskRef* nodep) override {
        // The modport persists only for JSON dump
        // The crossrefs are dealt with in V3LinkDot
        nodep->ftaskp(nullptr);
        iterateChildren(nodep);
    }

    //--------------------
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit ScopeCleanupVisitor(AstNetlist* nodep) { iterate(nodep); }
    ~ScopeCleanupVisitor() override = default;
};

//######################################################################
// Scope class functions

void V3Scope::scopeAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ":");
    {
        const ScopeVisitor visitor{nodep};
        ScopeCleanupVisitor{nodep};
    }  // Destruct before checking
    V3ConstPool::setScoped();
    V3Global::dumpCheckGlobalTree("scope", 0, dumpTreeEitherLevel() >= 3);
}
