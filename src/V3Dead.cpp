// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Dead code elimination
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
// DEAD TRANSFORMATIONS:
//      Remove any unreferenced modules
//      Remove any unreferenced variables
//
// TODO: A graph would make the process of circular and interlinked
// dependencies easier to resolve.
// NOTE: If redo this, consider using maybePointedTo()/broken() ish scheme
// instead of needing as many visitors.
//
// The following nodes have package pointers and are cleaned up here:
// AstRefDType, AstEnumItemRef, AstNodeVarRef, AstNodeFTask
// These have packagep but will not exist at this stage
// AstPackageImport, AstDot, AstClassOrPackageRef
//
// Note on packagep: After the V3Scope/V3LinkDotScoped stage, package links
// are no longer used, but their presence prevents us from removing empty
// packages. As the links as no longer used after V3Scope, we remove them
// here after scoping to allow more dead node removal.
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3Dead.h"

#include "V3Ast.h"
#include "V3Global.h"

#include <map>
#include <vector>

//######################################################################
// Dead state, as a visitor of each AstNode

class DeadVisitor final : public VNVisitor {
private:
    // NODE STATE
    // Entire Netlist:
    //  AstNodeModule::user1()  -> int. Count of number of cells referencing this module.
    //  AstVar::user1()         -> int. Count of number of references
    //  AstVarScope::user1()    -> int. Count of number of references
    //  AstNodeDType::user1()   -> int. Count of number of references
    const VNUser1InUse m_inuser1;

    // TYPES
    using AssignMap = std::multimap<AstVarScope*, AstNodeAssign*>;

    // STATE
    AstNodeModule* m_modp = nullptr;  // Current module
    AstSelLoopVars* m_selloopvarsp = nullptr;  // Current loop vars
    // List of all encountered to avoid another loop through tree
    std::vector<AstVar*> m_varsp;
    std::vector<AstNode*> m_dtypesp;
    std::vector<AstVarScope*> m_vscsp;
    std::vector<AstScope*> m_scopesp;
    std::vector<AstCell*> m_cellsp;
    std::vector<AstClass*> m_classesp;

    AssignMap m_assignMap;  // List of all simple assignments for each variable
    const bool m_elimUserVars;  // Allow removal of user's vars
    const bool m_elimDTypes;  // Allow removal of DTypes
    const bool m_elimCells;  // Allow removal of Cells
    bool m_sideEffect = false;  // Side effects discovered in assign RHS

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    void checkAll(AstNode* nodep) {
        if (nodep != nodep->dtypep()) {  // NodeDTypes reference themselves
            if (AstNode* const subnodep = nodep->dtypep()) subnodep->user1Inc();
        }
        if (AstNode* const subnodep = nodep->getChildDTypep()) subnodep->user1Inc();
    }
    void checkVarRef(AstNodeVarRef* nodep) const {
        if (nodep->classOrPackagep() && m_elimCells) nodep->classOrPackagep(nullptr);
    }
    void checkDType(AstNodeDType* nodep) {
        if (!nodep->generic()  // Don't remove generic types
            && m_elimDTypes  // dtypes stick around until post-widthing
            && !VN_IS(nodep, MemberDType)  // Keep member names iff upper type exists
            && !nodep->undead()  // VoidDType or something Netlist points to
        ) {
            m_dtypesp.push_back(nodep);
        }
        if (AstNode* const subnodep = nodep->virtRefDTypep()) subnodep->user1Inc();
        if (AstNode* const subnodep = nodep->virtRefDType2p()) subnodep->user1Inc();
    }

    // VISITORS
    virtual void visit(AstNodeModule* nodep) override {
        if (m_modp) m_modp->user1Inc();  // e.g. Class under Package
        VL_RESTORER(m_modp);
        {
            m_modp = nodep;
            if (!nodep->dead()) {
                iterateChildren(nodep);
                checkAll(nodep);
                if (AstClass* const classp = VN_CAST(nodep, Class)) {
                    if (classp->extendsp()) classp->extendsp()->user1Inc();
                    if (classp->classOrPackagep()) classp->classOrPackagep()->user1Inc();
                    m_classesp.push_back(classp);
                    // TODO we don't reclaim dead classes yet - graph implementation instead?
                    classp->user1Inc();
                }
            }
        }
    }
    virtual void visit(AstCFunc* nodep) override {
        iterateChildren(nodep);
        checkAll(nodep);
        if (nodep->scopep()) nodep->scopep()->user1Inc();
    }
    virtual void visit(AstScope* nodep) override {
        iterateChildren(nodep);
        checkAll(nodep);
        if (nodep->aboveScopep()) nodep->aboveScopep()->user1Inc();
        // Class packages might have no children, but need to remain as
        // long as the class they refer to is needed
        if (VN_IS(m_modp, Class) || VN_IS(m_modp, ClassPackage)) nodep->user1Inc();
        if (!nodep->isTop() && !nodep->varsp() && !nodep->blocksp() && !nodep->finalClksp()) {
            m_scopesp.push_back(nodep);
        }
    }
    virtual void visit(AstCell* nodep) override {
        iterateChildren(nodep);
        checkAll(nodep);
        m_cellsp.push_back(nodep);
        nodep->modp()->user1Inc();
    }

    virtual void visit(AstNodeVarRef* nodep) override {
        // Note NodeAssign skips calling this in some cases
        iterateChildren(nodep);
        checkAll(nodep);
        checkVarRef(nodep);
        if (nodep->varScopep()) {
            nodep->varScopep()->user1Inc();
            nodep->varScopep()->varp()->user1Inc();
        }
        if (nodep->varp()) nodep->varp()->user1Inc();
        if (nodep->classOrPackagep()) nodep->classOrPackagep()->user1Inc();
    }
    virtual void visit(AstNodeFTaskRef* nodep) override {
        iterateChildren(nodep);
        checkAll(nodep);
        if (nodep->classOrPackagep()) {
            if (m_elimCells) {
                nodep->classOrPackagep(nullptr);
            } else {
                nodep->classOrPackagep()->user1Inc();
            }
        }
    }
    virtual void visit(AstMethodCall* nodep) override {
        iterateChildren(nodep);
        checkAll(nodep);
    }
    virtual void visit(AstRefDType* nodep) override {
        iterateChildren(nodep);
        checkDType(nodep);
        checkAll(nodep);
        UASSERT_OBJ(!(m_elimCells && nodep->typedefp()), nodep,
                    "RefDType should point to data type before typedefs removed");
        if (nodep->classOrPackagep()) {
            if (m_elimCells) {
                nodep->classOrPackagep(nullptr);
            } else {
                nodep->classOrPackagep()->user1Inc();
            }
        }
    }
    virtual void visit(AstClassRefDType* nodep) override {
        iterateChildren(nodep);
        checkDType(nodep);
        checkAll(nodep);
        if (nodep->classOrPackagep()) {
            if (m_elimCells) {
                nodep->classOrPackagep(nullptr);
            } else {
                nodep->classOrPackagep()->user1Inc();
            }
        }
        if (nodep->classp()) nodep->classp()->user1Inc();
    }
    virtual void visit(AstNodeDType* nodep) override {
        iterateChildren(nodep);
        checkDType(nodep);
        checkAll(nodep);
    }
    virtual void visit(AstEnumItemRef* nodep) override {
        iterateChildren(nodep);
        checkAll(nodep);
        if (nodep->classOrPackagep()) {
            if (m_elimCells) {
                nodep->classOrPackagep(nullptr);
            } else {
                nodep->classOrPackagep()->user1Inc();
            }
        }
        checkAll(nodep);
    }
    virtual void visit(AstMemberSel* nodep) override {
        iterateChildren(nodep);
        if (nodep->varp()) nodep->varp()->user1Inc();
        if (nodep->fromp()->dtypep()) nodep->fromp()->dtypep()->user1Inc();  // classref
        checkAll(nodep);
    }
    virtual void visit(AstModport* nodep) override {
        iterateChildren(nodep);
        if (m_elimCells) {
            if (!nodep->varsp()) {
                VL_DO_DANGLING(pushDeletep(nodep->unlinkFrBack()), nodep);
                return;
            }
        }
        checkAll(nodep);
    }
    virtual void visit(AstSelLoopVars* nodep) override {
        // Var under a SelLoopVars means we haven't called V3Width to remove them yet
        VL_RESTORER(m_selloopvarsp);
        m_selloopvarsp = nodep;
        iterateChildren(nodep);
        checkAll(nodep);
    }
    virtual void visit(AstTypedef* nodep) override {
        iterateChildren(nodep);
        if (m_elimCells && !nodep->attrPublic()) {
            VL_DO_DANGLING(pushDeletep(nodep->unlinkFrBack()), nodep);
            return;
        }
        checkAll(nodep);
        // Don't let packages with only public variables disappear
        // Normal modules may disappear, e.g. if they are parameterized then removed
        if (nodep->attrPublic() && m_modp && VN_IS(m_modp, Package)) m_modp->user1Inc();
    }
    virtual void visit(AstVarScope* nodep) override {
        iterateChildren(nodep);
        checkAll(nodep);
        if (nodep->scopep()) nodep->scopep()->user1Inc();
        if (mightElimVar(nodep->varp())) m_vscsp.push_back(nodep);
    }
    virtual void visit(AstVar* nodep) override {
        iterateChildren(nodep);
        checkAll(nodep);
        if (nodep->isSigPublic() && m_modp && VN_IS(m_modp, Package)) m_modp->user1Inc();
        if (m_selloopvarsp) nodep->user1Inc();
        if (mightElimVar(nodep)) m_varsp.push_back(nodep);
    }
    virtual void visit(AstNodeAssign* nodep) override {
        // See if simple assignments to variables may be eliminated because
        // that variable is never used.
        // Similar code in V3Life
        VL_RESTORER(m_sideEffect);
        {
            m_sideEffect = false;
            iterateAndNextNull(nodep->rhsp());
            checkAll(nodep);
            // Has to be direct assignment without any EXTRACTing.
            AstVarRef* const varrefp = VN_CAST(nodep->lhsp(), VarRef);
            if (varrefp && !m_sideEffect
                && varrefp->varScopep()) {  // For simplicity, we only remove post-scoping
                m_assignMap.emplace(varrefp->varScopep(), nodep);
                checkAll(varrefp);  // Must track reference to dtype()
                checkVarRef(varrefp);
            } else {  // Track like any other statement
                iterateAndNextNull(nodep->lhsp());
            }
        }
    }

    //-----
    virtual void visit(AstNode* nodep) override {
        if (nodep->isOutputter()) m_sideEffect = true;
        iterateChildren(nodep);
        checkAll(nodep);
    }

    // METHODS
    void deadCheckMod() {
        // Kill any unused modules
        // V3LinkCells has a graph that is capable of this too, but we need to do it
        // after we've done all the generate blocks
        for (bool retry = true; retry;) {
            retry = false;
            AstNodeModule* nextmodp;
            for (AstNodeModule* modp = v3Global.rootp()->modulesp(); modp; modp = nextmodp) {
                nextmodp = VN_AS(modp->nextp(), NodeModule);
                if (modp->dead()
                    || (modp->level() > 2 && modp->user1() == 0 && !modp->internal())) {
                    // > 2 because L1 is the wrapper, L2 is the top user module
                    UINFO(4, "  Dead module " << modp << endl);
                    // And its children may now be killable too; correct counts
                    // Recurse, as cells may not be directly under the module but in a generate
                    if (!modp->dead()) {  // If was dead didn't increment user1's
                        modp->foreach<AstCell>([](const AstCell* cellp) {  //
                            cellp->modp()->user1Inc(-1);
                        });
                    }
                    VL_DO_DANGLING(modp->unlinkFrBack()->deleteTree(), modp);
                    retry = true;
                }
            }
        }
    }
    bool mightElimVar(AstVar* nodep) const {
        if (nodep->isSigPublic()) return false;  // Can't elim publics!
        if (nodep->isIO() || nodep->isClassMember()) return false;
        if (nodep->isTemp() && !nodep->isTrace()) return true;
        return m_elimUserVars;  // Post-Trace can kill most anything
    }

    void deadCheckScope() {
        for (bool retry = true; retry;) {
            retry = false;
            for (std::vector<AstScope*>::iterator it = m_scopesp.begin(); it != m_scopesp.end();
                 ++it) {
                AstScope* const scp = *it;
                if (!scp) continue;
                if (scp->user1() == 0) {
                    UINFO(4, "  Dead AstScope " << scp << endl);
                    scp->aboveScopep()->user1Inc(-1);
                    if (scp->dtypep()) scp->dtypep()->user1Inc(-1);
                    VL_DO_DANGLING(scp->unlinkFrBack()->deleteTree(), scp);
                    *it = nullptr;
                    retry = true;
                }
            }
        }
    }

    void deadCheckCells() {
        for (AstCell* cellp : m_cellsp) {
            if (cellp->user1() == 0 && !cellp->modp()->stmtsp()) {
                cellp->modp()->user1Inc(-1);
                VL_DO_DANGLING(cellp->unlinkFrBack()->deleteTree(), cellp);
            }
        }
    }
    void deadCheckClasses() {
        for (bool retry = true; retry;) {
            retry = false;
            for (auto& itr : m_classesp) {
                if (AstClass* const nodep = itr) {  // nullptr if deleted earlier
                    if (nodep->user1() == 0) {
                        if (nodep->extendsp()) nodep->extendsp()->user1Inc(-1);
                        if (nodep->classOrPackagep()) nodep->classOrPackagep()->user1Inc(-1);
                        VL_DO_DANGLING(pushDeletep(nodep->unlinkFrBack()), nodep);
                        itr = nullptr;
                        retry = true;
                    }
                }
            }
        }
    }

    void deadCheckVar() {
        // Delete any unused varscopes
        for (AstVarScope* vscp : m_vscsp) {
            if (vscp->user1() == 0) {
                UINFO(4, "  Dead " << vscp << endl);
                const std::pair<AssignMap::iterator, AssignMap::iterator> eqrange
                    = m_assignMap.equal_range(vscp);
                for (AssignMap::iterator itr = eqrange.first; itr != eqrange.second; ++itr) {
                    AstNodeAssign* const assp = itr->second;
                    UINFO(4, "    Dead assign " << assp << endl);
                    assp->dtypep()->user1Inc(-1);
                    VL_DO_DANGLING(assp->unlinkFrBack()->deleteTree(), assp);
                }
                if (vscp->scopep()) vscp->scopep()->user1Inc(-1);
                vscp->dtypep()->user1Inc(-1);
                VL_DO_DANGLING(vscp->unlinkFrBack()->deleteTree(), vscp);
            }
        }
        for (bool retry = true; retry;) {
            retry = false;
            for (std::vector<AstVar*>::iterator it = m_varsp.begin(); it != m_varsp.end(); ++it) {
                AstVar* const varp = *it;
                if (!varp) continue;
                if (varp->user1() == 0) {
                    UINFO(4, "  Dead " << varp << endl);
                    if (varp->dtypep()) varp->dtypep()->user1Inc(-1);
                    VL_DO_DANGLING(varp->unlinkFrBack()->deleteTree(), varp);
                    *it = nullptr;
                    retry = true;
                }
            }
        }
        for (std::vector<AstNode*>::iterator it = m_dtypesp.begin(); it != m_dtypesp.end(); ++it) {
            if ((*it)->user1() == 0) {
                const AstNodeUOrStructDType* classp;
                // It's possible that there if a reference to each individual member, but
                // not to the dtype itself.  Check and don't remove the parent dtype if
                // members are still alive.
                if ((classp = VN_CAST((*it), NodeUOrStructDType))) {
                    bool cont = true;
                    for (AstMemberDType* memberp = classp->membersp(); memberp;
                         memberp = VN_AS(memberp->nextp(), MemberDType)) {
                        if (memberp->user1() != 0) {
                            cont = false;
                            break;
                        }
                    }
                    if (!cont) continue;
                }
                VL_DO_DANGLING((*it)->unlinkFrBack()->deleteTree(), *it);
            }
        }
    }

public:
    // CONSTRUCTORS
    DeadVisitor(AstNetlist* nodep, bool elimUserVars, bool elimDTypes, bool elimScopes,
                bool elimCells)
        : m_elimUserVars{elimUserVars}
        , m_elimDTypes{elimDTypes}
        , m_elimCells{elimCells} {
        // Prepare to remove some datatypes
        nodep->typeTablep()->clearCache();
        // Operate on whole netlist
        iterate(nodep);

        deadCheckVar();
        // We only eliminate scopes when in a flattened structure
        // Otherwise we have no easy way to know if a scope is used
        if (elimScopes) deadCheckScope();
        if (elimCells) deadCheckCells();
        deadCheckClasses();
        // Modules after vars, because might be vars we delete inside a mod we delete
        deadCheckMod();

        // We may have removed some datatypes, cleanup
        nodep->typeTablep()->repairCache();
    }
    virtual ~DeadVisitor() override = default;
};

//######################################################################
// Dead class functions

void V3Dead::deadifyModules(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    { DeadVisitor{nodep, false, false, false, false}; }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("deadModules", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 6);
}

void V3Dead::deadifyDTypes(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    { DeadVisitor{nodep, false, true, false, false}; }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("deadDtypes", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}

void V3Dead::deadifyDTypesScoped(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    { DeadVisitor{nodep, false, true, true, false}; }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("deadDtypesScoped", 0,
                                  v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}

void V3Dead::deadifyAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    { DeadVisitor{nodep, true, true, false, true}; }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("deadAll", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}

void V3Dead::deadifyAllScoped(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    { DeadVisitor{nodep, true, true, true, true}; }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("deadAllScoped", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}
