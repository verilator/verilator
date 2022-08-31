// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Cleanup stage in V3Width
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

#ifndef VERILATOR_V3WIDTHCOMMIT_H_
#define VERILATOR_V3WIDTHCOMMIT_H_

#include "config_build.h"
#include "verilatedos.h"

#include "V3Ast.h"
#include "V3Error.h"

// clang-format off
#ifndef VERILATOR_V3WIDTH_CPP_
# error "V3WidthCommit for V3Width internal use only"
#endif
// clang-format on

//######################################################################

/// Remove all $signed, $unsigned, we're done with them.
/// This step is only called on real V3Width, not intermediate e.g. widthParams

class WidthRemoveVisitor final : public VNVisitor {
private:
    // METHODS
    void replaceWithSignedVersion(AstNode* nodep, AstNode* newp) {
        UINFO(6, " Replace " << nodep << " w/ " << newp << endl);
        nodep->replaceWith(newp);
        newp->dtypeFrom(nodep);
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }

    // VISITORS
    virtual void visit(AstSigned* nodep) override {
        VL_DO_DANGLING(replaceWithSignedVersion(nodep, nodep->lhsp()->unlinkFrBack()), nodep);
    }
    virtual void visit(AstUnsigned* nodep) override {
        VL_DO_DANGLING(replaceWithSignedVersion(nodep, nodep->lhsp()->unlinkFrBack()), nodep);
    }
    virtual void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    WidthRemoveVisitor() = default;
    virtual ~WidthRemoveVisitor() override = default;
    AstNode* mainAcceptEdit(AstNode* nodep) { return iterateSubtreeReturnEdits(nodep); }
};

//######################################################################
// Now that all widthing is complete,
// Copy all width() to widthMin().  V3Const expects this

class WidthCommitVisitor final : public VNVisitor {
    // NODE STATE
    // AstVar::user1p           -> bool, processed
    const VNUser1InUse m_inuser1;

    // STATE
    AstNodeModule* m_modp = nullptr;

public:
    // METHODS
    static AstConst* newIfConstCommitSize(AstConst* nodep) {
        if (((nodep->dtypep()->width() != nodep->num().width()) || !nodep->num().sized())
            && !nodep->num().isString()) {  // Need to force the number from unsized to sized
            V3Number num(nodep, nodep->dtypep()->width());
            num.opAssign(nodep->num());
            num.isSigned(nodep->isSigned());
            AstConst* const newp = new AstConst(nodep->fileline(), num);
            newp->dtypeFrom(nodep);
            return newp;
        } else {
            return nullptr;
        }
    }

private:
    // METHODS
    void editDType(AstNode* nodep) {
        // Edit dtypes for this node
        nodep->dtypep(editOneDType(nodep->dtypep()));
    }
    AstNodeDType* editOneDType(AstNodeDType* nodep) {
        // See if the dtype/refDType can be converted to a standard one
        // This reduces the number of dtypes in the system, and since
        // dtypep() figures into sameTree() results in better optimizations
        if (!nodep) return nullptr;
        // Recurse to handle the data type, as may change the size etc of this type
        if (!nodep->user1()) iterate(nodep);
        // Look for duplicate
        if (AstBasicDType* const bdtypep = VN_CAST(nodep, BasicDType)) {
            AstBasicDType* const newp = nodep->findInsertSameDType(bdtypep);
            if (newp != bdtypep && debug() >= 9) {
                UINFO(9, "dtype replacement ");
                nodep->dumpSmall(cout);
                cout << "  ---->  ";
                newp->dumpSmall(cout);
                cout << endl;
            }
            return newp;
        }
        return nodep;
    }
    void classEncapCheck(AstNode* nodep, AstNode* defp, AstClass* defClassp) {
        // Call on non-local class to check local/protected status and complain
        bool local = false;
        bool prot = false;
        if (const auto varp = VN_CAST(defp, Var)) {
            local = varp->isHideLocal();
            prot = varp->isHideProtected();
        } else if (const auto ftaskp = VN_CAST(defp, NodeFTask)) {
            local = ftaskp->isHideLocal();
            prot = ftaskp->isHideProtected();
        } else {
            nodep->v3fatalSrc("ref to unhandled definition type " << defp->prettyTypeName());
        }
        if (local || prot) {
            const auto refClassp = VN_CAST(m_modp, Class);
            const char* how = nullptr;
            if (local && defClassp && refClassp != defClassp) {
                how = "'local'";
            } else if (prot && defClassp && !AstClass::isClassExtendedFrom(refClassp, defClassp)) {
                how = "'protected'";
            }
            if (how) {
                UINFO(9, "refclass " << refClassp << endl);
                UINFO(9, "defclass " << defClassp << endl);
                nodep->v3warn(E_ENCAPSULATED, nodep->prettyNameQ()
                                                  << " is hidden as " << how
                                                  << " within this context (IEEE 1800-2017 8.18)\n"
                                                  << nodep->warnContextPrimary() << endl
                                                  << nodep->warnOther()
                                                  << "... Location of definition" << endl
                                                  << defp->warnContextSecondary());
            }
        }
    }

    // VISITORS
    virtual void visit(AstNodeModule* nodep) override {
        VL_RESTORER(m_modp);
        {
            m_modp = nodep;
            iterateChildren(nodep);
            editDType(nodep);
        }
    }
    virtual void visit(AstConst* nodep) override {
        UASSERT_OBJ(nodep->dtypep(), nodep, "No dtype");
        iterate(nodep->dtypep());  // Do datatype first
        if (AstConst* const newp = newIfConstCommitSize(nodep)) {
            nodep->replaceWith(newp);
            AstNode* const oldp = nodep;
            nodep = newp;
            // if (debug() > 4) oldp->dumpTree(cout, "  fixConstSize_old: ");
            // if (debug() > 4) newp->dumpTree(cout, "              _new: ");
            VL_DO_DANGLING(pushDeletep(oldp), oldp);
        }
        editDType(nodep);
    }
    virtual void visit(AstNodeDType* nodep) override {  //
        visitIterateNodeDType(nodep);
    }
    virtual void visit(AstNodeUOrStructDType* nodep) override {
        if (nodep->user1SetOnce()) return;  // Process once
        visitIterateNodeDType(nodep);
        nodep->clearCache();
    }
    virtual void visit(AstParamTypeDType* nodep) override {
        if (nodep->user1SetOnce()) return;  // Process once
        visitIterateNodeDType(nodep);
        // Move to type table as all dtype pointers must resolve there
        nodep->unlinkFrBack();  // Make non-child
        v3Global.rootp()->typeTablep()->addTypesp(nodep);
    }
    void visitIterateNodeDType(AstNodeDType* nodep) {
        // Rather than use dtypeChg which may make new nodes, we edit in place,
        // as we don't need to preserve any widthMin's, and every dtype with the same width
        // gets an identical edit.
        if (nodep->user1SetOnce()) return;  // Process once
        nodep->widthMinFromWidth();
        // Too late to any unspecified sign to be anything but unsigned
        if (nodep->numeric().isNosign()) nodep->numeric(VSigning::UNSIGNED);
        iterateChildren(nodep);
        nodep->virtRefDTypep(editOneDType(nodep->virtRefDTypep()));
        nodep->virtRefDType2p(editOneDType(nodep->virtRefDType2p()));
    }
    virtual void visit(AstNodeFTask* nodep) override {
        iterateChildren(nodep);
        editDType(nodep);
        if (nodep->classMethod() && nodep->pureVirtual() && VN_IS(m_modp, Class)
            && !VN_AS(m_modp, Class)->isVirtual()) {
            nodep->v3error(
                "Illegal to have 'pure virtual' in non-virtual class (IEEE 1800-2017 8.21)");
        }
    }
    virtual void visit(AstNodeVarRef* nodep) override {
        iterateChildren(nodep);
        editDType(nodep);
        classEncapCheck(nodep, nodep->varp(), VN_CAST(nodep->classOrPackagep(), Class));
    }
    virtual void visit(AstNodeFTaskRef* nodep) override {
        iterateChildren(nodep);
        editDType(nodep);
        classEncapCheck(nodep, nodep->taskp(), VN_CAST(nodep->classOrPackagep(), Class));
    }
    virtual void visit(AstMemberSel* nodep) override {
        iterateChildren(nodep);
        editDType(nodep);
        if (auto* const classrefp = VN_CAST(nodep->fromp()->dtypep(), ClassRefDType)) {
            classEncapCheck(nodep, nodep->varp(), classrefp->classp());
        }  // else might be struct, etc
    }
    virtual void visit(AstNodePreSel* nodep) override {  // LCOV_EXCL_LINE
        // This check could go anywhere after V3Param
        nodep->v3fatalSrc("Presels should have been removed before this point");
    }
    virtual void visit(AstNode* nodep) override {
        iterateChildren(nodep);
        editDType(nodep);
    }

public:
    // CONSTRUCTORS
    explicit WidthCommitVisitor(AstNetlist* nodep) {
        // Were changing widthMin's, so the table is now somewhat trashed
        nodep->typeTablep()->clearCache();
        iterate(nodep);
        // Don't want to repairCache, as all needed nodes have been added back in
        // a repair would prevent dead nodes from being detected
    }
    virtual ~WidthCommitVisitor() override = default;
};

//######################################################################

#endif  // Guard
