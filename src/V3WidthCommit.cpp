// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Commit expression widths
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2026 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
//
// Remove all $signed, $unsigned, we're done with them.
//
// This step is only called on real V3Width, not intermediate e.g. widthParams
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "config_build.h"
#include "verilatedos.h"

#include "V3WidthCommit.h"

#include "V3MemberMap.h"

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// Now that all widthing is complete,
// Copy all width() to widthMin().  V3Const expects this

class WidthCommitVisitor final : public VNVisitor {
    // NODE STATE
    // AstVar::user1p           -> bool, processed
    //  AstNodeFTask::user2()    -> int. Non-zero if ever referenced (called)
    //  AstNew::user2()          -> int. Count of number of references, minus references in
    //  functions never called
    const VNUser1InUse m_inuser1;
    const VNUser2InUse m_inuser2;

    // STATE
    AstNodeFTask* m_ftaskp = nullptr;  // Current function/task
    AstNodeModule* m_modp = nullptr;  // Current module
    std::string m_contNba;  // In continuous- or non-blocking assignment
    bool m_contReads = false;  // Check read continuous automatic variables
    bool m_dynsizedelem = false;  // Writing dynamically-sized array element, not the array itself
    VMemberMap m_memberMap;  // Member names cached for fast lookup
    bool m_taskRefWarn = true;  // Allow task reference warnings
    bool m_underSel = false;  // Under AstMemberSel or AstSel
    bool m_underAlwaysEdged = false;  // Under always with sequential SenTree
    std::vector<AstNew*> m_virtualNewsp;  // Instantiations of virtual classes
    std::vector<AstNodeFTask*> m_tasksp;  // All the tasks, we will check if they are ever called

public:
    // METHODS
    VL_DEFINE_DEBUG_FUNCTIONS;

private:
    // METHODS
    void editDType(AstNode* nodep) {
        // Called by every visitor. Edit dtypes for this node, also check for some warnings
        nodep->dtypep(editOneDType(nodep->dtypep()));
        if (m_ftaskp && m_ftaskp->verilogFunction() && m_taskRefWarn && nodep->isTimingControl())
            nodep->v3warn(
                FUNCTIMECTL,
                "Functions cannot contain time-controlling statements (IEEE 1800-2023 13.4)\n"
                    << nodep->warnContextPrimary() << "\n"
                    << nodep->warnMore() << "... Suggest make caller 'function "
                    << m_ftaskp->prettyName() << "' a task\n"
                    << m_ftaskp->warnContextSecondary());
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
                UINFO_PREFIX("dtype replacement ");
                nodep->dumpSmall(std::cout);
                std::cout << "  ---->  ";
                newp->dumpSmall(std::cout);
                std::cout << std::endl;
            }
            return newp;
        }
        return nodep;
    }
    void classEncapCheck(AstNode* nodep, AstNode* defp, AstClass* defClassp) {
        // Check local/protected status and complain
        bool local = false;
        bool prot = false;
        if (!defp) {
            // rand_mode() / constraint_mode() handled in V3Randomize
            UASSERT_OBJ(nodep->name() == "rand_mode" || nodep->name() == "constraint_mode", nodep,
                        "Only rand_mode() and constraint_mode() can have no def");
            return;
        }
        if (const auto anodep = VN_CAST(defp, Var)) {
            local = anodep->isHideLocal();
            prot = anodep->isHideProtected();
        } else if (const auto anodep = VN_CAST(defp, NodeFTask)) {
            local = anodep->isHideLocal();
            prot = anodep->isHideProtected();
        } else if (const auto anodep = VN_CAST(defp, Typedef)) {
            local = anodep->isHideLocal();
            prot = anodep->isHideProtected();
        } else {
            nodep->v3fatalSrc("ref to unhandled definition type " << defp->prettyTypeName());
        }
        if (local || prot) {
            const auto refClassp = VN_CAST(m_modp, Class);
            const char* how = nullptr;
            // Inner nested classes can access `local` or `protected` members of their outer class
            const auto nestedAccess = [refClassp](const AstClass*, const AstNode* memberp) {
                return memberp == refClassp;
            };
            if (local && defClassp
                && ((refClassp != defClassp) && !(defClassp->existsMember(nestedAccess)))) {
                how = "'local'";
            } else if (prot && defClassp && !AstClass::isClassExtendedFrom(refClassp, defClassp)
                       && !(defClassp->existsMember(nestedAccess))) {
                how = "'protected'";
            }
            if (how) {
                UINFO(9, "refclass " << refClassp);
                UINFO(9, "defclass " << defClassp);
                nodep->v3warn(ENCAPSULATED, nodep->prettyNameQ()
                                                << " is hidden as " << how
                                                << " within this context (IEEE 1800-2023 8.18)\n"
                                                << nodep->warnContextPrimary() << "\n"
                                                << nodep->warnOther()
                                                << "... Location of definition\n"
                                                << defp->warnContextSecondary());
            }
        }
    }
    void varLifetimeCheck(AstNode* nodep, AstVar* varp) {
        // Skip if we are under a member select (lhs of a dot)
        // We don't care about lifetime of anything else than rhs of a dot
        if (!m_underSel && !m_contNba.empty()) {
            std::string varType;
            const AstNodeDType* const varDtp = varp->dtypep()->skipRefp();
            if (varp->lifetime().isAutomatic() && !VN_IS(varDtp, IfaceRefDType)
                && !(varp->isFuncLocal() && varp->isIO()))
                varType = "Automatic lifetime";
            else if (varp->isClassMember() && !varp->lifetime().isStatic()
                     && !VN_IS(varDtp, IfaceRefDType))
                varType = "Class non-static";
            else if (varDtp->isDynamicallySized() && m_dynsizedelem)
                varType = "Dynamically-sized";
            if (!varType.empty()) {
                UINFO(1, "    Related var dtype: " << varDtp);
                nodep->v3error(varType
                               << " variable not allowed in " << m_contNba
                               << " assignment (IEEE 1800-2023 6.21): " << varp->prettyNameQ());
            }
        }
    }

    void deadCheckTasks() {
        for (AstNodeFTask* taskp : m_tasksp) {
            if (!taskp->user2()) {
                taskp->foreach([](AstNew* newp) { newp->user2Inc(-1); });
            }
        }
        for (AstNew* newp : m_virtualNewsp) {
            if (newp->user2() > 0)
                newp->v3error("Illegal to call 'new' using an abstract virtual class "
                              + AstNode::prettyNameQ(newp->classOrPackagep()->origName())
                              + " (IEEE 1800-2023 8.21)");
        }
    }

    // VISITORS
    void visit(AstNodeModule* nodep) override {
        VL_RESTORER(m_modp);
        m_modp = nodep;
        iterateChildren(nodep);
        editDType(nodep);
        if (AstClass* const classp = VN_CAST(nodep, Class)) {
            for (AstClassExtends* extendsp = classp->extendsp(); extendsp;
                 extendsp = extendsp->classp()->extendsp()) {
                const AstClass* const ebasep = extendsp->classp();
                if (ebasep->baseOverride().isFinal()) {
                    extendsp->v3error("Class " << nodep->prettyNameQ()
                                               << " is being extended from class marked ':final'"
                                                  " (IEEE 1800-2023 8.20)\n"
                                               << extendsp->warnContextPrimary() << "\n"
                                               << ebasep->warnOther()
                                               << "... Location of ':final' class being extended\n"
                                               << ebasep->warnContextSecondary());
                }
            }
        }
    }
    void visit(AstAlways* nodep) override {
        // As have not optimized SenTrees yet, an 'always .*' will be on first and only SenItem
        if (nodep->sentreep() && nodep->sentreep()->sensesp()
            && nodep->sentreep()->sensesp()->isComboStar()) {
            const bool noReads = nodep->forall(
                [&](const AstNodeVarRef* refp) { return !refp->access().isReadOrRW(); });
            if (noReads) {
                nodep->v3warn(ALWNEVER, "'always @*' will never execute as expression list is "
                                        "empty (no variables read)\n"
                                            << nodep->warnMore()
                                            << "... Suggest use 'always_comb'");
                VL_DO_DANGLING(pushDeletep(nodep->unlinkFrBack()), nodep);
                return;
            }
        }
        VL_RESTORER(m_underAlwaysEdged);
        m_underAlwaysEdged
            = nodep->sentreep() && nodep->sentreep()->sensesp() && nodep->sentreep()->hasEdge();
        // Iterate will delete ComboStar sentrees, so after above
        iterateChildren(nodep);
        editDType(nodep);
    }
    void visit(AstFork* nodep) override {
        VL_RESTORER(m_taskRefWarn);
        // fork..join_any is allowed to call tasks, and UVM does this
        if (!nodep->isTimingControl()) m_taskRefWarn = false;
        iterateChildren(nodep);
        editDType(nodep);
    }
    void visit(AstSenTree* nodep) override {
        if (nodep->sensesp() && nodep->sensesp()->isComboStar()) {
            UASSERT_OBJ(!nodep->sensesp()->nextp(), nodep, "Shouldn't be senitems after .*");
            // Make look like standalone always
            // (Rest of code assumed this before .* existed)
            VL_DO_DANGLING(pushDeletep(nodep->unlinkFrBack()), nodep);
            return;
        }
        iterateChildren(nodep);
        editDType(nodep);
    }
    void visit(AstAttrOf* nodep) override {
        switch (nodep->attrType()) {
        case VAttrType::FUNC_ARG_PROTO:  // FALLTHRU
        case VAttrType::FUNC_RETURN_PROTO:
            VL_DO_DANGLING(pushDeletep(nodep->unlinkFrBack()), nodep);
            return;
        default:;
        }
        iterateChildren(nodep);
        editDType(nodep);
    }
    void visit(AstClassExtends* nodep) override {
        if (nodep->user1SetOnce()) return;  // Process once
        // Extend arguments were converted to super.new arguments in V3LinkDot
        if (nodep->argsp()) pushDeletep(nodep->argsp()->unlinkFrBackWithNext());
        iterateChildren(nodep);
    }
    void visit(AstConst* nodep) override {
        if (nodep->user1SetOnce()) return;  // Process once
        UASSERT_OBJ(nodep->dtypep(), nodep, "No dtype");
        iterate(nodep->dtypep());  // Do datatype first
        if (AstConst* const newp = V3WidthCommit::newIfConstCommitSize(nodep)) {
            nodep->replaceWith(newp);
            AstNode* const oldp = nodep;
            nodep = newp;
            // UINFOTREE(5, oldp, "", "fixConstSize_old");
            // UINFOTREE(5, newp, "", "_new");
            VL_DO_DANGLING(pushDeletep(oldp), oldp);
        }
        editDType(nodep);
    }
    void visit(AstCastWrap* nodep) override {
        iterateChildren(nodep);
        editDType(nodep);
        UINFO(6, " Replace " << nodep << " w/ " << nodep->lhsp());
        nodep->replaceWith(nodep->lhsp()->unlinkFrBack());
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }
    void visit(AstConstraint* nodep) override {
        iterateChildren(nodep);
        editDType(nodep);
        {
            const AstClass* const classp = VN_CAST(m_modp, Class);
            if (nodep->isKwdPure()
                && (!classp || (!classp->isInterfaceClass() && !classp->isVirtual()))) {
                nodep->v3error("Illegal to have 'pure constraint' in non-abstract class"
                               " (IEEE 1800-2023 18.5.2)");
            }
        }
    }
    void visit(AstNodeDType* nodep) override {
        // Note some specific dtypes have unique visitors
        visitIterateNodeDType(nodep);
    }
    void visit(AstNodeUOrStructDType* nodep) override {
        if (nodep->user1SetOnce()) return;  // Process once
        visitIterateNodeDType(nodep);
    }
    void visit(AstEnumDType* nodep) override {
        nodep->tableMap().clear();  // Only needed up through V3Width process
        visitIterateNodeDType(nodep);
    }
    void visit(AstParamTypeDType* nodep) override {
        if (nodep->user1SetOnce()) return;  // Process once
        visitIterateNodeDType(nodep);
        // Move to type table as all dtype pointers must resolve there
        nodep->unlinkFrBack();  // Make non-child
        v3Global.rootp()->typeTablep()->addTypesp(nodep);
    }
    void visit(AstRefDType* nodep) override {
        visitIterateNodeDType(nodep);
        if (!nodep->typedefp()) return;  // Already checked and cleared
        classEncapCheck(nodep, nodep->typedefp(), VN_CAST(nodep->classOrPackagep(), Class));
        nodep->typedefp(nullptr);  // No longer needed
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
    void visit(AstNodeFTask* nodep) override {
        if (!nodep->taskPublic() && !nodep->dpiExport() && !nodep->dpiImport())
            m_tasksp.push_back(nodep);
        VL_RESTORER(m_ftaskp);
        m_ftaskp = nodep;
        iterateChildren(nodep);
        editDType(nodep);
        {
            const AstClass* const classp = VN_CAST(m_modp, Class);
            if (nodep->classMethod() && nodep->pureVirtual() && classp
                && !classp->isInterfaceClass() && !classp->isVirtual()) {
                nodep->v3error(
                    "Illegal to have 'pure virtual' in non-virtual class (IEEE 1800-2023 8.21)");
            }
        }
        bool extended = false;
        if (const AstClass* const classp = VN_CAST(m_modp, Class)) {
            for (AstClassExtends* extendsp = classp->extendsp(); extendsp;
                 extendsp = extendsp->classp()->extendsp()) {
                const AstClass* const eclassp = extendsp->classp();
                if (AstNodeFTask* const fbasep
                    = VN_CAST(m_memberMap.findMember(eclassp, nodep->name()), NodeFTask)) {
                    if (fbasep != nodep) {
                        extended = true;
                        if (nodep->baseOverride().isInitial()) {
                            nodep->v3error("Member "
                                           << nodep->prettyNameQ()
                                           << " is marked ':initial' but is being extended"
                                              " (IEEE 1800-2023 8.20)\n"
                                           << nodep->warnContextPrimary() << "\n"
                                           << fbasep->warnOther()
                                           << "... Location of declaration being extended\n"
                                           << fbasep->warnContextSecondary());
                        }
                        if (fbasep->baseOverride().isFinal()) {
                            nodep->v3error(
                                "Member "
                                << nodep->prettyNameQ()
                                << " is being extended from member marked ':final'"
                                   " (IEEE 1800-2023 8.20)\n"
                                << nodep->warnContextPrimary() << "\n"
                                << fbasep->warnOther()
                                << "... Location of ':final' declaration being extended\n"
                                << fbasep->warnContextSecondary());
                        }
                    }
                }
            }
        }
        if (!extended && nodep->baseOverride().isExtends()) {
            nodep->v3error("Member " << nodep->prettyNameQ()
                                     << " marked ':extends' but no base class function is"
                                        " being extend (IEEE 1800-2023 8.20)");
        }
    }
    void visit(AstNodeVarRef* nodep) override {
        iterateChildren(nodep);
        editDType(nodep);
        classEncapCheck(nodep, nodep->varp(), VN_CAST(nodep->classOrPackagep(), Class));
        if (nodep->access().isWriteOrRW() || m_contReads) varLifetimeCheck(nodep, nodep->varp());
        if (VN_IS(nodep, VarRef))
            nodep->name("");  // Clear to save memory; nodep->name() will work via nodep->varp()
    }
    void visit(AstAssign* nodep) override {
        iterateChildren(nodep);
        editDType(nodep);
        // Lint
        if (m_underAlwaysEdged) {
            const bool ignore = nodep->lhsp()->forall([&](const AstVarRef* refp) {
                // Ignore reads (e.g.: index expressions)
                if (refp->access().isReadOnly()) return true;
                const AstVar* const varp = refp->varp();
                // Ignore ...
                return varp->isUsedLoopIdx()  // ... loop indices
                       || varp->isTemp()  // ... temporaries
                       || varp->fileline()->warnIsOff(V3ErrorCode::BLKSEQ);  // ... user said so
            });
            if (!ignore) {
                nodep->v3warn(BLKSEQ,
                              "Blocking assignment '=' in sequential logic process\n"
                                  << nodep->warnMore()  //
                                  << "... Suggest using delayed assignment '<='");
            }
        }
    }
    void visit(AstAssignCont* nodep) override {
        iterateAndNextNull(nodep->timingControlp());
        {
            VL_RESTORER(m_contNba);
            VL_RESTORER(m_contReads);
            m_contNba = "continuous";
            m_contReads = true;
            iterateAndNextNull(nodep->lhsp());
            iterateAndNextNull(nodep->rhsp());
        }
        editDType(nodep);
        AstNode* const controlp
            = nodep->timingControlp() ? nodep->timingControlp()->unlinkFrBack() : nullptr;
        nodep->replaceWith(new AstAssign{nodep->fileline(), nodep->lhsp()->unlinkFrBack(),
                                         nodep->rhsp()->unlinkFrBack(), controlp});
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }
    void visit(AstAssignDly* nodep) override {
        iterateAndNextNull(nodep->timingControlp());
        iterateAndNextNull(nodep->rhsp());
        {
            VL_RESTORER(m_contNba);
            VL_RESTORER(m_contReads);
            m_contNba = "nonblocking";
            m_contReads = false;
            iterateAndNextNull(nodep->lhsp());
        }
        editDType(nodep);
    }
    void visit(AstAssignW* nodep) override {
        iterateAndNextNull(nodep->timingControlp());
        iterateAndNextNull(nodep->rhsp());
        {
            VL_RESTORER(m_contNba);
            VL_RESTORER(m_contReads);
            m_contNba = "continuous";
            m_contReads = false;
            iterateAndNextNull(nodep->lhsp());
        }
        editDType(nodep);
    }
    void visit(AstNodeFTaskRef* nodep) override {
        iterateChildren(nodep);
        editDType(nodep);
        classEncapCheck(nodep, nodep->taskp(), VN_CAST(nodep->classOrPackagep(), Class));
        if (nodep->taskp() && nodep->taskp()->verilogTask() && m_ftaskp
            && m_ftaskp->verilogFunction() && m_taskRefWarn) {
            nodep->v3warn(FUNCTIMECTL,
                          "Functions cannot invoke tasks (IEEE 1800-2023 13.4)\n"
                              << nodep->warnContextPrimary() << "\n"
                              << nodep->warnMore() << "... Suggest make caller 'function "
                              << m_ftaskp->prettyName() << "' a task\n"
                              << m_ftaskp->warnContextSecondary() << "\n"
                              << nodep->warnMore() << "... Or, suggest make called 'task "
                              << nodep->taskp()->prettyName() << "' a function void\n"
                              << nodep->taskp()->warnContextSecondary());
        }
        if (nodep->taskp()) nodep->taskp()->user2(1);
        if (AstNew* const newp = VN_CAST(nodep, New)) {
            if (!VN_IS(newp->backp(), Assign)) return;
            if (AstClass* const classp = VN_CAST(newp->classOrPackagep(), Class)) {
                if (classp->isVirtual() || classp->isInterfaceClass()) {
                    m_virtualNewsp.push_back(newp);
                    newp->user2Inc();
                }
            }
        }
    }
    void visit(AstMemberSel* nodep) override {
        {
            VL_RESTORER(m_underSel);
            m_underSel = true;
            iterateChildren(nodep);
        }
        editDType(nodep);
        if (AstClassRefDType* const classrefp = VN_CAST(nodep->fromp()->dtypep(), ClassRefDType)) {
            classEncapCheck(nodep, nodep->varp(), classrefp->classp());
        }  // else might be struct, etc
        varLifetimeCheck(nodep, nodep->varp());
    }
    void visit(AstVar* nodep) override {
        iterateChildren(nodep);
        editDType(nodep);
        if (nodep->isFuncLocal() && nodep->direction() == VDirection::INPUT && nodep->valuep()) {
            // It's the default value of optional argument.
            // Such values are added to function calls in V3Width so can be removed now
            pushDeletep(nodep->valuep()->unlinkFrBack());
        }
    }
    void visit(AstNodePreSel* nodep) override {  // LCOV_EXCL_LINE
        // This check could go anywhere after V3Param
        nodep->v3fatalSrc("Presels should have been removed before this point");
    }
    void visit(AstCMethodHard* nodep) override {
        VL_RESTORER(m_dynsizedelem);
        if (nodep->method() == VCMethod::ARRAY_AT || nodep->method() == VCMethod::ARRAY_AT_WRITE
            || nodep->method() == VCMethod::DYN_AT_WRITE_APPEND)
            m_dynsizedelem = true;
        iterateChildren(nodep);
        editDType(nodep);
    }
    void visit(AstAssocSel* nodep) override {
        VL_RESTORER(m_dynsizedelem);
        m_dynsizedelem = true;
        iterateChildren(nodep);
        editDType(nodep);
    }
    void visit(AstSel* nodep) override {
        {
            VL_RESTORER(m_underSel);
            m_underSel = true;
            iterateChildren(nodep);
        }
        editDType(nodep);
    }
    void visit(AstNode* nodep) override {
        iterateChildren(nodep);
        editDType(nodep);
    }

public:
    // CONSTRUCTORS
    explicit WidthCommitVisitor(AstNetlist* nodep) {
        // Were changing widthMin's, so the table is now somewhat trashed
        nodep->typeTablep()->clearCache();
        iterate(nodep);
        deadCheckTasks();
        // Don't want to AstTypeTable::repairCache, as all needed nodes
        // have been added back in; a repair would prevent dead nodes from
        // being detected
    }
    ~WidthCommitVisitor() override = default;
};

//######################################################################
// V3WidthCommit class functions

void V3WidthCommit::widthCommit(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ":");
    { WidthCommitVisitor{nodep}; }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("widthcommit", 0, dumpTreeEitherLevel() >= 6);
}
