// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Generate randomization procedures
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2024 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
// V3Randomize's Transformations:
//
// Each randomize() method call:
//      Mark class of object on which randomize() is called
// Mark all classes that inherit from previously marked classed
// Mark all classes whose instances are randomized member variables of marked classes
// Each marked class:
//      * define a virtual randomize() method that randomizes its random variables
// Each call to randomize():
//      * define __Vrandwith### functions for randomize() calls with inline constraints and
//        put then into randomized classes
//      * replace calls to randomize() that use inline constraints with calls to __Vrandwith###
//        functions
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "verilatedos.h"

#include "V3Randomize.h"

#include "V3Ast.h"
#include "V3Error.h"
#include "V3FileLine.h"
#include "V3Global.h"
#include "V3MemberMap.h"
#include "V3UniqueNames.h"

#include <queue>
#include <tuple>
#include <utility>

VL_DEFINE_DEBUG_FUNCTIONS;

// ######################################################################
// Establishes the target of a rand_mode() call

struct RandModeTarget final {
    // MEMBERS
    AstVar* const receiverp;  // Variable that is the target of the rand_mode() call
    AstNodeExpr* const fromp;  // Expression from which the rand_mode() call originates
    AstClass* const classp;  // Class in which rand_mode should be set

    // METHODS
    static RandModeTarget get(AstNodeExpr* fromp, AstNodeModule* modp) {
        if (!fromp) return {nullptr, nullptr, VN_AS(modp, Class)};
        if (AstCMethodHard* const methodHardp = VN_CAST(fromp, CMethodHard)) {
            return RandModeTarget::get(methodHardp->fromp(), modp);
        }
        AstVar* receiverp = nullptr;
        if (AstVarRef* const varrefp = VN_CAST(fromp, VarRef)) {
            receiverp = varrefp->varp();
        } else if (AstMemberSel* const memberSelp = VN_CAST(fromp, MemberSel)) {
            receiverp = memberSelp->varp();
        }
        UASSERT_OBJ(receiverp, fromp, "Unknown rand_mode() receiver");
        if (receiverp->isRand()) {
            if (AstMemberSel* const memberselp = VN_CAST(fromp, MemberSel)) {
                return {receiverp, memberselp->fromp(),
                        VN_AS(memberselp->fromp()->dtypep()->skipRefp(), ClassRefDType)->classp()};
            }
        } else {
            AstClassRefDType* const classRefDtp
                = VN_CAST(receiverp->dtypep()->skipRefp(), ClassRefDType);
            if (classRefDtp) return {receiverp, fromp, classRefDtp->classp()};
        }
        return {receiverp, nullptr, VN_AS(modp, Class)};
    }
};

// ######################################################################
// Stores info about a variable's rand_mode state

union VarRandMode final {
    // MEMBERS
    struct {
        bool usesRandMode : 1;  // True if variable uses rand_mode
        uint32_t index : 31;  // Index of var in rand_mode vector
    };
    int asInt;  // Representation as int to be stored in nodep->user*
};

//######################################################################
// Visitor that marks classes needing a randomize() method

class RandomizeMarkVisitor final : public VNVisitor {
    // NODE STATE
    // Cleared on Netlist
    //  AstClass::user1()       -> bool.  Set true to indicate needs randomize processing
    //  AstNodeExpr::user1()    -> bool.  Set true to indicate constraint expression depending on a
    //                                    randomized variable
    //  AstVar::user1()         -> bool.  Set true to indicate needs rand_mode
    //  AstVar::user2p()        -> AstNodeModule*. Pointer to containing module
    const VNUser1InUse m_inuser1;
    const VNUser2InUse m_inuser2;

    using DerivedSet = std::unordered_set<AstClass*>;
    using BaseToDerivedMap = std::unordered_map<const AstClass*, DerivedSet>;

    BaseToDerivedMap m_baseToDerivedMap;  // Mapping from base classes to classes that extend them
    AstClass* m_classp = nullptr;  // Current class
    AstNode* m_constraintExprp = nullptr;  // Current constraint expression
    AstNodeModule* m_modp;  // Current module
    AstNodeStmt* m_stmtp = nullptr;  // Current statement
    std::set<AstNodeVarRef*> m_staticRefs;  // References to static variables under `with` clauses

    // METHODS
    void markMembers(const AstClass* nodep) {
        for (const AstClass* classp = nodep; classp;
             classp = classp->extendsp() ? classp->extendsp()->classp() : nullptr) {
            for (const AstNode* memberp = classp->stmtsp(); memberp; memberp = memberp->nextp()) {
                // If member is rand and of class type, mark its class
                if (VN_IS(memberp, Var) && VN_AS(memberp, Var)->isRand()) {
                    if (const AstClassRefDType* const classRefp
                        = VN_CAST(memberp->dtypep()->skipRefp(), ClassRefDType)) {
                        AstClass* const rclassp = classRefp->classp();
                        if (!rclassp->user1()) {
                            rclassp->user1(true);
                            markMembers(rclassp);
                            markDerived(rclassp);
                        }
                    }
                }
            }
        }
    }
    void markDerived(const AstClass* nodep) {
        const auto it = m_baseToDerivedMap.find(nodep);
        if (it != m_baseToDerivedMap.end()) {
            for (auto* classp : it->second) {
                if (!classp->user1()) {
                    classp->user1(true);
                    markMembers(classp);
                    markDerived(classp);
                }
            }
        }
    }
    void markAllDerived() {
        for (const auto& p : m_baseToDerivedMap) {
            if (p.first->user1()) markDerived(p.first);
        }
    }
    void setPackageRefs() {
        for (AstNodeVarRef* staticRefp : m_staticRefs) {
            UINFO(9, "Updated classOrPackage ref for " << staticRefp->name() << endl);
            staticRefp->classOrPackagep(VN_AS(staticRefp->varp()->user2p(), NodeModule));
        }
    }

    // VISITORS
    void visit(AstClass* nodep) override {
        VL_RESTORER(m_classp);
        VL_RESTORER(m_modp);
        m_modp = m_classp = nodep;
        iterateChildrenConst(nodep);
        if (nodep->extendsp()) {
            // Save pointer to derived class
            const AstClass* const basep = nodep->extendsp()->classp();
            m_baseToDerivedMap[basep].insert(nodep);
        }
    }
    void visit(AstNodeStmt* nodep) override {
        VL_RESTORER(m_stmtp);
        m_stmtp = nodep;
        iterateChildren(nodep);
        if (!nodep->backp()) VL_DO_DANGLING(nodep->deleteTree(), nodep);
    }
    void visit(AstNodeFTaskRef* nodep) override {
        iterateChildrenConst(nodep);
        if (nodep->name() == "rand_mode") {
            AstMethodCall* const methodCallp = VN_CAST(nodep, MethodCall);
            AstNodeExpr* const fromp = methodCallp ? methodCallp->fromp() : nullptr;
            bool valid = true;
            if (VN_IS(fromp, ArraySel)) {
                nodep->v3warn(E_UNSUPPORTED,
                              "Unsupported: 'rand_mode()' on unpacked array element");
                valid = false;
            } else if (VN_IS(fromp, Sel)) {
                nodep->v3error("Cannot call 'rand_mode()' on packed array element");
                valid = false;
            } else if (AstCMethodHard* const methodHardp = VN_CAST(fromp, CMethodHard)) {
                if (methodHardp->name() == "at" && VN_IS(fromp, CMethodHard)) {
                    nodep->v3warn(E_UNSUPPORTED,
                                  "Unsupported: 'rand_mode()' on dynamic array element");
                    valid = false;
                } else {
                    methodHardp->v3fatal("Unknown rand_mode() receiver");
                }
            }
            if (!nodep->pinsp() && VN_IS(nodep->backp(), StmtExpr)) {
                nodep->v3warn(
                    IGNOREDRETURN,
                    "Ignoring return value of non-void function (IEEE 1800-2023 13.4.1)");
                valid = false;
            }
            if (valid) {
                const RandModeTarget randModeTarget = RandModeTarget::get(fromp, m_classp);
                if ((!randModeTarget.receiverp || !randModeTarget.receiverp->isRand())
                    && !nodep->pinsp()) {
                    nodep->v3error(
                        "Cannot call 'rand_mode()' as a function on non-random variable");
                    valid = false;
                } else if (!randModeTarget.classp) {
                    nodep->v3error("Cannot call 'rand_mode()' on non-random, non-class variable");
                    valid = false;
                } else if (nodep->pinsp() && !VN_IS(nodep->backp(), StmtExpr)) {
                    nodep->v3error("'rand_mode()' with arguments cannot be called as a function");
                    valid = false;
                } else if (randModeTarget.receiverp && randModeTarget.receiverp->isRand()) {
                    // Called on a rand member variable
                    VarRandMode randMode = {};
                    randMode.usesRandMode = true;
                    randModeTarget.receiverp->user1(randMode.asInt);
                } else {
                    // Called on 'this' or a non-rand class instance
                    randModeTarget.classp->foreachMember([&](AstClass*, AstVar* varp) {
                        if (!varp->isRand()) return;
                        VarRandMode randMode = {};
                        randMode.usesRandMode = true;
                        varp->user1(randMode.asInt);
                    });
                }
            }
            if (!valid) {
                if (!nodep->pinsp() && !VN_IS(nodep->backp(), StmtExpr)) {
                    nodep->replaceWith(new AstConst{nodep->fileline(), 0});
                    VL_DO_DANGLING(nodep->deleteTree(), nodep);
                } else {
                    m_stmtp->unlinkFrBack();
                }
            }
            return;
        }
        if (nodep->name() != "randomize") return;
        AstClass* classp = m_classp;
        if (const AstMethodCall* const methodCallp = VN_CAST(nodep, MethodCall)) {
            if (const AstClassRefDType* const classRefp
                = VN_CAST(methodCallp->fromp()->dtypep()->skipRefp(), ClassRefDType)) {
                classp = classRefp->classp();
            }
        }
        if (classp) {
            classp->user1(true);
            markMembers(classp);
        }
    }
    void visit(AstConstraintExpr* nodep) override {
        VL_RESTORER(m_constraintExprp);
        m_constraintExprp = nodep;
        iterateChildrenConst(nodep);
    }
    void visit(AstConstraintIf* nodep) override {
        {
            VL_RESTORER(m_constraintExprp);
            m_constraintExprp = nodep;
            iterateConst(nodep->condp());
        }
        iterateAndNextConstNull(nodep->thensp());
        iterateAndNextConstNull(nodep->elsesp());
    }
    void visit(AstNodeVarRef* nodep) override {
        if (!m_constraintExprp) return;

        if (nodep->varp()->lifetime().isStatic()) m_staticRefs.emplace(nodep);

        if (!nodep->varp()->isRand()) return;
        for (AstNode* backp = nodep; backp != m_constraintExprp && !backp->user1();
             backp = backp->backp())
            backp->user1(true);
    }
    void visit(AstMemberSel* nodep) override {
        if (!m_constraintExprp) return;
        if (VN_IS(nodep->fromp(), LambdaArgRef)) {
            if (!nodep->varp()->isRand()) return;
            for (AstNode* backp = nodep; backp != m_constraintExprp && !backp->user1();
                 backp = backp->backp())
                backp->user1(true);
        }
    }
    void visit(AstNodeModule* nodep) override {
        VL_RESTORER(m_modp);
        m_modp = nodep;
        iterateChildrenConst(nodep);
    }
    void visit(AstVar* nodep) override {
        nodep->user2p(m_modp);
        iterateChildrenConst(nodep);
    }

    void visit(AstNode* nodep) override { iterateChildrenConst(nodep); }

public:
    // CONSTRUCTORS
    explicit RandomizeMarkVisitor(AstNode* nodep) {
        iterateConst(nodep);
        markAllDerived();
        setPackageRefs();
    }
    ~RandomizeMarkVisitor() override = default;
};

//######################################################################
// Visitor that turns constraints into template strings for solvers

class ConstraintExprVisitor final : public VNVisitor {
    // NODE STATE
    // AstVar::user3() -> bool. Handled in constraints
    //  AstNodeExpr::user1()    -> bool. Depending on a randomized variable
    // VNuser3InUse m_inuser3; (Allocated for use in RandomizeVisitor)

    AstNodeFTask* const m_inlineInitTaskp;  // Method to add write_var calls to
                                            // (may be null, then new() is used)
    AstVar* const m_genp;  // VlRandomizer variable of the class
    AstVar* m_randModeVarp;  // Relevant randmode state variable
    bool m_wantSingle = false;  // Whether to merge constraint expressions with LOGAND
    VMemberMap& m_memberMap;  // Member names cached for fast lookup

    AstSFormatF* getConstFormat(AstNodeExpr* nodep) {
        return new AstSFormatF{nodep->fileline(), (nodep->width() & 3) ? "#b%b" : "#x%x", false,
                               nodep};
    }
    bool editFormat(AstNodeExpr* nodep) {
        if (nodep->user1()) return false;
        // Replace computable expression with SMT constant
        VNRelinker handle;
        nodep->unlinkFrBack(&handle);
        handle.relink(getConstFormat(nodep));
        return true;
    }
    void editSMT(AstNodeExpr* nodep, AstNodeExpr* lhsp = nullptr, AstNodeExpr* rhsp = nullptr,
                 AstNodeExpr* thsp = nullptr) {
        // Replace incomputable (result-dependent) expression with SMT expression
        std::string smtExpr = nodep->emitSMT();  // Might need child width (AstExtend)
        UASSERT_OBJ(smtExpr != "", nodep,
                    "Node needs randomization constraint, but no emitSMT: " << nodep);

        if (lhsp) lhsp = VN_AS(iterateSubtreeReturnEdits(lhsp->unlinkFrBack()), NodeExpr);
        if (rhsp) rhsp = VN_AS(iterateSubtreeReturnEdits(rhsp->unlinkFrBack()), NodeExpr);
        if (thsp) thsp = VN_AS(iterateSubtreeReturnEdits(thsp->unlinkFrBack()), NodeExpr);

        AstNodeExpr* argsp = nullptr;
        for (string::iterator pos = smtExpr.begin(); pos != smtExpr.end(); ++pos) {
            if (pos[0] == '%') {
                ++pos;
                switch (pos[0]) {
                case '%': break;
                case 'l':
                    pos[0] = '@';
                    UASSERT_OBJ(lhsp, nodep, "emitSMT() references undef node");
                    argsp = AstNode::addNext(argsp, lhsp);
                    lhsp = nullptr;
                    break;
                case 'r':
                    pos[0] = '@';
                    UASSERT_OBJ(rhsp, nodep, "emitSMT() references undef node");
                    argsp = AstNode::addNext(argsp, rhsp);
                    rhsp = nullptr;
                    break;
                case 't':
                    pos[0] = '@';
                    UASSERT_OBJ(thsp, nodep, "emitSMT() references undef node");
                    argsp = AstNode::addNext(argsp, thsp);
                    thsp = nullptr;
                    break;
                default: nodep->v3fatalSrc("Unknown emitSMT format code: %" << pos[0]); break;
                }
            }
        }
        UASSERT_OBJ(!lhsp, nodep, "Missing emitSMT %l for " << lhsp);
        UASSERT_OBJ(!rhsp, nodep, "Missing emitSMT %r for " << rhsp);
        UASSERT_OBJ(!thsp, nodep, "Missing emitSMT %t for " << thsp);
        AstSFormatF* const newp = new AstSFormatF{nodep->fileline(), smtExpr, false, argsp};
        nodep->replaceWith(newp);
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }

    AstNodeExpr* editSingle(FileLine* fl, AstNode* itemsp) {
        if (!itemsp) return nullptr;

        VL_RESTORER(m_wantSingle);
        m_wantSingle = true;

        {
            AstBegin* const tempp
                = new AstBegin{fl, "[EditWrapper]", itemsp->unlinkFrBackWithNext()};
            VL_DO_DANGLING(iterateAndNextNull(tempp->stmtsp()), itemsp);
            itemsp = tempp->stmtsp();
            if (itemsp) itemsp->unlinkFrBackWithNext();
            VL_DO_DANGLING(tempp->deleteTree(), tempp);
        }
        if (!itemsp) return nullptr;

        AstNodeExpr* exprsp = VN_CAST(itemsp, NodeExpr);
        UASSERT_OBJ(exprsp, itemsp, "Single not expression?");

        if (!exprsp->nextp()) return exprsp;

        std::ostringstream fmt;
        fmt << "(and";
        for (AstNode* itemp = exprsp; itemp; itemp = itemp->nextp()) fmt << " %@";
        fmt << ')';
        return new AstSFormatF{fl, fmt.str(), false, exprsp};
    }

    // VISITORS
    void visit(AstNodeVarRef* nodep) override {
        AstVar* const varp = nodep->varp();
        AstNodeModule* const classOrPackagep = nodep->classOrPackagep();
        const VarRandMode randMode = {.asInt = varp->user1()};
        if (!randMode.usesRandMode && editFormat(nodep)) return;

        // In SMT just variable name, but we also ensure write_var for the variable
        const std::string smtName = nodep->name();  // Can be anything unique
        VNRelinker relinker;
        nodep->unlinkFrBack(&relinker);
        AstNodeExpr* exprp = new AstSFormatF{nodep->fileline(), smtName, false, nullptr};
        if (randMode.usesRandMode) {
            AstNodeExpr* constFormatp = getConstFormat(nodep);
            AstCMethodHard* const atp = new AstCMethodHard{
                nodep->fileline(),
                new AstVarRef{varp->fileline(), VN_AS(m_randModeVarp->user2p(), NodeModule),
                              m_randModeVarp, VAccess::READ},
                "at", new AstConst{nodep->fileline(), randMode.index}};
            atp->dtypeSetUInt32();
            exprp = new AstCond{varp->fileline(), atp, exprp, constFormatp};
        } else {
            VL_DO_DANGLING(pushDeletep(nodep), nodep);
        }
        relinker.relink(exprp);

        if (!varp->user3()) {
            AstCMethodHard* const methodp = new AstCMethodHard{
                varp->fileline(),
                new AstVarRef{varp->fileline(), VN_AS(m_genp->user2p(), NodeModule), m_genp,
                              VAccess::READWRITE},
                "write_var"};
            methodp->dtypeSetVoid();
            AstClass* const classp = VN_AS(varp->user2p(), Class);
            AstVarRef* const varRefp
                = new AstVarRef{varp->fileline(), classp, varp, VAccess::WRITE};
            varRefp->classOrPackagep(classOrPackagep);
            methodp->addPinsp(varRefp);
            methodp->addPinsp(new AstConst{varp->dtypep()->fileline(), AstConst::Unsized64{},
                                           (size_t)varp->width()});
            AstNodeExpr* const varnamep
                = new AstCExpr{varp->fileline(), "\"" + smtName + "\"", varp->width()};
            varnamep->dtypep(varp->dtypep());
            methodp->addPinsp(varnamep);
            if (randMode.usesRandMode) {
                methodp->addPinsp(
                    new AstConst{varp->fileline(), AstConst::Unsized64{}, randMode.index});
            }
            AstNodeFTask* initTaskp = m_inlineInitTaskp;
            if (!initTaskp) {
                varp->user3(true);  // Mark as set up in new()
                initTaskp = VN_AS(m_memberMap.findMember(classp, "new"), NodeFTask);
                UASSERT_OBJ(initTaskp, classp, "No new() in class");
            }
            initTaskp->addStmtsp(methodp->makeStmt());
        }
    }
    void visit(AstNodeBiop* nodep) override {
        if (editFormat(nodep)) return;
        editSMT(nodep, nodep->lhsp(), nodep->rhsp());
    }
    void visit(AstNodeUniop* nodep) override {
        if (editFormat(nodep)) return;
        editSMT(nodep, nodep->lhsp());
    }
    void visit(AstNodeTriop* nodep) override {
        if (editFormat(nodep)) return;
        editSMT(nodep, nodep->lhsp(), nodep->rhsp(), nodep->thsp());
    }
    void visit(AstNodeCond* nodep) override {
        if (editFormat(nodep)) return;
        if (!nodep->condp()->user1()) {
            // Do not burden the solver if cond computable: (cond ? "then" : "else")
            iterate(nodep->thenp());
            iterate(nodep->elsep());
            return;
        }
        // Fall back to "(ite cond then else)"
        visit(static_cast<AstNodeTriop*>(nodep));
    }
    void visit(AstDist* nodep) override {
        nodep->v3warn(CONSTRAINTIGN, "Constraint expression ignored (unsupported)");
        nodep->replaceWith(new AstSFormatF{nodep->fileline(), "true", false, nullptr});
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
    }
    void visit(AstReplicate* nodep) override {
        // Biop, but RHS is harmful
        if (editFormat(nodep)) return;
        editSMT(nodep, nodep->srcp());
    }
    void visit(AstSFormatF* nodep) override {}
    void visit(AstStmtExpr* nodep) override {}
    void visit(AstConstraintIf* nodep) override {
        AstNodeExpr* newp = nullptr;
        FileLine* const fl = nodep->fileline();
        AstNodeExpr* const thenp = editSingle(fl, nodep->thensp());
        AstNodeExpr* const elsep = editSingle(fl, nodep->elsesp());
        if (thenp && elsep) {
            newp = new AstCond{fl, nodep->condp()->unlinkFrBack(), thenp, elsep};
        } else if (thenp) {
            newp = new AstLogIf{fl, nodep->condp()->unlinkFrBack(), thenp};
        } else if (elsep) {
            newp = new AstLogIf{fl, new AstNot{fl, nodep->condp()->unlinkFrBack()}, elsep};
        }
        if (newp) {
            newp->user1(true);  // Assume result-dependent
            nodep->replaceWith(new AstConstraintExpr{fl, newp});
        } else {
            nodep->unlinkFrBack();
        }
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
    }
    void visit(AstConstraintForeach* nodep) override {
        nodep->v3warn(CONSTRAINTIGN, "Constraint expression ignored (unsupported)");
        VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
    }
    void visit(AstConstraintBefore* nodep) override {
        nodep->v3warn(CONSTRAINTIGN, "Constraint expression ignored (unsupported)");
        VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
    }
    void visit(AstConstraintUnique* nodep) override {
        nodep->v3warn(CONSTRAINTIGN, "Constraint expression ignored (unsupported)");
        VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
    }
    void visit(AstConstraintExpr* nodep) override {
        iterateChildren(nodep);
        if (m_wantSingle) {
            nodep->replaceWith(nodep->exprp()->unlinkFrBack());
            VL_DO_DANGLING(nodep->deleteTree(), nodep);
            return;
        }
        // Only hard constraints are currently supported
        AstCMethodHard* const callp = new AstCMethodHard{
            nodep->fileline(),
            new AstVarRef{nodep->fileline(), VN_AS(m_genp->user2p(), NodeModule), m_genp,
                          VAccess::READWRITE},
            "hard", nodep->exprp()->unlinkFrBack()};
        callp->dtypeSetVoid();
        nodep->replaceWith(callp->makeStmt());
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
    }
    void visit(AstCMethodHard* nodep) override {
        if (editFormat(nodep)) return;

        UASSERT_OBJ(nodep->name() == "size", nodep, "Non-size method call in constraints");

        AstNode* fromp = nodep->fromp();
        // Warn early while the dtype is still there
        fromp->v3warn(E_UNSUPPORTED, "Unsupported: random member variable with type "
                                         << fromp->dtypep()->prettyDTypeNameQ());

        iterateChildren(nodep);  // Might change fromp
        fromp = nodep->fromp()->unlinkFrBack();
        fromp->dtypep(nodep->dtypep());
        nodep->replaceWith(fromp);
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }
    void visit(AstNodeExpr* nodep) override {
        if (editFormat(nodep)) return;
        nodep->v3fatalSrc(
            "Visit function missing? Constraint function missing for math node: " << nodep);
    }
    void visit(AstNode* nodep) override {
        nodep->v3fatalSrc(
            "Visit function missing? Constraint function missing for node: " << nodep);
    }

public:
    // CONSTRUCTORS
    explicit ConstraintExprVisitor(VMemberMap& memberMap, AstNode* nodep,
                                   AstNodeFTask* inlineInitTaskp, AstVar* genp,
                                   AstVar* randModeVarp)
        : m_inlineInitTaskp{inlineInitTaskp}
        , m_genp{genp}
        , m_randModeVarp{randModeVarp}
        , m_memberMap{memberMap} {
        iterateAndNextNull(nodep);
    }
};

class ClassLookupHelper final {
    const std::set<AstNodeModule*>
        m_visibleModules;  // Modules directly reachale from our lookup point
    std::map<AstNode*, AstNodeModule*>
        m_classMap;  // Memoized mapping between nodes and modules that define them

    // BFS search
    template <typename Action>
    static void foreachSuperClass(AstClass* classp, Action action) {
        std::queue<AstClass*> classes;
        classes.push(classp);
        while (!classes.empty()) {
            classp = classes.front();
            classes.pop();
            for (AstClassExtends* extendsp = classp->extendsp(); extendsp;
                 extendsp = VN_AS(extendsp->nextp(), ClassExtends)) {
                AstClass* const superClassp
                    = VN_AS(extendsp->childDTypep(), ClassRefDType)->classp();
                action(superClassp);
                classes.push(superClassp);
            }
        }
    }

    static std::set<AstNodeModule*> initVisibleModules(AstClass* classp) {
        std::set<AstNodeModule*> visibleModules = {classp};
        std::vector<AstNodeModule*> symLookupOrder = {classp};
        foreachSuperClass(classp,
                          [&](AstClass* superclassp) { visibleModules.emplace(superclassp); });
        return visibleModules;
    }

public:
    bool moduleInClassHierarchy(AstNodeModule* modp) const {
        return m_visibleModules.count(modp) != 0;
    }

    AstNodeModule* findDeclaringModule(AstNode* nodep, bool classHierarchyOnly = true) {
        auto it = m_classMap.find(nodep);
        if (it != m_classMap.end()) return it->second;
        for (AstNode* backp = nodep; backp; backp = backp->backp()) {
            AstNodeModule* const modp = VN_CAST(backp, NodeModule);
            if (modp) {
                m_classMap.emplace(nodep, modp);
                if (classHierarchyOnly)
                    UASSERT_OBJ(moduleInClassHierarchy(modp), nodep,
                                "Node does not belong to class");
                return modp;
            }
        }
        return nullptr;
    }

    ClassLookupHelper(AstClass* classp)
        : m_visibleModules(initVisibleModules(classp)) {}
};

enum class CaptureMode : uint8_t {
    CAP_NO = 0x0,
    CAP_VALUE = 0x01,
    CAP_THIS = 0x02,
    CAP_F_SET_CLASSORPACKAGEP = 0x4,
    CAP_F_XREF = 0x8
};
CaptureMode operator|(CaptureMode a, CaptureMode b) {
    return static_cast<CaptureMode>(static_cast<uint8_t>(a) | static_cast<uint8_t>(b));
}
CaptureMode operator&(CaptureMode a, CaptureMode b) {
    return static_cast<CaptureMode>(static_cast<uint8_t>(a) & static_cast<uint8_t>(b));
}
CaptureMode mode(CaptureMode a) { return a & static_cast<CaptureMode>(0x3); }
bool hasFlags(CaptureMode a, CaptureMode flags) {
    return ((static_cast<uint8_t>(a) & 0xc & static_cast<uint8_t>(flags))
            == static_cast<uint8_t>(flags));
}

class CaptureVisitor final : public VNVisitor {
    AstArg* m_argsp;  // Original references turned into arguments
    AstNodeModule* m_callerp;  // Module of the outer context (for capturing `this`)
    AstClass* m_classp;  // Module of inner context (for symbol lookup)
    std::map<const AstVar*, AstVar*> m_varCloneMap;  // Map original var nodes to their clones
    std::set<AstNode*> m_ignore;  // Nodes to ignore for capturing
    ClassLookupHelper m_lookup;  // Util for class lookup
    AstVar* m_thisp = nullptr;  // Variable for outer context's object, if necessary

    // METHODS

    bool captureVariable(FileLine* const fileline, AstNodeVarRef* varrefp, AstVar*& varp) {
        auto it = m_varCloneMap.find(varrefp->varp());
        if (it == m_varCloneMap.end()) {
            AstVar* const newVarp = varrefp->varp()->cloneTree(false);
            newVarp->fileline(fileline);
            newVarp->varType(VVarType::BLOCKTEMP);
            newVarp->funcLocal(true);
            newVarp->direction(VDirection::INPUT);
            newVarp->lifetime(VLifetime::AUTOMATIC);

            m_varCloneMap.emplace(varrefp->varp(), newVarp);
            varp = newVarp;
            return true;
        }
        varp = it->second;
        return false;
    }

    template <typename NodeT>
    void fixupClassOrPackage(AstNode* memberp, NodeT refp) {
        AstNodeModule* const declClassp = m_lookup.findDeclaringModule(memberp, false);
        if (declClassp != m_classp) refp->classOrPackagep(declClassp);
    }

    template <typename NodeT>
    bool isReferenceToInnerMember(NodeT nodep) {
        return VN_IS(nodep->fromp(), LambdaArgRef);
    }

    AstVar* importThisp(FileLine* fl) {
        if (!m_thisp) {
            AstClassRefDType* const refDTypep
                = new AstClassRefDType{fl, VN_AS(m_callerp, Class), nullptr};
            v3Global.rootp()->typeTablep()->addTypesp(refDTypep);
            m_thisp = new AstVar{fl, VVarType::BLOCKTEMP, "__Vthis", refDTypep};
            m_thisp->funcLocal(true);
            m_thisp->lifetime(VLifetime::AUTOMATIC);
            m_thisp->direction(VDirection::INPUT);
            m_argsp = AstNode::addNext(m_argsp, new AstArg{fl, "", new AstThisRef{fl, refDTypep}});
        }
        return m_thisp;
    }

    AstVar* getVar(AstVar* const varp) const {
        const auto it = m_varCloneMap.find(varp);
        if (it == m_varCloneMap.end()) { return nullptr; }
        return it->second;
    }

    CaptureMode getVarRefCaptureMode(AstNodeVarRef* varRefp) {
        AstNodeModule* const modp = m_lookup.findDeclaringModule(varRefp->varp(), false);

        const bool callerIsClass = VN_IS(m_callerp, Class);
        const bool refIsXref = VN_IS(varRefp, VarXRef);
        const bool varIsFuncLocal = varRefp->varp()->isFuncLocal();
        const bool varHasAutomaticLifetime = varRefp->varp()->lifetime().isAutomatic();
        const bool varIsDeclaredInCaller = modp == m_callerp;
        const bool varIsFieldOfCaller = modp ? m_lookup.moduleInClassHierarchy(modp) : false;

        if (refIsXref) return CaptureMode::CAP_VALUE | CaptureMode::CAP_F_XREF;
        if (varIsFuncLocal && varHasAutomaticLifetime) return CaptureMode::CAP_VALUE;
        // Static var in function (will not be inlined, because it's in class)
        if (callerIsClass && varIsFuncLocal) return CaptureMode::CAP_VALUE;
        if (callerIsClass && varIsDeclaredInCaller) return CaptureMode::CAP_THIS;
        if (callerIsClass && varIsFieldOfCaller) return CaptureMode::CAP_THIS;
        UASSERT_OBJ(!callerIsClass, varRefp, "Invalid reference?");
        return CaptureMode::CAP_VALUE;
    }

    void captureRefByValue(AstNodeVarRef* nodep, CaptureMode capModeFlags) {
        AstVar* newVarp;
        bool newCapture = captureVariable(nodep->fileline(), nodep, newVarp /*ref*/);
        AstNodeVarRef* const newVarRefp = newCapture ? nodep->cloneTree(false) : nullptr;
        if (!hasFlags(capModeFlags, CaptureMode::CAP_F_SET_CLASSORPACKAGEP)) {
            // Keeping classOrPackagep will cause a broken link after inlining
            nodep->classOrPackagep(nullptr);  // AstScope will figure this out
        }
        nodep->varp(newVarp);
        if (!newCapture) return;
        if (hasFlags(capModeFlags, CaptureMode::CAP_F_XREF)) {
            AstVarRef* const notXVarRefp
                = new AstVarRef{nodep->fileline(), newVarp, VAccess::READ};
            notXVarRefp->classOrPackagep(nodep->classOrPackagep());
            nodep->replaceWith(notXVarRefp);
            nodep->deleteTree();
            nodep = notXVarRefp;
        }
        m_ignore.emplace(nodep);
        m_argsp = AstNode::addNext(m_argsp, new AstArg{nodep->fileline(), "", newVarRefp});
    }

    void captureRefByThis(AstNodeVarRef* nodep, CaptureMode capModeFlags) {
        AstVar* const thisp = importThisp(nodep->fileline());
        AstVarRef* const thisRefp = new AstVarRef{nodep->fileline(), thisp, nodep->access()};
        m_ignore.emplace(thisRefp);
        AstMemberSel* const memberSelp
            = new AstMemberSel(nodep->fileline(), thisRefp, nodep->varp());
        nodep->replaceWith(memberSelp);
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
        m_ignore.emplace(memberSelp);
    }

    // VISITORS

    void visit(AstNodeVarRef* nodep) override {
        if (m_ignore.count(nodep)) return;
        m_ignore.emplace(nodep);
        UASSERT_OBJ(nodep->varp(), nodep, "Variable unlinked");
        CaptureMode capMode = getVarRefCaptureMode(nodep);
        if (mode(capMode) == CaptureMode::CAP_NO) return;
        if (mode(capMode) == CaptureMode::CAP_VALUE) captureRefByValue(nodep, capMode);
        if (mode(capMode) == CaptureMode::CAP_THIS) captureRefByThis(nodep, capMode);
    }
    void visit(AstNodeFTaskRef* nodep) override {
        if (m_ignore.count(nodep)) {
            iterateChildren(nodep);
            return;
        }
        m_ignore.emplace(nodep);
        UASSERT_OBJ(nodep->taskp(), nodep, "Task unlinked");
        // We assume that constraint targets are not referenced this way.
        if (VN_IS(nodep, MethodCall) || VN_IS(nodep, New)) {
            m_ignore.emplace(nodep);
            iterateChildren(nodep);
            return;
        }
        AstClass* classp = VN_CAST(m_lookup.findDeclaringModule(nodep->taskp(), false), Class);
        if ((classp == m_callerp) && VN_IS(m_callerp, Class)) {
            AstNodeExpr* const pinsp = nodep->pinsp();
            if (pinsp) pinsp->unlinkFrBack();
            AstVar* const thisp = importThisp(nodep->fileline());
            AstVarRef* const thisRefp = new AstVarRef{
                nodep->fileline(), thisp, nodep->isPure() ? VAccess::READ : VAccess::READWRITE};
            m_ignore.emplace(thisRefp);
            AstMethodCall* const methodCallp
                = new AstMethodCall{nodep->fileline(), thisRefp, thisp->name(), pinsp};
            methodCallp->taskp(nodep->taskp());
            methodCallp->dtypep(nodep->dtypep());
            nodep->replaceWith(methodCallp);
            VL_DO_DANGLING(pushDeletep(nodep), nodep);
            m_ignore.emplace(methodCallp);
        }
    }
    void visit(AstMemberSel* nodep) override {
        if (!isReferenceToInnerMember(nodep)) {
            iterateChildren(nodep);
            return;
        }
        AstVarRef* const varRefp
            = new AstVarRef(nodep->fileline(), nodep->varp(), nodep->access());
        fixupClassOrPackage(nodep->varp(), varRefp);
        varRefp->user1(nodep->user1());
        nodep->replaceWith(varRefp);
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
        m_ignore.emplace(varRefp);
    }
    void visit(AstMethodCall* nodep) override {
        if (!isReferenceToInnerMember(nodep) || m_ignore.count(nodep)) {
            iterateChildren(nodep);
            return;
        }
        AstNodeExpr* const pinsp
            = nodep->pinsp() ? nodep->pinsp()->unlinkFrBackWithNext() : nullptr;
        AstNodeFTaskRef* taskRefp = nullptr;
        if (VN_IS(nodep->taskp(), Task))
            taskRefp = new AstTaskRef{nodep->fileline(), nodep->name(), pinsp};
        else if (VN_IS(nodep->taskp(), Func))
            taskRefp = new AstFuncRef{nodep->fileline(), nodep->name(), pinsp};
        UASSERT_OBJ(taskRefp, nodep, "Node needs to point to regular method");
        taskRefp->taskp(nodep->taskp());
        taskRefp->dtypep(nodep->dtypep());
        fixupClassOrPackage(nodep->taskp(), taskRefp);
        taskRefp->user1(nodep->user1());
        nodep->replaceWith(taskRefp);
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
        m_ignore.emplace(taskRefp);
    }
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    explicit CaptureVisitor(AstNode* const nodep, AstNodeModule* callerp, AstClass* const classp,
                            const bool clone = true, VNRelinker* const linkerp = nullptr)
        : m_argsp(nullptr)
        , m_callerp(callerp)
        , m_classp(classp)
        , m_lookup(classp) {
        iterateAndNextNull(nodep);
    }

    // PUBLIC METHODS

    AstArg* getArgs() const { return m_argsp; }

    void addFunctionArguments(AstNodeFTask* funcp) const {
        for (AstArg* argp = getArgs(); argp; argp = VN_AS(argp->nextp(), Arg)) {
            if (AstNodeVarRef* varrefp = VN_CAST(argp->exprp(), NodeVarRef)) {
                if ((varrefp->classOrPackagep() == m_callerp) || VN_IS(varrefp, VarXRef)) {
                    // Keeping classOrPackagep will cause a broken link after inlining
                    varrefp->classOrPackagep(nullptr);
                }
                funcp->addStmtsp(getVar(varrefp->varp()));
            } else {
                UASSERT_OBJ(VN_IS(argp->exprp(), ThisRef), argp->exprp(), "Wrong arg expression");
                funcp->addStmtsp(m_thisp);
            }
        }
    }
};

//######################################################################
// Visitor that defines a randomize method where needed

class RandomizeVisitor final : public VNVisitor {
    // NODE STATE
    // Cleared on Netlist
    //  AstClass::user1()       -> bool.  Set true to indicate needs randomize processing
    //  AstVar::user2p()        -> AstClass*. Pointer to containing class
    //  AstEnumDType::user2()   -> AstVar*.  Pointer to table with enum values
    //  AstConstraint::user2p() -> AstTask*. Pointer to constraint setup procedure
    //  AstClass::user2p()      -> AstTask*. Pointer to full constraint setup procedure
    //  AstVar::user3()         -> bool. Handled in constraints
    //  AstClass::user3p()      -> AstVar*.  Constrained randomizer variable
    //  AstClass::user4p()      -> AstVar*.  Rand mode state variable
    // VNUser1InUse    m_inuser1;      (Allocated for use in RandomizeMarkVisitor)
    // VNUser2InUse    m_inuser2;      (Allocated for use in RandomizeMarkVisitor)
    const VNUser3InUse m_inuser3;
    const VNUser4InUse m_inuser4;

    // STATE
    V3UniqueNames m_inlineUniqueNames;  // For generating unique function names
    VMemberMap m_memberMap;  // Member names cached for fast lookup
    AstNodeModule* m_modp = nullptr;  // Current module
    const AstNodeFTask* m_ftaskp = nullptr;  // Current function/task
    AstNodeStmt* m_stmtp = nullptr;  // Current statement
    AstDynArrayDType* m_dynarrayDtp = nullptr;  // Dynamic array type (for rand mode)
    size_t m_enumValueTabCount = 0;  // Number of tables with enum values created
    int m_randCaseNum = 0;  // Randcase number within a module for var naming
    std::map<std::string, AstCDType*> m_randcDtypes;  // RandC data type deduplication

    // METHODS
    void createRandomGenerator(AstClass* const classp) {
        if (classp->user3p()) return;
        if (classp->extendsp()) {
            createRandomGenerator(classp->extendsp()->classp());
            return;
        }
        AstVar* const genp = new AstVar{classp->fileline(), VVarType::MEMBER, "constraint",
                                        classp->findBasicDType(VBasicDTypeKwd::RANDOM_GENERATOR)};
        genp->user2p(classp);
        classp->addMembersp(genp);
        classp->user3p(genp);
    }
    AstVar* getRandomGenerator(AstClass* const classp) {
        if (classp->user3p()) return VN_AS(classp->user3p(), Var);
        if (classp->extendsp()) return getRandomGenerator(classp->extendsp()->classp());
        return nullptr;
    }
    AstTask* getCreateConstraintSetupFunc(AstClass* classp) {
        if (classp->user2p()) return VN_AS(classp->user2p(), Task);
        AstTask* const setupAllTaskp
            = new AstTask{classp->fileline(), "__Vsetup_constraints", nullptr};
        setupAllTaskp->classMethod(true);
        setupAllTaskp->isVirtual(true);
        classp->addMembersp(setupAllTaskp);
        classp->user2p(setupAllTaskp);
        return setupAllTaskp;
    }
    AstVar* getCreateRandModeVar(AstClass* const classp) {
        if (classp->user4p()) return VN_AS(classp->user4p(), Var);
        if (AstClassExtends* const extendsp = classp->extendsp()) {
            return getCreateRandModeVar(extendsp->classp());
        }
        FileLine* const fl = classp->fileline();
        if (!m_dynarrayDtp) {
            m_dynarrayDtp = new AstDynArrayDType{
                fl, v3Global.rootp()->typeTablep()->findBitDType()->dtypep()};
            m_dynarrayDtp->dtypep(m_dynarrayDtp);
            v3Global.rootp()->typeTablep()->addTypesp(m_dynarrayDtp);
        }
        AstVar* const randModeVarp
            = new AstVar{fl, VVarType::MODULETEMP, "__Vrandmode", m_dynarrayDtp};

        randModeVarp->user2p(classp);
        classp->addStmtsp(randModeVarp);
        classp->user4p(randModeVarp);
        return randModeVarp;
    }
    AstVar* getRandModeVar(AstClass* const classp) {
        if (classp->user4p()) return VN_AS(classp->user4p(), Var);
        if (AstClassExtends* const extendsp = classp->extendsp()) {
            return getRandModeVar(extendsp->classp());
        }
        return nullptr;
    }
    void addSetRandMode(AstNodeFTask* const ftaskp, AstVar* const genp,
                        AstVar* const randModeVarp) {
        FileLine* const fl = ftaskp->fileline();
        AstCMethodHard* const setRandModep = new AstCMethodHard{
            fl, new AstVarRef{fl, VN_AS(genp->user2p(), NodeModule), genp, VAccess::WRITE},
            "set_randmode",
            new AstVarRef{fl, VN_AS(randModeVarp->user2p(), NodeModule), randModeVarp,
                          VAccess::READ}};
        setRandModep->dtypeSetVoid();
        ftaskp->addStmtsp(setRandModep->makeStmt());
    }
    void createRandomizeClassVars(AstNetlist* const netlistp) {
        netlistp->foreach([&](AstClass* const classp) {
            if (classp->existsMember(
                    [&](const AstClass*, const AstConstraint*) { return true; })) {
                createRandomGenerator(classp);
            }
            uint32_t randModeCount = 0;
            classp->foreachMember([&](AstClass*, AstVar* memberVarp) {
                VarRandMode randMode = {.asInt = memberVarp->user1()};
                if (!randMode.usesRandMode) return;
                // SystemVerilog only allows single inheritance, so we don't need to worry about
                // index overlap. If the index > 0, it's already been set.
                if (randMode.index == 0) {
                    randMode.index = randModeCount++;
                    memberVarp->user1(randMode.asInt);
                } else {
                    randModeCount = randMode.index + 1;
                }
            });
            if (randModeCount > 0) {
                AstVar* const randModeVarp = getCreateRandModeVar(classp);
                AstNodeModule* const randModeModp = VN_AS(randModeVarp->user2p(), NodeModule);
                FileLine* fl = randModeVarp->fileline();
                AstCMethodHard* const dynarrayNewp = new AstCMethodHard{
                    fl, new AstVarRef{fl, randModeModp, randModeVarp, VAccess::WRITE},
                    "renew_copy", new AstConst{fl, randModeCount}};
                dynarrayNewp->addPinsp(
                    new AstVarRef{fl, randModeModp, randModeVarp, VAccess::READ});
                dynarrayNewp->dtypeSetVoid();
                AstNodeFTask* const newp = VN_AS(m_memberMap.findMember(classp, "new"), NodeFTask);
                fl = classp->fileline();
                UASSERT_OBJ(newp, classp, "No new() in class");
                newp->addStmtsp(dynarrayNewp->makeStmt());
                newp->addStmtsp(makeRandModeInitLoop(
                    fl, new AstVarRef{fl, randModeModp, randModeVarp, VAccess::WRITE},
                    new AstConst{fl, 1}, true));
            }
        });
    }
    static AstNode* makeRandModeInitLoop(FileLine* const fl, AstNodeExpr* const lhsp,
                                         AstNodeExpr* const rhsp, bool inTask) {
        AstVar* const iterVarp = new AstVar{fl, VVarType::BLOCKTEMP, "i", lhsp->findUInt32DType()};
        iterVarp->funcLocal(inTask);
        iterVarp->lifetime(VLifetime::AUTOMATIC);
        AstCMethodHard* const sizep = new AstCMethodHard{fl, lhsp, "size", nullptr};
        sizep->dtypeSetUInt32();
        AstCMethodHard* const atp = new AstCMethodHard{fl, lhsp->cloneTree(false), "at",
                                                       new AstVarRef{fl, iterVarp, VAccess::READ}};
        atp->dtypeSetUInt32();
        AstNode* const stmtsp = iterVarp;
        stmtsp->addNext(
            new AstAssign{fl, new AstVarRef{fl, iterVarp, VAccess::WRITE}, new AstConst{fl, 0}});
        stmtsp->addNext(
            new AstWhile{fl, new AstLt{fl, new AstVarRef{fl, iterVarp, VAccess::READ}, sizep},
                         new AstAssign{fl, atp, rhsp},
                         new AstAssign{fl, new AstVarRef{fl, iterVarp, VAccess::WRITE},
                                       new AstAdd{fl, new AstConst{fl, 1},
                                                  new AstVarRef{fl, iterVarp, VAccess::READ}}}});
        return new AstBegin{fl, "", stmtsp, false, true};
    }
    AstNodeStmt* wrapIfRandMode(AstVar* const varp, AstNodeStmt* stmtp) {
        FileLine* const fl = stmtp->fileline();
        const VarRandMode randMode = {.asInt = varp->user1()};
        if (randMode.usesRandMode) {
            AstVar* randModeVarp = getRandModeVar(VN_AS(m_modp, Class));
            AstCMethodHard* const atp
                = new AstCMethodHard{fl,
                                     new AstVarRef{fl, VN_AS(randModeVarp->user2p(), Class),
                                                   randModeVarp, VAccess::READ},
                                     "at", new AstConst{fl, randMode.index}};
            atp->dtypeSetUInt32();
            return new AstIf{fl, atp, stmtp};
        }
        return stmtp;
    }
    AstVar* enumValueTabp(AstEnumDType* const nodep) {
        if (nodep->user2p()) return VN_AS(nodep->user2p(), Var);
        UINFO(9, "Construct Venumvaltab " << nodep << endl);
        AstNodeArrayDType* const vardtypep = new AstUnpackArrayDType{
            nodep->fileline(), nodep->dtypep(),
            new AstRange{nodep->fileline(), static_cast<int>(nodep->itemCount()), 0}};
        AstInitArray* const initp = new AstInitArray{nodep->fileline(), vardtypep, nullptr};
        v3Global.rootp()->typeTablep()->addTypesp(vardtypep);
        AstVar* const varp
            = new AstVar{nodep->fileline(), VVarType::MODULETEMP,
                         "__Venumvaltab_" + cvtToStr(m_enumValueTabCount++), vardtypep};
        varp->isConst(true);
        varp->isStatic(true);
        varp->valuep(initp);
        // Add to root, as don't know module we are in, and aids later structure sharing
        v3Global.rootp()->dollarUnitPkgAddp()->addStmtsp(varp);

        UASSERT_OBJ(nodep->itemsp(), nodep, "Enum without items");
        for (AstEnumItem* itemp = nodep->itemsp(); itemp;
             itemp = VN_AS(itemp->nextp(), EnumItem)) {
            AstConst* const vconstp = VN_AS(itemp->valuep(), Const);
            UASSERT_OBJ(vconstp, nodep, "Enum item without constified value");
            initp->addValuep(vconstp->cloneTree(false));
        }
        nodep->user2p(varp);
        return varp;
    }

    AstCDType* findVlRandCDType(FileLine* const fl, uint64_t items) {
        // For 8 items we need to have a 9 item LFSR so items is max count
        // width(items) = log2(items) + 1
        const std::string type = AstCDType::typeToHold(V3Number::log2bQuad(items) + 1);
        const std::string name = "VlRandC<" + type + ", " + cvtToStr(items) + "ULL>";
        // Create or reuse (to avoid duplicates) randomization object dtype
        const auto pair = m_randcDtypes.emplace(name, nullptr);
        if (pair.second) {
            AstCDType* newp = new AstCDType{fl, name};
            v3Global.rootp()->typeTablep()->addTypesp(newp);
            pair.first->second = newp;
        }
        return pair.first->second;
    }

    AstVar* newRandcVarsp(AstVar* const varp) {
        // If a randc, make a VlRandC object to hold the state
        if (!varp->isRandC()) return nullptr;
        uint64_t items = 0;

        if (AstEnumDType* const enumDtp = VN_CAST(varp->dtypep()->skipRefToEnump(), EnumDType)) {
            items = static_cast<uint64_t>(enumDtp->itemCount());
        } else {
            AstBasicDType* const basicp = varp->dtypep()->skipRefp()->basicp();
            UASSERT_OBJ(basicp, varp, "Unexpected randc variable dtype");
            if (basicp->width() > 32) {
                varp->v3error("Maximum implemented width for randc is 32 bits, "
                              << varp->prettyNameQ() << " is " << basicp->width() << " bits");
                varp->isRandC(false);
                varp->isRand(true);
                return nullptr;
            }
            items = 1ULL << basicp->width();
        }
        AstCDType* newdtp = findVlRandCDType(varp->fileline(), items);
        AstVar* newp
            = new AstVar{varp->fileline(), VVarType::MEMBER, varp->name() + "__Vrandc", newdtp};
        newp->isInternal(true);
        varp->addNextHere(newp);
        UINFO(9, "created " << varp << endl);
        return newp;
    }
    AstNodeStmt* newRandStmtsp(FileLine* fl, AstNodeExpr* exprp, AstVar* randcVarp, int offset = 0,
                               AstMemberDType* memberp = nullptr) {
        if (const auto* const structDtp
            = VN_CAST(memberp ? memberp->subDTypep()->skipRefp() : exprp->dtypep()->skipRefp(),
                      StructDType)) {
            AstNodeStmt* stmtsp = nullptr;
            if (structDtp->packed()) offset += memberp ? memberp->lsb() : 0;
            for (AstMemberDType* smemberp = structDtp->membersp(); smemberp;
                 smemberp = VN_AS(smemberp->nextp(), MemberDType)) {
                AstNodeStmt* randp = nullptr;
                if (structDtp->packed()) {
                    randp = newRandStmtsp(fl, stmtsp ? exprp->cloneTree(false) : exprp, nullptr,
                                          offset, smemberp);
                } else {
                    AstStructSel* structSelp
                        = new AstStructSel{fl, exprp->cloneTree(false), smemberp->name()};
                    structSelp->dtypep(smemberp->childDTypep());
                    if (!structSelp->dtypep()) structSelp->dtypep(smemberp->subDTypep());
                    randp = newRandStmtsp(fl, structSelp, nullptr);
                }
                if (stmtsp) {
                    stmtsp->addNext(randp);
                } else {
                    stmtsp = randp;
                }
            }
            return stmtsp;
        } else {
            AstNodeExpr* valp;
            if (AstEnumDType* const enumDtp = VN_CAST(memberp ? memberp->subDTypep()->subDTypep()
                                                              : exprp->dtypep()->subDTypep(),
                                                      EnumDType)) {
                AstVarRef* const tabRefp
                    = new AstVarRef{fl, enumValueTabp(enumDtp), VAccess::READ};
                tabRefp->classOrPackagep(v3Global.rootp()->dollarUnitPkgAddp());
                AstNodeExpr* const randp
                    = newRandValue(fl, randcVarp, exprp->findBasicDType(VBasicDTypeKwd::UINT32));
                AstNodeExpr* const moddivp = new AstModDiv{
                    fl, randp, new AstConst{fl, static_cast<uint32_t>(enumDtp->itemCount())}};
                moddivp->dtypep(enumDtp);
                valp = new AstArraySel{fl, tabRefp, moddivp};
            } else {
                valp
                    = newRandValue(fl, randcVarp, (memberp ? memberp->dtypep() : exprp->dtypep()));
            }
            AstAssign* assignp
                = new AstAssign{fl,
                                new AstSel{fl, exprp, offset + (memberp ? memberp->lsb() : 0),
                                           memberp ? memberp->width() : exprp->width()},
                                valp};
            AstVar* varp = nullptr;
            exprp->exists([&](const AstVarRef* varrefp) {
                if (varrefp->access().isWriteOrRW()) varp = varrefp->varp();
                return varp != nullptr;
            });
            return wrapIfRandMode(varp, assignp);
        }
    }
    AstNodeExpr* newRandValue(FileLine* const fl, AstVar* const randcVarp,
                              AstNodeDType* const dtypep) {
        if (randcVarp) {
            AstVarRef* const argsp = new AstVarRef{fl, randcVarp, VAccess::READWRITE};
            argsp->AstNode::addNext(new AstText{fl, ".randomize(__Vm_rng)"});
            AstCExpr* const newp = new AstCExpr{fl, argsp};
            newp->dtypep(dtypep);
            return newp;
        } else {
            return new AstRandRNG{fl, dtypep};
        }
    }
    void addPrePostCall(AstClass* const classp, AstFunc* const funcp, const string& name) {
        if (AstTask* userFuncp = VN_CAST(m_memberMap.findMember(classp, name), Task)) {
            AstTaskRef* const callp
                = new AstTaskRef{userFuncp->fileline(), userFuncp->name(), nullptr};
            callp->taskp(userFuncp);
            funcp->addStmtsp(callp->makeStmt());
        }
    }
    AstTask* newSetupConstraintTask(AstClass* const nodep, const std::string& name) {
        AstTask* const taskp = new AstTask{nodep->fileline(), name + "_setup_constraint", nullptr};
        taskp->classMethod(true);
        nodep->addMembersp(taskp);
        return taskp;
    }
    AstNodeStmt* implementConstraintsClear(FileLine* const fileline, AstVar* const genp) {
        AstCMethodHard* const clearp = new AstCMethodHard{
            fileline,
            new AstVarRef{fileline, VN_AS(genp->user2p(), NodeModule), genp, VAccess::READWRITE},
            "clear"};
        clearp->dtypeSetVoid();
        return clearp->makeStmt();
    }

    void addBasicRandomizeBody(AstFunc* const basicRandomizep, AstClass* const nodep) {
        FileLine* const fl = nodep->fileline();
        AstVar* const basicFvarp = VN_AS(basicRandomizep->fvarp(), Var);
        AstVarRef* const basicFvarRefp = new AstVarRef{fl, basicFvarp, VAccess::WRITE};
        AstConst* const beginBasicValp = new AstConst{fl, AstConst::WidthedValue{}, 32, 1};
        basicRandomizep->addStmtsp(new AstAssign{fl, basicFvarRefp, beginBasicValp});

        nodep->foreachMember([&](AstClass* classp, AstVar* memberVarp) {
            if (!memberVarp->isRand() || memberVarp->user3()) return;
            const AstNodeDType* const dtypep = memberVarp->dtypep()->skipRefp();
            if (VN_IS(dtypep, BasicDType) || VN_IS(dtypep, StructDType)) {
                AstVar* const randcVarp = newRandcVarsp(memberVarp);
                AstVarRef* const refp = new AstVarRef{fl, classp, memberVarp, VAccess::WRITE};
                AstNodeStmt* const stmtp = newRandStmtsp(fl, refp, randcVarp);
                basicRandomizep->addStmtsp(stmtp);
            } else if (const AstClassRefDType* const classRefp = VN_CAST(dtypep, ClassRefDType)) {
                if (classRefp->classp() == nodep) {
                    memberVarp->v3warn(E_UNSUPPORTED,
                                       "Unsupported: random member variable with the "
                                       "type of the containing class");
                    return;
                }
                AstFunc* const memberFuncp
                    = V3Randomize::newRandomizeFunc(m_memberMap, classRefp->classp());
                AstMethodCall* const callp
                    = new AstMethodCall{fl, new AstVarRef{fl, classp, memberVarp, VAccess::WRITE},
                                        "randomize", nullptr};
                callp->taskp(memberFuncp);
                callp->dtypeFrom(memberFuncp);
                AstVarRef* const basicFvarRefReadp = basicFvarRefp->cloneTree(false);
                basicFvarRefReadp->access(VAccess::READ);
                AstIf* const assignIfNotNullp = new AstIf{
                    fl,
                    new AstNeq{fl, new AstVarRef{fl, classp, memberVarp, VAccess::READ},
                               new AstConst{fl, AstConst::Null{}}},
                    new AstAssign{fl, basicFvarRefp->cloneTree(false),
                                  new AstAnd{fl, basicFvarRefReadp, callp}}};
                basicRandomizep->addStmtsp(wrapIfRandMode(memberVarp, assignIfNotNullp));
            } else {
                memberVarp->v3warn(E_UNSUPPORTED, "Unsupported: random member variable with type "
                                                      << memberVarp->dtypep()->prettyDTypeNameQ());
            }
        });
    }

    // VISITORS
    void visit(AstNodeModule* nodep) override {
        VL_RESTORER(m_modp);
        VL_RESTORER(m_randCaseNum);
        m_modp = nodep;
        m_randCaseNum = 0;
        iterateChildren(nodep);
    }
    void visit(AstNodeFTask* nodep) override {
        VL_RESTORER(m_ftaskp);
        m_ftaskp = nodep;
        iterateChildren(nodep);
    }
    void visit(AstClass* nodep) override {
        VL_RESTORER(m_modp);
        VL_RESTORER(m_randCaseNum);
        m_modp = nodep;
        m_randCaseNum = 0;

        iterateChildren(nodep);
        if (!nodep->user1()) return;  // Doesn't need randomize, or already processed
        UINFO(9, "Define randomize() for " << nodep << endl);
        AstFunc* const randomizep = V3Randomize::newRandomizeFunc(m_memberMap, nodep);
        AstVar* const fvarp = VN_AS(randomizep->fvarp(), Var);
        addPrePostCall(nodep, randomizep, "pre_randomize");
        FileLine* fl = nodep->fileline();

        AstVar* const randModeVarp = getRandModeVar(nodep);
        AstNodeExpr* beginValp = nullptr;
        AstVar* genp = getRandomGenerator(nodep);
        if (genp) {
            nodep->foreachMember([&](AstClass* const classp, AstConstraint* const constrp) {
                AstTask* taskp = VN_AS(constrp->user2p(), Task);
                if (!taskp) {
                    taskp = newSetupConstraintTask(classp, constrp->name());
                    constrp->user2p(taskp);
                }
                AstTaskRef* const setupTaskRefp
                    = new AstTaskRef{constrp->fileline(), taskp->name(), nullptr};
                setupTaskRefp->taskp(taskp);
                setupTaskRefp->classOrPackagep(classp);

                AstTask* const setupAllTaskp = getCreateConstraintSetupFunc(nodep);

                setupAllTaskp->addStmtsp(setupTaskRefp->makeStmt());

                ConstraintExprVisitor{m_memberMap, constrp->itemsp(), nullptr, genp, randModeVarp};
                if (constrp->itemsp()) taskp->addStmtsp(constrp->itemsp()->unlinkFrBackWithNext());
            });
            randomizep->addStmtsp(implementConstraintsClear(fl, genp));
            AstTask* setupAllTaskp = getCreateConstraintSetupFunc(nodep);
            AstTaskRef* const setupTaskRefp = new AstTaskRef{fl, setupAllTaskp->name(), nullptr};
            setupTaskRefp->taskp(setupAllTaskp);
            randomizep->addStmtsp(implementConstraintsClear(fl, genp));
            randomizep->addStmtsp(setupTaskRefp->makeStmt());

            AstNodeModule* const genModp = VN_AS(genp->user2p(), NodeModule);
            AstVarRef* const genRefp = new AstVarRef{fl, genModp, genp, VAccess::READWRITE};
            AstNode* const argsp = genRefp;
            argsp->addNext(new AstText{fl, ".next(__Vm_rng)"});

            AstNodeExpr* const solverCallp = new AstCExpr{fl, argsp};
            solverCallp->dtypeSetBit();
            beginValp = solverCallp;

            if (randModeVarp) {
                AstNodeModule* const randModeClassp = VN_AS(randModeVarp->user2p(), Class);
                AstNodeFTask* const newp
                    = VN_AS(m_memberMap.findMember(randModeClassp, "new"), NodeFTask);
                UASSERT_OBJ(newp, randModeClassp, "No new() in class");
                addSetRandMode(newp, genp, randModeVarp);
            }
        } else {
            beginValp = new AstConst{fl, AstConst::WidthedValue{}, 32, 1};
        }

        AstVarRef* const fvarRefp = new AstVarRef{fl, fvarp, VAccess::WRITE};
        randomizep->addStmtsp(new AstAssign{fl, fvarRefp, beginValp});

        AstNodeFTask* const newp = VN_AS(m_memberMap.findMember(nodep, "new"), NodeFTask);
        UASSERT_OBJ(newp, nodep, "No new() in class");

        AstFunc* const basicRandomizep
            = V3Randomize::newRandomizeFunc(m_memberMap, nodep, "__Vbasic_randomize");
        addBasicRandomizeBody(basicRandomizep, nodep);
        AstFuncRef* const basicRandomizeCallp = new AstFuncRef{fl, "__Vbasic_randomize", nullptr};
        basicRandomizeCallp->taskp(basicRandomizep);
        basicRandomizeCallp->dtypep(basicRandomizep->dtypep());
        AstVarRef* const fvarRefReadp = fvarRefp->cloneTree(false);
        fvarRefReadp->access(VAccess::READ);

        randomizep->addStmtsp(new AstAssign{fl, fvarRefp->cloneTree(false),
                                            new AstAnd{fl, fvarRefReadp, basicRandomizeCallp}});
        addPrePostCall(nodep, randomizep, "post_randomize");
        nodep->user1(false);
    }
    void visit(AstRandCase* nodep) override {
        // RANDCASE
        //   CASEITEM expr1 : stmt1
        //   CASEITEM expr2 : stmt2
        // ->
        //   tmp = URandomRange{0, num} + 1   // + 1 so weight 0 means never
        //   if (tmp < expr1) stmt1;
        //   else if (tmp < (expr2 + expr1)) stmt1;
        //   else warning
        // Note this code assumes that the expressions after V3Const are fast to compute
        // Optimize: we would be better with a binary search tree to reduce ifs that execute
        if (debug() >= 9) nodep->dumpTree("-  rcin:: ");
        AstNodeDType* const sumDTypep = nodep->findUInt64DType();

        FileLine* const fl = nodep->fileline();
        const std::string name = "__Vrandcase" + cvtToStr(m_randCaseNum++);
        AstVar* const randVarp = new AstVar{fl, VVarType::BLOCKTEMP, name, sumDTypep};
        randVarp->noSubst(true);
        if (m_ftaskp) randVarp->funcLocal(true);
        AstNodeExpr* sump = new AstConst{fl, AstConst::WidthedValue{}, 64, 0};
        AstNodeIf* const firstIfsp
            = new AstIf{fl, new AstConst{fl, AstConst::BitFalse{}}, nullptr, nullptr};
        AstNodeIf* ifsp = firstIfsp;

        for (AstCaseItem* itemp = nodep->itemsp(); itemp;
             itemp = VN_AS(itemp->nextp(), CaseItem)) {
            AstNodeExpr* const condp = itemp->condsp()->unlinkFrBack();
            sump
                = new AstAdd{condp->fileline(), sump, new AstExtend{itemp->fileline(), condp, 64}};
            AstNode* const stmtsp
                = itemp->stmtsp() ? itemp->stmtsp()->unlinkFrBackWithNext() : nullptr;
            AstVarRef* const randVarRefp = new AstVarRef{fl, randVarp, VAccess::WRITE};
            AstNodeIf* const newifp
                = new AstIf{itemp->fileline(),
                            new AstLte{condp->fileline(), randVarRefp, sump->cloneTreePure(true)},
                            stmtsp, nullptr};
            ifsp->addElsesp(newifp);
            ifsp = newifp;
        }
        AstDisplay* dispp = new AstDisplay{
            fl, VDisplayType::DT_ERROR, "All randcase items had 0 weights (IEEE 1800-2023 18.16)",
            nullptr, nullptr};
        UASSERT_OBJ(m_modp, nodep, "randcase not under module");
        dispp->fmtp()->timeunit(m_modp->timeunit());
        ifsp->addElsesp(dispp);

        AstNode* const newp = randVarp;
        AstNodeExpr* randp = new AstRand{fl, nullptr, false};
        randp->dtypeSetUInt64();
        AstVarRef* const randVarRefp = new AstVarRef{fl, randVarp, VAccess::WRITE};
        newp->addNext(new AstAssign{fl, randVarRefp,
                                    new AstAdd{fl, new AstConst{fl, AstConst::Unsized64{}, 1},
                                               new AstModDiv{fl, randp, sump}}});
        newp->addNext(firstIfsp);
        if (debug() >= 9) newp->dumpTreeAndNext(cout, "-  rcnew: ");
        nodep->replaceWith(newp);
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }
    void visit(AstNodeFTaskRef* nodep) override {
        if (nodep->name() == "rand_mode") {
            AstMethodCall* const methodCallp = VN_CAST(nodep, MethodCall);
            AstNodeExpr* const fromp = methodCallp ? methodCallp->fromp() : nullptr;
            const RandModeTarget randModeTarget = RandModeTarget::get(fromp, m_modp);
            UASSERT_OBJ(randModeTarget.classp, nodep,
                        "Should have checked in RandomizeMarkVisitor");
            AstVar* const randModeVarp = getRandModeVar(randModeTarget.classp);
            AstNodeExpr* lhsp = nullptr;
            if (randModeTarget.classp == m_modp) {
                // Called on 'this' or a member of 'this'
                lhsp = new AstVarRef{nodep->fileline(), VN_AS(randModeVarp->user2p(), NodeModule),
                                     randModeVarp, VAccess::WRITE};
            } else {
                AstMemberSel* const memberselp = new AstMemberSel{
                    nodep->fileline(), randModeTarget.fromp->unlinkFrBack(), randModeVarp};
                memberselp->foreach([](AstVarRef* varrefp) { varrefp->access(VAccess::WRITE); });
                lhsp = memberselp;
            }
            if (nodep->pinsp()) {  // Set rand mode
                UASSERT_OBJ(VN_IS(nodep->backp(), StmtExpr), nodep, "Should be a statement");
                AstNodeExpr* const rhsp = VN_AS(nodep->pinsp(), Arg)->exprp()->unlinkFrBack();
                if (randModeTarget.receiverp && randModeTarget.receiverp->isRand()) {
                    // Called on a rand member variable. Set the variable's rand mode
                    const VarRandMode randMode = {.asInt = randModeTarget.receiverp->user1()};
                    UASSERT_OBJ(randMode.usesRandMode, nodep, "Failed to set usesRandMode");
                    AstCMethodHard* const atp
                        = new AstCMethodHard{nodep->fileline(), lhsp, "at",
                                             new AstConst{nodep->fileline(), randMode.index}};
                    atp->dtypeSetUInt32();
                    m_stmtp->replaceWith(new AstAssign{nodep->fileline(), atp, rhsp});
                } else {
                    // Called on 'this' or a non-rand class instance. Set the rand mode of all
                    // members
                    m_stmtp->replaceWith(
                        makeRandModeInitLoop(nodep->fileline(), lhsp, rhsp, m_ftaskp));
                }
                pushDeletep(m_stmtp);
            } else {  // Retrieve rand mode
                UASSERT_OBJ(randModeTarget.receiverp, nodep, "Should have receiver");
                UASSERT_OBJ(randModeTarget.receiverp->isRand(), nodep, "Should be rand");
                const VarRandMode randMode = {.asInt = randModeTarget.receiverp->user1()};
                UASSERT_OBJ(randMode.usesRandMode, nodep, "Failed to set usesRandMode");
                AstCMethodHard* const atp
                    = new AstCMethodHard{nodep->fileline(), lhsp, "at",
                                         new AstConst{nodep->fileline(), randMode.index}};
                atp->dtypeSetUInt32();
                nodep->replaceWith(atp);
                VL_DO_DANGLING(pushDeletep(nodep), nodep);
            }
            return;
        }

        AstWith* const withp = VN_CAST(nodep->pinsp(), With);

        if (!(nodep->name() == "randomize") || !withp) {
            iterateChildren(nodep);
            return;
        }
        withp->unlinkFrBack();

        iterateChildren(nodep);

        AstClass* classp = nullptr;
        if (AstMethodCall* const callp = VN_CAST(nodep, MethodCall)) {
            UASSERT_OBJ(callp->fromp()->dtypep(), callp->fromp(), "Object dtype is not linked");
            AstClassRefDType* const classrefdtypep
                = VN_CAST(callp->fromp()->dtypep(), ClassRefDType);
            if (!classrefdtypep) {
                nodep->v3warn(E_UNSUPPORTED,
                              "Inline constraints are not supported for this node type");
                return;
            }
            classp = classrefdtypep->classp();
            UASSERT_OBJ(classp, classrefdtypep, "Class type is unlinked to its ref type");
        } else {
            classp = VN_CAST(m_modp, Class);
            UASSERT_OBJ(classp, m_modp, "Module not class, should have failed in V3Width");
        }
        if (classp->user1()) {
            // We need to first ensure that the class constraints are transformed
            // NOTE: This is safe only because AstClass visit function overwrites all
            // nesting-dependent state variables
            iterate(classp);
        }

        AstVar* const classGenp = getRandomGenerator(classp);
        AstVar* const localGenp
            = new AstVar{nodep->fileline(), VVarType::BLOCKTEMP, "randomizer",
                         classp->findBasicDType(VBasicDTypeKwd::RANDOM_GENERATOR)};
        localGenp->funcLocal(true);

        AstFunc* const randomizeFuncp = V3Randomize::newRandomizeFunc(
            m_memberMap, classp, m_inlineUniqueNames.get(nodep), false);

        // Detach the expression and prepare variable copies
        const CaptureVisitor captured{withp->exprp(), m_modp, classp, false};

        // Add function arguments
        captured.addFunctionArguments(randomizeFuncp);

        // Add constraints clearing code
        if (classGenp) {
            randomizeFuncp->addStmtsp(
                implementConstraintsClear(randomizeFuncp->fileline(), classGenp));
        }

        randomizeFuncp->addStmtsp(localGenp);

        AstFunc* const basicRandomizeFuncp
            = V3Randomize::newRandomizeFunc(m_memberMap, classp, "__Vbasic_randomize");
        AstFuncRef* const basicRandomizeFuncCallp
            = new AstFuncRef{nodep->fileline(), "__Vbasic_randomize", nullptr};
        basicRandomizeFuncCallp->taskp(basicRandomizeFuncp);
        basicRandomizeFuncCallp->dtypep(basicRandomizeFuncp->dtypep());

        // Copy (derive) class constraints if present
        if (classGenp) {
            AstTask* const constrSetupFuncp = getCreateConstraintSetupFunc(classp);
            AstTaskRef* const callp
                = new AstTaskRef{nodep->fileline(), constrSetupFuncp->name(), nullptr};
            callp->taskp(constrSetupFuncp);
            randomizeFuncp->addStmtsp(callp->makeStmt());
            randomizeFuncp->addStmtsp(new AstAssign{
                nodep->fileline(), new AstVarRef{nodep->fileline(), localGenp, VAccess::WRITE},
                new AstVarRef{nodep->fileline(), VN_AS(classGenp->user2p(), NodeModule), classGenp,
                              VAccess::READ}});
        }

        // Set rand mode if present (not needed if classGenp exists and was copied)
        AstVar* const randModeVarp = getRandModeVar(classp);
        if (!classGenp && randModeVarp) addSetRandMode(randomizeFuncp, localGenp, randModeVarp);

        // Generate constraint setup code and a hardcoded call to the solver
        AstNode* const capturedTreep = withp->exprp()->unlinkFrBackWithNext();
        randomizeFuncp->addStmtsp(capturedTreep);
        {
            ConstraintExprVisitor{m_memberMap, capturedTreep, randomizeFuncp, localGenp,
                                  randModeVarp};
        }

        // Call the solver and set return value
        AstVarRef* const randNextp
            = new AstVarRef{nodep->fileline(), localGenp, VAccess::READWRITE};
        randNextp->AstNode::addNext(new AstText{nodep->fileline(), ".next(__Vm_rng)"});
        AstNodeExpr* const solverCallp = new AstCExpr{nodep->fileline(), randNextp};
        solverCallp->dtypeSetBit();
        randomizeFuncp->addStmtsp(new AstAssign{
            nodep->fileline(),
            new AstVarRef{nodep->fileline(), VN_AS(randomizeFuncp->fvarp(), Var), VAccess::WRITE},
            new AstAnd{nodep->fileline(), basicRandomizeFuncCallp, solverCallp}});

        // Replace the node with a call to that function
        nodep->name(randomizeFuncp->name());
        nodep->addPinsp(captured.getArgs());
        nodep->taskp(randomizeFuncp);
        nodep->dtypeFrom(randomizeFuncp->dtypep());
        nodep->classOrPackagep(classp);
        UINFO(9, "Added `%s` randomization procedure");
        VL_DO_DANGLING(withp->deleteTree(), withp);
    }
    void visit(AstNodeStmt* nodep) override {
        VL_RESTORER(m_stmtp);
        m_stmtp = nodep;
        iterateChildren(nodep);
    }
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit RandomizeVisitor(AstNetlist* nodep)
        : m_inlineUniqueNames("__Vrandwith") {
        createRandomizeClassVars(nodep);
        iterate(nodep);
        nodep->foreach([&](AstConstraint* constrp) {
            VL_DO_DANGLING(pushDeletep(constrp->unlinkFrBack()), constrp);
        });
    }
    ~RandomizeVisitor() override = default;
};

//######################################################################
// Randomize method class functions

void V3Randomize::randomizeNetlist(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    {
        const RandomizeMarkVisitor markVisitor{nodep};
        RandomizeVisitor randomizeVisitor{nodep};
    }
    V3Global::dumpCheckGlobalTree("randomize", 0, dumpTreeEitherLevel() >= 3);
}

AstFunc* V3Randomize::newRandomizeFunc(VMemberMap& memberMap, AstClass* nodep,
                                       const std::string& name, bool allowVirtual) {
    AstFunc* funcp = VN_AS(memberMap.findMember(nodep, name), Func);
    if (!funcp) {
        v3Global.useRandomizeMethods(true);
        AstNodeDType* const dtypep
            = nodep->findBitDType(32, 32, VSigning::SIGNED);  // IEEE says int return of 0/1
        AstVar* const fvarp = new AstVar{nodep->fileline(), VVarType::MEMBER, name, dtypep};
        fvarp->lifetime(VLifetime::AUTOMATIC);
        fvarp->funcLocal(true);
        fvarp->funcReturn(true);
        fvarp->direction(VDirection::OUTPUT);
        nodep->addMembersp(funcp);
        funcp = new AstFunc{nodep->fileline(), name, nullptr, fvarp};
        funcp->dtypep(dtypep);
        funcp->classMethod(true);
        funcp->isVirtual(allowVirtual && nodep->isExtended());
        nodep->addMembersp(funcp);
        memberMap.insert(nodep, funcp);
        AstClass* const basep = nodep->baseMostClassp();
        basep->needRNG(true);
    }
    return funcp;
}

AstFunc* V3Randomize::newSRandomFunc(VMemberMap& memberMap, AstClass* nodep) {
    AstClass* const basep = nodep->baseMostClassp();
    AstFunc* funcp = VN_AS(memberMap.findMember(basep, "srandom"), Func);
    if (!funcp) {
        v3Global.useRandomizeMethods(true);
        AstNodeDType* const dtypep
            = basep->findBitDType(32, 32, VSigning::SIGNED);  // IEEE says argument 0/1
        AstVar* const ivarp = new AstVar{basep->fileline(), VVarType::MEMBER, "seed", dtypep};
        ivarp->lifetime(VLifetime::AUTOMATIC);
        ivarp->funcLocal(true);
        ivarp->direction(VDirection::INPUT);
        funcp = new AstFunc{basep->fileline(), "srandom", ivarp, nullptr};
        funcp->dtypep(basep->findVoidDType());
        funcp->classMethod(true);
        funcp->isVirtual(false);
        basep->addMembersp(funcp);
        memberMap.insert(nodep, funcp);
        funcp->addStmtsp(new AstCStmt{basep->fileline(), "__Vm_rng.srandom(seed);\n"});
        basep->needRNG(true);
    }
    return funcp;
}
