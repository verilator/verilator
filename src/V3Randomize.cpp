// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Generate randomization procedures
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
// Determines if a class is used with randomization

enum ClassRandom : uint8_t {
    NONE,  // randomize() is not called
    IS_RANDOMIZED,  // randomize() is called
    IS_RANDOMIZED_INLINE,  // randomize() with args is called
};

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
        AstClass* classp = VN_CAST(modp, Class);
        if (AstVarRef* const varrefp = VN_CAST(fromp, VarRef)) {
            receiverp = varrefp->varp();
            if (receiverp->isRand()) {
                fromp = nullptr;
                if (receiverp->lifetime().isStatic()) {
                    classp = VN_AS(varrefp->classOrPackagep(), Class);
                }
            }
        } else if (AstMemberSel* const memberSelp = VN_CAST(fromp, MemberSel)) {
            receiverp = memberSelp->varp();
            if (receiverp->isRand()) {
                fromp = memberSelp->fromp();
                classp = VN_AS(fromp->dtypep()->skipRefp(), ClassRefDType)->classp();
            }
        }
        UASSERT_OBJ(receiverp, fromp, "Unknown rand_mode() receiver");
        if (!receiverp->isRand()) {
            AstClassRefDType* const classRefDtp
                = VN_CAST(receiverp->dtypep()->skipRefp(), ClassRefDType);
            if (classRefDtp) classp = classRefDtp->classp();
        }
        return {receiverp, fromp, classp};
    }
};

// ######################################################################
// Stores info about a variable's rand_mode state/a constraint's constraint_mode state

union RandomizeMode final {
    // MEMBERS
    struct {
        bool usesMode : 1;  // Variable/constraint uses rand_mode/constraint_mode
        uint32_t index : 31;  // Index of var/constraint in rand_mode/constraint_mode vector
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
    //  AstNodeFTask::user2p()  -> AstNodeModule*. Pointer to containing module
    const VNUser1InUse m_inuser1;
    const VNUser2InUse m_inuser2;

    using DerivedSet = std::unordered_set<AstClass*>;
    using BaseToDerivedMap = std::unordered_map<const AstClass*, DerivedSet>;

    BaseToDerivedMap m_baseToDerivedMap;  // Mapping from base classes to classes that extend them
    AstClass* m_classp = nullptr;  // Current class
    AstNode* m_constraintExprGenp = nullptr;  // Current constraint or constraint if expression
    AstNodeModule* m_modp;  // Current module
    AstNodeStmt* m_stmtp = nullptr;  // Current statement
    std::set<AstNodeVarRef*> m_staticRefs;  // References to static variables under `with` clauses

    // METHODS
    void markMembers(const AstClass* nodep) {
        for (const AstClass* classp = nodep; classp;
             classp = classp->extendsp() ? classp->extendsp()->classp() : nullptr) {
            for (AstNode* memberp = classp->stmtsp(); memberp; memberp = memberp->nextp()) {
                AstVar* const varp = VN_CAST(memberp, Var);
                if (!varp) continue;
                // If member is randomizable and of class type, mark its class
                if (varp->rand().isRandomizable()) {
                    const AstNodeDType* const varDtypep = varp->dtypep()->skipRefp();
                    const AstClassRefDType* classRefp = VN_CAST(varDtypep, ClassRefDType);
                    if (!classRefp) {
                        const AstNodeDType* subDTypep = varDtypep->subDTypep();
                        if (subDTypep) subDTypep = subDTypep->skipRefp();
                        classRefp = VN_CAST(subDTypep, ClassRefDType);
                    }
                    if (classRefp) {
                        AstClass* const rclassp = classRefp->classp();
                        if (!rclassp->user1()) {
                            rclassp->user1(IS_RANDOMIZED);
                            markMembers(rclassp);
                            markDerived(rclassp);
                        }
                    }
                    // If the class is randomized inline, all members use rand mode
                    if (nodep->user1() == IS_RANDOMIZED_INLINE) {
                        RandomizeMode randMode = {};
                        randMode.usesMode = true;
                        varp->user1(randMode.asInt);
                    }
                }
            }
        }
    }
    void markDerived(const AstClass* nodep) {
        const auto it = m_baseToDerivedMap.find(nodep);
        if (it != m_baseToDerivedMap.end()) {
            for (auto* classp : it->second) {
                if (classp->user1() < nodep->user1()) {
                    classp->user1(nodep->user1());
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
            } else if (VN_IS(fromp, StructSel)) {
                nodep->v3warn(E_UNSUPPORTED,
                              "Unsupported: 'rand_mode()' on unpacked struct element");
                valid = false;
            } else if (VN_IS(fromp, Sel)) {
                nodep->v3error("Cannot call 'rand_mode()' on packed array element");
                valid = false;
            } else if (AstCMethodHard* const methodHardp = VN_CAST(fromp, CMethodHard)) {
                if (methodHardp->name() == "at" || methodHardp->name() == "atWrite") {
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
                } else if (randModeTarget.receiverp
                           && randModeTarget.receiverp->lifetime().isStatic()
                           && randModeTarget.receiverp->isRand()) {
                    nodep->v3warn(E_UNSUPPORTED, "Unsupported: 'rand_mode()' on static variable");
                    valid = false;
                } else if (randModeTarget.receiverp && randModeTarget.receiverp->isRand()) {
                    // Called on a rand member variable
                    RandomizeMode randMode = {};
                    randMode.usesMode = true;
                    randModeTarget.receiverp->user1(randMode.asInt);
                } else {
                    // Called on 'this' or a non-rand class instance
                    randModeTarget.classp->foreachMember([&](AstClass*, AstVar* varp) {
                        if (!varp->isRand()) return;
                        if (varp->lifetime().isStatic()) {
                            nodep->v3warn(E_UNSUPPORTED,
                                          "Unsupported: 'rand_mode()' on static variable: "
                                              << varp->prettyNameQ());
                        }
                        RandomizeMode randMode = {};
                        randMode.usesMode = true;
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

        if (nodep->name() == "constraint_mode") {
            bool valid = true;
            if (nodep->pinsp() && !VN_IS(nodep->backp(), StmtExpr)) {
                nodep->v3error(
                    "'constraint_mode()' with arguments cannot be called as a function");
                valid = false;
            } else if (!nodep->pinsp() && VN_IS(nodep->backp(), StmtExpr)) {
                nodep->v3warn(
                    IGNOREDRETURN,
                    "Ignoring return value of non-void function (IEEE 1800-2023 13.4.1)");
                valid = false;
            }
            AstConstraint* constrp = nullptr;
            AstClass* classp = m_classp;
            if (const AstMethodCall* const methodCallp = VN_CAST(nodep, MethodCall)) {
                if (const AstConstraintRef* const constrRefp
                    = VN_CAST(methodCallp->fromp(), ConstraintRef)) {
                    constrp = constrRefp->constrp();
                    if (constrRefp->fromp()) classp = VN_AS(constrRefp->classOrPackagep(), Class);
                    if (constrp->isStatic()) {
                        nodep->v3warn(E_UNSUPPORTED,
                                      "Unsupported: 'constraint_mode()' on static constraint");
                        valid = false;
                    }
                } else if (AstClassRefDType* classRefDtp
                           = VN_CAST(methodCallp->fromp()->dtypep()->skipRefp(), ClassRefDType)) {
                    classp = classRefDtp->classp();
                } else {
                    nodep->v3error("Cannot call 'constraint_mode()' on a non-class variable");
                    valid = false;
                }
            }
            if (!nodep->pinsp() && !constrp) {
                nodep->v3error("Cannot call 'constraint_mode()' as a function on a variable");
                valid = false;
            }
            if (valid) {
                RandomizeMode constraintMode = {};
                constraintMode.usesMode = true;
                if (constrp) {
                    constrp->user1(constraintMode.asInt);
                } else {
                    classp->foreachMember([=](AstClass*, AstConstraint* constrp) {
                        if (constrp->isStatic()) {
                            nodep->v3warn(E_UNSUPPORTED,
                                          "Unsupported: 'constraint_mode()' on static constraint: "
                                              << constrp->prettyNameQ());
                        }
                        constrp->user1(constraintMode.asInt);
                    });
                }
            } else {
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
            if (!classp->user1()) classp->user1(IS_RANDOMIZED);
            markMembers(classp);
        }
        for (AstNode* pinp = nodep->pinsp(); pinp; pinp = pinp->nextp()) {
            AstArg* const argp = VN_CAST(pinp, Arg);
            if (!argp) continue;
            classp->user1(IS_RANDOMIZED_INLINE);
            AstNodeExpr* exprp = argp->exprp();
            AstVar* fromVarp = nullptr;  // If nodep is a method call, this is its receiver
            if (AstMethodCall* methodCallp = VN_CAST(nodep, MethodCall)) {
                if (AstMemberSel* const memberSelp = VN_CAST(methodCallp->fromp(), MemberSel)) {
                    fromVarp = memberSelp->varp();
                } else {
                    AstVarRef* const varrefp = VN_AS(methodCallp->fromp(), VarRef);
                    fromVarp = varrefp->varp();
                }
            }
            while (exprp) {
                AstVar* randVarp = nullptr;
                if (AstMemberSel* const memberSelp = VN_CAST(exprp, MemberSel)) {
                    randVarp = memberSelp->varp();
                    exprp = memberSelp->fromp();
                } else {
                    AstVarRef* const varrefp = VN_AS(exprp, VarRef);
                    randVarp = varrefp->varp();
                    exprp = nullptr;
                }
                if (randVarp == fromVarp) break;
                UASSERT_OBJ(randVarp, nodep, "No rand variable found");
                AstNode* backp = randVarp;
                while (backp && !VN_IS(backp, Class)) backp = backp->backp();
                RandomizeMode randMode = {};
                randMode.usesMode = true;
                randVarp->user1(randMode.asInt);
                VN_AS(backp, Class)->user1(IS_RANDOMIZED_INLINE);
            }
        }
    }
    void visit(AstConstraintExpr* nodep) override {
        VL_RESTORER(m_constraintExprGenp);
        m_constraintExprGenp = nodep;
        iterateChildrenConst(nodep);
    }
    void visit(AstConstraintIf* nodep) override {
        {
            VL_RESTORER(m_constraintExprGenp);
            m_constraintExprGenp = nodep;
            iterateConst(nodep->condp());
        }
        iterateAndNextConstNull(nodep->thensp());
        iterateAndNextConstNull(nodep->elsesp());
    }
    void visit(AstNodeVarRef* nodep) override {
        if (!m_constraintExprGenp) return;

        if (nodep->varp()->lifetime().isStatic()) m_staticRefs.emplace(nodep);

        if (nodep->varp()->rand().isRandomizable()) nodep->user1(true);
    }
    void visit(AstMemberSel* nodep) override {
        if (!m_constraintExprGenp) return;
        iterateChildrenConst(nodep);
        // Member select are randomized when both object and member are marked as rand.
        // Variable references in with clause are converted to member selects and their from() is
        // of type AstLambdaArgRef. They are randomized too.
        const bool randObject = nodep->fromp()->user1() || VN_IS(nodep->fromp(), LambdaArgRef);
        nodep->user1(randObject && nodep->varp()->rand().isRandomizable());
    }
    void visit(AstNodeModule* nodep) override {
        VL_RESTORER(m_modp);
        m_modp = nodep;
        iterateChildrenConst(nodep);
    }
    void visit(AstNodeFTask* nodep) override {
        nodep->user2p(m_modp);
        iterateChildrenConst(nodep);
    }
    void visit(AstVar* nodep) override {
        nodep->user2p(m_modp);
        iterateChildrenConst(nodep);
    }

    void visit(AstNodeExpr* nodep) override {
        iterateChildrenConst(nodep);
        if (!m_constraintExprGenp) return;
        nodep->user1((nodep->op1p() && nodep->op1p()->user1())
                     || (nodep->op2p() && nodep->op2p()->user1())
                     || (nodep->op3p() && nodep->op3p()->user1())
                     || (nodep->op4p() && nodep->op4p()->user1()));
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
        fmt << "(bvand";
        for (AstNode* itemp = exprsp; itemp; itemp = itemp->nextp()) fmt << " %@";
        fmt << ')';
        return new AstSFormatF{fl, fmt.str(), false, exprsp};
    }

    AstNodeExpr* newSel(FileLine* fl, AstNodeExpr* arrayp, AstNodeExpr* idxp) {
        // similar to V3WidthSel.cpp
        AstNodeDType* const arrDtp = arrayp->unlinkFrBack()->dtypep();
        AstNodeExpr* selp = nullptr;
        if (VN_IS(arrDtp, QueueDType) || VN_IS(arrDtp, DynArrayDType))
            selp = new AstCMethodHard{fl, arrayp, "at", idxp};
        else if (VN_IS(arrDtp, UnpackArrayDType))
            selp = new AstArraySel{fl, arrayp, idxp};
        else if (VN_IS(arrDtp, AssocArrayDType))
            selp = new AstAssocSel{fl, arrayp, idxp};
        UASSERT_OBJ(selp, arrayp, "Selecting from non-array?");
        selp->dtypep(arrDtp->subDTypep());
        return selp;
    }

    // VISITORS
    void visit(AstNodeVarRef* nodep) override {
        AstVar* const varp = nodep->varp();
        if (varp->user4p()) {
            varp->user4p()->v3warn(
                CONSTRAINTIGN,
                "Size constraint combined with element constraint may not work correctly");
        }

        AstNodeModule* const classOrPackagep = nodep->classOrPackagep();
        const RandomizeMode randMode = {.asInt = varp->user1()};
        if (!randMode.usesMode && editFormat(nodep)) return;

        // In SMT just variable name, but we also ensure write_var for the variable
        const std::string smtName = nodep->name();  // Can be anything unique
        VNRelinker relinker;
        nodep->unlinkFrBack(&relinker);
        AstNodeExpr* exprp = new AstSFormatF{nodep->fileline(), smtName, false, nullptr};
        if (randMode.usesMode) {
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
            uint32_t dimension = 0;
            if (VN_IS(varp->dtypep(), UnpackArrayDType) || VN_IS(varp->dtypep(), DynArrayDType)
                || VN_IS(varp->dtypep(), QueueDType) || VN_IS(varp->dtypep(), AssocArrayDType)) {
                const std::pair<uint32_t, uint32_t> dims
                    = varp->dtypep()->dimensions(/*includeBasic=*/true);
                const uint32_t unpackedDimensions = dims.second;
                dimension = unpackedDimensions;
            }
            if (VN_IS(varp->dtypeSkipRefp(), StructDType)
                && !VN_AS(varp->dtypeSkipRefp(), StructDType)->packed()) {
                VN_AS(varp->dtypeSkipRefp(), StructDType)->markConstrainedRand(true);
                dimension = 1;
            }
            methodp->dtypeSetVoid();
            AstClass* const classp = VN_AS(varp->user2p(), Class);
            AstVarRef* const varRefp
                = new AstVarRef{varp->fileline(), classp, varp, VAccess::WRITE};
            varRefp->classOrPackagep(classOrPackagep);
            methodp->addPinsp(varRefp);
            AstNodeDType* tmpDtypep = varp->dtypep();
            while (VN_IS(tmpDtypep, UnpackArrayDType) || VN_IS(tmpDtypep, DynArrayDType)
                   || VN_IS(tmpDtypep, QueueDType) || VN_IS(tmpDtypep, AssocArrayDType))
                tmpDtypep = tmpDtypep->subDTypep();
            const size_t width = tmpDtypep->width();
            methodp->addPinsp(
                new AstConst{varp->dtypep()->fileline(), AstConst::Unsized64{}, width});
            AstNodeExpr* const varnamep
                = new AstCExpr{varp->fileline(), "\"" + smtName + "\"", varp->width()};
            varnamep->dtypep(varp->dtypep());
            methodp->addPinsp(varnamep);
            methodp->addPinsp(
                new AstConst{varp->dtypep()->fileline(), AstConst::Unsized64{}, dimension});
            if (randMode.usesMode) {
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
    void visit(AstReplicate* nodep) override {
        // Biop, but RHS is harmful
        if (editFormat(nodep)) return;
        editSMT(nodep, nodep->srcp());
    }
    void visit(AstSel* nodep) override {
        if (editFormat(nodep)) return;
        VNRelinker handle;
        AstNodeExpr* const widthp = nodep->widthp()->unlinkFrBack(&handle);
        FileLine* const fl = nodep->fileline();
        AstNodeExpr* const msbp
            = new AstSFormatF{fl, "%1d", false,
                              new AstAdd{fl, nodep->lsbp()->cloneTreePure(false),
                                         new AstSub{fl, widthp, new AstConst{fl, 1}}}};
        handle.relink(msbp);
        AstNodeExpr* const lsbp
            = new AstSFormatF{fl, "%1d", false, nodep->lsbp()->unlinkFrBack(&handle)};
        handle.relink(lsbp);

        editSMT(nodep, nodep->fromp(), lsbp, msbp);
    }
    void visit(AstStructSel* nodep) override {
        if (VN_IS(nodep->fromp()->dtypep()->skipRefp(), StructDType)) {
            AstNodeExpr* const fromp = nodep->fromp();
            if (VN_IS(fromp, StructSel)) {
                VN_AS(fromp->dtypep()->skipRefp(), StructDType)->markConstrainedRand(true);
            }
            AstMemberDType* memberp = VN_AS(fromp->dtypep()->skipRefp(), StructDType)->membersp();
            while (memberp) {
                if (memberp->name() == nodep->name()) {
                    memberp->markConstrainedRand(true);
                    break;
                } else
                    memberp = VN_CAST(memberp->nextp(), MemberDType);
            }
        }
        iterateChildren(nodep);
        if (editFormat(nodep)) return;
        FileLine* const fl = nodep->fileline();
        AstSFormatF* const newp
            = new AstSFormatF{fl, nodep->fromp()->name() + "." + nodep->name(), false, nullptr};
        nodep->replaceWith(newp);
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }
    void visit(AstAssocSel* nodep) override {
        if (editFormat(nodep)) return;
        FileLine* const fl = nodep->fileline();
        if (VN_IS(nodep->bitp(), CvtPackString) && VN_IS(nodep->bitp()->dtypep(), BasicDType)) {
            AstCvtPackString* const stringp = VN_AS(nodep->bitp(), CvtPackString);
            const size_t stringSize = VN_AS(stringp->lhsp(), Const)->width();
            if (stringSize > 128) {
                stringp->v3warn(
                    CONSTRAINTIGN,
                    "Unsupported: Constrained randomization of associative array keys of "
                        << stringSize << "bits, limit is 128 bits");
            }
            VNRelinker handle;
            AstNodeExpr* const idxp
                = new AstSFormatF{fl, "#x%32x", false, stringp->lhsp()->unlinkFrBack(&handle)};
            handle.relink(idxp);
            editSMT(nodep, nodep->fromp(), idxp);
        } else {
            if (VN_IS(nodep->bitp()->dtypep(), BasicDType)
                || (VN_IS(nodep->bitp()->dtypep(), StructDType)
                    && VN_AS(nodep->bitp()->dtypep(), StructDType)->packed())
                || VN_IS(nodep->bitp()->dtypep(), EnumDType)
                || VN_IS(nodep->bitp()->dtypep(), PackArrayDType)) {
                VNRelinker handle;
                const int actual_width = nodep->bitp()->width();
                std::string fmt;
                // Normalize to standard bit width
                if (actual_width <= 8) {
                    fmt = "#x%2x";
                } else if (actual_width <= 16) {
                    fmt = "#x%4x";
                } else {
                    fmt = "#x%" + std::to_string(VL_WORDS_I(actual_width) * 8) + "x";
                }

                AstNodeExpr* const idxp
                    = new AstSFormatF{fl, fmt, false, nodep->bitp()->unlinkFrBack(&handle)};
                handle.relink(idxp);
                editSMT(nodep, nodep->fromp(), idxp);
            } else {
                nodep->bitp()->v3error(
                    "Illegal non-integral expression or subexpression in random constraint."
                    " (IEEE 1800-2023 18.3)");
            }
        }
    }
    void visit(AstArraySel* nodep) override {
        if (editFormat(nodep)) return;
        FileLine* const fl = nodep->fileline();
        VNRelinker handle;
        AstNodeExpr* const indexp
            = new AstSFormatF{fl, "#x%8x", false, nodep->bitp()->unlinkFrBack(&handle)};
        handle.relink(indexp);
        editSMT(nodep, nodep->fromp(), indexp);
    }
    void visit(AstMemberSel* nodep) override {
        if (nodep->user1()) {
            nodep->v3warn(CONSTRAINTIGN, "Global constraints ignored (unsupported)");
        }
        editFormat(nodep);
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
    void visit(AstBegin* nodep) override {}
    void visit(AstConstraintForeach* nodep) override {
        // Convert to plain foreach
        FileLine* const fl = nodep->fileline();

        if (m_wantSingle) {
            AstNode* const itemp = editSingle(fl, nodep->stmtsp());
            AstNode* const cstmtp = new AstText{fl, "ret += \" \" + "};
            cstmtp->addNext(itemp);
            cstmtp->addNext(new AstText{fl, ";"});
            AstNode* const exprsp = new AstText{fl, "([&]{ std::string ret;"};
            exprsp->addNext(new AstBegin{
                fl, "",
                new AstForeach{fl, nodep->arrayp()->unlinkFrBack(), new AstCStmt{fl, cstmtp}},
                false, true});
            exprsp->addNext(
                new AstText{fl, "return ret.empty() ? \"#b1\" : \"(bvand\" + ret + \")\";})()"});
            AstNodeExpr* const newp = new AstCExpr{fl, exprsp};
            newp->dtypeSetString();
            nodep->replaceWith(new AstSFormatF{fl, "%@", false, newp});
        } else {
            iterateAndNextNull(nodep->stmtsp());
            nodep->replaceWith(
                new AstBegin{fl, "",
                             new AstForeach{fl, nodep->arrayp()->unlinkFrBack(),
                                            nodep->stmtsp()->unlinkFrBackWithNext()},
                             false, true});
        }
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
    }
    void visit(AstConstraintBefore* nodep) override {
        nodep->v3warn(CONSTRAINTIGN, "Constraint expression ignored (imperfect distribution)");
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
        FileLine* const fl = nodep->fileline();

        if (nodep->name() == "at" && nodep->fromp()->user1()) {
            iterateChildren(nodep);
            AstNodeExpr* const argsp
                = AstNode::addNext(nodep->fromp()->unlinkFrBack(), nodep->pinsp()->unlinkFrBack());
            AstSFormatF* const newp = new AstSFormatF{fl, "(select %@ %@)", false, argsp};
            nodep->replaceWith(newp);
            VL_DO_DANGLING(nodep->deleteTree(), nodep);
            return;
        }

        if (nodep->name() == "inside") {
            bool randArr = nodep->fromp()->user1();

            AstVar* const newVarp
                = new AstVar{fl, VVarType::BLOCKTEMP, "__Vinside", nodep->findSigned32DType()};
            AstNodeExpr* const idxRefp = new AstVarRef{nodep->fileline(), newVarp, VAccess::READ};
            AstSelLoopVars* const arrayp
                = new AstSelLoopVars{fl, nodep->fromp()->cloneTreePure(false), newVarp};
            AstNodeExpr* const selp = newSel(nodep->fileline(), nodep->fromp(), idxRefp);
            selp->user1(randArr);
            AstNode* const itemp = new AstEq{fl, selp, nodep->pinsp()->unlinkFrBack()};
            itemp->user1(true);
            AstNode* const cstmtp = new AstText{fl, "ret += \" \" + "};
            cstmtp->addNext(iterateSubtreeReturnEdits(itemp));
            cstmtp->addNext(new AstText{fl, ";"});
            AstNode* const exprsp = new AstText{fl, "([&]{ std::string ret;"};
            exprsp->addNext(new AstBegin{
                fl, "", new AstForeach{fl, arrayp, new AstCStmt{fl, cstmtp}}, false, true});
            exprsp->addNext(
                new AstText{fl, "return ret.empty() ? \"#b0\" : \"(bvor\" + ret + \")\";})()"});
            AstNodeExpr* const newp = new AstCExpr{fl, exprsp};
            newp->dtypeSetString();
            nodep->replaceWith(new AstSFormatF{fl, "%@", false, newp});
            VL_DO_DANGLING(nodep->deleteTree(), nodep);
            return;
        }

        nodep->v3warn(CONSTRAINTIGN,
                      "Unsupported: randomizing this expression, treating as state");
        nodep->user1(false);

        if (editFormat(nodep)) return;
        nodep->v3fatalSrc("Method not handled in constraints? " << nodep);
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
    AstClass* m_targetp;  // Module of inner context (for symbol lookup)
    std::map<const AstVar*, AstVar*> m_varCloneMap;  // Map original var nodes to their clones
    std::set<AstNode*> m_ignore;  // Nodes to ignore for capturing
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

    template <typename T_Node>
    void fixupClassOrPackage(AstNode* memberp, T_Node refp) {
        AstNodeModule* const declClassp = VN_AS(memberp->user2p(), NodeModule);
        if (declClassp != m_targetp) refp->classOrPackagep(declClassp);
    }

    template <typename T_Node>
    bool isReferenceToInnerMember(T_Node nodep) {
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
        AstNodeModule* const varModp = VN_AS(varRefp->varp()->user2p(), NodeModule);
        AstClass* const varClassp = VN_CAST(varModp, Class);
        AstClass* const callerClassp = VN_CAST(m_callerp, Class);

        const bool callerIsClass = callerClassp;
        const bool refIsXref = VN_IS(varRefp, VarXRef);
        const bool varIsFuncLocal = varRefp->varp()->isFuncLocal();
        const bool varHasAutomaticLifetime = varRefp->varp()->lifetime().isAutomatic();
        const bool varIsFieldOfCaller = AstClass::isClassExtendedFrom(callerClassp, varClassp);
        const bool varIsParam = varRefp->varp()->isParam();
        const bool varIsConstraintIterator
            = VN_IS(varRefp->varp()->firstAbovep(), SelLoopVars)
              && VN_IS(varRefp->varp()->firstAbovep()->firstAbovep(), ConstraintForeach);
        if (refIsXref) return CaptureMode::CAP_VALUE | CaptureMode::CAP_F_XREF;
        if (varIsConstraintIterator) return CaptureMode::CAP_NO;
        if (varIsFuncLocal && varHasAutomaticLifetime) return CaptureMode::CAP_VALUE;
        if (varIsParam) return CaptureMode::CAP_VALUE;
        // Static var in function (will not be inlined, because it's in class)
        if (callerIsClass && varIsFuncLocal) return CaptureMode::CAP_VALUE;
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
        AstClass* classp = VN_CAST(nodep->taskp()->user2p(), Class);
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
        if (AstTask* const taskp = VN_CAST(nodep->taskp(), Task))
            taskRefp = new AstTaskRef{nodep->fileline(), taskp, pinsp};
        else if (AstFunc* const taskp = VN_CAST(nodep->taskp(), Func))
            taskRefp = new AstFuncRef{nodep->fileline(), taskp, pinsp};
        UASSERT_OBJ(taskRefp, nodep, "Node needs to point to regular method");
        fixupClassOrPackage(nodep->taskp(), taskRefp);
        taskRefp->user1(nodep->user1());
        nodep->replaceWith(taskRefp);
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
        m_ignore.emplace(taskRefp);
    }
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    explicit CaptureVisitor(AstNode* const nodep, AstNodeModule* callerp, AstClass* const targetp)
        : m_argsp(nullptr)
        , m_callerp(callerp)
        , m_targetp(targetp) {
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
    //  AstVar::user2p()        -> AstNodeModule*. Pointer to containing module
    //  AstNodeFTask::user2p()  -> AstNodeModule*. Pointer to containing module
    //  AstEnumDType::user2()   -> AstVar*.  Pointer to table with enum values
    //  AstConstraint::user2p() -> AstTask*. Pointer to constraint setup procedure
    //  AstClass::user2p()      -> AstVar*.  Rand mode state variable
    //  AstVar::user3()         -> bool. Handled in constraints
    //  AstClass::user3p()      -> AstVar*.  Constrained randomizer variable
    //  AstConstraint::user3p() -> AstTask*. Pointer to resize procedure
    //  AstClass::user4p()      -> AstVar*.  Constraint mode state variable
    //  AstVar::user4p()        -> AstVar*.  Size variable for constrained queues
    // VNUser1InUse    m_inuser1;      (Allocated for use in RandomizeMarkVisitor)
    // VNUser2InUse    m_inuser2;      (Allocated for use in RandomizeMarkVisitor)
    const VNUser3InUse m_inuser3;
    const VNUser4InUse m_inuser4;

    // STATE
    V3UniqueNames m_inlineUniqueNames;  // For generating unique function names
    V3UniqueNames m_modeUniqueNames{"__Vmode"};  // For generating unique rand/constraint
                                                 // mode state var names
    VMemberMap m_memberMap;  // Member names cached for fast lookup
    AstNodeModule* m_modp = nullptr;  // Current module
    const AstNodeFTask* m_ftaskp = nullptr;  // Current function/task
    AstNodeStmt* m_stmtp = nullptr;  // Current statement
    AstDynArrayDType* m_dynarrayDtp = nullptr;  // Dynamic array type (for rand mode)
    size_t m_enumValueTabCount = 0;  // Number of tables with enum values created
    int m_randCaseNum = 0;  // Randcase number within a module for var naming
    std::map<std::string, AstCDType*> m_randcDtypes;  // RandC data type deduplication
    AstConstraint* m_constraintp = nullptr;  // Current constraint

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
        static const char* const name = "__Vsetup_constraints";
        AstTask* setupAllTaskp = VN_AS(m_memberMap.findMember(classp, name), Task);
        if (setupAllTaskp) return setupAllTaskp;
        setupAllTaskp = new AstTask{classp->fileline(), "__Vsetup_constraints", nullptr};
        setupAllTaskp->classMethod(true);
        setupAllTaskp->isVirtual(true);
        classp->addMembersp(setupAllTaskp);
        m_memberMap.insert(classp, setupAllTaskp);
        return setupAllTaskp;
    }
    AstTask* getCreateAggrResizeTask(AstClass* const classp) {
        static const char* const name = "__Vresize_constrained_arrays";
        AstTask* resizeTaskp = VN_AS(m_memberMap.findMember(classp, name), Task);
        if (resizeTaskp) return resizeTaskp;
        resizeTaskp = new AstTask{classp->fileline(), name, nullptr};
        resizeTaskp->classMethod(true);
        resizeTaskp->isVirtual(true);
        classp->addMembersp(resizeTaskp);
        m_memberMap.insert(classp, resizeTaskp);
        return resizeTaskp;
    }
    AstVar* getCreateRandModeVar(AstClass* const classp) {
        if (classp->user2p()) return VN_AS(classp->user2p(), Var);
        if (AstClassExtends* const extendsp = classp->extendsp()) {
            return getCreateRandModeVar(extendsp->classp());
        }
        AstVar* const randModeVarp = createModeVar(classp, "__Vrandmode");
        classp->user2p(randModeVarp);
        return randModeVarp;
    }
    static AstVar* getRandModeVar(AstClass* const classp) {
        if (classp->user2p()) return VN_AS(classp->user2p(), Var);
        if (AstClassExtends* const extendsp = classp->extendsp()) {
            return getRandModeVar(extendsp->classp());
        }
        return nullptr;
    }
    AstVar* getCreateConstraintModeVar(AstClass* const classp) {
        if (classp->user4p()) return VN_AS(classp->user4p(), Var);
        if (AstClassExtends* const extendsp = classp->extendsp()) {
            return getCreateConstraintModeVar(extendsp->classp());
        }
        AstVar* const constraintModeVarp = createModeVar(classp, "__Vconstraintmode");
        classp->user4p(constraintModeVarp);
        return constraintModeVarp;
    }
    static AstVar* getConstraintModeVar(AstClass* const classp) {
        if (classp->user4p()) return VN_AS(classp->user4p(), Var);
        if (AstClassExtends* const extendsp = classp->extendsp()) {
            return getConstraintModeVar(extendsp->classp());
        }
        return nullptr;
    }
    AstVar* createModeVar(AstClass* const classp, const char* const name) {
        FileLine* const fl = classp->fileline();
        if (!m_dynarrayDtp) {
            m_dynarrayDtp = new AstDynArrayDType{
                fl, v3Global.rootp()->typeTablep()->findBitDType()->dtypep()};
            m_dynarrayDtp->dtypep(m_dynarrayDtp);
            v3Global.rootp()->typeTablep()->addTypesp(m_dynarrayDtp);
        }
        AstVar* const modeVarp = new AstVar{fl, VVarType::MODULETEMP, name, m_dynarrayDtp};
        modeVarp->user2p(classp);
        classp->addStmtsp(modeVarp);
        return modeVarp;
    }
    static void addSetRandMode(AstNodeFTask* const ftaskp, AstVar* const genp,
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
        netlistp->foreach([this](AstClass* const classp) {
            bool hasConstraints = false;
            uint32_t randModeCount = 0;
            uint32_t constraintModeCount = 0;
            classp->foreachMember([&](AstClass*, AstNode* memberp) {
                // SystemVerilog only allows single inheritance, so we don't need to worry about
                // index overlap. If the index > 0, it's already been set.
                if (VN_IS(memberp, Constraint)) {
                    hasConstraints = true;
                    RandomizeMode constraintMode = {.asInt = memberp->user1()};
                    if (!constraintMode.usesMode) return;
                    if (constraintMode.index == 0) {
                        constraintMode.index = constraintModeCount++;
                        memberp->user1(constraintMode.asInt);
                    } else {
                        constraintModeCount = constraintMode.index + 1;
                    }
                } else if (VN_IS(memberp, Var)) {
                    RandomizeMode randMode = {.asInt = memberp->user1()};
                    if (!randMode.usesMode) return;
                    if (randMode.index == 0) {
                        randMode.index = randModeCount++;
                        memberp->user1(randMode.asInt);
                    } else {
                        randModeCount = randMode.index + 1;
                    }
                }
            });
            if (hasConstraints) createRandomGenerator(classp);
            if (randModeCount > 0) {
                AstVar* const randModeVarp = getCreateRandModeVar(classp);
                makeModeInit(randModeVarp, classp, randModeCount);
            }
            if (constraintModeCount > 0) {
                AstVar* const constraintModeVarp = getCreateConstraintModeVar(classp);
                makeModeInit(constraintModeVarp, classp, constraintModeCount);
            }
        });
    }
    void makeModeInit(AstVar* modeVarp, AstClass* classp, uint32_t modeCount) {
        AstNodeModule* const modeVarModp = VN_AS(modeVarp->user2p(), NodeModule);
        FileLine* fl = modeVarp->fileline();
        AstCMethodHard* const dynarrayNewp
            = new AstCMethodHard{fl, new AstVarRef{fl, modeVarModp, modeVarp, VAccess::WRITE},
                                 "resize", new AstConst{fl, modeCount}};
        dynarrayNewp->dtypeSetVoid();
        AstNodeFTask* const newp = VN_AS(m_memberMap.findMember(classp, "new"), NodeFTask);
        UASSERT_OBJ(newp, classp, "No new() in class");
        newp->addStmtsp(dynarrayNewp->makeStmt());
        newp->addStmtsp(makeModeSetLoop(fl,
                                        new AstVarRef{fl, modeVarModp, modeVarp, VAccess::WRITE},
                                        new AstConst{fl, 1}, true));
    }
    static AstNode* makeModeSetLoop(FileLine* const fl, AstNodeExpr* const lhsp,
                                    AstNodeExpr* const rhsp, bool inTask) {
        AstVar* const iterVarp = new AstVar{fl, VVarType::BLOCKTEMP, "i", lhsp->findUInt32DType()};
        iterVarp->funcLocal(inTask);
        iterVarp->lifetime(VLifetime::AUTOMATIC);
        AstCMethodHard* const sizep = new AstCMethodHard{fl, lhsp, "size", nullptr};
        sizep->dtypeSetUInt32();
        AstCMethodHard* const setp = new AstCMethodHard{
            fl, lhsp->cloneTree(false), "atWrite", new AstVarRef{fl, iterVarp, VAccess::READ}};
        setp->dtypeSetUInt32();
        AstNode* const stmtsp = iterVarp;
        stmtsp->addNext(
            new AstAssign{fl, new AstVarRef{fl, iterVarp, VAccess::WRITE}, new AstConst{fl, 0}});
        stmtsp->addNext(
            new AstWhile{fl, new AstLt{fl, new AstVarRef{fl, iterVarp, VAccess::READ}, sizep},
                         new AstAssign{fl, setp, rhsp},
                         new AstAssign{fl, new AstVarRef{fl, iterVarp, VAccess::WRITE},
                                       new AstAdd{fl, new AstConst{fl, 1},
                                                  new AstVarRef{fl, iterVarp, VAccess::READ}}}});
        return new AstBegin{fl, "", stmtsp, false, true};
    }
    static AstNodeStmt* wrapIfRandMode(AstClass* classp, AstVar* const varp, AstNodeStmt* stmtp) {
        const RandomizeMode rmode = {.asInt = varp->user1()};
        return VN_AS(wrapIfMode(rmode, getRandModeVar(classp), stmtp), NodeStmt);
    }
    static AstNode* wrapIfConstraintMode(AstClass* classp, AstConstraint* const constrp,
                                         AstNode* stmtp) {
        const RandomizeMode rmode = {.asInt = constrp->user1()};
        return wrapIfMode(rmode, getConstraintModeVar(classp), stmtp);
    }
    static AstNode* wrapIfMode(const RandomizeMode mode, AstVar* modeVarp, AstNode* stmtp) {
        FileLine* const fl = stmtp->fileline();
        if (mode.usesMode) {
            AstCMethodHard* const atp = new AstCMethodHard{
                fl, new AstVarRef{fl, VN_AS(modeVarp->user2p(), Class), modeVarp, VAccess::READ},
                "at", new AstConst{fl, mode.index}};
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
                varp->rand(VRandAttr::RAND);
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
    AstNodeStmt* createArrayForeachLoop(FileLine* const fl, AstNodeDType* const dtypep,
                                        AstNodeExpr* exprp, AstVar* const outputVarp) {
        V3UniqueNames* uniqueNamep = new V3UniqueNames{"__Vrandarr"};
        AstNodeDType* tempDTypep = dtypep;
        AstVar* randLoopIndxp = nullptr;
        AstNodeStmt* stmtsp = nullptr;
        auto createLoopIndex = [&](AstNodeDType* tempDTypep) {
            if (VN_IS(tempDTypep, AssocArrayDType)) {
                return new AstVar{fl, VVarType::VAR, uniqueNamep->get(""),
                                  VN_AS(tempDTypep, AssocArrayDType)->keyDTypep()};
            }
            return new AstVar{fl, VVarType::VAR, uniqueNamep->get(""),
                              dtypep->findBasicDType(VBasicDTypeKwd::UINT32)};
        };
        auto createForeachLoop = [&](AstNodeExpr* tempElementp, AstVar* randLoopIndxp) {
            AstSelLoopVars* const randLoopVarp
                = new AstSelLoopVars{fl, exprp->cloneTree(false), randLoopIndxp};
            return new AstForeach{fl, randLoopVarp,
                                  newRandStmtsp(fl, tempElementp, nullptr, outputVarp)};
        };
        AstNodeExpr* tempElementp = nullptr;
        while (VN_IS(tempDTypep, DynArrayDType) || VN_IS(tempDTypep, UnpackArrayDType)
               || VN_IS(tempDTypep, AssocArrayDType) || VN_IS(tempDTypep, QueueDType)) {
            AstVar* const newRandLoopIndxp = createLoopIndex(tempDTypep);
            randLoopIndxp = AstNode::addNext(randLoopIndxp, newRandLoopIndxp);
            AstNodeExpr* tempExprp = tempElementp ? tempElementp : exprp;
            AstVarRef* tempRefp = new AstVarRef{fl, newRandLoopIndxp, VAccess::READ};
            if (VN_IS(tempDTypep, DynArrayDType))
                tempElementp = new AstCMethodHard{fl, tempExprp, "atWrite", tempRefp};
            else if (VN_IS(tempDTypep, UnpackArrayDType)) {
                AstNodeArrayDType* const aryDTypep = VN_CAST(tempDTypep, NodeArrayDType);
                // Adjust the bitp to ensure it covers all possible indices
                tempElementp = new AstArraySel{
                    fl, tempExprp,
                    new AstSel{
                        fl,
                        new AstSub{fl, tempRefp,
                                   new AstConst{fl, static_cast<uint32_t>(aryDTypep->lo())}},
                        new AstConst{fl, 0},
                        new AstConst{
                            fl, static_cast<uint32_t>(V3Number::log2b(aryDTypep->hi()) + 1)}}};
            } else if (VN_IS(tempDTypep, AssocArrayDType))
                tempElementp = new AstAssocSel{fl, tempExprp, tempRefp};
            else if (VN_IS(tempDTypep, QueueDType))
                tempElementp = new AstCMethodHard{fl, tempExprp, "atWriteAppend", tempRefp};
            tempElementp->dtypep(tempDTypep->subDTypep());
            tempDTypep = tempDTypep->virtRefDTypep();
        }
        stmtsp = createForeachLoop(tempElementp, randLoopIndxp);
        return stmtsp;
    }
    AstNodeStmt* newRandStmtsp(FileLine* fl, AstNodeExpr* exprp, AstVar* randcVarp,
                               AstVar* const outputVarp, int offset = 0,
                               AstMemberDType* memberp = nullptr) {
        AstNodeDType* const memberDtp
            = memberp ? memberp->subDTypep()->skipRefp() : exprp->dtypep()->skipRefp();
        if (const auto* const structDtp = VN_CAST(memberDtp, StructDType)) {
            AstNodeStmt* stmtsp = nullptr;
            if (structDtp->packed()) offset += memberp ? memberp->lsb() : 0;
            for (AstMemberDType* smemberp = structDtp->membersp(); smemberp;
                 smemberp = VN_AS(smemberp->nextp(), MemberDType)) {
                AstNodeStmt* randp = nullptr;
                if (structDtp->packed()) {
                    randp = newRandStmtsp(fl, stmtsp ? exprp->cloneTree(false) : exprp, nullptr,
                                          outputVarp, offset, smemberp);
                } else {
                    AstStructSel* structSelp
                        = new AstStructSel{fl, exprp->cloneTree(false), smemberp->name()};
                    structSelp->dtypep(smemberp->childDTypep());
                    if (!structSelp->dtypep()) structSelp->dtypep(smemberp->subDTypep());
                    randp = newRandStmtsp(fl, structSelp, nullptr, outputVarp);
                }
                stmtsp = stmtsp ? stmtsp->addNext(randp) : randp;
            }
            return stmtsp;
        } else if (const auto* const unionDtp = VN_CAST(memberDtp, UnionDType)) {
            if (!unionDtp->packed()) {
                unionDtp->v3error("Unpacked unions shall not be declared as rand or randc."
                                  " (IEEE 1800-2023 18.4)");
                return nullptr;
            }
            AstMemberDType* const firstMemberp = unionDtp->membersp();
            return newRandStmtsp(fl, exprp, nullptr, outputVarp, offset, firstMemberp);
        } else if (const AstClassRefDType* const classRefDtp = VN_CAST(memberDtp, ClassRefDType)) {
            AstFunc* const memberFuncp
                = V3Randomize::newRandomizeFunc(m_memberMap, classRefDtp->classp());
            AstMethodCall* const callp = new AstMethodCall{fl, exprp, "randomize", nullptr};
            callp->taskp(memberFuncp);
            callp->dtypeFrom(memberFuncp);
            AstAssign* const assignp = new AstAssign{
                fl, new AstVarRef{fl, outputVarp, VAccess::WRITE},
                new AstAnd{fl, new AstVarRef{fl, outputVarp, VAccess::READ}, callp}};
            return new AstIf{
                fl, new AstNeq{fl, exprp->cloneTree(false), new AstConst{fl, AstConst::Null{}}},
                assignp};
        } else if (AstDynArrayDType* const dynarrayDtp = VN_CAST(memberDtp, DynArrayDType)) {
            return createArrayForeachLoop(fl, dynarrayDtp, exprp, outputVarp);
        } else if (AstQueueDType* const queueDtp = VN_CAST(memberDtp, QueueDType)) {
            return createArrayForeachLoop(fl, queueDtp, exprp, outputVarp);
        } else if (AstUnpackArrayDType* const unpackarrayDtp
                   = VN_CAST(memberDtp, UnpackArrayDType)) {
            return createArrayForeachLoop(fl, unpackarrayDtp, exprp, outputVarp);
        } else if (AstAssocArrayDType* const assocarrayDtp = VN_CAST(memberDtp, AssocArrayDType)) {
            return createArrayForeachLoop(fl, assocarrayDtp, exprp, outputVarp);
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
            return wrapIfRandMode(VN_AS(m_modp, Class), varp, assignp);
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
            AstTaskRef* const callp = new AstTaskRef{userFuncp->fileline(), userFuncp, nullptr};
            funcp->addStmtsp(callp->makeStmt());
        }
    }
    AstTask* newSetupConstraintTask(AstClass* const nodep, const std::string& name) {
        AstTask* const taskp = new AstTask{nodep->fileline(), name + "_setup_constraint", nullptr};
        taskp->classMethod(true);
        nodep->addMembersp(taskp);
        return taskp;
    }
    AstTask* newResizeConstrainedArrayTask(AstClass* const nodep, const std::string& name) {
        AstTask* const taskp
            = new AstTask{nodep->fileline(), name + "_resize_constrained_array", nullptr};
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
    AstVar* getVarFromRef(AstNodeExpr* const exprp) {
        if (AstMemberSel* const memberSelp = VN_CAST(exprp, MemberSel)) {
            return memberSelp->varp();
        } else if (AstVarRef* const varrefp = VN_CAST(exprp, VarRef)) {
            return varrefp->varp();
        }
        exprp->v3fatalSrc("Not a MemberSel nor VarRef");
        return nullptr;  // LCOV_EXCL_LINE
    }
    AstNodeExpr* makeSiblingRefp(AstNodeExpr* const exprp, AstVar* const varp,
                                 const VAccess access) {
        if (AstMemberSel* const memberSelp = VN_CAST(exprp, MemberSel)) {
            return new AstMemberSel{exprp->fileline(), memberSelp->fromp()->cloneTree(false),
                                    varp};
        }
        UASSERT_OBJ(VN_IS(exprp, VarRef), exprp, "Should be a VarRef");
        return new AstVarRef{exprp->fileline(), VN_AS(varp->user2p(), Class), varp, access};
    }
    AstNodeExpr* getFromp(AstNodeExpr* const exprp) {
        if (AstMemberSel* const memberSelp = VN_CAST(exprp, MemberSel)) {
            return memberSelp->fromp();
        } else if (AstMethodCall* const methodCallp = VN_CAST(exprp, MethodCall)) {
            return methodCallp->fromp();
        }
        return nullptr;
    }
    AstVar* makeTmpRandModeVar(AstNodeExpr* siblingExprp, AstVar* randModeVarp,
                               AstNode*& storeStmtspr, AstNodeStmt*& restoreStmtspr) {
        FileLine* const fl = randModeVarp->fileline();
        AstVar* const randModeTmpVarp = new AstVar{
            fl, VVarType::BLOCKTEMP, m_modeUniqueNames.get(randModeVarp), randModeVarp->dtypep()};
        randModeTmpVarp->funcLocal(m_ftaskp);
        randModeTmpVarp->lifetime(VLifetime::AUTOMATIC);
        storeStmtspr = AstNode::addNext(
            storeStmtspr,
            new AstAssign{fl, new AstVarRef{fl, randModeTmpVarp, VAccess::WRITE},
                          makeSiblingRefp(siblingExprp, randModeVarp, VAccess::READ)});
        storeStmtspr = AstNode::addNext(
            storeStmtspr,
            makeModeSetLoop(fl, makeSiblingRefp(siblingExprp, randModeVarp, VAccess::WRITE),
                            new AstConst{fl, 0}, m_ftaskp));
        restoreStmtspr = AstNode::addNext(
            restoreStmtspr,
            new AstAssign{fl, makeSiblingRefp(siblingExprp, randModeVarp, VAccess::WRITE),
                          new AstVarRef{fl, randModeTmpVarp, VAccess::READ}});
        return randModeTmpVarp;
    }
    // Returns the common prefix of two hierarchical accesses, or nullptr if there is none
    // e.g. a.b.c and a.b.d -> a.b
    AstNodeExpr* sliceToCommonPrefix(AstNodeExpr* thisp, AstNodeExpr* otherp) {
        static std::vector<AstNodeExpr*> thisHier, otherHier;  // Keep around
                                                               // to avoid reallocations
        thisHier.clear();
        otherHier.clear();
        while (thisp) {
            thisHier.push_back(thisp);
            thisp = getFromp(thisp);
        }
        while (otherp) {
            otherHier.push_back(otherp);
            otherp = getFromp(otherp);
        }
        AstNodeExpr* commonp = nullptr;
        for (auto thisIt = thisHier.rbegin(), otherIt = otherHier.rbegin();
             thisIt != thisHier.rend() && otherIt != otherHier.rend(); ++thisIt, ++otherIt) {
            if ((*thisIt)->type() != (*otherIt)->type()) break;
            if (AstMemberSel* memberSelp = VN_CAST(*thisIt, MemberSel)) {
                AstMemberSel* otherMemberSelp = VN_AS(*otherIt, MemberSel);
                if (memberSelp->varp() == otherMemberSelp->varp()) {
                    commonp = memberSelp;
                    continue;
                }
            } else if (AstMethodCall* thisMethodCallp = VN_CAST(*thisIt, MethodCall)) {
                AstMethodCall* otherMethodCallp = VN_AS(*otherIt, MethodCall);
                if (thisMethodCallp->taskp() == otherMethodCallp->taskp()) {
                    commonp = thisMethodCallp;
                    continue;
                }
            } else if (AstVarRef* firstVarRefp = VN_CAST(*thisIt, VarRef)) {
                AstVarRef* secondVarRefp = VN_AS(*otherIt, VarRef);
                if (firstVarRefp->varp() == secondVarRefp->varp()) {
                    commonp = firstVarRefp;
                    continue;
                }
            }
            break;
        }
        return commonp;
    }

    void addBasicRandomizeBody(AstFunc* const basicRandomizep, AstClass* const nodep,
                               AstVar* randModeVarp) {
        FileLine* const fl = nodep->fileline();
        AstVar* const basicFvarp = VN_AS(basicRandomizep->fvarp(), Var);
        AstVarRef* const basicFvarRefp = new AstVarRef{fl, basicFvarp, VAccess::WRITE};
        AstConst* const beginBasicValp = new AstConst{fl, AstConst::WidthedValue{}, 32, 1};
        basicRandomizep->addStmtsp(new AstAssign{fl, basicFvarRefp, beginBasicValp});
        AstNodeFTask* const newp = VN_AS(m_memberMap.findMember(nodep, "new"), NodeFTask);
        UASSERT_OBJ(newp, nodep, "No new() in class");
        nodep->foreachMember([&](AstClass* classp, AstVar* memberVarp) {
            if (!memberVarp->rand().isRandomizable()) return;
            const RandomizeMode randMode = {.asInt = memberVarp->user1()};
            if (randMode.usesMode
                && !memberVarp->rand().isRand()) {  // Not randomizable by default
                AstCMethodHard* setp = new AstCMethodHard{
                    nodep->fileline(),
                    new AstVarRef{fl, VN_AS(randModeVarp->user2p(), NodeModule), randModeVarp,
                                  VAccess::WRITE},
                    "atWrite", new AstConst{nodep->fileline(), randMode.index}};
                setp->dtypeSetUInt32();
                newp->addStmtsp(new AstAssign{fl, setp, new AstConst{fl, 0}});
            }
            if (memberVarp->user3()) return;  // Handled in constraints
            const AstNodeDType* const dtypep = memberVarp->dtypep()->skipRefp();
            if (const AstClassRefDType* const classRefp = VN_CAST(dtypep, ClassRefDType)) {
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
                basicRandomizep->addStmtsp(wrapIfRandMode(nodep, memberVarp, assignIfNotNullp));
            } else {
                AstVar* const randcVarp = newRandcVarsp(memberVarp);
                AstVarRef* const refp = new AstVarRef{fl, classp, memberVarp, VAccess::WRITE};
                AstNodeStmt* const stmtp = newRandStmtsp(fl, refp, randcVarp, basicFvarp);
                basicRandomizep->addStmtsp(new AstBegin{fl, "", stmtp});
            }
        });
    }

    // Creates a lvalue reference to the randomize mode var. Called by visit(AstNodeFTaskRef*)
    AstNodeExpr* makeModeAssignLhs(FileLine* const fl, AstClass* const classp,
                                   AstNodeExpr* const fromp, AstVar* const modeVarp) {
        if (classp == m_modp) {
            // Called on 'this' or a member of 'this'
            return new AstVarRef{fl, VN_AS(modeVarp->user2p(), NodeModule), modeVarp,
                                 VAccess::WRITE};
        } else {
            AstMemberSel* const memberselp = new AstMemberSel{fl, fromp->unlinkFrBack(), modeVarp};
            memberselp->foreach([](AstVarRef* varrefp) { varrefp->access(VAccess::WRITE); });
            return memberselp;
        }
    }
    // Replace the node with an assignment to the mode variable. Called by visit(AstNodeFTaskRef*)
    void replaceWithModeAssign(AstNodeFTaskRef* const ftaskRefp, AstNode* const receiverp,
                               AstNodeExpr* const lhsp) {
        FileLine* const fl = ftaskRefp->fileline();
        if (ftaskRefp->pinsp()) {
            UASSERT_OBJ(VN_IS(ftaskRefp->backp(), StmtExpr), ftaskRefp, "Should be a statement");
            AstNodeExpr* const rhsp = VN_AS(ftaskRefp->pinsp(), Arg)->exprp()->unlinkFrBack();
            if (receiverp) {
                // Called on a rand member variable/constraint. Set the variable/constraint's
                // mode
                const RandomizeMode rmode = {.asInt = receiverp->user1()};
                UASSERT_OBJ(rmode.usesMode, ftaskRefp, "Failed to set usesMode");
                AstCMethodHard* const setp
                    = new AstCMethodHard{fl, lhsp, "atWrite", new AstConst{fl, rmode.index}};
                setp->dtypeSetUInt32();
                m_stmtp->replaceWith(new AstAssign{fl, setp, rhsp});
            } else {
                // For rand_mode: Called on 'this' or a non-rand class instance.
                // For constraint_mode: Called on a class instance.
                // Set the rand mode of all members
                m_stmtp->replaceWith(makeModeSetLoop(fl, lhsp, rhsp, m_ftaskp));
            }
            pushDeletep(m_stmtp);
        } else {
            UASSERT_OBJ(receiverp, ftaskRefp, "Should have receiver");
            const RandomizeMode rmode = {.asInt = receiverp->user1()};
            UASSERT_OBJ(rmode.usesMode, ftaskRefp, "Failed to set usesMode");
            AstCMethodHard* const setp
                = new AstCMethodHard{fl, lhsp, "atWrite", new AstConst{fl, rmode.index}};
            setp->dtypeSetUInt32();
            ftaskRefp->replaceWith(setp);
            VL_DO_DANGLING(pushDeletep(ftaskRefp), ftaskRefp);
        }
    };

    // Handle inline random variable control. After this, the randomize() call has no args
    void handleRandomizeArgs(AstNodeFTaskRef* const nodep) {
        if (!nodep->pinsp()) return;
        // This assumes arguments to always be a member sel from nodep->fromp(), if applicable
        // e.g. LinkDot transformed a.randomize(b, a.c) -> a.randomize(a.b, a.c)
        // Merge pins with common prefixes so that setting their rand mode doesn't interfere
        // with each other.
        // e.g. a.randomize(a.b, a.c, a.b.d) -> a.randomize(a.b, a.c)
        for (AstNode *pinp = nodep->pinsp(), *nextp = nullptr; pinp; pinp = nextp) {
            nextp = pinp->nextp();
            AstArg* const argp = VN_CAST(pinp, Arg);
            if (!argp) continue;
            AstNode* otherNextp = nullptr;
            for (AstNode* otherPinp = nextp; otherPinp; otherPinp = otherNextp) {
                otherNextp = otherPinp->nextp();
                AstArg* const otherArgp = VN_CAST(otherPinp, Arg);
                if (!otherArgp) continue;
                if (AstNodeExpr* const prefixp
                    = sliceToCommonPrefix(argp->exprp(), otherArgp->exprp())) {
                    if (prefixp == argp->exprp()) {
                        if (nextp == otherPinp) nextp = nextp->nextp();
                        VL_DO_DANGLING(otherPinp->unlinkFrBack()->deleteTree(), otherPinp);
                        continue;
                    }
                }
                if (AstNodeExpr* const prefixp
                    = sliceToCommonPrefix(otherArgp->exprp(), argp->exprp())) {
                    if (prefixp == otherArgp->exprp()) {
                        VL_DO_DANGLING(pinp->unlinkFrBack()->deleteTree(), pinp);
                        break;
                    }
                }
            }
        }
        // Construct temp vars, and store and restore statements
        std::set<AstVar*> savedRandModeVarps;
        AstVar* tmpVarps = nullptr;
        AstNode* storeStmtsp = nullptr;
        AstNode* setStmtsp = nullptr;
        AstNodeStmt* restoreStmtsp = nullptr;
        for (AstNode *pinp = nodep->pinsp(), *nextp = nullptr; pinp; pinp = nextp) {
            nextp = pinp->nextp();
            AstArg* const argp = VN_CAST(pinp, Arg);
            if (!argp) continue;
            AstNodeExpr* exprp = VN_AS(pinp, Arg)->exprp();
            AstNodeExpr* const commonPrefixp = sliceToCommonPrefix(exprp, nodep);
            UASSERT_OBJ(commonPrefixp != exprp, nodep,
                        "Common prefix should be different than pin");
            FileLine* const fl = argp->fileline();
            while (exprp) {
                if (commonPrefixp == exprp) break;
                AstVar* const randVarp = getVarFromRef(exprp);
                AstClass* const classp = VN_AS(randVarp->user2p(), Class);
                AstVar* const randModeVarp = getRandModeVar(classp);
                if (savedRandModeVarps.find(randModeVarp) == savedRandModeVarps.end()) {
                    AstVar* const randModeTmpVarp
                        = makeTmpRandModeVar(exprp, randModeVarp, storeStmtsp, restoreStmtsp);
                    savedRandModeVarps.insert(randModeVarp);
                    tmpVarps = AstNode::addNext(tmpVarps, randModeTmpVarp);
                }
                const RandomizeMode randMode = {.asInt = randVarp->user1()};
                AstCMethodHard* setp
                    = new AstCMethodHard{fl, makeSiblingRefp(exprp, randModeVarp, VAccess::WRITE),
                                         "atWrite", new AstConst{fl, randMode.index}};
                setp->dtypeSetUInt32();
                setStmtsp
                    = AstNode::addNext(setStmtsp, new AstAssign{fl, setp, new AstConst{fl, 1}});
                exprp = getFromp(exprp);
            }
            pinp->unlinkFrBack()->deleteTree();
        }
        if (tmpVarps) {
            UASSERT_OBJ(storeStmtsp && setStmtsp && restoreStmtsp, nodep, "Should have stmts");
            VNRelinker relinker;
            m_stmtp->unlinkFrBack(&relinker);
            AstNode* const stmtsp = tmpVarps;
            stmtsp->addNext(storeStmtsp);
            stmtsp->addNext(setStmtsp);
            stmtsp->addNext(m_stmtp);
            stmtsp->addNext(restoreStmtsp);
            relinker.relink(new AstBegin{nodep->fileline(), "", stmtsp, false, true});
        }
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
        nodep->baseMostClassp()->needRNG(true);
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
                    = new AstTaskRef{constrp->fileline(), taskp, nullptr};
                setupTaskRefp->classOrPackagep(classp);

                AstTask* const setupAllTaskp = getCreateConstraintSetupFunc(nodep);

                setupAllTaskp->addStmtsp(setupTaskRefp->makeStmt());

                if (AstTask* const resizeTaskp = VN_CAST(constrp->user3p(), Task)) {
                    AstTask* const resizeAllTaskp = getCreateAggrResizeTask(nodep);
                    AstTaskRef* const resizeTaskRefp
                        = new AstTaskRef{constrp->fileline(), resizeTaskp, nullptr};
                    resizeTaskRefp->classOrPackagep(classp);
                    resizeAllTaskp->addStmtsp(resizeTaskRefp->makeStmt());
                }

                ConstraintExprVisitor{m_memberMap, constrp->itemsp(), nullptr, genp, randModeVarp};
                if (constrp->itemsp()) {
                    taskp->addStmtsp(wrapIfConstraintMode(
                        nodep, constrp, constrp->itemsp()->unlinkFrBackWithNext()));
                }
            });
            randomizep->addStmtsp(implementConstraintsClear(fl, genp));
            AstTask* setupAllTaskp = getCreateConstraintSetupFunc(nodep);
            AstTaskRef* const setupTaskRefp = new AstTaskRef{fl, setupAllTaskp, nullptr};
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

        if (AstTask* const resizeAllTaskp
            = VN_AS(m_memberMap.findMember(nodep, "__Vresize_constrained_arrays"), Task)) {
            AstTaskRef* const resizeTaskRefp = new AstTaskRef{fl, resizeAllTaskp, nullptr};
            randomizep->addStmtsp(resizeTaskRefp->makeStmt());
        }

        AstFunc* const basicRandomizep
            = V3Randomize::newRandomizeFunc(m_memberMap, nodep, "__Vbasic_randomize");
        addBasicRandomizeBody(basicRandomizep, nodep, randModeVarp);
        AstFuncRef* const basicRandomizeCallp = new AstFuncRef{fl, basicRandomizep, nullptr};
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
            AstVar* const receiverp = randModeTarget.receiverp;
            AstVar* const randModeVarp = getRandModeVar(randModeTarget.classp);
            AstNodeExpr* const lhsp = makeModeAssignLhs(nodep->fileline(), randModeTarget.classp,
                                                        randModeTarget.fromp, randModeVarp);
            replaceWithModeAssign(nodep,
                                  // If the receiver is not rand, set the rand_mode for all members
                                  receiverp && receiverp->rand().isRand() ? receiverp : nullptr,
                                  lhsp);
            return;
        }

        if (nodep->name() == "constraint_mode") {
            AstMethodCall* const methodCallp = VN_CAST(nodep, MethodCall);
            AstNodeExpr* fromp = methodCallp ? methodCallp->fromp() : nullptr;
            AstConstraint* constrp = nullptr;
            AstClass* classp = VN_CAST(m_modp, Class);
            if (AstConstraintRef* const constrRefp = VN_CAST(fromp, ConstraintRef)) {
                constrp = constrRefp->constrp();
                if (constrRefp->fromp()) {
                    fromp = constrRefp->fromp();
                    classp = VN_AS(fromp->dtypep()->skipRefp(), ClassRefDType)->classp();
                }
            } else if (fromp) {
                classp = VN_AS(fromp->dtypep()->skipRefp(), ClassRefDType)->classp();
            }
            UASSERT_OBJ(classp, nodep, "Failed to find class");
            AstVar* const constraintModeVarp = getConstraintModeVar(classp);
            AstNodeExpr* const lhsp
                = makeModeAssignLhs(nodep->fileline(), classp, fromp, constraintModeVarp);
            replaceWithModeAssign(nodep, constrp, lhsp);
            return;
        }

        if (nodep->name() != "randomize") return;

        handleRandomizeArgs(nodep);

        AstWith* const withp = VN_CAST(nodep->pinsp(), With);

        if (!withp) {
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

        addPrePostCall(classp, randomizeFuncp, "pre_randomize");

        // Detach the expression and prepare variable copies
        const CaptureVisitor captured{withp->exprp(), m_modp, classp};

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
            = new AstFuncRef{nodep->fileline(), basicRandomizeFuncp, nullptr};

        // Copy (derive) class constraints if present
        if (classGenp) {
            AstTask* const constrSetupFuncp = getCreateConstraintSetupFunc(classp);
            AstTaskRef* const callp = new AstTaskRef{nodep->fileline(), constrSetupFuncp, nullptr};
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

        addPrePostCall(classp, randomizeFuncp, "post_randomize");

        // Replace the node with a call to that function
        nodep->name(randomizeFuncp->name());
        nodep->addPinsp(captured.getArgs());
        nodep->taskp(randomizeFuncp);
        nodep->dtypeFrom(randomizeFuncp->dtypep());
        nodep->classOrPackagep(classp);
        UINFO(9, "Added `%s` randomization procedure");
        VL_DO_DANGLING(withp->deleteTree(), withp);
    }
    void visit(AstConstraint* nodep) override {
        VL_RESTORER(m_constraintp);
        m_constraintp = nodep;
        iterateChildren(nodep);
    }
    void visit(AstCMethodHard* nodep) override {
        iterateChildren(nodep);
        FileLine* const fl = nodep->fileline();
        if (m_constraintp && nodep->fromp()->user1() && nodep->name() == "size") {
            AstClass* const classp = VN_AS(m_modp, Class);
            AstVarRef* const queueVarRefp = VN_CAST(nodep->fromp(), VarRef);
            if (!queueVarRefp) {
                // Warning from ConstraintExprVisitor will be thrown
                return;
            }
            AstVar* const queueVarp = queueVarRefp->varp();
            AstVar* sizeVarp = VN_CAST(queueVarp->user4p(), Var);
            if (!sizeVarp) {
                sizeVarp = new AstVar{fl, VVarType::BLOCKTEMP, "__V" + queueVarp->name() + "_size",
                                      nodep->findSigned32DType()};
                classp->addMembersp(sizeVarp);
                m_memberMap.insert(classp, sizeVarp);
                sizeVarp->user2p(classp);

                queueVarp->user4p(sizeVarp);

                AstTask* resizerTaskp = VN_AS(m_constraintp->user3p(), Task);
                if (!resizerTaskp) {
                    resizerTaskp = newResizeConstrainedArrayTask(classp, m_constraintp->name());
                    m_constraintp->user3p(resizerTaskp);
                }
                AstCMethodHard* const resizep
                    = new AstCMethodHard{fl, nodep->fromp()->unlinkFrBack(), "resize",
                                         new AstVarRef{fl, sizeVarp, VAccess::READ}};
                resizep->dtypep(nodep->findVoidDType());
                resizerTaskp->addStmtsp(new AstStmtExpr{fl, resizep});

                // Since size variable is signed int, we need additional constraint
                // to make sure it is always >= 0.
                AstVarRef* const sizeVarRefp = new AstVarRef{fl, sizeVarp, VAccess::READ};
                sizeVarRefp->user1(true);
                AstGteS* const sizeGtep = new AstGteS{fl, sizeVarRefp, new AstConst{fl, 0}};
                sizeGtep->user1(true);
                m_constraintp->addItemsp(new AstConstraintExpr{fl, sizeGtep});
            }
            AstVarRef* const sizeVarRefp = new AstVarRef{fl, sizeVarp, VAccess::READ};
            sizeVarRefp->user1(true);
            nodep->replaceWith(sizeVarRefp);
            VL_DO_DANGLING(nodep->deleteTree(), nodep);
        }
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
                                       const std::string& name, bool allowVirtual,
                                       bool childDType) {
    AstFunc* funcp = VN_AS(memberMap.findMember(nodep, name), Func);
    if (!funcp) {
        v3Global.useRandomizeMethods(true);
        AstNodeDType* const dtypep
            = childDType
                  ? new AstBasicDType{nodep->fileline(), VBasicDTypeKwd::INT}
                  : nodep->findBitDType(32, 32, VSigning::SIGNED);  // IEEE says int return of 0/1
        AstVar* const fvarp = childDType
                                  ? new AstVar{nodep->fileline(), VVarType::MEMBER, name,
                                               VFlagChildDType{}, dtypep}
                                  : new AstVar{nodep->fileline(), VVarType::MEMBER, name, dtypep};
        fvarp->lifetime(VLifetime::AUTOMATIC);
        fvarp->funcLocal(true);
        fvarp->funcReturn(true);
        fvarp->direction(VDirection::OUTPUT);
        nodep->addMembersp(funcp);
        funcp = new AstFunc{nodep->fileline(), name, nullptr, fvarp};
        if (!childDType) funcp->dtypep(dtypep);
        funcp->classMethod(true);
        funcp->isVirtual(allowVirtual && nodep->isExtended());
        nodep->addMembersp(funcp);
        memberMap.insert(nodep, funcp);
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
