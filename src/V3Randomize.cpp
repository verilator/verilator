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
//      define a virtual randomize() method that randomizes its random variables
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

#include <utility>

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// Visitor that marks classes needing a randomize() method

class RandomizeMarkVisitor final : public VNVisitorConst {
    // NODE STATE
    // Cleared on Netlist
    //  AstClass::user1()       -> bool.  Set true to indicate needs randomize processing
    //  AstNodeExpr::user1()    -> bool.  Set true to indicate constraint expression depending on a
    //                                    randomized variable
    //  AstVar::user2p()        -> AstNodeModule*. Pointer to containing module
    const VNUser1InUse m_inuser1;
    const VNUser2InUse m_inuser2;

    using DerivedSet = std::unordered_set<AstClass*>;
    using BaseToDerivedMap = std::unordered_map<const AstClass*, DerivedSet>;

    BaseToDerivedMap m_baseToDerivedMap;  // Mapping from base classes to classes that extend them
    AstClass* m_classp = nullptr;  // Current class
    AstNode* m_constraintExprp = nullptr;  // Current constraint expression
    AstNodeModule* m_modp;  // Current module
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
    void visit(AstNodeFTaskRef* nodep) override {
        iterateChildrenConst(nodep);
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
    bool m_wantSingle = false;  // Whether to merge constraint expressions with LOGAND
    VMemberMap& m_memberMap;  // Member names cached for fast lookup

    bool editFormat(AstNodeExpr* nodep) {
        if (nodep->user1()) return false;
        // Replace computable expression with SMT constant
        VNRelinker handle;
        nodep->unlinkFrBack(&handle);
        AstSFormatF* const newp = new AstSFormatF{
            nodep->fileline(), (nodep->width() & 3) ? "#b%b" : "#x%x", false, nodep};
        handle.relink(newp);
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
        if (editFormat(nodep)) return;
        // In SMT just variable name, but we also ensure write_var for the variable
        const std::string smtName = nodep->name();  // Can be anything unique
        nodep->replaceWith(new AstSFormatF{nodep->fileline(), smtName, false, nullptr});

        AstVar* const varp = nodep->varp();

        VL_DO_DANGLING(pushDeletep(nodep), nodep);

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
            methodp->addPinsp(varRefp);
            methodp->addPinsp(new AstConst{varp->dtypep()->fileline(), AstConst::Unsized64{},
                                           (size_t)varp->width()});
            AstNodeExpr* const varnamep
                = new AstCExpr{varp->fileline(), "\"" + smtName + "\"", varp->width()};
            varnamep->dtypep(varp->dtypep());
            methodp->addPinsp(varnamep);
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
                                   AstNodeFTask* inlineInitTaskp, AstVar* genp)
        : m_inlineInitTaskp{inlineInitTaskp}
        , m_genp{genp}
        , m_memberMap{memberMap} {
        iterateAndNextNull(nodep);
    }
};

template <typename TreeNodeType>
class CaptureFrame final {
    TreeNodeType* m_treep;  // Original tree
    AstArg* m_argsp;  // Original references turned into arguments
    AstNodeModule* m_myModulep;  // Module for which static references will stay uncaptured.
    // Map original var nodes to their clones
    std::map<const AstVar*, AstVar*> m_varCloneMap;

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

    template <typename Action>
    static void foreachSuperClass(AstClass* classp, Action action) {
        for (AstClassExtends* extendsp = classp->extendsp(); extendsp;
             extendsp = VN_AS(extendsp->nextp(), ClassExtends)) {
            AstClass* const superclassp = VN_AS(extendsp->childDTypep(), ClassRefDType)->classp();
            action(superclassp);
            foreachSuperClass(superclassp, action);
        }
    }

public:
    explicit CaptureFrame(TreeNodeType* const nodep, AstNodeModule* const myModulep,
                          const bool clone = true, VNRelinker* const linkerp = nullptr)
        : m_treep(clone ? nodep->cloneTree(true) : nodep->unlinkFrBackWithNext(linkerp))
        , m_argsp(nullptr)
        , m_myModulep(myModulep) {

        std::set<AstNodeModule*> visibleModules = {myModulep};
        if (AstClass* classp = VN_CAST(m_myModulep, Class)) {
            foreachSuperClass(classp,
                              [&](AstClass* superclassp) { visibleModules.emplace(superclassp); });
        }
        m_treep->foreachAndNext([&](AstNodeVarRef* varrefp) {
            UASSERT_OBJ(varrefp->varp(), varrefp, "Variable unlinked");
            if (!varrefp->varp()->isFuncLocal() && !VN_IS(varrefp, VarXRef)
                && (visibleModules.count(varrefp->classOrPackagep())))
                return;
            AstVar* newVarp;
            bool newCapture = captureVariable(varrefp->fileline(), varrefp, newVarp /*ref*/);
            AstNodeVarRef* const newVarRefp = newCapture ? varrefp->cloneTree(false) : nullptr;
            if (!varrefp->varp()->lifetime().isStatic() || varrefp->classOrPackagep()) {
                // Keeping classOrPackagep will cause a broken link after inlining
                varrefp->classOrPackagep(nullptr);  // AstScope will figure this out
            }
            varrefp->varp(newVarp);
            if (!newCapture) return;
            if (VN_IS(varrefp, VarXRef)) {
                AstVarRef* const notXVarRefp
                    = new AstVarRef{varrefp->fileline(), newVarp, VAccess::READ};
                notXVarRefp->classOrPackagep(varrefp->classOrPackagep());
                varrefp->replaceWith(notXVarRefp);
                varrefp->deleteTree();
                varrefp = notXVarRefp;
            }
            m_argsp = AstNode::addNext(m_argsp, new AstArg{varrefp->fileline(), "", newVarRefp});
        });
    }

    // PUBLIC METHODS

    TreeNodeType* getTree() const { return m_treep; }

    AstVar* getVar(AstVar* const varp) const {
        const auto it = m_varCloneMap.find(varp);
        if (it == m_varCloneMap.end()) { return nullptr; }
        return it->second;
    }

    AstArg* getArgs() const { return m_argsp; }
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
    // VNUser1InUse    m_inuser1;      (Allocated for use in RandomizeMarkVisitor)
    // VNUser2InUse    m_inuser2;      (Allocated for use in RandomizeMarkVisitor)
    const VNUser3InUse m_inuser3;

    // STATE
    V3UniqueNames m_inlineUniqueNames;  // For generating unique function names
    VMemberMap m_memberMap;  // Member names cached for fast lookup
    AstNodeModule* m_modp = nullptr;  // Current module
    const AstNodeFTask* m_ftaskp = nullptr;  // Current function/task
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
    void createRandomizeClassVars(AstNetlist* const netlistp) {
        netlistp->foreach([&](AstClass* const classp) {
            if (classp->existsMember(
                    [&](const AstClass*, const AstConstraint*) { return true; })) {
                createRandomGenerator(classp);
            }
        });
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
            return new AstAssign{fl,
                                 new AstSel{fl, exprp, offset + (memberp ? memberp->lsb() : 0),
                                            memberp ? memberp->width() : exprp->width()},
                                 valp};
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

                ConstraintExprVisitor{m_memberMap, constrp->itemsp(), nullptr, genp};
                if (constrp->itemsp()) taskp->addStmtsp(constrp->itemsp()->unlinkFrBackWithNext());
            });
            randomizep->addStmtsp(implementConstraintsClear(fl, genp));
            AstTask* setupAllTaskp = getCreateConstraintSetupFunc(nodep);
            AstTaskRef* const setupTaskRefp = new AstTaskRef{fl, setupAllTaskp->name(), nullptr};
            setupTaskRefp->taskp(setupAllTaskp);
            randomizep->addStmtsp(implementConstraintsClear(fl, genp));
            randomizep->addStmtsp(setupTaskRefp->makeStmt());

            AstVarRef* genRefp
                = new AstVarRef{fl, VN_AS(genp->user2p(), NodeModule), genp, VAccess::READWRITE};
            AstNode* const argsp = genRefp;
            argsp->addNext(new AstText{fl, ".next(__Vm_rng)"});
            AstNodeExpr* const solverCallp = new AstCExpr{fl, argsp};
            solverCallp->dtypeSetBit();
            beginValp = solverCallp;
        } else {
            beginValp = new AstConst{fl, AstConst::WidthedValue{}, 32, 1};
        }

        AstVarRef* const fvarRefp = new AstVarRef{fl, fvarp, VAccess::WRITE};
        randomizep->addStmtsp(new AstAssign{fl, fvarRefp, beginValp});

        AstNodeFTask* const newp = VN_AS(m_memberMap.findMember(nodep, "new"), NodeFTask);
        UASSERT_OBJ(newp, nodep, "No new() in class");

        nodep->foreachMember([&](AstClass* classp, AstVar* memberVarp) {
            if (!memberVarp->isRand() || memberVarp->user3()) return;
            const AstNodeDType* const dtypep = memberVarp->dtypep()->skipRefp();
            if (VN_IS(dtypep, BasicDType) || VN_IS(dtypep, StructDType)) {
                AstVar* const randcVarp = newRandcVarsp(memberVarp);
                AstVarRef* const refp = new AstVarRef{fl, classp, memberVarp, VAccess::WRITE};
                AstNodeStmt* const stmtp = newRandStmtsp(fl, refp, randcVarp);
                randomizep->addStmtsp(stmtp);
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
                AstVarRef* fvarRefReadp = fvarRefp->cloneTree(false);
                fvarRefReadp->access(VAccess::READ);
                AstIf* const assignIfNotNullp = new AstIf{
                    fl,
                    new AstNeq{fl, new AstVarRef{fl, classp, memberVarp, VAccess::READ},
                               new AstConst{fl, AstConst::Null{}}},
                    new AstAssign{fl, fvarRefp->cloneTree(false),
                                  new AstAnd{fl, fvarRefReadp, callp}}};
                randomizep->addStmtsp(assignIfNotNullp);
            } else {
                memberVarp->v3warn(E_UNSUPPORTED, "Unsupported: random member variable with type "
                                                      << memberVarp->dtypep()->prettyDTypeNameQ());
            }
        });
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

        AstFunc* const randomizeFuncp
            = V3Randomize::newRandomizeFunc(m_memberMap, classp, m_inlineUniqueNames.get(nodep));

        // Detach the expression and prepare variable copies
        const CaptureFrame<AstNode> captured{withp->exprp(), classp, false};
        UASSERT_OBJ(VN_IS(captured.getTree(), ConstraintExpr), captured.getTree(),
                    "Wrong expr type");

        // Add function arguments
        for (AstArg* argp = captured.getArgs(); argp; argp = VN_AS(argp->nextp(), Arg)) {
            AstNodeVarRef* varrefp = VN_AS(argp->exprp(), NodeVarRef);
            if ((varrefp->classOrPackagep() == m_modp) || VN_IS(varrefp, VarXRef)) {
                // Keeping classOrPackagep will cause a broken link after inlining
                varrefp->classOrPackagep(nullptr);
            }
            randomizeFuncp->addStmtsp(captured.getVar(varrefp->varp()));
        }

        // Add constraints clearing code
        if (classGenp) {
            randomizeFuncp->addStmtsp(
                implementConstraintsClear(randomizeFuncp->fileline(), classGenp));
        }

        randomizeFuncp->addStmtsp(localGenp);

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

        // Generate constraint setup code and a hardcoded call to the solver
        randomizeFuncp->addStmtsp(captured.getTree());
        ConstraintExprVisitor{m_memberMap, captured.getTree(), randomizeFuncp, localGenp};

        // Call the solver and set return value
        AstVarRef* const randNextp
            = new AstVarRef{nodep->fileline(), localGenp, VAccess::READWRITE};
        randNextp->AstNode::addNext(new AstText{nodep->fileline(), ".next(__Vm_rng)"});
        AstNodeExpr* const solverCallp = new AstCExpr{nodep->fileline(), randNextp};
        solverCallp->dtypeSetBit();
        randomizeFuncp->addStmtsp(new AstAssign{
            nodep->fileline(),
            new AstVarRef{nodep->fileline(), VN_AS(randomizeFuncp->fvarp(), Var), VAccess::WRITE},
            solverCallp});

        // Replace the node with a call to that function
        nodep->name(randomizeFuncp->name());
        nodep->addPinsp(captured.getArgs());
        nodep->taskp(randomizeFuncp);
        nodep->dtypeFrom(randomizeFuncp->dtypep());
        nodep->classOrPackagep(classp);
        UINFO(9, "Added `%s` randomization procedure");
        VL_DO_DANGLING(withp->deleteTree(), withp);
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
                                       const std::string& name) {
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
        funcp->isVirtual(nodep->isExtended());
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
