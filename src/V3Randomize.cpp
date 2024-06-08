// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Expression width calculations
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

#include "V3Randomize.h"

#include "V3MemberMap.h"

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// Visitor that marks classes needing a randomize() method

class RandomizeMarkVisitor final : public VNVisitorConst {
    // NODE STATE
    // Cleared on Netlist
    //  AstClass::user1()       -> bool.  Set true to indicate needs randomize processing
    //  AstConstraintExpr::user1() -> bool.  Set true to indicate state-dependent
    //  AstNodeExpr::user1()    -> bool.  Set true to indicate constraint expression depending on a
    //                                    randomized variable
    const VNUser1InUse m_inuser1;

    using DerivedSet = std::unordered_set<AstClass*>;
    using BaseToDerivedMap = std::unordered_map<const AstClass*, DerivedSet>;

    BaseToDerivedMap m_baseToDerivedMap;  // Mapping from base classes to classes that extend them
    AstClass* m_classp = nullptr;  // Current class
    AstConstraintExpr* m_constraintExprp = nullptr;  // Current constraint expression

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

    // VISITORS
    void visit(AstClass* nodep) override {
        VL_RESTORER(m_classp);
        m_classp = nodep;
        iterateChildrenConst(nodep);
        if (nodep->extendsp()) {
            // Save pointer to derived class
            const AstClass* const basep = nodep->extendsp()->classp();
            m_baseToDerivedMap[basep].insert(nodep);
        }
    }
    void visit(AstMethodCall* nodep) override {
        iterateChildrenConst(nodep);
        if (nodep->name() != "randomize") return;
        if (const AstClassRefDType* const classRefp
            = VN_CAST(nodep->fromp()->dtypep()->skipRefp(), ClassRefDType)) {
            AstClass* const classp = classRefp->classp();
            classp->user1(true);
            markMembers(classp);
        }
    }
    void visit(AstNodeFTaskRef* nodep) override {
        iterateChildrenConst(nodep);
        if (nodep->name() != "randomize") return;
        if (m_classp) m_classp->user1(true);
    }
    void visit(AstConstraintExpr* nodep) override {
        VL_RESTORER(m_constraintExprp);
        m_constraintExprp = nodep;
        iterateChildrenConst(nodep);
    }
    void visit(AstNodeVarRef* nodep) override {
        if (!m_constraintExprp) return;
        if (!nodep->varp()->isRand()) {
            m_constraintExprp->user1(true);
            nodep->v3warn(CONSTRAINTIGN, "State-dependent constraint ignored (unsupported)");
            return;
        }
        for (AstNode* backp = nodep; backp != m_constraintExprp && !backp->user1();
             backp = backp->backp())
            backp->user1(true);
    }

    void visit(AstNode* nodep) override { iterateChildrenConst(nodep); }

public:
    // CONSTRUCTORS
    explicit RandomizeMarkVisitor(AstNetlist* nodep) {
        iterateConst(nodep);
        markAllDerived();
    }
    ~RandomizeMarkVisitor() override = default;
};

//######################################################################
// Visitor that turns constraints into template strings for solvers

class ConstraintExprVisitor final : public VNVisitor {
    // NODE STATE
    //  AstVar::user4()         -> bool. Handled in constraints
    //  AstNodeExpr::user1()    -> bool. Depending on a randomized variable
    // VNUser4InUse    m_inuser4;      (Allocated for use in RandomizeVisitor)

    AstTask* const m_taskp;  // X_setup_constraint() method of the constraint
    AstVar* const m_genp;  // VlRandomizer variable of the class

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
    void editSMT(AstNodeExpr* nodep, AstNodeExpr* lhsp = nullptr, AstNodeExpr* rhsp = nullptr) {
        // Replace incomputable (result-dependent) expression with SMT expression
        std::string smtExpr = nodep->emitSMT();  // Might need child width (AstExtend)
        UASSERT_OBJ(smtExpr != "", nodep,
                    "Node needs randomization constraint, but no emitSMT: " << nodep);

        if (lhsp) lhsp = VN_AS(iterateSubtreeReturnEdits(lhsp->unlinkFrBack()), NodeExpr);
        if (rhsp) rhsp = VN_AS(iterateSubtreeReturnEdits(rhsp->unlinkFrBack()), NodeExpr);

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
                default: nodep->v3fatalSrc("Unknown emitSMT format code: %" << pos[0]); break;
                }
            }
        }
        UASSERT_OBJ(!lhsp, nodep, "Missing emitSMT %l for " << lhsp);
        UASSERT_OBJ(!rhsp, nodep, "Missing emitSMT %r for " << rhsp);
        AstSFormatF* const newp = new AstSFormatF{nodep->fileline(), smtExpr, false, argsp};
        nodep->replaceWith(newp);
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }

    // VISITORS
    void visit(AstNodeVarRef* nodep) override {
        if (editFormat(nodep)) return;
        // In SMT just variable name, but we also ensure write_var for the variable
        const std::string smtName = nodep->name();  // Can be anything unique
        nodep->replaceWith(new AstSFormatF{nodep->fileline(), smtName, false, nullptr});

        AstVar* const varp = nodep->varp();

        VL_DO_DANGLING(pushDeletep(nodep), nodep);

        if (!varp->user4()) {
            varp->user4(true);
            AstCMethodHard* const methodp = new AstCMethodHard{
                varp->fileline(), new AstVarRef{varp->fileline(), m_genp, VAccess::READWRITE},
                "write_var"};
            methodp->dtypeSetVoid();
            methodp->addPinsp(new AstVarRef{varp->fileline(), varp, VAccess::WRITE});
            methodp->addPinsp(new AstConst{varp->dtypep()->fileline(), AstConst::Unsized64{},
                                           (size_t)varp->width()});
            AstNodeExpr* const varnamep
                = new AstCExpr{varp->fileline(), "\"" + smtName + "\"", varp->width()};
            varnamep->dtypep(varp->dtypep());
            methodp->addPinsp(varnamep);
            m_taskp->addStmtsp(new AstStmtExpr{varp->fileline(), methodp});
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
    void visit(AstReplicate* nodep) override {
        // Biop, but RHS is harmful
        if (editFormat(nodep)) return;
        editSMT(nodep, nodep->srcp());
    }
    void visit(AstSFormatF* nodep) override {}
    void visit(AstConstraintExpr* nodep) override { iterateChildren(nodep); }
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
    explicit ConstraintExprVisitor(AstConstraintExpr* nodep, AstTask* taskp, AstVar* genp)
        : m_taskp(taskp)
        , m_genp(genp) {
        iterate(nodep);
    }
};

//######################################################################
// Visitor that defines a randomize method where needed

class RandomizeVisitor final : public VNVisitor {
    // NODE STATE
    // Cleared on Netlist
    //  AstClass::user1()       -> bool.  Set true to indicate needs randomize processing
    //  AstConstraintExpr::user1() -> bool.  Set true to indicate state-dependent
    //  AstEnumDType::user2()   -> AstVar*.  Pointer to table with enum values
    //  AstClass::user3()       -> AstFunc*. Pointer to randomize() method of a class
    //  AstVar::user4()         -> bool. Handled in constraints
    //  AstClass::user4()       -> AstVar*.  Constrained randomizer variable
    // VNUser1InUse    m_inuser1;      (Allocated for use in RandomizeMarkVisitor)
    const VNUser2InUse m_inuser2;
    const VNUser3InUse m_inuser3;
    const VNUser4InUse m_inuser4;

    // STATE
    VMemberMap m_memberMap;  // Member names cached for fast lookup
    AstNodeModule* m_modp = nullptr;  // Current module
    const AstNodeFTask* m_ftaskp = nullptr;  // Current function/task
    size_t m_enumValueTabCount = 0;  // Number of tables with enum values created
    int m_randCaseNum = 0;  // Randcase number within a module for var naming
    std::map<std::string, AstCDType*> m_randcDtypes;  // RandC data type deduplication

    // METHODS
    AstVar* enumValueTabp(AstEnumDType* nodep) {
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

    AstCDType* findVlRandCDType(FileLine* fl, uint64_t items) {
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

    AstVar* newRandcVarsp(AstVar* varp) {
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
    AstNodeStmt* newRandStmtsp(FileLine* fl, AstNodeVarRef* varrefp, AstVar* randcVarp,
                               int offset = 0, AstMemberDType* memberp = nullptr) {
        if (const auto* const structDtp
            = VN_CAST(memberp ? memberp->subDTypep()->skipRefp() : varrefp->dtypep()->skipRefp(),
                      StructDType)) {
            AstNodeStmt* stmtsp = nullptr;
            offset += memberp ? memberp->lsb() : 0;
            for (AstMemberDType* smemberp = structDtp->membersp(); smemberp;
                 smemberp = VN_AS(smemberp->nextp(), MemberDType)) {
                AstNodeStmt* const randp = newRandStmtsp(
                    fl, stmtsp ? varrefp->cloneTree(false) : varrefp, nullptr, offset, smemberp);
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
                                                              : varrefp->dtypep()->subDTypep(),
                                                      EnumDType)) {
                AstVarRef* const tabRefp
                    = new AstVarRef{fl, enumValueTabp(enumDtp), VAccess::READ};
                tabRefp->classOrPackagep(v3Global.rootp()->dollarUnitPkgAddp());
                AstNodeExpr* const randp
                    = newRandValue(fl, randcVarp, varrefp->findBasicDType(VBasicDTypeKwd::UINT32));
                AstNodeExpr* const moddivp = new AstModDiv{
                    fl, randp, new AstConst{fl, static_cast<uint32_t>(enumDtp->itemCount())}};
                moddivp->dtypep(enumDtp);
                valp = new AstArraySel{fl, tabRefp, moddivp};
            } else {
                valp = newRandValue(fl, randcVarp,
                                    (memberp ? memberp->dtypep() : varrefp->varp()->dtypep()));
            }
            return new AstAssign{fl,
                                 new AstSel{fl, varrefp, offset + (memberp ? memberp->lsb() : 0),
                                            memberp ? memberp->width() : varrefp->width()},
                                 valp};
        }
    }
    AstNodeExpr* newRandValue(FileLine* fl, AstVar* randcVarp, AstNodeDType* dtypep) {
        if (randcVarp) {
            AstNode* argsp = new AstVarRef{fl, randcVarp, VAccess::READWRITE};
            argsp->addNext(new AstText{fl, ".randomize(__Vm_rng)"});
            AstCExpr* newp = new AstCExpr{fl, argsp};
            newp->dtypep(dtypep);
            return newp;
        } else {
            return new AstRandRNG{fl, dtypep};
        }
    }
    void addPrePostCall(AstClass* classp, AstFunc* funcp, const string& name) {
        if (AstTask* userFuncp = VN_CAST(m_memberMap.findMember(classp, name), Task)) {
            AstTaskRef* const callp
                = new AstTaskRef{userFuncp->fileline(), userFuncp->name(), nullptr};
            callp->taskp(userFuncp);
            funcp->addStmtsp(callp->makeStmt());
        }
    }
    AstTask* newSetupConstraintTask(AstClass* nodep, const std::string& name) {
        AstTask* const taskp = new AstTask{nodep->fileline(), name + "_setup_constraint", nullptr};
        taskp->classMethod(true);
        nodep->addMembersp(taskp);
        return taskp;
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
        AstFunc* const funcp = V3Randomize::newRandomizeFunc(nodep);
        nodep->user3p(funcp);
        AstVar* const fvarp = VN_AS(funcp->fvarp(), Var);
        addPrePostCall(nodep, funcp, "pre_randomize");
        FileLine* fl = nodep->fileline();

        AstNodeExpr* beginValp = nullptr;
        if (nodep->extendsp()) {
            // Call randomize() from the base class
            AstFunc* const baseRandomizep = VN_AS(nodep->extendsp()->classp()->user3p(), Func);
            if (baseRandomizep) {
                AstFuncRef* const baseRandCallp = new AstFuncRef{fl, "randomize", nullptr};
                baseRandCallp->taskp(baseRandomizep);
                baseRandCallp->dtypeFrom(baseRandomizep->dtypep());
                baseRandCallp->classOrPackagep(nodep->extendsp()->classp());
                baseRandCallp->superReference(true);
                beginValp = baseRandCallp;
            }
        }
        if (m_modp->user4p()) {
            AstNode* const argsp = new AstVarRef{nodep->fileline(), VN_AS(m_modp->user4p(), Var),
                                                 VAccess::READWRITE};
            argsp->addNext(new AstText{fl, ".next(__Vm_rng)"});
            AstNodeExpr* const solverCallp = new AstCExpr{fl, argsp};
            solverCallp->dtypeSetBit();
            beginValp = beginValp ? new AstAnd{fl, beginValp, solverCallp} : solverCallp;
        }
        if (!beginValp) beginValp = new AstConst{fl, AstConst::WidthedValue{}, 32, 1};

        funcp->addStmtsp(new AstAssign{fl, new AstVarRef{fl, fvarp, VAccess::WRITE}, beginValp});

        for (AstNode* memberp = nodep->stmtsp(); memberp; memberp = memberp->nextp()) {
            AstVar* const memberVarp = VN_CAST(memberp, Var);
            if (!memberVarp || !memberVarp->isRand() || memberVarp->user4()) continue;
            const AstNodeDType* const dtypep = memberp->dtypep()->skipRefp();
            if (VN_IS(dtypep, BasicDType) || VN_IS(dtypep, StructDType)) {
                AstVar* const randcVarp = newRandcVarsp(memberVarp);
                AstVarRef* const refp = new AstVarRef{fl, memberVarp, VAccess::WRITE};
                AstNodeStmt* const stmtp = newRandStmtsp(fl, refp, randcVarp);
                funcp->addStmtsp(stmtp);
            } else if (const AstClassRefDType* const classRefp = VN_CAST(dtypep, ClassRefDType)) {
                if (classRefp->classp() == nodep) {
                    memberp->v3warn(
                        E_UNSUPPORTED,
                        "Unsupported: random member variable with type of a current class");
                    continue;
                }
                AstVarRef* const refp = new AstVarRef{fl, memberVarp, VAccess::WRITE};
                AstFunc* const memberFuncp = V3Randomize::newRandomizeFunc(classRefp->classp());
                AstMethodCall* const callp = new AstMethodCall{fl, refp, "randomize", nullptr};
                callp->taskp(memberFuncp);
                callp->dtypeFrom(memberFuncp);
                AstAssign* const assignp = new AstAssign{
                    fl, new AstVarRef{fl, fvarp, VAccess::WRITE},
                    new AstAnd{fl, new AstVarRef{fl, fvarp, VAccess::READ}, callp}};
                AstIf* const assignIfNotNullp
                    = new AstIf{fl,
                                new AstNeq{fl, new AstVarRef{fl, memberVarp, VAccess::READ},
                                           new AstConst{fl, AstConst::Null{}}},
                                assignp};
                funcp->addStmtsp(assignIfNotNullp);
            } else {
                memberp->v3warn(E_UNSUPPORTED, "Unsupported: random member variable with type "
                                                   << memberp->dtypep()->prettyDTypeNameQ());
            }
        }
        addPrePostCall(nodep, funcp, "post_randomize");
        nodep->user1(false);
    }
    void visit(AstConstraint* nodep) override {
        AstNodeFTask* const newp = VN_AS(m_memberMap.findMember(m_modp, "new"), NodeFTask);
        UASSERT_OBJ(newp, m_modp, "No new() in class");
        AstTask* const taskp = newSetupConstraintTask(VN_AS(m_modp, Class), nodep->name());
        AstTaskRef* const setupTaskRefp
            = new AstTaskRef{nodep->fileline(), taskp->name(), nullptr};
        setupTaskRefp->taskp(taskp);
        newp->addStmtsp(new AstStmtExpr{nodep->fileline(), setupTaskRefp});

        AstVar* genp = VN_AS(m_modp->user4p(), Var);
        if (!genp) {
            genp = new AstVar(nodep->fileline(), VVarType::MEMBER, "constraint",
                              m_modp->findBasicDType(VBasicDTypeKwd::RANDOM_GENERATOR));
            VN_AS(m_modp, Class)->addMembersp(genp);
            m_modp->user4p(genp);
        }

        while (nodep->itemsp()) {
            AstConstraintExpr* const condsp = VN_CAST(nodep->itemsp(), ConstraintExpr);
            if (!condsp || condsp->user1()) {
                nodep->itemsp()->v3warn(CONSTRAINTIGN,
                                        "Constraint expression ignored (unsupported)");
                pushDeletep(nodep->itemsp()->unlinkFrBack());
                continue;
            }
            { ConstraintExprVisitor{condsp->unlinkFrBack(), taskp, genp}; }
            // Only hard constraints are now supported
            AstCMethodHard* const methodp = new AstCMethodHard{
                condsp->fileline(), new AstVarRef{condsp->fileline(), genp, VAccess::READWRITE},
                "hard", condsp->exprp()->unlinkFrBack()};
            methodp->dtypeSetVoid();
            taskp->addStmtsp(new AstStmtExpr{condsp->fileline(), methodp});
            VL_DO_DANGLING(condsp->deleteTree(), condsp);
        }
        VL_DO_DANGLING(pushDeletep(nodep->unlinkFrBack()), nodep);
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
        AstNodeIf* firstIfsp
            = new AstIf{fl, new AstConst{fl, AstConst::BitFalse{}}, nullptr, nullptr};
        AstNodeIf* ifsp = firstIfsp;

        for (AstCaseItem* itemp = nodep->itemsp(); itemp;
             itemp = VN_AS(itemp->nextp(), CaseItem)) {
            AstNodeExpr* const condp = itemp->condsp()->unlinkFrBack();
            sump
                = new AstAdd{condp->fileline(), sump, new AstExtend{itemp->fileline(), condp, 64}};
            AstNode* const stmtsp
                = itemp->stmtsp() ? itemp->stmtsp()->unlinkFrBackWithNext() : nullptr;
            AstNodeIf* const newifp
                = new AstIf{itemp->fileline(),
                            new AstLte{condp->fileline(),
                                       new AstVarRef{condp->fileline(), randVarp, VAccess::READ},
                                       sump->cloneTreePure(true)},
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

        AstNode* newp = randVarp;
        AstNodeExpr* randp = new AstRand{fl, nullptr, false};
        randp->dtypeSetUInt64();
        newp->addNext(new AstAssign{fl, new AstVarRef{fl, randVarp, VAccess::WRITE},
                                    new AstAdd{fl, new AstConst{fl, AstConst::Unsized64{}, 1},
                                               new AstModDiv{fl, randp, sump}}});
        newp->addNext(firstIfsp);
        if (debug() >= 9) newp->dumpTreeAndNext(cout, "-  rcnew: ");
        nodep->replaceWith(newp);
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit RandomizeVisitor(AstNetlist* nodep) { iterate(nodep); }
    ~RandomizeVisitor() override = default;
};

//######################################################################
// Randomize method class functions

void V3Randomize::randomizeNetlist(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    {
        const RandomizeMarkVisitor markVisitor{nodep};
        RandomizeVisitor{nodep};
    }
    V3Global::dumpCheckGlobalTree("randomize", 0, dumpTreeEitherLevel() >= 3);
}

AstFunc* V3Randomize::newRandomizeFunc(AstClass* nodep) {
    VMemberMap memberMap;
    AstFunc* funcp = VN_AS(memberMap.findMember(nodep, "randomize"), Func);
    if (!funcp) {
        v3Global.useRandomizeMethods(true);
        AstNodeDType* const dtypep
            = nodep->findBitDType(32, 32, VSigning::SIGNED);  // IEEE says int return of 0/1
        AstVar* const fvarp = new AstVar{nodep->fileline(), VVarType::MEMBER, "randomize", dtypep};
        fvarp->lifetime(VLifetime::AUTOMATIC);
        fvarp->funcLocal(true);
        fvarp->funcReturn(true);
        fvarp->direction(VDirection::OUTPUT);
        funcp = new AstFunc{nodep->fileline(), "randomize", nullptr, fvarp};
        funcp->dtypep(dtypep);
        funcp->classMethod(true);
        funcp->isVirtual(nodep->isExtended());
        nodep->addMembersp(funcp);
        AstClass* const basep = nodep->baseMostClassp();
        basep->needRNG(true);
    }
    return funcp;
}

AstFunc* V3Randomize::newSRandomFunc(AstClass* nodep) {
    VMemberMap memberMap;
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
        funcp->addStmtsp(new AstCStmt{basep->fileline(), "__Vm_rng.srandom(seed);\n"});
        basep->needRNG(true);
    }
    return funcp;
}
