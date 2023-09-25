// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Expression width calculations
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2023 by Wilson Snyder. This program is free software; you
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

#define VL_MT_DISABLED_CODE_UNIT 1

#include "config_build.h"
#include "verilatedos.h"

#include "V3Randomize.h"

#include "V3Ast.h"
#include "V3MemberMap.h"

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// Visitor that marks classes needing a randomize() method

class RandomizeMarkVisitor final : public VNVisitorConst {
private:
    // NODE STATE
    // Cleared on Netlist
    //  AstClass::user1()       -> bool.  Set true to indicate needs randomize processing
    const VNUser1InUse m_inuser1;

    using DerivedSet = std::unordered_set<AstClass*>;
    using BaseToDerivedMap = std::unordered_map<AstClass*, DerivedSet>;

    BaseToDerivedMap m_baseToDerivedMap;  // Mapping from base classes to classes that extend them
    AstClass* m_classp = nullptr;  // Current class

    // METHODS
    void markMembers(AstClass* nodep) {
        for (auto* classp = nodep; classp;
             classp = classp->extendsp() ? classp->extendsp()->classp() : nullptr) {
            for (auto* memberp = classp->stmtsp(); memberp; memberp = memberp->nextp()) {
                // If member is rand and of class type, mark its class
                if (VN_IS(memberp, Var) && VN_AS(memberp, Var)->isRand()) {
                    if (const auto* const classRefp = VN_CAST(memberp->dtypep(), ClassRefDType)) {
                        auto* const rclassp = classRefp->classp();
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
    void markDerived(AstClass* nodep) {
        const auto it = m_baseToDerivedMap.find(nodep);
        if (it != m_baseToDerivedMap.end()) {
            for (auto* classp : it->second) {
                if (!classp->user1p()) {
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
            AstClass* const basep = nodep->extendsp()->classp();
            m_baseToDerivedMap[basep].insert(nodep);
        }
    }
    void visit(AstMethodCall* nodep) override {
        iterateChildrenConst(nodep);
        if (nodep->name() != "randomize") return;
        if (const AstClassRefDType* const classRefp
            = VN_CAST(nodep->fromp()->dtypep(), ClassRefDType)) {
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
// Visitor that defines a randomize method where needed

class RandomizeVisitor final : public VNVisitor {
private:
    // NODE STATE
    // Cleared on Netlist
    //  AstClass::user1()       -> bool.  Set true to indicate needs randomize processing
    //  AstEnumDType::user2()   -> AstVar*.  Pointer to table with enum values
    //  AstClass::user3()       -> AstFunc*. Pointer to randomize() method of a class
    // VNUser1InUse    m_inuser1;      (Allocated for use in RandomizeMarkVisitor)
    const VNUser2InUse m_inuser2;

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
        AstNodeArrayDType* const vardtypep
            = new AstUnpackArrayDType{nodep->fileline(), nodep->dtypep(),
                                      new AstRange{nodep->fileline(), nodep->itemCount(), 0}};
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
        const std::string type = AstCDType::typeToHold(items);
        const std::string name = "VlRandC<" + type + ", " + cvtToStr(items) + "ULL>";
        // Create or reuse (to avoid duplicates) randomization object dtype
        auto it = m_randcDtypes.find(name);
        if (it != m_randcDtypes.end()) return it->second;
        AstCDType* newp = new AstCDType{fl, name};
        v3Global.rootp()->typeTablep()->addTypesp(newp);
        m_randcDtypes.emplace(std::make_pair(name, newp));
        return newp;
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
                varp->v3error("Maxiumum implemented width for randc is 32 bits, "
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
                beginValp = baseRandCallp;
            }
        }
        if (!beginValp) beginValp = new AstConst{fl, AstConst::WidthedValue{}, 32, 1};

        funcp->addStmtsp(new AstAssign{fl, new AstVarRef{fl, fvarp, VAccess::WRITE}, beginValp});

        for (auto* memberp = nodep->stmtsp(); memberp; memberp = memberp->nextp()) {
            AstVar* const memberVarp = VN_CAST(memberp, Var);
            if (!memberVarp || !memberVarp->isRand()) continue;
            const AstNodeDType* const dtypep = memberp->dtypep()->skipRefp();
            if (VN_IS(dtypep, BasicDType) || VN_IS(dtypep, StructDType)) {
                AstVar* const randcVarp = newRandcVarsp(memberVarp);
                AstVarRef* const refp = new AstVarRef{fl, memberVarp, VAccess::WRITE};
                AstNodeStmt* const stmtp = newRandStmtsp(fl, refp, randcVarp);
                funcp->addStmtsp(stmtp);
            } else if (const auto* const classRefp = VN_CAST(dtypep, ClassRefDType)) {
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
            fl, VDisplayType::DT_ERROR, "All randcase items had 0 weights (IEEE 1800-2017 18.16)",
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
    V3Global::dumpCheckGlobalTree("randomize", 0, dumpTreeLevel() >= 3);
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
