// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Deals with signal strength
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
// The approach is to create var__s0 and var__s1 for each var that is on LHS of at least two
// assignments or its assignment has strength highz0 or highz1, which may change its value. var__s0
// is used for storing strength of the strongest assignment of value 0 to var, var__s1 stores
// strength of the strongest assigment of value 1. We want to replace the current assignments to
// the var with one assignment with the RHS depending on __s0 and __s1.
//
// First we iterate through the list of assignments that have the var on the LHS.
// We want to do the following steps, but we may not know the value of the RHS at verilation time,
// so we need to do all of them and add a comparison of the RHS with the value corresponding to the
// step.
// * If the RHS has value 0, we try to update __s0
// * If the RHS has value 1, we try to update __s1
// * If the RHS has value x, we try to update both __s vars (to handle the case when
// assignment of x is the strongest)
//
// When RHS has value z, no __s vars are touched (it is the weakest signal and any other value will
// overwrite it), so we can skip this case.
//
// After the iteration we create new assignment to var, according to values of __s0 and __s1:
// s0 > s1:
//   var = 0
// s0 < s1:
//   var = 1
// s0 == s1 and s0 != 0:
//   var = x
// s0 == s1 and s0 == 0:
//   var = z

#include "config_build.h"
#include "verilatedos.h"

#include "V3SignalStrength.h"

#include "V3Ast.h"
#include "V3Global.h"
#include "V3Graph.h"
#include "V3Inst.h"
#include "V3Stats.h"

#include <algorithm>
#include <map>

//######################################################################

class SignalStrengthVisitor final : public VNVisitor {

    // TYPES
    using Assigns = std::vector<AstAssignW*>;
    using VarToAssignsMap = std::unordered_map<AstVar*, Assigns>;

    // MEMBERS
    VarToAssignsMap m_assigns;  // Assigns in current module

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    AstAssign* getStrengthAssignmentp(FileLine* const fl, AstVar* const strengthVarp,
                                      uint8_t strengthLevel, AstNode* const assignedValuep,
                                      AstConst* const compareConstp) {
        return new AstAssign{
            fl, new AstVarRef{fl, strengthVarp, VAccess::WRITE},
            new AstCond{fl,
                        new AstLogAnd{fl,
                                      new AstLt{fl, new AstVarRef{fl, strengthVarp, VAccess::READ},
                                                new AstConst{fl, strengthLevel}},
                                      new AstEqCase{fl, assignedValuep, compareConstp}},
                        new AstConst{fl, strengthLevel},
                        new AstVarRef{fl, strengthVarp, VAccess::READ}}};
    }

    AstBegin* getStrengthComputingBlockp(AstVar* const strength0Varp, AstVar* const strength1Varp,
                                         const Assigns& assigns, const std::string& varName) {
        FileLine* const declVarFl = strength0Varp->fileline();
        AstBegin* const strengthBlockp
            = new AstBegin{declVarFl, varName + "__strength_computing_block", nullptr};

        strengthBlockp->addStmtsp(
            new AstAssign{declVarFl, new AstVarRef{declVarFl, strength0Varp, VAccess::WRITE},
                          new AstConst{declVarFl, 0}});
        strengthBlockp->addStmtsp(
            new AstAssign{declVarFl, new AstVarRef{declVarFl, strength1Varp, VAccess::WRITE},
                          new AstConst{declVarFl, 0}});

        for (size_t i = 0; i < assigns.size(); i++) {
            uint8_t strength0Level, strength1Level;
            if (AstStrengthSpec* strengthSpec = assigns[i]->strengthSpecp()) {
                strength0Level = strengthSpec->strength0();
                strength1Level = strengthSpec->strength1();
            } else {
                strength0Level = 6;  // default strength in strong (6)
                strength1Level = 6;
            }

            FileLine* const assignFl = assigns[i]->fileline();
            if (strength0Level != 0) {
                strengthBlockp->addStmtsp(getStrengthAssignmentp(
                    assignFl, strength0Varp, strength0Level, assigns[i]->rhsp()->cloneTree(false),
                    new AstConst{assignFl, AstConst::WidthedValue(), 1, 0}));

                strengthBlockp->addStmtsp(getStrengthAssignmentp(
                    assignFl, strength0Varp, strength0Level, assigns[i]->rhsp()->cloneTree(false),
                    new AstConst{assignFl, AstConst::StringToParse(), "1'x"}));
            }
            if (strength1Level != 0) {
                strengthBlockp->addStmtsp(getStrengthAssignmentp(
                    assignFl, strength1Varp, strength1Level, assigns[i]->rhsp()->cloneTree(false),
                    new AstConst{assignFl, AstConst::WidthedValue(), 1, 1}));

                strengthBlockp->addStmtsp(getStrengthAssignmentp(
                    assignFl, strength1Varp, strength1Level, assigns[i]->rhsp()->cloneTree(false),
                    new AstConst{assignFl, AstConst::StringToParse(), "1'x"}));
            }

            assigns[i]->unlinkFrBack()->deleteTree();
        }
        return strengthBlockp;
    }

    AstNode* getExpressionWhenStrengthsAreQeual(AstVar* const strengthVarp) {
        FileLine* const declVarFl = strengthVarp->fileline();
        return new AstCond{declVarFl,
                           new AstEq{declVarFl,
                                     new AstVarRef{declVarFl, strengthVarp, VAccess::READ},
                                     new AstConst{declVarFl, AstConst::StringToParse(), "'0"}},
                           new AstConst{declVarFl, AstConst::StringToParse(), "'z"},
                           new AstConst{declVarFl, AstConst::StringToParse(), "'x"}};
    }

    AstAssignW* getAccumulatedAssignmentp(AstVar* const varp, AstVar* const strength0Varp,
                                          AstVar* const strength1Varp) {
        FileLine* const declVarFl = varp->fileline();
        AstVarRef* const varRefp = new AstVarRef{declVarFl, varp, VAccess::WRITE};
        return new AstAssignW{
            declVarFl, varRefp,
            new AstCond{
                declVarFl,
                new AstGt{declVarFl, new AstVarRef{declVarFl, strength0Varp, VAccess::READ},
                          new AstVarRef{declVarFl, strength1Varp, VAccess::READ}},
                new AstConst{declVarFl, AstConst::StringToParse(), "'0"},
                new AstCond{declVarFl,
                            new AstEq{declVarFl,
                                      new AstVarRef{declVarFl, strength0Varp, VAccess::READ},
                                      new AstVarRef{declVarFl, strength1Varp, VAccess::READ}},
                            getExpressionWhenStrengthsAreQeual(strength0Varp),
                            new AstConst{declVarFl, AstConst::StringToParse(), "'1"}}}};
    }

    // VISITORS
    virtual void visit(AstAssignW* nodep) override {
        if (AstVarRef* const varRefp = VN_CAST(nodep->lhsp(), VarRef)) {
            VVarType varType = varRefp->varp()->varType();
            bool isWire = varType == VVarType::WIRE || varType == VVarType::SUPPLY0
                          || varType == VVarType::SUPPLY1;
            bool isRanged = varRefp->varp()->basicp()->isRanged();
            if (isWire && !isRanged) {
                m_assigns[varRefp->varp()].push_back(nodep);
            } else if (nodep->strengthSpecp()) {
                if (isRanged
                    && varType == VVarType::WIRE)  // declaring supply nets implies having
                                                   // assignment with signal strength, but we don't
                                                   // want to throw UNSUPPORTED just on declaration
                    nodep->v3warn(
                        E_UNSUPPORTED,
                        "Unsupported: Signal strengths are unsupported in wires of size > 1");
                if (!isWire)
                    nodep->v3warn(E_UNSUPPORTED, "Unsupported: Signal strengths are unsupported "
                                                 "on the following variable type: "
                                                     << varType);

                nodep->strengthSpecp()->unlinkFrBack()->deleteTree();
            }
        } else if (nodep->strengthSpecp()) {
            nodep->v3warn(E_UNSUPPORTED,
                          "Unsupported: Assignments with signal strength with LHS of type: "
                              << nodep->lhsp()->prettyTypeName());
        }
    }

    virtual void visit(AstNodeModule* nodep) override {
        UINFO(8, nodep << endl);
        m_assigns = VarToAssignsMap();
        iterateChildren(nodep);
        for (auto& varpAssigns : m_assigns) {
            Assigns& assigns = varpAssigns.second;
            if (assigns.size() > 1  // Handle also highz0 and highz1 strengths in single assignment
                || (assigns.size() == 1 && assigns[0]->strengthSpecp()
                    && (assigns[0]->strengthSpecp()->strength0() == 0
                        || assigns[0]->strengthSpecp()->strength1() == 0))) {
                AstVar* const varp = varpAssigns.first;
                FileLine* const declVarFl = varp->fileline();
                AstVar* const strength0Varp = new AstVar{
                    declVarFl, VVarType::MODULETEMP, varp->name() + "__s0", VFlagChildDType(),
                    new AstBasicDType{declVarFl, VBasicDTypeKwd::INTEGER}};
                AstVar* const strength1Varp = new AstVar{
                    declVarFl, VVarType::MODULETEMP, varp->name() + "__s1", VFlagChildDType(),
                    new AstBasicDType{declVarFl, VBasicDTypeKwd::INTEGER}};
                nodep->addStmtp(strength0Varp);
                nodep->addStmtp(strength1Varp);

                AstBegin* const strengthBlockp = getStrengthComputingBlockp(
                    strength0Varp, strength1Varp, assigns, varp->name());
                nodep->addStmtp(
                    new AstAlways{declVarFl, VAlwaysKwd::ALWAYS, nullptr, strengthBlockp});

                AstAssignW* const accumulatedAssignmentp
                    = getAccumulatedAssignmentp(varp, strength0Varp, strength1Varp);
                nodep->addStmtp(accumulatedAssignmentp);
            } else {
                if (assigns[0]->strengthSpecp())
                    assigns[0]->strengthSpecp()->unlinkFrBack()->deleteTree();
            }
        }
    }

    virtual void visit(AstNetlist* nodep) override { iterateChildrenBackwards(nodep); }

    virtual void visit(AstNode* nodep) override {}

public:
    // CONSTRUCTORS
    explicit SignalStrengthVisitor(AstNode* nodep) { iterate(nodep); }
    virtual ~SignalStrengthVisitor() override {}
};

//######################################################################
// SignalStrength class functions

void V3SignalStrength::strengthAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    { SignalStrengthVisitor{nodep}; }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("signal_strength", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}
