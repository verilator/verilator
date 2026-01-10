// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Create triggers necessary for scheduling across
//                         virtual interfaces
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
// V3SchedVirtIface's Transformations:
//
// Each interface type written to via virtual interface, or written to normally but read via
// virtual interface:
//     Create a trigger var for it
// Each statement:
//     If it writes to a virtual interface, or to a variable read via virtual interface:
//         Set the corresponding trigger to 1
//         If the write is done by an AssignDly, the trigger is also set by AssignDly
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3AstNodeExpr.h"
#include "V3Sched.h"
#include "V3UniqueNames.h"

VL_DEFINE_DEBUG_FUNCTIONS;

namespace V3Sched {

namespace {

class VirtIfaceVisitor final : public VNVisitor {
private:
    // NODE STATE
    // AstVarRef::user1() -> bool. Whether it has been visited
    const VNUser1InUse m_user1InUse;

    // TYPES
    using OnWriteToVirtIface = std::function<void(AstVarRef*, AstIface*)>;
    using OnWriteToVirtIfaceMember
        = std::function<void(AstVarRef*, AstIface*, const std::string&)>;

    // STATE
    AstNetlist* const m_netlistp;  // Root node
    V3UniqueNames m_vifTriggerNames{"__VvifTrigger"};  // Unique names for virt iface
                                                       // triggers
    VirtIfaceTriggers m_triggers;  // Interfaces and corresponding trigger vars

    // METHODS
    // For each write across a virtual interface boundary
    // Returns true if there is a write across a virtual interface boundary
    static bool writesToVirtIface(const AstNode* const nodep) {
        return nodep->exists([](const AstVarRef* const refp) {
            if (!refp->access().isWriteOrRW()) return false;
            AstIfaceRefDType* const dtypep = VN_CAST(refp->varp()->dtypep(), IfaceRefDType);
            const bool writesToVirtIfaceMember
                = (dtypep && dtypep->isVirtual() && VN_IS(refp->firstAbovep(), MemberSel));
            const bool writesToIfaceSensVar = refp->varp()->sensIfacep();
            return writesToVirtIfaceMember || writesToIfaceSensVar;
        });
    }

    // Create trigger reference for a specific interface member
    AstVarRef* createVirtIfaceMemberTriggerRefp(FileLine* const flp, AstIface* ifacep,
                                                const AstVar* memberVarp) {
        // Check if we already have a trigger for this specific member
        AstVarScope* existingTrigger = m_triggers.findMemberTrigger(ifacep, memberVarp);
        if (!existingTrigger) {
            AstScope* const scopeTopp = m_netlistp->topScopep()->scopep();
            // Create a unique name for this member trigger
            const std::string triggerName
                = m_vifTriggerNames.get(ifacep) + "_Vtrigm_" + memberVarp->name();
            AstVarScope* const vscp = scopeTopp->createTemp(triggerName, 1);
            m_triggers.addMemberTrigger(ifacep, memberVarp, vscp);
            existingTrigger = vscp;
        }
        return new AstVarRef{flp, existingTrigger, VAccess::WRITE};
    }

    // VISITORS
    void visit(AstNodeProcedure* nodep) override {
        // Not sure if needed, but be paranoid to match previous behavior as didn't optimize
        // before ..
        if (VN_IS(nodep, AlwaysPost) && writesToVirtIface(nodep)) {
            nodep->foreach([](AstVarRef* refp) { refp->varScopep()->optimizeLifePost(false); });
        }
        iterateChildren(nodep);
    }
    void visit(AstVarRef* const nodep) override {
        if (nodep->access().isReadOnly()) return;
        if (nodep->user1SetOnce()) return;
        AstIface* ifacep = nullptr;
        AstVar* memberVarp = nullptr;
        if (AstIfaceRefDType* const dtypep = VN_CAST(nodep->varp()->dtypep(), IfaceRefDType)) {
            if (dtypep->isVirtual()) {
                if (AstMemberSel* const memberSelp = VN_CAST(nodep->firstAbovep(), MemberSel)) {
                    // Extract the member varp from the MemberSel node
                    memberVarp = memberSelp->varp();
                    ifacep = dtypep->ifacep();
                }
            }
        } else if ((ifacep = nodep->varp()->sensIfacep())) {
            memberVarp = nodep->varp();
        }

        if (ifacep && memberVarp) {
            FileLine* const flp = nodep->fileline();
            VNRelinker relinker;
            nodep->unlinkFrBack(&relinker);
            relinker.relink(new AstExprStmt{
                flp,
                new AstAssign{flp, createVirtIfaceMemberTriggerRefp(flp, ifacep, memberVarp),
                              new AstConst{flp, AstConst::BitTrue{}}},
                nodep});
        }
    }
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit VirtIfaceVisitor(AstNetlist* nodep)
        : m_netlistp{nodep} {
        iterate(nodep);
    }
    ~VirtIfaceVisitor() override = default;

    // METHODS
    VirtIfaceTriggers take_triggers() { return std::move(m_triggers); }
};

}  //namespace

VirtIfaceTriggers makeVirtIfaceTriggers(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ":");
    VirtIfaceTriggers triggers{};
    if (v3Global.hasVirtIfaces()) {
        triggers = VirtIfaceVisitor{nodep}.take_triggers();
        // Dump afer destructor so VNDeleter runs
        V3Global::dumpCheckGlobalTree("sched_vif", 0, dumpTreeEitherLevel() >= 6);
    }
    return triggers;
}

}  //namespace V3Sched
