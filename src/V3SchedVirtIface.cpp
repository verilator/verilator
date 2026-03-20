// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Create triggers necessary for scheduling across
//                         virtual interfaces
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2003-2026 Wilson Snyder
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
    // AstMemberSel::user1() -> bool. Whether it has been visited
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
    std::map<std::pair<const AstIface*, const AstVar*>, AstVarScope*>
        m_oldVals;  // Shadow variables for old values

    // METHODS
    // For each write across a virtual interface boundary
    // Returns true if there is a write across a virtual interface boundary
    static bool writesToVirtIface(const AstNode* const nodep) {
        return nodep->exists([](const AstVarRef* const refp) {
            if (!refp->access().isWriteOrRW()) return false;
            AstIfaceRefDType* const dtypep = VN_CAST(refp->varp()->dtypep(), IfaceRefDType);
            const bool writesToVirtIfaceMember
                = (dtypep && dtypep->isVirtual() && VN_IS(refp->firstAbovep(), MemberSel));
            const bool writesToIfaceSensVar = refp->varp()->isVirtIface();
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

    // Get or create an oldval shadow variable for a VIF member.
    // The shadow variable tracks the previous value to enable conditional triggering.
    AstVarScope* getOrCreateOldVal(const AstIface* ifacep, const AstVar* memberVarp) {
        const auto key = std::make_pair(ifacep, memberVarp);
        const auto it = m_oldVals.find(key);
        if (it != m_oldVals.end()) return it->second;

        AstScope* const scopeTopp = m_netlistp->topScopep()->scopep();
        const std::string name = "__Vvif_oldval_" + ifacep->name() + "_" + memberVarp->name();
        AstVarScope* const vscp = scopeTopp->createTemp(name, memberVarp->dtypep());
        // Ignore writes for scheduling so we don't introduce OrderGraph cycles
        vscp->varp()->setIgnoreSchedWrite();
        m_oldVals[key] = vscp;
        return vscp;
    }

    template <typename T>
    void handleIface(T nodep) {
        static_assert(std::is_same<typename std::remove_cv<T>::type,
                                   typename std::add_pointer<AstVarRef>::type>::value
                          || std::is_same<typename std::remove_cv<T>::type,
                                          typename std::add_pointer<AstMemberSel>::type>::value,
                      "Node has to be of AstVarRef* or AstMemberSel* type");
        if (nodep->access().isReadOnly()) return;
        if (nodep->user1SetOnce()) return;
        AstIface* ifacep = nullptr;
        AstVar* memberVarp = nullptr;
        if (nodep->varp()->isVirtIface()) {
            if (AstMemberSel* const memberSelp = VN_CAST(nodep->firstAbovep(), MemberSel)) {
                ifacep = VN_AS(nodep->varp()->dtypep(), IfaceRefDType)->ifacep();
                memberVarp = memberSelp->varp();
            }
        } else if ((ifacep = nodep->varp()->sensIfacep())) {
            memberVarp = nodep->varp();
        }

        if (ifacep && memberVarp) {
            FileLine* const flp = nodep->fileline();

            // Try to find the parent assignment to enable conditional triggering.
            // If the write is the LHS of an assignment, we compare the old value
            // (stored in a shadow variable) against the new value (RHS). The trigger
            // only fires when the value actually changes, preventing infinite
            // convergence loops.
            AstNodeExpr* rhsClone1 = nullptr;  // For old != new comparison
            AstNodeExpr* rhsClone2 = nullptr;  // For oldval update
            AstVarScope* oldValVscp = nullptr;
            if (const AstNodeAssign* const parentAssignp = VN_CAST(nodep->backp(), NodeAssign)) {
                if (parentAssignp->lhsp() == static_cast<const AstNode*>(nodep)) {
                    oldValVscp = getOrCreateOldVal(ifacep, memberVarp);
                    AstNode* const cloned1 = parentAssignp->rhsp()->cloneTree(false);
                    rhsClone1 = VN_CAST(cloned1, NodeExpr);
                    if (rhsClone1) {
                        AstNode* const cloned2 = parentAssignp->rhsp()->cloneTree(false);
                        rhsClone2 = VN_CAST(cloned2, NodeExpr);
                        if (!rhsClone2) {
                            VL_DO_DANGLING(rhsClone1->deleteTree(), rhsClone1);
                            VL_DO_DANGLING(cloned2->deleteTree(), cloned2);
                            oldValVscp = nullptr;
                        }
                    } else {
                        VL_DO_DANGLING(cloned1->deleteTree(), cloned1);
                        oldValVscp = nullptr;
                    }
                }
            }

            VNRelinker relinker;
            nodep->unlinkFrBack(&relinker);

            AstVarRef* const trigWriteRefp
                = createVirtIfaceMemberTriggerRefp(flp, ifacep, memberVarp);

            AstNodeStmt* triggerStmtp = nullptr;
            if (oldValVscp && rhsClone1 && rhsClone2) {
                // Conditional trigger: trigger = (oldval != newval)
                AstNodeExpr* const oldReadp = new AstVarRef{flp, oldValVscp, VAccess::READ};
                AstNodeExpr* const changedExprp = new AstNeq{flp, oldReadp, rhsClone1};
                triggerStmtp = new AstAssign{flp, trigWriteRefp, changedExprp};
                // Update shadow: oldval = newval
                triggerStmtp->addNext(
                    new AstAssign{flp, new AstVarRef{flp, oldValVscp, VAccess::WRITE}, rhsClone2});
            } else {
                // Fall back to unconditional trigger
                triggerStmtp
                    = new AstAssign{flp, trigWriteRefp, new AstConst{flp, AstConst::BitTrue{}}};
            }

            relinker.relink(new AstExprStmt{flp, triggerStmtp, nodep});
        }
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
    void visit(AstMemberSel* const nodep) override { handleIface(nodep); }
    void visit(AstVarRef* const nodep) override { handleIface(nodep); }
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
