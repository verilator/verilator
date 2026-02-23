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

            // Try to find the RHS of the parent assignment so we can make the trigger
            // conditional on the value actually changing. This avoids spurious ICO/NBA
            // re-evaluations when combinational logic unconditionally writes the same value
            // to a virtual interface signal (e.g. via continuous assign statements).
            AstNodeExpr* oldValReadp = nullptr;
            AstNodeExpr* newValExprp = nullptr;
            if (const AstNodeAssign* const parentAssignp
                = VN_CAST(nodep->backp(), NodeAssign)) {
                // Only apply conditional trigger for continuous assigns (AstAssignW).
                // These are the only context where repeatedly writing the same value
                // causes infinite ICO convergence loops. Procedural assigns (blocking
                // and non-blocking) are clocked and don't have this problem; applying
                // the conditional trigger to them introduces circular ordering
                // dependencies that the scheduler cannot resolve.
                if (VN_IS(parentAssignp, AssignW) && parentAssignp->lhsp() == nodep) {
                    // Clone nodep as a READ to capture the old value before the write.
                    T const clonedNodep = nodep->cloneTree(false);
                    clonedNodep->access(VAccess::READ);
                    oldValReadp = clonedNodep;
                    // Clone the RHS as new value expression
                    newValExprp = parentAssignp->rhsp()->cloneTree(false);
                }
            }

            VNRelinker relinker;
            nodep->unlinkFrBack(&relinker);

            // Create the trigger write ref (this also ensures the trigger varscope exists)
            AstVarRef* const trigWriteRefp
                = createVirtIfaceMemberTriggerRefp(flp, ifacep, memberVarp);

            AstNodeStmt* triggerStmtp = nullptr;
            if (oldValReadp && newValExprp) {
                // Conditional trigger: only fire if the value is actually changing.
                // Generated: trigger = (old_vif_read != new_value_expr)
                // This avoids infinite ICO/NBA convergence loops when combinational logic
                // repeatedly writes the same value to a virtual interface signal.
                AstNodeExpr* const changedExprp = new AstNeq{flp, oldValReadp, newValExprp};
                triggerStmtp = new AstAssign{flp, trigWriteRefp, changedExprp};
            } else {
                // Fall back to unconditional trigger if we can't determine the new value
                triggerStmtp = new AstAssign{flp, trigWriteRefp,
                                             new AstConst{flp, AstConst::BitTrue{}}};
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
