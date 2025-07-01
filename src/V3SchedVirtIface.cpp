// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Create triggers necessary for scheduling across
//                         virtual interfaces
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
// V3SchedVirtIface's Transformations:
//
// Each interface type written to via virtual interface, or written to normally but read via
// virtual interface:
//     Create a trigger var for it
// Each AssignW, AssignPost:
//     If it writes to a virtual interface, or to a variable read via virtual interface:
//         Convert to an always
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
    // AstIface::user1() -> AstVarScope*. Trigger var for this interface
    const VNUser1InUse m_user1InUse;

    // TYPES
    using OnWriteToVirtIface = std::function<void(AstVarRef*, AstIface*)>;
    using OnWriteToVirtIfaceMember
        = std::function<void(AstVarRef*, AstIface*, const std::string&)>;

    // STATE
    AstNetlist* const m_netlistp;  // Root node
    AstAssign* m_trigAssignp = nullptr;  // Previous/current trigger assignment
    AstIface* m_trigAssignIfacep = nullptr;  // Interface type whose trigger is assigned
                                             // by m_trigAssignp
    std::string m_trigAssignMemberName;  // Member name whose trigger is assigned
    V3UniqueNames m_vifTriggerNames{"__VvifTrigger"};  // Unique names for virt iface
                                                       // triggers
    VirtIfaceTriggers m_triggers;  // Interfaces and corresponding trigger vars

    // METHODS
    // For each write across a virtual interface boundary
    static void foreachWrittenVirtIface(AstNode* const nodep, const OnWriteToVirtIface& onWrite) {
        nodep->foreach([&](AstVarRef* const refp) {
            if (refp->access().isReadOnly()) return;
            if (AstIfaceRefDType* const dtypep = VN_CAST(refp->varp()->dtypep(), IfaceRefDType)) {
                if (dtypep->isVirtual() && VN_IS(refp->firstAbovep(), MemberSel)) {
                    onWrite(refp, dtypep->ifacep());
                }
            } else if (AstIface* const ifacep = refp->varp()->sensIfacep()) {
                onWrite(refp, ifacep);
            }
        });
    }
    // For each write across a virtual interface boundary (member-level tracking)
    static void foreachWrittenVirtIfaceMember(
        AstNode* const nodep,
        const std::function<void(AstVarRef*, AstIface*, const std::string&)>& onWrite) {
        nodep->foreach([&](AstVarRef* const refp) {
            if (refp->access().isReadOnly()) return;
            if (AstIfaceRefDType* const dtypep = VN_CAST(refp->varp()->dtypep(), IfaceRefDType)) {
                if (dtypep->isVirtual()) {
                    if (AstMemberSel* const memberSelp = VN_CAST(refp->firstAbovep(), MemberSel)) {
                        // Extract the member name from the MemberSel node
                        const std::string memberName = memberSelp->name();
                        onWrite(refp, dtypep->ifacep(), memberName);
                    }
                }
            } else if (AstIface* const ifacep = refp->varp()->sensIfacep()) {
                // For variables marked as interface-sensitive, use the variable name as member
                const std::string memberName = refp->varp()->name();
                onWrite(refp, ifacep, memberName);
            }
        });
    }
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
    // Error on write across a virtual interface boundary
    static void unsupportedWriteToVirtIface(AstNode* nodep, const char* locationp) {
        if (!nodep) return;
        foreachWrittenVirtIface(nodep, [locationp](AstVarRef* const selp, AstIface*) {
            selp->v3warn(E_UNSUPPORTED,
                         "Unsupported: write to virtual interface in " << locationp);
        });
    }
    // Create trigger var for the given interface if it doesn't exist; return a write ref to it
    AstVarRef* createVirtIfaceTriggerRefp(FileLine* const flp, AstIface* ifacep) {
        if (!ifacep->user1()) {
            AstScope* const scopeTopp = m_netlistp->topScopep()->scopep();
            AstVarScope* const vscp = scopeTopp->createTemp(m_vifTriggerNames.get(ifacep), 1);
            ifacep->user1p(vscp);
            m_triggers.emplace_back(std::make_pair(ifacep, vscp));
        }
        return new AstVarRef{flp, VN_AS(ifacep->user1p(), VarScope), VAccess::WRITE};
    }

    // Create trigger reference for a specific interface member
    AstVarRef* createVirtIfaceMemberTriggerRefp(FileLine* const flp, AstIface* ifacep,
                                                const std::string& memberName) {
        // Check if we already have a trigger for this specific member
        AstVarScope* existingTrigger = m_triggers.findMemberTrigger(ifacep, memberName);
        if (!existingTrigger) {
            AstScope* const scopeTopp = m_netlistp->topScopep()->scopep();
            // Create a unique name for this member trigger
            const std::string triggerName = m_vifTriggerNames.get(ifacep) + "__" + memberName;
            AstVarScope* const vscp = scopeTopp->createTemp(triggerName, 1);
            m_triggers.addMemberTrigger(ifacep, memberName, vscp);
            existingTrigger = vscp;
        }
        return new AstVarRef{flp, existingTrigger, VAccess::WRITE};
    }

    // VISITORS
    void visit(AstNodeProcedure* nodep) override {
        VL_RESTORER(m_trigAssignp);
        m_trigAssignp = nullptr;
        VL_RESTORER(m_trigAssignIfacep);
        m_trigAssignIfacep = nullptr;
        VL_RESTORER(m_trigAssignMemberName);
        m_trigAssignMemberName.clear();
        iterateChildren(nodep);
    }
    void visit(AstCFunc* nodep) override {
        VL_RESTORER(m_trigAssignp);
        m_trigAssignp = nullptr;
        VL_RESTORER(m_trigAssignIfacep);
        m_trigAssignIfacep = nullptr;
        VL_RESTORER(m_trigAssignMemberName);
        m_trigAssignMemberName.clear();
        iterateChildren(nodep);
    }
    void visit(AstAssignW* nodep) override {
        if (writesToVirtIface(nodep)) {
            // Convert to always, as we have to assign the trigger var
            nodep->convertToAlways();
        }
    }
    void visit(AstAssignPost* nodep) override {
        if (writesToVirtIface(nodep)) {
            // Convert to always, as we have to assign the trigger var
            FileLine* const flp = nodep->fileline();
            AstAlwaysPost* const postp = new AstAlwaysPost{flp};
            nodep->replaceWith(postp);
            postp->addStmtsp(
                new AstAssign{flp, nodep->lhsp()->unlinkFrBack(), nodep->rhsp()->unlinkFrBack()});
            VL_DO_DANGLING(nodep->deleteTree(), nodep);
        }
    }
    void visit(AstNodeIf* nodep) override {
        unsupportedWriteToVirtIface(nodep->condp(), "if condition");
        {
            VL_RESTORER(m_trigAssignp);
            VL_RESTORER(m_trigAssignIfacep);
            VL_RESTORER(m_trigAssignMemberName);
            iterateAndNextNull(nodep->thensp());
        }
        {
            VL_RESTORER(m_trigAssignp);
            VL_RESTORER(m_trigAssignIfacep);
            VL_RESTORER(m_trigAssignMemberName);
            iterateAndNextNull(nodep->elsesp());
        }
        if (v3Global.usesTiming()) {
            // Clear the trigger assignment, as there could have been timing controls in either
            // branch
            m_trigAssignp = nullptr;
            m_trigAssignIfacep = nullptr;
            m_trigAssignMemberName.clear();
        }
    }
    void visit(AstWhile* nodep) override {
        unsupportedWriteToVirtIface(nodep->precondsp(), "loop condition");
        unsupportedWriteToVirtIface(nodep->condp(), "loop condition");
        unsupportedWriteToVirtIface(nodep->incsp(), "loop increment statement");
        {
            VL_RESTORER(m_trigAssignp);
            VL_RESTORER(m_trigAssignIfacep);
            VL_RESTORER(m_trigAssignMemberName);
            iterateAndNextNull(nodep->stmtsp());
        }
        if (v3Global.usesTiming()) {
            // Clear the trigger assignment, as there could have been timing controls in the loop
            m_trigAssignp = nullptr;
            m_trigAssignIfacep = nullptr;
            m_trigAssignMemberName.clear();
        }
    }
    void visit(AstJumpBlock* nodep) override {
        {
            VL_RESTORER(m_trigAssignp);
            VL_RESTORER(m_trigAssignIfacep);
            VL_RESTORER(m_trigAssignMemberName);
            iterateChildren(nodep);
        }
        if (v3Global.usesTiming()) {
            // Clear the trigger assignment, as there could have been timing controls in the jump
            // block
            m_trigAssignp = nullptr;
            m_trigAssignIfacep = nullptr;
            m_trigAssignMemberName.clear();
        }
    }
    void visit(AstNodeStmt* nodep) override {
        if (v3Global.usesTiming()
            && nodep->exists([](AstNode* nodep) { return nodep->isTimingControl(); })) {
            m_trigAssignp = nullptr;
            m_trigAssignIfacep = nullptr;
            m_trigAssignMemberName.clear();
        }
        FileLine* const flp = nodep->fileline();

        foreachWrittenVirtIfaceMember(nodep, [&](AstVarRef*, AstIface* ifacep,
                                                 const std::string& memberName) {
            if (ifacep != m_trigAssignIfacep || memberName != m_trigAssignMemberName) {
                // Write to different interface member than before - need new trigger assignment
                m_trigAssignIfacep = ifacep;
                m_trigAssignMemberName = memberName;
                m_trigAssignp = nullptr;
            }
            if (!m_trigAssignp) {
                m_trigAssignp
                    = new AstAssign{flp, createVirtIfaceMemberTriggerRefp(flp, ifacep, memberName),
                                    new AstConst{flp, AstConst::BitTrue{}}};
                nodep->addNextHere(m_trigAssignp);
            }
        });
        // Fallback to whole-interface tracking if no member-specific assignments found
        if (!m_trigAssignp) {
            foreachWrittenVirtIface(nodep, [&](AstVarRef*, AstIface* ifacep) {
                if (ifacep != m_trigAssignIfacep) {
                    m_trigAssignIfacep = ifacep;
                    m_trigAssignMemberName.clear();
                    m_trigAssignp = nullptr;
                }
                if (!m_trigAssignp) {
                    m_trigAssignp = new AstAssign{flp, createVirtIfaceTriggerRefp(flp, ifacep),
                                                  new AstConst{flp, AstConst::BitTrue{}}};
                    nodep->addNextHere(m_trigAssignp);
                }
            });
        }
    }
    void visit(AstNodeExpr*) override {}  // Accelerate
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
    if (v3Global.hasVirtIfaces()) {
        VirtIfaceVisitor visitor{nodep};
        V3Global::dumpCheckGlobalTree("sched_vif", 0, dumpTreeEitherLevel() >= 6);
        return visitor.take_triggers();
    }
    return {};
}

}  //namespace V3Sched
