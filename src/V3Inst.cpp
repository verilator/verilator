// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Add temporaries, such as for inst nodes
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
// V3Inst's Transformations:
//
// Each module:
//      Pins:
//          Create a wire assign to interconnect to submodule
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Inst.h"

#include "V3Const.h"
#include "V3Control.h"
#include "V3Width.h"

VL_DEFINE_DEBUG_FUNCTIONS;

static void markContinuousLhs(AstNode* const nodep) {
    nodep->foreach([](AstNodeVarRef* refp) {
        if (refp->access().isWriteOrRW()) refp->varp()->isContinuously(true);
    });
}

// Flip the access of the driven leaves of a pin connection expression so it
// can be used on the LHS of an assignment; index and select operands stay
// read-only. Struct-member selects cannot appear here: V3Width lowers them to
// selects before V3Inst.
static bool markConnectionLhs(AstNodeExpr* const nodep) {
    return V3Inst::forEachDrivenLeaf(nodep, [](AstNodeVarRef* refp) {
        UASSERT_OBJ(refp->access().isReadOnly(), refp, "Input connection should be read-only");
        refp->access(VAccess::WRITE);
    });
}

// Prepare a pin connection expression as the LHS of the reverse (inside-out)
// assignment. Returns the flipped expression on success, nullptr if the
// connection cannot be driven. The input is left unmodified on failure.
static AstNodeExpr* tryConnectionLhs(AstNodeExpr* const nodep) {
    AstNodeExpr* const clonep = nodep->cloneTree(false);
    if (markConnectionLhs(clonep)) return clonep;
    VL_DO_DANGLING(clonep->deleteTree(), clonep);
    return nullptr;
}

// Input port that a clocking block output drives, directly or through a sub-instance.
// A port only reached through a sub-instance is still connected one-way when its
// connection cannot be driven, as it was before clocking drives flowed out.
static bool isClockingDrivenPort(const AstVar* const varp) {
    return varp->isClockingDriven() || varp->isClockingDrivenThru();
}

// A clocking block output inside the cell may drive an input port, while the
// connection keeps feeding the port otherwise (e.g. the same interface used as a
// monitor), so connect them both ways. A single process in the Re-NBA region, with
// the clocking drives (IEEE 1800-2023 14.16), copies whichever side changed since it
// last ran: a continuous assignment from the connection may be re-evaluated after a
// drive, and separate processes per direction may run in either order. The first
// run takes the connection, as the initial values of the copies are arbitrary.
static void addClockingConnection(AstCell* const cellp, const string& name,
                                  AstNodeVarRef* const portp, AstNodeExpr* const connp,
                                  AstNodeExpr* const outRhsp, AstNodeExpr* const drivenp) {
    FileLine* const flp = portp->fileline();
    AstVar* const lastPortVarp
        = new AstVar{flp, VVarType::MODULETEMP, name + "__VlastPort", portp->dtypep()};
    AstVar* const lastConnVarp
        = new AstVar{flp, VVarType::MODULETEMP, name + "__VlastConn", connp->dtypep()};
    AstVar* const didInitVarp
        = new AstVar{flp, VVarType::MODULETEMP, name + "__VdidInit", VFlagBitPacked{}, 1};
    cellp->addNextHere(lastPortVarp);
    cellp->addNextHere(lastConnVarp);
    cellp->addNextHere(didInitVarp);
    const auto newPortp = [&](VAccess access) {
        AstNodeVarRef* const refp = portp->cloneTree(false);
        refp->access(access);
        return refp;
    };
    const auto newRefp
        = [&](AstVar* varp, VAccess access) { return new AstVarRef{flp, varp, access}; };
    portp->access(VAccess::READ);
    AstSenTree* const sentreep
        = new AstSenTree{flp, new AstSenItem{flp, VEdgeType::ET_CHANGED, portp}};
    sentreep->addSensesp(new AstSenItem{flp, VEdgeType::ET_CHANGED, connp->cloneTree(false)});
    AstNodeExpr* const connChangedp
        = new AstNeq{flp, connp->cloneTree(false), newRefp(lastConnVarp, VAccess::READ)};
    connChangedp->dtypeSetBit();
    AstNodeExpr* const firstOrConnChangedp
        = new AstLogOr{flp, new AstLogNot{flp, newRefp(didInitVarp, VAccess::READ)}, connChangedp};
    AstIf* const inIfp
        = new AstIf{flp, firstOrConnChangedp, new AstAssign{flp, newPortp(VAccess::WRITE), connp}};
    AstNodeExpr* const portChangedp
        = new AstNeq{flp, newPortp(VAccess::READ), newRefp(lastPortVarp, VAccess::READ)};
    portChangedp->dtypeSetBit();
    AstNodeExpr* const drivenSinceLastp
        = new AstLogAnd{flp, newRefp(didInitVarp, VAccess::READ), portChangedp};
    AstIf* const outIfp = new AstIf{flp, drivenSinceLastp, new AstAssign{flp, drivenp, outRhsp}};
    outIfp->addElsesp(inIfp);
    AstNode* const stmtsp = outIfp;
    stmtsp->addNext(
        new AstAssign{flp, newRefp(lastPortVarp, VAccess::WRITE), newPortp(VAccess::READ)});
    stmtsp->addNext(
        new AstAssign{flp, newRefp(lastConnVarp, VAccess::WRITE), connp->cloneTree(false)});
    stmtsp->addNext(new AstAssign{flp, newRefp(didInitVarp, VAccess::WRITE),
                                  new AstConst{flp, AstConst::BitTrue{}}});
    cellp->addNextHere(new AstAlwaysReactive{flp, sentreep, stmtsp});
    cellp->addNextHere(
        new AstInitialStatic{flp, new AstAssign{flp, newRefp(didInitVarp, VAccess::WRITE),
                                                new AstConst{flp, AstConst::BitFalse{}}}});
}

//######################################################################
// Inst state, as a visitor of each AstNode

class InstVisitor final : public VNVisitor {
    // NODE STATE
    // Cleared each Cell:
    //  AstPin::user1p()        -> bool.  True if created assignment already
    const VNUser1InUse m_inuser1;

    // STATE
    AstCell* m_cellp = nullptr;  // Current cell

    // METHODS
    // If appropriate, add an AstAlias to connect the given Cell pin to the given expression.
    // Returns true if an alias was made, in which case there is nothing else to do for this pin.
    bool tryAliasPin(AstPin* nodep, AstNodeExpr* exprp) {
        AstVar* const modVarp = nodep->modVarp();
        // An interface reference is aliased via AstAliasScope below, not as a variable
        if (modVarp->isIfaceRef()) return false;
        // Only a whole variable can be aliased, anything else needs the assignment
        AstVarRef* const refp = VN_CAST(exprp, VarRef);
        if (!refp) return false;
        AstVar* const exprVarp = refp->varp();
        // A virtual interface port connected to a real interface can't be an alias
        if (exprVarp->isIfaceRef()) return false;
        // A ref port must become an alias
        if (!modVarp->direction().isRef()) {
            // V3FsmDetect recognizes the registers of an fsm_register_wrapper instance via
            // the assignments of its pins, so leave those as assignments
            AstNodeModule* const cellModp = m_cellp->modp();
            if (V3Control::getFsmRegisterWrapper(cellModp->origName())
                || V3Control::getFsmRegisterWrapper(cellModp->prettyDehashOrigOrName())) {
                return false;
            }
            // A virtual interface method call is dispatched at run time, so the body of an
            // interface reached that way must use the signals of the instance it is called
            // on, not those of whichever instance this connection happens to be made to
            if (const AstIface* const ifacep = VN_CAST(m_cellp->modp(), Iface)) {
                if (ifacep->hasVirtualRef()) return false;
            }
            // Forced signals must keep their own storage, the two sides can be forced separately
            if (modVarp->isForced() || exprVarp->isForced()) return false;
            // Same for public
            if (modVarp->isSigUserRWPublic() || exprVarp->isSigUserRWPublic()) return false;
            // V3Tristate resolved the connected net already, and drives it from the
            // resolution it built for it, so a port merged into it would be driven by
            // the resolution of the instance as well
            if (exprVarp->isTristate()) return false;
        }
        // They will become the same variable, so propagate file-line and attributes
        exprVarp->fileline()->modifyStateInherit(modVarp->fileline());
        modVarp->fileline()->modifyStateInherit(exprVarp->fileline());
        exprVarp->propagateAttrFrom(modVarp);
        modVarp->propagateAttrFrom(exprVarp);
        refp->access(VAccess::READWRITE);
        FileLine* const flp = exprp->fileline();
        AstNodeExpr* const itemsp
            = new AstVarXRef{flp, modVarp, m_cellp->name(), VAccess::READWRITE};
        itemsp->addNext(exprp);
        m_cellp->addNextHere(new AstAlias{flp, itemsp});
        return true;
    }

    // VISITORS
    void visit(AstCell* nodep) override {
        UINFO(4, "  CELL   " << nodep);
        VL_RESTORER(m_cellp);
        m_cellp = nodep;
        // VV*****  We reset user1p() on each cell!!!
        AstNode::user1ClearTree();
        iterateChildren(nodep);
    }

    void visit(AstPin* nodep) override {
        // PIN(p,expr) -> ASSIGNW(VARXREF(p),expr)    (if sub's input)
        //            or  ASSIGNW(expr,VARXREF(p))    (if sub's output)
        UINFO(4, "   PIN  " << nodep);
        if (!nodep->user1()) {
            // Simplify it
            V3Inst::pinReconnectSimple(nodep, m_cellp, false);
        }
        UINFOTREE(9, nodep, "", "Pin_oldb");
        if (!nodep->exprp()) return;  // No-connect
        V3Inst::checkOutputShort(nodep);
        if (!nodep->exprp()) return;  // Connection removed by checkOutputShort
        // Use user1p on the PIN to indicate we created an assign for this pin
        if (!nodep->user1SetOnce()) {
            // Make an ASSIGNW (expr, pin)
            AstNodeExpr* const exprp = VN_AS(nodep->exprp(), NodeExpr)->cloneTree(false);
            UASSERT_OBJ(exprp->width() == nodep->modVarp()->width(), nodep,
                        "Width mismatch, should have been handled in pinReconnectSimple");
            if (nodep->modVarp()->isInout()) {
                nodep->v3fatalSrc("Unsupported: Verilator is a 2-state simulator");
            } else if (nodep->modVarp()->isWritable()) {
                if (!tryAliasPin(nodep, exprp)) {
                    AstNodeExpr* const rhsp = new AstVarXRef{exprp->fileline(), nodep->modVarp(),
                                                             m_cellp->name(), VAccess::READ};
                    markContinuousLhs(exprp);
                    AstAssignW* const assp = new AstAssignW{exprp->fileline(), exprp, rhsp};
                    m_cellp->addNextHere(new AstAlways{assp});
                }
            } else if (nodep->modVarp()->isNonOutput()) {
                if (!tryAliasPin(nodep, exprp)) {
                    AstNodeExpr* const drivenp = isClockingDrivenPort(nodep->modVarp())
                                                     ? tryConnectionLhs(exprp)
                                                     : nullptr;
                    if (drivenp) {
                        FileLine* const flp = exprp->fileline();
                        const auto newPortRefp = [&]() {
                            return new AstVarXRef{flp, nodep->modVarp(), m_cellp->name(),
                                                  VAccess::READ};
                        };
                        addClockingConnection(
                            m_cellp, "__Vclkpin__" + m_cellp->name() + "__" + nodep->name(),
                            newPortRefp(), exprp, newPortRefp(), drivenp);
                        VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
                        return;
                    }
                    // Don't bother moving constants now,
                    // we'll be pushing the const down to the cell soon enough.
                    AstVarXRef* const lhsp = new AstVarXRef{exprp->fileline(), nodep->modVarp(),
                                                            m_cellp->name(), VAccess::WRITE};

                    markContinuousLhs(lhsp);
                    AstAssignW* const assp = new AstAssignW{exprp->fileline(), lhsp, exprp};
                    m_cellp->addNextHere(new AstAlways{assp});
                    UINFOTREE(9, assp, "", "_new");
                }
            } else if (nodep->modVarp()->isIfaceRef()) {
                // Create an AstAliasScope for Vars to Cells so we can
                // link with their scope later
                AstNodeExpr* const lhsp = new AstVarXRef{exprp->fileline(), nodep->modVarp(),
                                                         m_cellp->name(), VAccess::READ};
                const AstVarRef* const refp = VN_CAST(exprp, VarRef);
                const AstVarXRef* const xrefp = VN_CAST(exprp, VarXRef);
                UASSERT_OBJ(refp || xrefp, exprp,
                            "Interfaces: Pin is not connected to a VarRef or VarXRef");
                m_cellp->addNextHere(new AstAliasScope{exprp->fileline(), lhsp, exprp});
            } else {
                nodep->v3error("Assigned pin is neither input nor output");
            }
        }

        // We're done with the pin
        VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
    }

    // Save some time
    void visit(AstNodeExpr*) override {}
    void visit(AstNodeAssign*) override {}
    void visit(AstAlways*) override {}

    //--------------------
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit InstVisitor(AstNetlist* nodep) { iterate(nodep); }
    ~InstVisitor() override = default;
};

//######################################################################
// Inst static function

class InstStatic final {
    InstStatic() = default;  // Static class

    static AstNodeExpr* extendOrSel(FileLine* fl, AstNodeExpr* rhsp, const AstNode* cmpWidthp) {
        if (cmpWidthp->width() > rhsp->width()) {
            rhsp = (rhsp->isSigned() ? static_cast<AstNodeExpr*>(new AstExtendS{fl, rhsp})
                                     : static_cast<AstNodeExpr*>(new AstExtend{fl, rhsp}));
            // Need proper widthMin, which may differ from AstSel created above
            rhsp->dtypeFrom(cmpWidthp);
        } else if (cmpWidthp->width() < rhsp->width()) {
            rhsp = new AstSel{fl, rhsp, 0, cmpWidthp->width()};
            // Need proper widthMin, which may differ from AstSel created above
            rhsp->dtypeFrom(cmpWidthp);
        }
        // else don't change dtype, as might be e.g. array of something
        return rhsp;
    }

public:
    static AstAssignW* pinReconnectSimple(AstPin* pinp, AstCell* cellp, bool forTristate,
                                          bool alwaysCvt) {
        // If a pin connection is "simple" leave it as-is
        // Else create a intermediate wire to perform the interconnect
        // Return the new assignment, if one was made
        // Note this module calls cloneTree() via new AstVar
        AstVar* const pinVarp = pinp->modVarp();
        if (!pinp->exprp()) {
            // No-connect, perhaps promote based on `unconnected_drive,
            // otherwise done
            if (pinVarp->direction() == VDirection::INPUT
                && cellp->modp()->unconnectedDrive().isSetTrue()) {
                pinp->exprp(new AstConst{pinp->fileline(), AstConst::All1{}});
            } else if (pinVarp->direction() == VDirection::INPUT
                       && cellp->modp()->unconnectedDrive().isSetFalse()) {
                pinp->exprp(new AstConst{pinp->fileline(), AstConst::All0{}});
            } else {
                return nullptr;
            }
        }
        const AstVarRef* const connectRefp = VN_CAST(pinp->exprp(), VarRef);
        const AstVarXRef* const connectXRefp = VN_CAST(pinp->exprp(), VarXRef);
        const AstNodeDType* const pinDTypep = pinVarp->dtypep()->skipRefp();
        const AstBasicDType* const pinBasicp = VN_CAST(pinDTypep, BasicDType);
        const AstNodeDType* const connDTypep
            = connectRefp ? connectRefp->varp()->dtypep()->skipRefp() : nullptr;
        const AstBasicDType* const connBasicp = VN_CAST(connDTypep, BasicDType);
        AstAssignW* assignp = nullptr;
        //
        if (!alwaysCvt && connectRefp && connDTypep->sameTree(pinDTypep)
            && !connectRefp->varp()->isSc()) {  // Need the signal as a 'shell' to convert types
            // Done. Same data type
        } else if (!alwaysCvt && connectRefp && connectRefp->varp()->isIfaceRef()) {
            // Done. Interface
        } else if (!alwaysCvt && connectXRefp && connectXRefp->varp()
                   && connectXRefp->varp()->isIfaceRef()) {
        } else if (!alwaysCvt && connBasicp && pinBasicp
                   && connBasicp->width() == pinBasicp->width()
                   && connBasicp->lo() == pinBasicp->lo()
                   && !connectRefp->varp()
                           ->isSc()  // Need the signal as a 'shell' to convert types
                   && connBasicp->width() == pinVarp->width()) {
            // Done. One to one interconnect won't need a temporary variable.
        } else if (!alwaysCvt && !forTristate && VN_IS(pinp->exprp(), Const)) {
            // Done. Constant. Still check for driving an output, like below.
            V3Inst::checkOutputShort(pinp);
            if (!pinp->exprp()) return nullptr;
        } else {
            // Make a new temp wire
            // UINFOTREE(9, pinp, "", "in_pin");
            V3Inst::checkOutputShort(pinp);
            if (!pinp->exprp()) return nullptr;
            // Simplify, so stuff like '{a[0], b[0]}[1]' produced during
            // instance array expansion are brought to normal 'a[0]'
            AstNodeExpr* const pinexprp
                = V3Const::constifyEdit(VN_AS(pinp->exprp(), NodeExpr)->unlinkFrBack());
            const string newvarname
                = (string{pinVarp->isWritable() ? "__Vcellout" : "__Vcellinp"}
                   // Prevent name conflict if both tri & non-tri add signals
                   + (forTristate ? "t" : "") + "__" + cellp->name() + "__" + pinp->name());
            AstVar* const newvarp
                = new AstVar{pinVarp->fileline(), VVarType::MODULETEMP, newvarname, pinVarp};
            // Important to add statement next to cell, in case there is a
            // generate with same named cell
            cellp->addNextHere(newvarp);
            if (pinVarp->isInout()) {
                pinVarp->v3fatalSrc("Unsupported: Inout connections to pins must be"
                                    " direct one-to-one connection (without any expression)");
                // V3Tristate should have cleared up before this point
            } else if (pinVarp->isWritable()) {
                // See also V3Inst
                AstNodeExpr* rhsp = new AstVarRef{pinp->fileline(), newvarp, VAccess::READ};
                UINFO(5, "pinRecon width " << pinVarp->width() << " >? " << rhsp->width() << " >? "
                                           << pinexprp->width());
                rhsp = extendOrSel(pinp->fileline(), rhsp, pinVarp);
                pinp->exprp(new AstVarRef{newvarp->fileline(), newvarp, VAccess::WRITE});
                markContinuousLhs(pinexprp);
                if (VN_IS(pinexprp, NodeStream)) {
                    assignp = new AstAssignW{pinp->fileline(), pinexprp, rhsp};
                    V3Width::streamAssignLowerEdit(assignp);
                } else {
                    AstNodeExpr* rhsSelp = extendOrSel(pinp->fileline(), rhsp, pinexprp);
                    // A reversed array is assigned by the left-to-right order of elements
                    // (IEEE 1800-2023 7.6)
                    const AstUnpackArrayDType* const arrayp
                        = VN_CAST(pinexprp->dtypep()->skipRefp(), UnpackArrayDType);
                    if (arrayp && arrayp->isReverseOf(rhsSelp->dtypep())) {
                        rhsSelp = new AstCvtUnpackToUnpack{pinp->fileline(), rhsSelp,
                                                           pinexprp->dtypep()};
                    }
                    assignp = new AstAssignW{pinp->fileline(), pinexprp, rhsSelp};
                }
            } else {
                // V3Tristate split pins resolve the drive separately
                AstNodeExpr* const drivenp = !forTristate && isClockingDrivenPort(pinVarp)
                                                 ? tryConnectionLhs(pinexprp)
                                                 : nullptr;
                // A port the clocking block drives itself would silently lose the drive.
                // A port only reached through a sub-instance keeps the plain input
                // connection, so connections that compiled before still do.
                if (!drivenp && !forTristate && pinVarp->isClockingDriven()) {
                    pinp->v3error("Unsupported: Clocking block output driving input port "
                                  "through non-decomposable connection "
                                  << pinp->prettyNameQ());
                    VL_DO_DANGLING(pinexprp->deleteTree(), pinexprp);
                    return nullptr;
                }
                if (drivenp) {
                    FileLine* const flp = pinp->fileline();
                    addClockingConnection(
                        cellp, newvarname, new AstVarRef{flp, newvarp, VAccess::READ}, pinexprp,
                        extendOrSel(flp, new AstVarRef{flp, newvarp, VAccess::READ}, drivenp),
                        drivenp);
                    pinp->exprp(new AstVarRef{flp, newvarp, VAccess::READ});
                    return nullptr;
                }
                // V3 width should have range/extended to make the widths correct
                newvarp->isContinuously(true);
                pinp->exprp(new AstVarRef{pinp->fileline(), newvarp, VAccess::READ});
                assignp = new AstAssignW{pinp->fileline(),
                                         new AstVarRef{pinp->fileline(), newvarp, VAccess::WRITE},
                                         pinexprp};
            }
            if (assignp) cellp->addNextHere(new AstAlways{assignp});
            // UINFOTREE(1, pinp, "", "out");
            // UINFOTREE(1, assignp, "", "aout");
        }
        return assignp;
    }
};

//######################################################################
// Inst class functions

bool V3Inst::forEachDrivenLeaf(AstNodeExpr* nodep,
                               const std::function<void(AstNodeVarRef*)>& leaff) {
    if (AstNodeVarRef* const refp = VN_CAST(nodep, NodeVarRef)) {
        leaff(refp);
        return true;
    }
    // Note AstSel (bit/part select) is not an AstNodeSel (array select);
    // both expose fromp() for the selected value.
    if (AstSel* const selp = VN_CAST(nodep, Sel)) return forEachDrivenLeaf(selp->fromp(), leaff);
    if (AstNodeSel* const selp = VN_CAST(nodep, NodeSel)) {
        return forEachDrivenLeaf(selp->fromp(), leaff);
    }
    if (AstConcat* const concatp = VN_CAST(nodep, Concat)) {
        const bool lhsOk = forEachDrivenLeaf(concatp->lhsp(), leaff);
        return forEachDrivenLeaf(concatp->rhsp(), leaff) && lhsOk;
    }
    // V3Width wraps a concatenated port connection in a single replication; V3Const
    // removes it before V3Inst, but V3AssertPre still sees it
    if (AstReplicate* const repp = VN_CAST(nodep, Replicate)) {
        if (VN_AS(repp->countp(), Const)->toUInt() == 1) {
            return forEachDrivenLeaf(repp->srcp(), leaff);
        }
    }
    return false;
}

AstAssignW* V3Inst::pinReconnectSimple(AstPin* pinp, AstCell* cellp, bool forTristate,
                                       bool alwaysCvt) {
    return InstStatic::pinReconnectSimple(pinp, cellp, forTristate, alwaysCvt);
}

void V3Inst::checkOutputShort(const AstPin* nodep) {
    if (nodep->modVarp()->direction() == VDirection::OUTPUT) {
        if (VN_IS(nodep->exprp(), Const) || VN_IS(nodep->exprp(), Extend)
            || (VN_IS(nodep->exprp(), Concat)
                && (VN_IS(VN_AS(nodep->exprp(), Concat)->lhsp(), Const)))) {
            // Uses v3warn for error, as might be found multiple times
            nodep->v3warn(E_PORTSHORT, "Output port is connected to a constant pin,"
                                       " electrical short");
            // Delete so we don't create a 'CONST = ...' assignment
            nodep->exprp()->unlinkFrBack()->deleteTree();
        }
    }
}

//######################################################################
// Inst class visitor

void V3Inst::instAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ":");
    { InstVisitor{nodep}; }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("inst", 0, dumpTreeEitherLevel() >= 3);
}
