// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Add temporaries, such as for inst nodes
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2020 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
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

#include "config_build.h"
#include "verilatedos.h"

#include "V3Global.h"
#include "V3Inst.h"
#include "V3Ast.h"
#include "V3Changed.h"
#include "V3Const.h"

#include <algorithm>
#include <cstdarg>

//######################################################################
// Inst state, as a visitor of each AstNode

class InstVisitor : public AstNVisitor {
private:
    // NODE STATE
    // Cleared each Cell:
    //  AstPin::user1p()        -> bool.  True if created assignment already
    AstUser1InUse       m_inuser1;

    // STATE
    AstCell*            m_cellp;        // Current cell

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    // VISITORS
    virtual void visit(AstCell* nodep) VL_OVERRIDE {
        UINFO(4,"  CELL   "<<nodep<<endl);
        m_cellp = nodep;
        //VV*****  We reset user1p() on each cell!!!
        AstNode::user1ClearTree();
        iterateChildren(nodep);
        m_cellp = NULL;
    }
    virtual void visit(AstPin* nodep) VL_OVERRIDE {
        // PIN(p,expr) -> ASSIGNW(VARXREF(p),expr)    (if sub's input)
        //            or  ASSIGNW(expr,VARXREF(p))    (if sub's output)
        UINFO(4,"   PIN  "<<nodep<<endl);
        if (!nodep->exprp()) return;  // No-connect
        if (debug()>=9) nodep->dumpTree(cout, "  Pin_oldb: ");
        V3Inst::checkOutputShort(nodep);
        // Use user1p on the PIN to indicate we created an assign for this pin
        if (!nodep->user1SetOnce()) {
            // Simplify it
            V3Inst::pinReconnectSimple(nodep, m_cellp, false);
            // Make an ASSIGNW (expr, pin)
            AstNode* exprp = nodep->exprp()->cloneTree(false);
            UASSERT_OBJ(exprp->width() == nodep->modVarp()->width(), nodep,
                        "Width mismatch, should have been handled in pinReconnectSimple");
            if (nodep->modVarp()->isInoutish()) {
                nodep->v3fatalSrc("Unsupported: Verilator is a 2-state simulator");
            } else if (nodep->modVarp()->isWritable()) {
                AstNode* rhsp = new AstVarXRef(exprp->fileline(),
                                               nodep->modVarp(), m_cellp->name(), false);
                AstAssignW* assp = new AstAssignW(exprp->fileline(), exprp, rhsp);
                m_cellp->addNextHere(assp);
            } else if (nodep->modVarp()->isNonOutput()) {
                // Don't bother moving constants now,
                // we'll be pushing the const down to the cell soon enough.
                AstNode* assp = new AstAssignW
                    (exprp->fileline(),
                     new AstVarXRef(exprp->fileline(), nodep->modVarp(), m_cellp->name(), true),
                     exprp);
                m_cellp->addNextHere(assp);
                if (debug()>=9) assp->dumpTree(cout, "     _new: ");
            } else if (nodep->modVarp()->isIfaceRef()
                       || (VN_IS(nodep->modVarp()->subDTypep(), UnpackArrayDType)
                           && VN_IS(VN_CAST(nodep->modVarp()->subDTypep(),
                                            UnpackArrayDType)->subDTypep(), IfaceRefDType))) {
                // Create an AstAssignVarScope for Vars to Cells so we can
                // link with their scope later
                AstNode* lhsp = new AstVarXRef(exprp->fileline(),
                                               nodep->modVarp(), m_cellp->name(), false);
                const AstVarRef* refp = VN_CAST(exprp, VarRef);
                const AstVarXRef* xrefp = VN_CAST(exprp, VarXRef);
                UASSERT_OBJ(refp || xrefp, exprp,
                            "Interfaces: Pin is not connected to a VarRef or VarXRef");
                AstAssignVarScope* assp = new AstAssignVarScope(exprp->fileline(), lhsp, exprp);
                m_cellp->addNextHere(assp);
            } else {
                nodep->v3error("Assigned pin is neither input nor output");
            }
        }

        // We're done with the pin
        VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
    }

    virtual void visit(AstUdpTable* nodep) VL_OVERRIDE {
        if (!v3Global.opt.bboxUnsup()) {
            // If we support primitives, update V3Undriven to remove special case
            nodep->v3error("Unsupported: Verilog 1995 UDP Tables.  Use --bbox-unsup to ignore tables.");
        }
    }

    // Save some time
    virtual void visit(AstNodeMath*) VL_OVERRIDE {}
    virtual void visit(AstNodeAssign*) VL_OVERRIDE {}
    virtual void visit(AstAlways*) VL_OVERRIDE {}

    //--------------------
    // Default: Just iterate
    virtual void visit(AstNode* nodep) VL_OVERRIDE {
        iterateChildren(nodep);
    }
public:
    // CONSTRUCTORS
    explicit InstVisitor(AstNetlist* nodep) {
        m_cellp = NULL;
        //
        iterate(nodep);
    }
    virtual ~InstVisitor() {}
};

//######################################################################

class InstDeModVarVisitor : public AstNVisitor {
    // Expand all module variables, and save names for later reference
private:
    // STATE
    typedef std::map<string,AstVar*> VarNameMap;
    VarNameMap  m_modVarNameMap;  // Per module, name of cloned variables

    VL_DEBUG_FUNC;  // Declare debug()

    // VISITORS
    virtual void visit(AstVar* nodep) VL_OVERRIDE {
        if (VN_IS(nodep->dtypep(), IfaceRefDType)) {
            UINFO(8,"   dm-1-VAR    "<<nodep<<endl);
            insert(nodep);
        }
        iterateChildren(nodep);
    }
    // Save some time
    virtual void visit(AstNodeMath*) VL_OVERRIDE {}
    // Default: Just iterate
    virtual void visit(AstNode* nodep) VL_OVERRIDE {
        iterateChildren(nodep);
    }
public:
    // METHODS
    void insert(AstVar* nodep) {
        UINFO(8,"    dmINSERT    "<<nodep<<endl);
        m_modVarNameMap.insert(make_pair(nodep->name(), nodep));
    }
    AstVar* find(const string& name) {
        VarNameMap::iterator it = m_modVarNameMap.find(name);
        if (it != m_modVarNameMap.end()) {
            return it->second;
        } else {
            return NULL;
        }
    }
    void dump() {
        for (VarNameMap::iterator it=m_modVarNameMap.begin(); it!=m_modVarNameMap.end(); ++it) {
            cout<<"-namemap: "<<it->first<<" -> "<<it->second<<endl;
        }
    }
public:
    // CONSTRUCTORS
    explicit InstDeModVarVisitor() {}
    void main(AstNodeModule* nodep) {
        UINFO(8,"  dmMODULE    "<<nodep<<endl);
        m_modVarNameMap.clear();
        iterate(nodep);
    }
    virtual ~InstDeModVarVisitor() {}
};

//######################################################################

class InstDeVisitor : public AstNVisitor {
    // Find all cells with arrays, and convert to non-arrayed
private:
    // STATE
    AstRange*   m_cellRangep;  // Range for arrayed instantiations, NULL for normal instantiations
    int         m_instSelNum;  // Current instantiation count 0..N-1
    InstDeModVarVisitor m_deModVars;  // State of variables for current cell module

    typedef std::map<string,AstVar*> VarNameMap;

    VL_DEBUG_FUNC;  // Declare debug()

    // VISITORS
    virtual void visit(AstVar* nodep) VL_OVERRIDE {
        if (VN_IS(nodep->dtypep(), UnpackArrayDType)
            && VN_IS(VN_CAST(nodep->dtypep(), UnpackArrayDType)->subDTypep(), IfaceRefDType)) {
            UINFO(8,"   dv-vec-VAR    "<<nodep<<endl);
            AstUnpackArrayDType* arrdtype = VN_CAST(nodep->dtypep(), UnpackArrayDType);
            AstNode* prevp = NULL;
            for (int i = arrdtype->lsb(); i <= arrdtype->msb(); ++i) {
                string varNewName = nodep->name() + "__BRA__" + cvtToStr(i) + "__KET__";
                UINFO(8,"VAR name insert "<<varNewName<<"  "<<nodep<<endl);
                if (!m_deModVars.find(varNewName)) {
                    AstIfaceRefDType* ifaceRefp
                        = VN_CAST(arrdtype->subDTypep(), IfaceRefDType)->cloneTree(false);
                    arrdtype->addNextHere(ifaceRefp);
                    ifaceRefp->cellp(NULL);

                    AstVar* varNewp = nodep->cloneTree(false);
                    varNewp->name(varNewName);
                    varNewp->origName(varNewp->origName() + "__BRA__" + cvtToStr(i) + "__KET__");
                    varNewp->dtypep(ifaceRefp);
                    m_deModVars.insert(varNewp);
                    if (!prevp) {
                        prevp = varNewp;
                    } else {
                        prevp->addNextHere(varNewp);
                    }
                }
            }
            if (prevp) nodep->addNextHere(prevp);
            if (prevp && debug()==9) { prevp->dumpTree(cout, "newintf: "); cout << endl; }
        }
        iterateChildren(nodep);
    }

    virtual void visit(AstCell* nodep) VL_OVERRIDE {
        UINFO(4,"  CELL   "<<nodep<<endl);
        // Find submodule vars
        UASSERT_OBJ(nodep->modp(), nodep, "Unlinked");
        m_deModVars.main(nodep->modp());
        //
        if (nodep->rangep()) {
            m_cellRangep = nodep->rangep();

            AstVar* ifaceVarp = VN_CAST(nodep->nextp(), Var);
            bool isIface = ifaceVarp
                && VN_IS(ifaceVarp->dtypep(), UnpackArrayDType)
                && VN_IS(VN_CAST(ifaceVarp->dtypep(),
                                 UnpackArrayDType)->subDTypep(), IfaceRefDType);

            // Make all of the required clones
            for (int i = 0; i < m_cellRangep->elementsConst(); i++) {
                m_instSelNum = m_cellRangep->littleEndian() ? (m_cellRangep->elementsConst() - 1 - i) : i;
                int instNum = m_cellRangep->lsbConst() + i;

                AstCell* newp = nodep->cloneTree(false);
                nodep->addNextHere(newp);
                // Remove ranging and fix name
                newp->rangep()->unlinkFrBack()->deleteTree();
                // Somewhat illogically, we need to rename the original name of the cell too.
                // as that is the name users expect for dotting
                // The spec says we add [x], but that won't work in C...
                newp->name(newp->name()+"__BRA__"+cvtToStr(instNum)+"__KET__");
                newp->origName(newp->origName()+"__BRA__"+cvtToStr(instNum)+"__KET__");
                UINFO(8,"    CELL loop  "<<newp<<endl);

                // If this AstCell is actually an interface instantiation, also clone the IfaceRef
                // within the same parent module as the cell
                if (isIface) {
                    AstUnpackArrayDType* arrdtype = VN_CAST(ifaceVarp->dtypep(), UnpackArrayDType);
                    AstIfaceRefDType* origIfaceRefp = VN_CAST(arrdtype->subDTypep(), IfaceRefDType);
                    origIfaceRefp->cellp(NULL);
                    AstVar* varNewp = ifaceVarp->cloneTree(false);
                    AstIfaceRefDType* ifaceRefp
                        = VN_CAST(arrdtype->subDTypep(), IfaceRefDType)->cloneTree(false);
                    arrdtype->addNextHere(ifaceRefp);
                    ifaceRefp->cellp(newp);
                    ifaceRefp->cellName(newp->name());
                    varNewp->name(varNewp->name() + "__BRA__" + cvtToStr(instNum) + "__KET__");
                    varNewp->origName(varNewp->origName() + "__BRA__" + cvtToStr(instNum) + "__KET__");
                    varNewp->dtypep(ifaceRefp);
                    newp->addNextHere(varNewp);
                    if (debug()==9) { varNewp->dumpTree(cout, "newintf: "); cout << endl; }
                }
                // Fixup pins
                iterateAndNextNull(newp->pinsp());
                if (debug()==9) { newp->dumpTree(cout, "newcell: "); cout<<endl; }
            }

            // Done.  Delete original
            m_cellRangep = NULL;
            if (isIface) {
                ifaceVarp->unlinkFrBack();
                VL_DO_DANGLING(pushDeletep(ifaceVarp), ifaceVarp);
            }
            nodep->unlinkFrBack(); VL_DO_DANGLING(pushDeletep(nodep), nodep);
        } else {
            m_cellRangep = NULL;
            iterateChildren(nodep);
        }
    }

    virtual void visit(AstPin* nodep) VL_OVERRIDE {
        // Any non-direct pins need reconnection with a part-select
        if (!nodep->exprp()) return;  // No-connect
        if (m_cellRangep) {
            UINFO(4,"   PIN  "<<nodep<<endl);
            int pinwidth = nodep->modVarp()->width();
            int expwidth = nodep->exprp()->width();
            std::pair<uint32_t,uint32_t> pinDim = nodep->modVarp()->dtypep()->dimensions(false);
            std::pair<uint32_t,uint32_t> expDim = nodep->exprp()->dtypep()->dimensions(false);
            UINFO(4,"   PINVAR  "<<nodep->modVarp()<<endl);
            UINFO(4,"   EXP     "<<nodep->exprp()<<endl);
            UINFO(4,"   pinwidth ew="<<expwidth<<" pw="<<pinwidth
                  <<"  ed="<<expDim.first<<","<<expDim.second
                  <<"  pd="<<pinDim.first<<","<<pinDim.second<<endl);
            if (expDim.first == pinDim.first && expDim.second == pinDim.second+1) {
                // Connection to array, where array dimensions match the instant dimension
                AstRange* rangep = VN_CAST(nodep->exprp()->dtypep(), UnpackArrayDType)->rangep();
                int arraySelNum = rangep->littleEndian()
                    ? (rangep->elementsConst() - 1 - m_instSelNum) : m_instSelNum;
                AstNode* exprp = nodep->exprp()->unlinkFrBack();
                exprp = new AstArraySel(exprp->fileline(), exprp, arraySelNum);
                nodep->exprp(exprp);
            } else if (expwidth == pinwidth) {
                // NOP: Arrayed instants: widths match so connect to each instance
            } else if (expwidth == pinwidth*m_cellRangep->elementsConst()) {
                // Arrayed instants: one bit for each of the instants (each
                // assign is 1 pinwidth wide)
                if (m_cellRangep->littleEndian()) {
                    nodep->exprp()->v3warn(
                        LITENDIAN,
                        "Little endian cell range connecting to vector: MSB < LSB of cell range: "
                        <<m_cellRangep->lsbConst()<<":"<<m_cellRangep->msbConst());
                }
                AstNode* exprp = nodep->exprp()->unlinkFrBack();
                bool inputPin = nodep->modVarp()->isNonOutput();
                if (!inputPin && !VN_IS(exprp, VarRef)
                    && !VN_IS(exprp, Concat)  // V3Const will collapse the SEL with the one we're about to make
                    && !VN_IS(exprp, Sel)) {  // V3Const will collapse the SEL with the one we're about to make
                    nodep->v3error("Unsupported: Per-bit array instantiations with output connections to non-wires.");
                    // Note spec allows more complicated matches such as slices and such
                }
                exprp = new AstSel(exprp->fileline(), exprp,
                                   pinwidth*m_instSelNum,
                                   pinwidth);
                nodep->exprp(exprp);
            } else {
                nodep->v3fatalSrc("Width mismatch; V3Width should have errored out.");
            }
        } else if (AstArraySel* arrselp = VN_CAST(nodep->exprp(), ArraySel)) {
            if (AstUnpackArrayDType* arrp = VN_CAST(arrselp->lhsp()->dtypep(), UnpackArrayDType)) {
                if (!VN_IS(arrp->subDTypep(), IfaceRefDType))
                    return;

                V3Const::constifyParamsEdit(arrselp->rhsp());
                const AstConst* constp = VN_CAST(arrselp->rhsp(), Const);
                if (!constp) {
                    nodep->v3error("Unsupported: Non-constant index when passing interface to module");
                    return;
                }
                string index = AstNode::encodeNumber(constp->toSInt());
                AstVarRef* varrefp = VN_CAST(arrselp->lhsp(), VarRef);
                AstVarXRef* newp = new AstVarXRef(nodep->fileline(),
                                                  varrefp->name()+"__BRA__"+index+"__KET__",
                                                  "", true);
                newp->dtypep(nodep->modVarp()->dtypep());
                newp->packagep(varrefp->packagep());
                arrselp->addNextHere(newp);
                VL_DO_DANGLING(arrselp->unlinkFrBack()->deleteTree(), arrselp);
            }
        } else {
            AstVar* pinVarp = nodep->modVarp();
            AstUnpackArrayDType* pinArrp = VN_CAST(pinVarp->dtypep(), UnpackArrayDType);
            if (!pinArrp || !VN_IS(pinArrp->subDTypep(), IfaceRefDType))
                return;
            AstNode* prevp = NULL;
            AstNode* prevPinp = NULL;
            // Clone the var referenced by the pin, and clone each var referenced by the varref
            // Clone pin varp:
            for (int i = pinArrp->lsb(); i <= pinArrp->msb(); ++i) {
                string varNewName = pinVarp->name() + "__BRA__" + cvtToStr(i) + "__KET__";
                AstVar* varNewp = NULL;

                // Only clone the var once for all usages of a given child module
                if (!pinVarp->backp()) {
                    varNewp = m_deModVars.find(varNewName);
                } else {
                    AstIfaceRefDType* ifaceRefp = VN_CAST(pinArrp->subDTypep(), IfaceRefDType);
                    ifaceRefp->cellp(NULL);
                    varNewp = pinVarp->cloneTree(false);
                    varNewp->name(varNewName);
                    varNewp->origName(varNewp->origName() + "__BRA__" + cvtToStr(i) + "__KET__");
                    varNewp->dtypep(ifaceRefp);
                    m_deModVars.insert(varNewp);
                    if (!prevp) {
                        prevp = varNewp;
                    } else {
                        prevp->addNextHere(varNewp);
                    }
                }
                if (!varNewp) {
                    if (debug()>=9) m_deModVars.dump();
                    nodep->v3fatalSrc("Module dearray failed for "
                                      <<AstNode::prettyNameQ(varNewName));
                }

                // But clone the pin for each module instance
                // Now also clone the pin itself and update its varref
                AstPin* newp = nodep->cloneTree(false);
                newp->modVarp(varNewp);
                newp->name(newp->name() + "__BRA__" + cvtToStr(i) + "__KET__");
                // And replace exprp with a new varxref
                const AstVarRef* varrefp = VN_CAST(newp->exprp(), VarRef);
                string newname = varrefp->name() + "__BRA__" + cvtToStr(i) + "__KET__";
                AstVarXRef* newVarXRefp = new AstVarXRef(nodep->fileline(), newname, "", true);
                newVarXRefp->varp(newp->modVarp());
                newVarXRefp->dtypep(newp->modVarp()->dtypep());
                newp->exprp()->unlinkFrBack()->deleteTree();
                newp->exprp(newVarXRefp);
                if (!prevPinp) {
                    prevPinp = newp;
                } else {
                    prevPinp->addNextHere(newp);
                }
            }
            if (prevp) {
                pinVarp->replaceWith(prevp);
                pushDeletep(pinVarp);
            }  // else pinVarp already unlinked when another instance did this step
            nodep->replaceWith(prevPinp);
            pushDeletep(nodep);
        }
    }

    // Save some time
    virtual void visit(AstNodeMath*) VL_OVERRIDE {}
    //--------------------
    // Default: Just iterate
    virtual void visit(AstNode* nodep) VL_OVERRIDE {
        iterateChildren(nodep);
    }
public:
    // CONSTRUCTORS
    explicit InstDeVisitor(AstNetlist* nodep) {
        m_cellRangep = NULL;
        m_instSelNum = 0;
        //
        iterate(nodep);
    }
    virtual ~InstDeVisitor() {}
};

//######################################################################
// Inst static function

class InstStatic {
private:
    VL_DEBUG_FUNC;  // Declare debug()
    InstStatic() {}  // Static class

    static AstNode* extendOrSel(FileLine* fl, AstNode* rhsp, AstNode* cmpWidthp) {
        if (cmpWidthp->width() > rhsp->width()) {
            rhsp = (rhsp->isSigned()
                    ? static_cast<AstNode*>(new AstExtendS(fl, rhsp))
                    : static_cast<AstNode*>(new AstExtend (fl, rhsp)));
            rhsp->dtypeFrom(cmpWidthp);  // Need proper widthMin, which may differ from AstSel created above
        } else if (cmpWidthp->width() < rhsp->width()) {
            rhsp = new AstSel(fl, rhsp, 0, cmpWidthp->width());
            rhsp->dtypeFrom(cmpWidthp);  // Need proper widthMin, which may differ from AstSel created above
        }
        // else don't change dtype, as might be e.g. array of something
        return rhsp;
    }

public:
    static AstAssignW* pinReconnectSimple(AstPin* pinp, AstCell* cellp,
                                          bool forTristate, bool alwaysCvt) {
        // If a pin connection is "simple" leave it as-is
        // Else create a intermediate wire to perform the interconnect
        // Return the new assignment, if one was made
        // Note this module calles cloneTree() via new AstVar

        AstVar* pinVarp = pinp->modVarp();
        AstVarRef* connectRefp = VN_CAST(pinp->exprp(), VarRef);
        AstVarXRef* connectXRefp = VN_CAST(pinp->exprp(), VarXRef);
        AstBasicDType* pinBasicp = VN_CAST(pinVarp->dtypep(), BasicDType);  // Maybe NULL
        AstBasicDType* connBasicp = NULL;
        AstAssignW* assignp = NULL;
        if (connectRefp) connBasicp = VN_CAST(connectRefp->varp()->dtypep(), BasicDType);
        //
        if (!alwaysCvt
            && connectRefp
            && connectRefp->varp()->dtypep()->sameTree(pinVarp->dtypep())
            && !connectRefp->varp()->isSc()) {  // Need the signal as a 'shell' to convert types
            // Done. Same data type
        } else if (!alwaysCvt
                   && connectRefp
                   && connectRefp->varp()->isIfaceRef()) {
            // Done. Interface
        } else if (!alwaysCvt
                   && connectXRefp
                   && connectXRefp->varp()
                   && connectXRefp->varp()->isIfaceRef()) {
        } else if (!alwaysCvt
                   && connBasicp
                   && pinBasicp
                   && connBasicp->width() == pinBasicp->width()
                   && connBasicp->lsb() == pinBasicp->lsb()
                   && !connectRefp->varp()->isSc()  // Need the signal as a 'shell' to convert types
                   && connBasicp->width() == pinVarp->width()) {
            // Done. One to one interconnect won't need a temporary variable.
        } else if (!alwaysCvt && !forTristate && VN_IS(pinp->exprp(), Const)) {
            // Done. Constant.
        } else {
            // Make a new temp wire
            //if (1||debug()>=9) { pinp->dumpTree(cout, "-in_pin:"); }
            V3Inst::checkOutputShort(pinp);
            AstNode* pinexprp = pinp->exprp()->unlinkFrBack();
            string newvarname = (string(pinVarp->isWritable() ? "__Vcellout" : "__Vcellinp")
                                 // Prevent name conflict if both tri & non-tri add signals
                                 +(forTristate?"t":"")
                                 +"__"+cellp->name()+"__"+pinp->name());
            AstVar* newvarp = new AstVar(pinVarp->fileline(),
                                         AstVarType::MODULETEMP, newvarname, pinVarp);
            // Important to add statement next to cell, in case there is a
            // generate with same named cell
            cellp->addNextHere(newvarp);
            if (pinVarp->isInoutish()) {
                pinVarp->v3fatalSrc("Unsupported: Inout connections to pins must be"
                                    " direct one-to-one connection (without any expression)");
            } else if (pinVarp->isWritable()) {
                // See also V3Inst
                AstNode* rhsp = new AstVarRef(pinp->fileline(), newvarp, false);
                UINFO(5,"pinRecon width "<<pinVarp->width()<<" >? "
                      <<rhsp->width()<<" >? "<<pinexprp->width()<<endl);
                rhsp = extendOrSel(pinp->fileline(), rhsp, pinVarp);
                pinp->exprp(new AstVarRef(newvarp->fileline(), newvarp, true));
                AstNode* rhsSelp = extendOrSel(pinp->fileline(), rhsp, pinexprp);
                assignp = new AstAssignW(pinp->fileline(), pinexprp, rhsSelp);
            } else {
                // V3 width should have range/extended to make the widths correct
                assignp = new AstAssignW(pinp->fileline(),
                                         new AstVarRef(pinp->fileline(), newvarp, true),
                                         pinexprp);
                pinp->exprp(new AstVarRef(pinexprp->fileline(), newvarp, false));
            }
            if (assignp) cellp->addNextHere(assignp);
            //if (debug()) { pinp->dumpTree(cout, "-  out:"); }
            //if (debug()) { assignp->dumpTree(cout, "- aout:"); }
        }
        return assignp;
    }
};

//######################################################################
// Inst class functions

AstAssignW* V3Inst::pinReconnectSimple(AstPin* pinp, AstCell* cellp,
                                       bool forTristate, bool alwaysCvt) {
    return InstStatic::pinReconnectSimple(pinp, cellp, forTristate, alwaysCvt);
}

void V3Inst::checkOutputShort(AstPin* nodep) {
    if (nodep->modVarp()->direction() == VDirection::OUTPUT) {
        if (VN_IS(nodep->exprp(), Const)
            || VN_IS(nodep->exprp(), Extend)
            || (VN_IS(nodep->exprp(), Concat)
                && (VN_IS(VN_CAST(nodep->exprp(), Concat)->lhsp(), Const)))) {
            // Uses v3warn for error, as might be found multiple times
            nodep->v3warn(E_PORTSHORT, "Output port is connected to a constant pin,"
                          " electrical short");
        }
    }
}

//######################################################################
// Inst class visitor

void V3Inst::instAll(AstNetlist* nodep) {
    UINFO(2,__FUNCTION__<<": "<<endl);
    {
        InstVisitor visitor (nodep);
    }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("inst", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}

void V3Inst::dearrayAll(AstNetlist* nodep) {
    UINFO(2,__FUNCTION__<<": "<<endl);
    {
        InstDeVisitor visitor (nodep);
    }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("dearray", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 6);
}
