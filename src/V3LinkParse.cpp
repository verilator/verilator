// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Parse module/signal name references
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
// LinkParse TRANSFORMATIONS:
//      Top-down traversal
//          Move some attributes around
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3Global.h"
#include "V3LinkParse.h"
#include "V3Ast.h"
#include "V3Config.h"

#include <algorithm>
#include <cstdarg>
#include <map>
#include <set>
#include <vector>

//######################################################################
// Link state, as a visitor of each AstNode

class LinkParseVisitor : public AstNVisitor {
private:
    // NODE STATE
    // Cleared on netlist
    //  AstNode::user1()        -> bool.  True if processed
    //  AstNode::user2()        -> bool.  True if fileline recomputed
    AstUser1InUse       m_inuser1;
    AstUser2InUse       m_inuser2;

    // TYPES
    typedef std::map<std::pair<void*,string>,AstTypedef*> ImplTypedefMap;
    typedef std::set<FileLine*> FileLineSet;

    // STATE
    AstVar*             m_varp;         // Variable we're under
    ImplTypedefMap      m_implTypedef;  // Created typedefs for each <container,name>
    FileLineSet         m_filelines;    // Filelines that have been seen
    bool                m_inAlways;     // Inside an always
    bool                m_inGenerate;   // Inside a generate
    bool                m_needStart;    // Need start marker on lower AstParse
    AstNodeModule*      m_valueModp;    // If set, move AstVar->valuep() initial values to this module
    AstNodeModule*      m_modp;         // Current module
    AstNodeFTask*       m_ftaskp;       // Current task
    AstNodeDType*       m_dtypep;       // Current data type

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    void cleanFileline(AstNode* nodep) {
        if (!nodep->user2SetOnce()) {  // Process once
            // We make all filelines unique per AstNode.  This allows us to
            // later turn off messages on a fileline when an issue is found
            // so that messages on replicated blocks occur only once,
            // without suppressing other token's messages as a side effect.
            // We could have verilog.l create a new one on every token,
            // but that's a lot more structures than only doing AST nodes.
            if (m_filelines.find(nodep->fileline()) != m_filelines.end()) {
                nodep->fileline(new FileLine(nodep->fileline()));
            }
            m_filelines.insert(nodep->fileline());
        }
    }

    string nameFromTypedef(AstNode* nodep) {
        // Try to find a name for a typedef'ed enum/struct
        if (AstTypedef* typedefp = VN_CAST(nodep->backp(), Typedef)) {
            // Create a name for the enum, to aid debug and tracing
            // This name is not guaranteed to be globally unique (due to later parameterization)
            string above;
            if (m_modp && VN_IS(m_modp, Package)) above = m_modp->name()+"::";
            else if (m_modp) above = m_modp->name()+".";
            return above + typedefp->name();
        }
        return "";
    }

    void visitIterateNodeDType(AstNodeDType* nodep) {
        if (!nodep->user1SetOnce()) {  // Process only once.
            cleanFileline(nodep);
            AstNodeDType* upperDtypep = m_dtypep;
            m_dtypep = nodep;
            iterateChildren(nodep);
            m_dtypep = upperDtypep;
        }
    }

    // VISITs
    virtual void visit(AstNodeFTask* nodep) VL_OVERRIDE {
        V3Config::applyFTask(m_modp, nodep);

        if (!nodep->user1SetOnce()) {  // Process only once.
            cleanFileline(nodep);
            m_ftaskp = nodep;
            iterateChildren(nodep);
            m_ftaskp = NULL;
        }
    }
    virtual void visit(AstNodeFTaskRef* nodep) VL_OVERRIDE {
        if (!nodep->user1SetOnce()) {  // Process only once.
            cleanFileline(nodep);
            UINFO(5,"   "<<nodep<<endl);
            AstNodeModule* upperValueModp = m_valueModp;
            m_valueModp = NULL;
            iterateChildren(nodep);
            m_valueModp = upperValueModp;
        }
    }
    virtual void visit(AstNodeDType* nodep) VL_OVERRIDE {
        visitIterateNodeDType(nodep);
    }
    virtual void visit(AstEnumDType* nodep) VL_OVERRIDE {
        if (nodep->name() == "") {
            nodep->name(nameFromTypedef(nodep));  // Might still remain ""
        }
        visitIterateNodeDType(nodep);
    }
    virtual void visit(AstNodeUOrStructDType* nodep) VL_OVERRIDE {
        if (nodep->name() == "") {
            nodep->name(nameFromTypedef(nodep));  // Might still remain ""
        }
        visitIterateNodeDType(nodep);
    }
    virtual void visit(AstEnumItem* nodep) VL_OVERRIDE {
        // Expand ranges
        cleanFileline(nodep);
        iterateChildren(nodep);
        if (nodep->rangep()) {
            if (!VN_IS(nodep->rangep()->msbp(), Const)
                || !VN_IS(nodep->rangep()->lsbp(), Const)) {
                nodep->v3error("Enum ranges must be integral, per spec");
            }
            int msb = nodep->rangep()->msbConst();
            int lsb = nodep->rangep()->lsbConst();
            int increment = (msb > lsb) ? -1 : 1;
            int offset_from_init = 0;
            AstNode* addp = NULL;
            for (int i=msb; i!=(lsb+increment); i+=increment, offset_from_init++) {
                string name = nodep->name() + cvtToStr(i);
                AstNode* valuep = NULL;
                if (nodep->valuep()) valuep = new AstAdd
                                         (nodep->fileline(),
                                          nodep->valuep()->cloneTree(true),
                                          new AstConst(nodep->fileline(),
                                                       AstConst::Unsized32(),
                                                       offset_from_init));
                AstNode* newp = new AstEnumItem(nodep->fileline(), name, NULL, valuep);
                if (addp) addp = addp->addNextNull(newp);
                else addp = newp;
            }
            nodep->replaceWith(addp);
            VL_DO_DANGLING(nodep->deleteTree(), nodep);
        }
    }

    virtual void visit(AstVar* nodep) VL_OVERRIDE {
        cleanFileline(nodep);
        if (VN_IS(nodep->subDTypep(), ParseTypeDType)) {
            // It's a parameter type. Use a different node type for this.
            AstNodeDType* dtypep = VN_CAST(nodep->valuep(), NodeDType);
            if (!dtypep) {
                nodep->v3error("Parameter type's initial value isn't a type: "
                               <<nodep->prettyNameQ());
                nodep->unlinkFrBack();
            } else {
                dtypep->unlinkFrBack();
                AstNode* newp = new AstParamTypeDType(nodep->fileline(),
                                                      nodep->varType(), nodep->name(),
                                                      VFlagChildDType(), dtypep);
                nodep->replaceWith(newp); VL_DO_DANGLING(nodep->deleteTree(), nodep);
            }
            return;
        }

        // Maybe this variable has a signal attribute
        V3Config::applyVarAttr(m_modp, m_ftaskp, nodep);

        if (v3Global.opt.publicFlatRW()) {
            switch (nodep->varType()) {
            case AstVarType::VAR:
            case AstVarType::PORT:
            case AstVarType::WIRE:
                nodep->sigUserRWPublic(true);
                break;
            default: break;
            }
        }

        // We used modTrace before leveling, and we may now
        // want to turn it off now that we know the levelizations
        if (v3Global.opt.traceDepth()
            && m_modp
            && (m_modp->level()-1) > v3Global.opt.traceDepth()) {
            m_modp->modTrace(false);
            nodep->trace(false);
        }
        m_varp = nodep;

        iterateChildren(nodep);
        m_varp = NULL;
        // temporaries under an always aren't expected to be blocking
        if (m_inAlways) nodep->fileline()->modifyWarnOff(V3ErrorCode::BLKSEQ, true);
        if (nodep->valuep()) {
            // A variable with an = value can be three things:
            FileLine* fl = nodep->valuep()->fileline();
            // 1. Parameters and function inputs: It's a default to use if not overridden
            if (nodep->isParam() || (m_ftaskp && nodep->isNonOutput())) {
            }
            else if (!m_ftaskp && nodep->isNonOutput()) {
                nodep->v3error("Unsupported: Default value on module input: "
                               <<nodep->prettyNameQ());
                nodep->valuep()->unlinkFrBack()->deleteTree();
            }  // 2. Under modules, it's an initial value to be loaded at time 0 via an AstInitial
            else if (m_valueModp) {
                // Making an AstAssign (vs AstAssignW) to a wire is an error, suppress it
                FileLine* newfl = new FileLine(fl);
                newfl->warnOff(V3ErrorCode::PROCASSWIRE, true);
                nodep->addNextHere
                    (new AstInitial
                     (newfl, new AstAssign(newfl, new AstVarRef(newfl, nodep->name(), true),
                                           nodep->valuep()->unlinkFrBack())));
            }  // 3. Under blocks, it's an initial value to be under an assign
            else {
                nodep->addNextHere
                    (new AstAssign(fl, new AstVarRef(fl, nodep->name(), true),
                                   nodep->valuep()->unlinkFrBack()));
            }
        }
        if (nodep->isIfaceRef() && !nodep->isIfaceParent()) {
            // Only AstIfaceRefDType's at this point correspond to ports;
            // haven't made additional ones for interconnect yet, so assert is simple
            // What breaks later is we don't have a Scope/Cell representing
            // the interface to attach to
            if (m_modp->level()<=2) nodep->v3error("Unsupported: Interfaced port on top level module");
        }
    }

    virtual void visit(AstAttrOf* nodep) VL_OVERRIDE {
        cleanFileline(nodep);
        iterateChildren(nodep);
        if (nodep->attrType() == AstAttrType::DT_PUBLIC) {
            AstTypedef* typep = VN_CAST(nodep->backp(), Typedef);
            UASSERT_OBJ(typep, nodep, "Attribute not attached to typedef");
            typep->attrPublic(true);
            VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
        }
        else if (nodep->attrType() == AstAttrType::VAR_CLOCK) {
            UASSERT_OBJ(m_varp, nodep, "Attribute not attached to variable");
            nodep->v3warn(DEPRECATED, "sc_clock is deprecated and will be removed");
            m_varp->attrScClocked(true);
            VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
        }
        else if (nodep->attrType() == AstAttrType::VAR_CLOCK_ENABLE) {
            UASSERT_OBJ(m_varp, nodep, "Attribute not attached to variable");
            m_varp->attrClockEn(true);
            VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
        }
        else if (nodep->attrType() == AstAttrType::VAR_PUBLIC) {
            UASSERT_OBJ(m_varp, nodep, "Attribute not attached to variable");
            m_varp->sigUserRWPublic(true); m_varp->sigModPublic(true);
            VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
        }
        else if (nodep->attrType() == AstAttrType::VAR_PUBLIC_FLAT) {
            UASSERT_OBJ(m_varp, nodep, "Attribute not attached to variable");
            m_varp->sigUserRWPublic(true);
            VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
        }
        else if (nodep->attrType() == AstAttrType::VAR_PUBLIC_FLAT_RD) {
            UASSERT_OBJ(m_varp, nodep, "Attribute not attached to variable");
            m_varp->sigUserRdPublic(true);
            VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
        }
        else if (nodep->attrType() == AstAttrType::VAR_PUBLIC_FLAT_RW) {
            UASSERT_OBJ(m_varp, nodep, "Attribute not attached to variable");
            m_varp->sigUserRWPublic(true);
            VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
        }
        else if (nodep->attrType() == AstAttrType::VAR_ISOLATE_ASSIGNMENTS) {
            UASSERT_OBJ(m_varp, nodep, "Attribute not attached to variable");
            m_varp->attrIsolateAssign(true);
            VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
        }
        else if (nodep->attrType() == AstAttrType::VAR_SFORMAT) {
            UASSERT_OBJ(m_varp, nodep, "Attribute not attached to variable");
            m_varp->attrSFormat(true);
            VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
        }
        else if (nodep->attrType() == AstAttrType::VAR_SPLIT_VAR) {
            UASSERT_OBJ(m_varp, nodep, "Attribute not attached to variable");
            if (!VN_IS(m_modp, Module)) {
                m_varp->v3warn(SPLITVAR, m_varp->prettyNameQ() << " has split_var metacomment, "
                               "but will not be split because it is not declared in a module.");
            } else {
                m_varp->attrSplitVar(true);
            }
            VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
        }
        else if (nodep->attrType() == AstAttrType::VAR_SC_BV) {
            UASSERT_OBJ(m_varp, nodep, "Attribute not attached to variable");
            m_varp->attrScBv(true);
            VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
        }
        else if (nodep->attrType() == AstAttrType::VAR_CLOCKER) {
            UASSERT_OBJ(m_varp, nodep, "Attribute not attached to variable");
            m_varp->attrClocker(VVarAttrClocker::CLOCKER_YES);
            VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
        }
        else if (nodep->attrType() == AstAttrType::VAR_NO_CLOCKER) {
            UASSERT_OBJ(m_varp, nodep, "Attribute not attached to variable");
            m_varp->attrClocker(VVarAttrClocker::CLOCKER_NO);
            VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
        }
    }

    virtual void visit(AstAlwaysPublic* nodep) VL_OVERRIDE {
        // AlwaysPublic was attached under a var, but it's a statement that should be
        // at the same level as the var
        cleanFileline(nodep);
        iterateChildren(nodep);
        if (m_varp) {
            nodep->unlinkFrBack();
            m_varp->addNext(nodep);
            // lvalue is true, because we know we have a verilator public_flat_rw
            // but someday we may be more general
            bool lvalue = m_varp->isSigUserRWPublic();
            nodep->addStmtp(new AstVarRef(nodep->fileline(), m_varp, lvalue));
        }
    }

    virtual void visit(AstDefImplicitDType* nodep) VL_OVERRIDE {
        cleanFileline(nodep);
        UINFO(8,"   DEFIMPLICIT "<<nodep<<endl);
        // Must remember what names we've already created, and combine duplicates
        // so that for "var enum {...} a,b" a & b will share a common typedef
        // Unique name space under each containerp() so that an addition of
        // a new type won't change every verilated module.
        AstTypedef* defp = NULL;
        ImplTypedefMap::iterator it = m_implTypedef.find(make_pair(nodep->containerp(), nodep->name()));
        if (it != m_implTypedef.end()) {
            defp = it->second;
        } else {
            // Definition must be inserted right after the variable (etc) that needed it
            // AstVar, AstTypedef, AstNodeFTask are common containers
            AstNode* backp = nodep->backp();
            for (; backp; backp=backp->backp()) {
                if (VN_IS(backp, Var)) break;
                else if (VN_IS(backp, Typedef)) break;
                else if (VN_IS(backp, NodeFTask)) break;
            }
            UASSERT_OBJ(backp, nodep,
                        "Implicit enum/struct type created under unexpected node type");
            AstNodeDType* dtypep = nodep->childDTypep(); dtypep->unlinkFrBack();
            if (VN_IS(backp, Typedef)) {  // A typedef doesn't need us to make yet another level of typedefing
                // For typedefs just remove the AstRefDType level of abstraction
                nodep->replaceWith(dtypep);
                VL_DO_DANGLING(nodep->deleteTree(), nodep);
                return;
            } else {
                defp = new AstTypedef(nodep->fileline(), nodep->name(), NULL,
                                      VFlagChildDType(), dtypep);
                m_implTypedef.insert(make_pair(make_pair(nodep->containerp(), defp->name()), defp));
                backp->addNextHere(defp);
            }
        }
        nodep->replaceWith(new AstRefDType(nodep->fileline(), defp->name()));
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
    }

    virtual void visit(AstTypedefFwd* nodep) VL_OVERRIDE {
        // We only needed the forward declaration in order to parse correctly.
        // We won't even check it was ever really defined, as it might have been in a header
        // file referring to a module we never needed
        VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
    }

    virtual void visit(AstForeach* nodep) VL_OVERRIDE {
        // FOREACH(array,loopvars,body)
        // -> BEGIN(declare vars, loopa=lowest; WHILE(loopa<=highest, ... body))
        //nodep->dumpTree(cout, "-foreach-old:");
        AstNode* newp = nodep->bodysp()->unlinkFrBackWithNext();
        AstNode* arrayp = nodep->arrayp();
        int dimension = 1;
        // Must do innermost (last) variable first
        AstNode* firstVarsp = nodep->varsp()->unlinkFrBackWithNext();
        AstNode* lastVarsp = firstVarsp;
        while (lastVarsp->nextp()) { lastVarsp = lastVarsp->nextp(); dimension++; }
        for (AstNode* varsp = lastVarsp; varsp; varsp=varsp->backp()) {
            UINFO(9,"foreachVar "<<varsp<<endl);
            FileLine* fl = varsp->fileline();
            AstNode* varp = new AstVar(fl, AstVarType::BLOCKTEMP,
                                       varsp->name(), nodep->findSigned32DType());
            // These will be the left and right dimensions and size of the array:
            AstNode* leftp = new AstAttrOf(fl, AstAttrType::DIM_LEFT,
                                           new AstVarRef(fl, arrayp->name(), false),
                                           new AstConst(fl, dimension));
            AstNode* rightp = new AstAttrOf(fl, AstAttrType::DIM_RIGHT,
                                            new AstVarRef(fl, arrayp->name(), false),
                                            new AstConst(fl, dimension));
            AstNode* sizep = new AstAttrOf(fl, AstAttrType::DIM_SIZE,
                                           new AstVarRef(fl, arrayp->name(), false),
                                           new AstConst(fl, dimension));
            AstNode* stmtsp = varp;
            // Assign left-dimension into the loop var:
            stmtsp->addNext(new AstAssign
                            (fl, new AstVarRef(fl, varp->name(), true), leftp));
            // This will turn into a constant bool for static arrays
            AstNode* notemptyp = new AstGt(fl, sizep, new AstConst(fl, 0));
            // This will turn into a bool constant, indicating whether
            // we count the loop variable up or down:
            AstNode* countupp = new AstLte(fl, leftp->cloneTree(true),
                                           rightp->cloneTree(true));
            AstNode* comparep = new AstCond(
                fl, countupp->cloneTree(true),
                // Left increments up to right
                new AstLte(fl, new AstVarRef(fl, varp->name(), false),
                           rightp->cloneTree(true)),
                // Left decrements down to right
                new AstGte(fl, new AstVarRef(fl, varp->name(), false), rightp));
            // This will reduce to comparep for static arrays
            AstNode* condp = new AstAnd(fl, notemptyp, comparep);
            AstNode* incp = new AstAssign(
                fl, new AstVarRef(fl, varp->name(), true),
                new AstAdd(fl, new AstVarRef(fl, varp->name(), false),
                           new AstCond(fl, countupp,
                                       new AstConst(fl, 1),
                                       new AstConst(fl, -1))));
            stmtsp->addNext(new AstWhile(fl, condp, newp, incp));
            newp = new AstBegin(nodep->fileline(), "", stmtsp, false, true);
            dimension--;
        }
        //newp->dumpTree(cout, "-foreach-new:");
        VL_DO_DANGLING(firstVarsp->deleteTree(), firstVarsp);
        nodep->replaceWith(newp); VL_DO_DANGLING(nodep->deleteTree(), nodep);
    }

    virtual void visit(AstNodeModule* nodep) VL_OVERRIDE {
        V3Config::applyModule(nodep);

        AstNodeModule* origModp = m_modp;
        {
            // Module: Create sim table for entire module and iterate
            cleanFileline(nodep);
            //
            m_modp = nodep;
            m_valueModp = nodep;
            iterateChildren(nodep);
        }
        m_modp = origModp;
        m_valueModp = nodep;
    }
    void visitIterateNoValueMod(AstNode* nodep) {
        // Iterate a node which shouldn't have any local variables moved to an Initial
        cleanFileline(nodep);
        //
        AstNodeModule* upperValueModp = m_valueModp;
        m_valueModp = NULL;
        iterateChildren(nodep);
        m_valueModp = upperValueModp;
    }
    virtual void visit(AstInitial* nodep) VL_OVERRIDE {
        visitIterateNoValueMod(nodep);
    }
    virtual void visit(AstFinal* nodep) VL_OVERRIDE {
        visitIterateNoValueMod(nodep);
    }
    virtual void visit(AstAlways* nodep) VL_OVERRIDE {
        m_inAlways = true;
        visitIterateNoValueMod(nodep);
        m_inAlways = false;
    }
    virtual void visit(AstCover* nodep) VL_OVERRIDE {
        visitIterateNoValueMod(nodep);
    }
    virtual void visit(AstRestrict* nodep) VL_OVERRIDE {
        visitIterateNoValueMod(nodep);
    }

    virtual void visit(AstBegin* nodep) VL_OVERRIDE {
        V3Config::applyCoverageBlock(m_modp, nodep);
        cleanFileline(nodep);
        AstNode* backp = nodep->backp();
        // IEEE says directly nested item is not a new block
        bool nestedIf = (nodep->implied()  // User didn't provide begin/end
                         && (VN_IS(nodep->stmtsp(), GenIf)
                             || VN_IS(nodep->stmtsp(), GenCase))  // Has an if/case
                         && !nodep->stmtsp()->nextp());  // Has only one item
        // It's not FOR(BEGIN(...)) but we earlier changed it to BEGIN(FOR(...))
        if (nodep->genforp() && nodep->name() == "") {
            nodep->name("genblk");
        }
        else if (nodep->generate() && nodep->name() == ""
            && (VN_IS(backp, CaseItem) || VN_IS(backp, GenIf))
            && !nestedIf) {
            nodep->name("genblk");
        }
        iterateChildren(nodep);
    }
    virtual void visit(AstCase* nodep) VL_OVERRIDE {
        V3Config::applyCase(nodep);
        cleanFileline(nodep);
        iterateChildren(nodep);
    }

    virtual void visit(AstNode* nodep) VL_OVERRIDE {
        // Default: Just iterate
        cleanFileline(nodep);
        iterateChildren(nodep);
    }

public:
    // CONSTRUCTORS
    explicit LinkParseVisitor(AstNetlist* rootp) {
        m_varp = NULL;
        m_modp = NULL;
        m_ftaskp = NULL;
        m_dtypep = NULL;
        m_inAlways = false;
        m_inGenerate = false;
        m_needStart = false;
        m_valueModp = NULL;
        iterate(rootp);
    }
    virtual ~LinkParseVisitor() {}
};

//######################################################################
// Link class functions

void V3LinkParse::linkParse(AstNetlist* rootp) {
    UINFO(4,__FUNCTION__<<": "<<endl);
    {
        LinkParseVisitor visitor(rootp);
    }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("linkparse", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 6);
}
