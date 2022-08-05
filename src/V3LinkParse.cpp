// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Parse module/signal name references
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
//*************************************************************************
// LinkParse TRANSFORMATIONS:
//      Top-down traversal
//          Move some attributes around
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3LinkParse.h"

#include "V3Ast.h"
#include "V3Config.h"
#include "V3Global.h"

#include <algorithm>
#include <map>
#include <set>
#include <vector>

//######################################################################
// Link state, as a visitor of each AstNode

class LinkParseVisitor final : public VNVisitor {
private:
    // NODE STATE
    // Cleared on netlist
    //  AstNode::user1()        -> bool.  True if processed
    //  AstNode::user2()        -> bool.  True if fileline recomputed
    const VNUser1InUse m_inuser1;
    const VNUser2InUse m_inuser2;

    // TYPES
    using ImplTypedefMap = std::map<const std::pair<void*, std::string>, AstTypedef*>;

    // STATE
    AstVar* m_varp = nullptr;  // Variable we're under
    ImplTypedefMap m_implTypedef;  // Created typedefs for each <container,name>
    std::unordered_set<FileLine*> m_filelines;  // Filelines that have been seen
    bool m_inAlways = false;  // Inside an always
    AstNodeModule* m_valueModp
        = nullptr;  // If set, move AstVar->valuep() initial values to this module
    AstNodeModule* m_modp = nullptr;  // Current module
    AstNodeFTask* m_ftaskp = nullptr;  // Current task
    AstNodeDType* m_dtypep = nullptr;  // Current data type
    int m_genblkAbove = 0;  // Begin block number of if/case/for above
    int m_genblkNum = 0;  // Begin block number, 0=none seen
    VLifetime m_lifetime = VLifetime::STATIC;  // Propagating lifetime

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
        if (const AstTypedef* const typedefp = VN_CAST(nodep->backp(), Typedef)) {
            // Create a name for the enum, to aid debug and tracing
            // This name is not guaranteed to be globally unique (due to later parameterization)
            string above;
            if (m_modp && VN_IS(m_modp, Package)) {
                above = m_modp->name() + "::";
            } else if (m_modp) {
                above = m_modp->name() + ".";
            }
            return above + typedefp->name();
        }
        return "";
    }

    void visitIterateNodeDType(AstNodeDType* nodep) {
        if (!nodep->user1SetOnce()) {  // Process only once.
            cleanFileline(nodep);
            {
                VL_RESTORER(m_dtypep);
                m_dtypep = nodep;
                iterateChildren(nodep);
            }
        }
    }

    bool nestedIfBegin(AstBegin* nodep) {  // Point at begin inside the GenIf
        // IEEE says directly nested item is not a new block
        // The genblk name will get attached to the if true/false LOWER begin block(s)
        //    1: GENIF
        // -> 1:3: BEGIN [GEN] [IMPLIED]  // nodep passed to this function
        //    1:3:1: GENIF
        //    1:3:1:2: BEGIN genblk1 [GEN] [IMPLIED]
        const AstNode* const backp = nodep->backp();
        return (nodep->implied()  // User didn't provide begin/end
                && VN_IS(backp, GenIf) && VN_CAST(backp, GenIf)->elsesp() == nodep
                && !nodep->nextp()  // No other statements under upper genif else
                && (VN_IS(nodep->stmtsp(), GenIf))  // Begin has if underneath
                && !nodep->stmtsp()->nextp());  // Has only one item
    }

    // VISITs
    virtual void visit(AstNodeFTask* nodep) override {
        if (!nodep->user1SetOnce()) {  // Process only once.
            V3Config::applyFTask(m_modp, nodep);
            cleanFileline(nodep);
            VL_RESTORER(m_ftaskp);
            VL_RESTORER(m_lifetime);
            {
                m_ftaskp = nodep;
                m_lifetime = nodep->lifetime();
                if (m_lifetime.isNone()) {
                    // Automatic always until we support static
                    m_lifetime = VLifetime::AUTOMATIC;
                }
                iterateChildren(nodep);
            }
        }
    }
    virtual void visit(AstNodeFTaskRef* nodep) override {
        if (!nodep->user1SetOnce()) {  // Process only once.
            cleanFileline(nodep);
            UINFO(5, "   " << nodep << endl);
            {
                VL_RESTORER(m_valueModp);
                m_valueModp = nullptr;
                iterateChildren(nodep);
            }
        }
    }
    virtual void visit(AstNodeDType* nodep) override { visitIterateNodeDType(nodep); }
    virtual void visit(AstEnumDType* nodep) override {
        if (nodep->name() == "") {
            nodep->name(nameFromTypedef(nodep));  // Might still remain ""
        }
        visitIterateNodeDType(nodep);
    }
    virtual void visit(AstNodeUOrStructDType* nodep) override {
        if (nodep->name() == "") {
            nodep->name(nameFromTypedef(nodep));  // Might still remain ""
        }
        visitIterateNodeDType(nodep);
    }
    virtual void visit(AstEnumItem* nodep) override {
        // Expand ranges
        cleanFileline(nodep);
        iterateChildren(nodep);
        if (nodep->rangep()) {
            if (VL_UNCOVERABLE(!VN_IS(nodep->rangep()->leftp(), Const)  // LCOV_EXCL_START
                               || !VN_IS(nodep->rangep()->rightp(), Const))) {
                // We check this rule in the parser, so shouldn't fire
                nodep->v3error("Enum ranges must be integral, per spec");
            }  // LCOV_EXCL_STOP
            const int left = nodep->rangep()->leftConst();
            const int right = nodep->rangep()->rightConst();
            const int increment = (left > right) ? -1 : 1;
            int offset_from_init = 0;
            AstNode* addp = nullptr;
            for (int i = left; i != (right + increment); i += increment, offset_from_init++) {
                const string name = nodep->name() + cvtToStr(i);
                AstNode* valuep = nullptr;
                if (nodep->valuep()) {
                    valuep = new AstAdd(
                        nodep->fileline(), nodep->valuep()->cloneTree(true),
                        new AstConst(nodep->fileline(), AstConst::Unsized32(), offset_from_init));
                }
                AstNode* const newp = new AstEnumItem(nodep->fileline(), name, nullptr, valuep);
                if (addp) {
                    addp = addp->addNextNull(newp);
                } else {
                    addp = newp;
                }
            }
            nodep->replaceWith(addp);
            VL_DO_DANGLING(nodep->deleteTree(), nodep);
        }
    }

    virtual void visit(AstVar* nodep) override {
        cleanFileline(nodep);
        if (nodep->lifetime().isNone()) {
            if (m_ftaskp) {
                nodep->lifetime(VLifetime::AUTOMATIC);
            } else {
                nodep->lifetime(m_lifetime);
            }
        }
        if (nodep->isParam() && !nodep->valuep()
            && nodep->fileline()->language() < V3LangCode::L1800_2009) {
            nodep->v3error("Parameter requires default value, or use IEEE 1800-2009 or later.");
        }
        if (VN_IS(nodep->subDTypep(), ParseTypeDType)) {
            // It's a parameter type. Use a different node type for this.
            AstNodeDType* const dtypep = VN_CAST(nodep->valuep(), NodeDType);
            if (!dtypep) {
                nodep->v3error(
                    "Parameter type's initial value isn't a type: " << nodep->prettyNameQ());
                nodep->unlinkFrBack();
            } else {
                dtypep->unlinkFrBack();
                AstNode* const newp = new AstParamTypeDType(
                    nodep->fileline(), nodep->varType(), nodep->name(), VFlagChildDType(), dtypep);
                nodep->replaceWith(newp);
                VL_DO_DANGLING(nodep->deleteTree(), nodep);
            }
            return;
        }

        // Maybe this variable has a signal attribute
        V3Config::applyVarAttr(m_modp, m_ftaskp, nodep);

        if (v3Global.opt.publicFlatRW()) {
            switch (nodep->varType()) {
            case VVarType::VAR:  // FALLTHRU
            case VVarType::GPARAM:  // FALLTHRU
            case VVarType::LPARAM:  // FALLTHRU
            case VVarType::PORT:  // FALLTHRU
            case VVarType::WIRE: nodep->sigUserRWPublic(true); break;
            default: break;
            }
        }

        // We used modTrace before leveling, and we may now
        // want to turn it off now that we know the levelizations
        if (v3Global.opt.traceDepth() && m_modp
            && (m_modp->level() - 1) > v3Global.opt.traceDepth()) {
            m_modp->modTrace(false);
            nodep->trace(false);
        }
        m_varp = nodep;

        iterateChildren(nodep);
        m_varp = nullptr;
        // temporaries under an always aren't expected to be blocking
        if (m_inAlways) nodep->fileline()->modifyWarnOff(V3ErrorCode::BLKSEQ, true);
        if (nodep->valuep()) {
            // A variable with an = value can be three things:
            FileLine* const fl = nodep->valuep()->fileline();
            if (nodep->isParam() || (m_ftaskp && nodep->isNonOutput())) {
                // 1. Parameters and function inputs: It's a default to use if not overridden
            } else if (!m_ftaskp && !VN_IS(m_modp, Class) && nodep->isNonOutput()) {
                nodep->v3warn(E_UNSUPPORTED, "Unsupported: Default value on module input: "
                                                 << nodep->prettyNameQ());
                nodep->valuep()->unlinkFrBack()->deleteTree();
            }  // 2. Under modules/class, it's an initial value to be loaded at time 0 via an
               // AstInitial
            else if (m_valueModp) {
                // Making an AstAssign (vs AstAssignW) to a wire is an error, suppress it
                FileLine* const newfl = new FileLine(fl);
                newfl->warnOff(V3ErrorCode::PROCASSWIRE, true);
                auto* const assp
                    = new AstAssign(newfl, new AstVarRef(newfl, nodep->name(), VAccess::WRITE),
                                    nodep->valuep()->unlinkFrBack());
                if (nodep->lifetime().isAutomatic()) {
                    nodep->addNextHere(new AstInitialAutomatic{newfl, assp});
                } else {
                    nodep->addNextHere(new AstInitialStatic{newfl, assp});
                }
            }  // 4. Under blocks, it's an initial value to be under an assign
            else {
                nodep->addNextHere(new AstAssign(fl,
                                                 new AstVarRef(fl, nodep->name(), VAccess::WRITE),
                                                 nodep->valuep()->unlinkFrBack()));
            }
        }
        if (nodep->isIfaceRef() && !nodep->isIfaceParent()) {
            // Only AstIfaceRefDType's at this point correspond to ports;
            // haven't made additional ones for interconnect yet, so assert is simple
            // What breaks later is we don't have a Scope/Cell representing
            // the interface to attach to
            if (m_modp->level() <= 2) {
                nodep->v3warn(E_UNSUPPORTED, "Unsupported: Interfaced port on top level module");
            }
        }
    }

    virtual void visit(AstAttrOf* nodep) override {
        cleanFileline(nodep);
        iterateChildren(nodep);
        if (nodep->attrType() == VAttrType::DT_PUBLIC) {
            AstTypedef* const typep = VN_AS(nodep->backp(), Typedef);
            UASSERT_OBJ(typep, nodep, "Attribute not attached to typedef");
            typep->attrPublic(true);
            VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
        } else if (nodep->attrType() == VAttrType::VAR_CLOCK_ENABLE) {
            UASSERT_OBJ(m_varp, nodep, "Attribute not attached to variable");
            m_varp->attrClockEn(true);
            VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
        } else if (nodep->attrType() == VAttrType::VAR_FORCEABLE) {
            UASSERT_OBJ(m_varp, nodep, "Attribute not attached to variable");
            m_varp->setForceable();
            v3Global.setHasForceableSignals();
            VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
        } else if (nodep->attrType() == VAttrType::VAR_PUBLIC) {
            UASSERT_OBJ(m_varp, nodep, "Attribute not attached to variable");
            m_varp->sigUserRWPublic(true);
            m_varp->sigModPublic(true);
            VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
        } else if (nodep->attrType() == VAttrType::VAR_PUBLIC_FLAT) {
            UASSERT_OBJ(m_varp, nodep, "Attribute not attached to variable");
            m_varp->sigUserRWPublic(true);
            VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
        } else if (nodep->attrType() == VAttrType::VAR_PUBLIC_FLAT_RD) {
            UASSERT_OBJ(m_varp, nodep, "Attribute not attached to variable");
            m_varp->sigUserRdPublic(true);
            VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
        } else if (nodep->attrType() == VAttrType::VAR_PUBLIC_FLAT_RW) {
            UASSERT_OBJ(m_varp, nodep, "Attribute not attached to variable");
            m_varp->sigUserRWPublic(true);
            VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
        } else if (nodep->attrType() == VAttrType::VAR_ISOLATE_ASSIGNMENTS) {
            UASSERT_OBJ(m_varp, nodep, "Attribute not attached to variable");
            m_varp->attrIsolateAssign(true);
            VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
        } else if (nodep->attrType() == VAttrType::VAR_SFORMAT) {
            UASSERT_OBJ(m_varp, nodep, "Attribute not attached to variable");
            m_varp->attrSFormat(true);
            VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
        } else if (nodep->attrType() == VAttrType::VAR_SPLIT_VAR) {
            UASSERT_OBJ(m_varp, nodep, "Attribute not attached to variable");
            if (!VN_IS(m_modp, Module)) {
                m_varp->v3warn(
                    SPLITVAR,
                    m_varp->prettyNameQ()
                        << " has split_var metacomment, "
                           "but will not be split because it is not declared in a module.");
            } else {
                m_varp->attrSplitVar(true);
            }
            VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
        } else if (nodep->attrType() == VAttrType::VAR_SC_BV) {
            UASSERT_OBJ(m_varp, nodep, "Attribute not attached to variable");
            m_varp->attrScBv(true);
            VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
        } else if (nodep->attrType() == VAttrType::VAR_CLOCKER) {
            UASSERT_OBJ(m_varp, nodep, "Attribute not attached to variable");
            m_varp->attrClocker(VVarAttrClocker::CLOCKER_YES);
            VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
        } else if (nodep->attrType() == VAttrType::VAR_NO_CLOCKER) {
            UASSERT_OBJ(m_varp, nodep, "Attribute not attached to variable");
            m_varp->attrClocker(VVarAttrClocker::CLOCKER_NO);
            VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
        }
    }

    virtual void visit(AstAlwaysPublic* nodep) override {
        // AlwaysPublic was attached under a var, but it's a statement that should be
        // at the same level as the var
        cleanFileline(nodep);
        iterateChildren(nodep);
        if (m_varp) {
            nodep->unlinkFrBack();
            m_varp->addNext(nodep);
            // lvalue is true, because we know we have a verilator public_flat_rw
            // but someday we may be more general
            const bool lvalue = m_varp->isSigUserRWPublic();
            nodep->addStmtp(
                new AstVarRef(nodep->fileline(), m_varp, lvalue ? VAccess::WRITE : VAccess::READ));
        }
    }

    virtual void visit(AstDefImplicitDType* nodep) override {
        cleanFileline(nodep);
        UINFO(8, "   DEFIMPLICIT " << nodep << endl);
        // Must remember what names we've already created, and combine duplicates
        // so that for "var enum {...} a,b" a & b will share a common typedef
        // Unique name space under each containerp() so that an addition of
        // a new type won't change every verilated module.
        AstTypedef* defp = nullptr;
        const ImplTypedefMap::iterator it
            = m_implTypedef.find(std::make_pair(nodep->containerp(), nodep->name()));
        if (it != m_implTypedef.end()) {
            defp = it->second;
        } else {
            // Definition must be inserted right after the variable (etc) that needed it
            // AstVar, AstTypedef, AstNodeFTask are common containers
            AstNode* backp = nodep->backp();
            for (; backp; backp = backp->backp()) {
                if (VN_IS(backp, Var) || VN_IS(backp, Typedef) || VN_IS(backp, NodeFTask)) break;
            }
            UASSERT_OBJ(backp, nodep,
                        "Implicit enum/struct type created under unexpected node type");
            AstNodeDType* const dtypep = nodep->childDTypep();
            dtypep->unlinkFrBack();
            if (VN_IS(backp, Typedef)) {
                // A typedef doesn't need us to make yet another level of typedefing
                // For typedefs just remove the AstRefDType level of abstraction
                nodep->replaceWith(dtypep);
                VL_DO_DANGLING(nodep->deleteTree(), nodep);
                return;
            } else {
                defp = new AstTypedef(nodep->fileline(), nodep->name(), nullptr, VFlagChildDType(),
                                      dtypep);
                m_implTypedef.insert(
                    std::make_pair(std::make_pair(nodep->containerp(), defp->name()), defp));
                backp->addNextHere(defp);
            }
        }
        nodep->replaceWith(new AstRefDType(nodep->fileline(), defp->name()));
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
    }

    virtual void visit(AstForeach* nodep) override {
        // FOREACH(array, loopvars, body)
        UINFO(9, "FOREACH " << nodep << endl);
        // Separate iteration vars from base from variable
        // Input:
        //      v--- arrayp
        //   1. DOT(DOT(first, second), ASTSELLOOPVARS(third, var0..var1))
        // Separated:
        //   bracketp = ASTSELLOOPVARS(...)
        //   arrayp = DOT(DOT(first, second), third)
        //   firstVarp = var0..var1
        // Other examples
        //   2. ASTSELBIT(first, var0))
        //   3. ASTSELLOOPVARS(first, var0..var1))
        //   4. DOT(DOT(first, second), ASTSELBIT(third, var0))
        AstNode* bracketp = nodep->arrayp();
        while (AstDot* dotp = VN_CAST(bracketp, Dot)) bracketp = dotp->rhsp();
        if (AstSelBit* const selp = VN_CAST(bracketp, SelBit)) {
            // Convert to AstSelLoopVars so V3LinkDot knows what's being defined
            AstNode* const newp
                = new AstSelLoopVars{selp->fileline(), selp->fromp()->unlinkFrBack(),
                                     selp->rhsp()->unlinkFrBackWithNext()};
            selp->replaceWith(newp);
            VL_DO_DANGLING(selp->deleteTree(), selp);
        } else if (VN_IS(bracketp, SelLoopVars)) {
            // Ok
        } else {
            nodep->v3error(
                "Syntax error; foreach missing bracketed loop variable (IEEE 1800-2017 12.7.3)");
            VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
            return;
        }
        iterateChildren(nodep);
    }

    virtual void visit(AstNodeModule* nodep) override {
        V3Config::applyModule(nodep);

        VL_RESTORER(m_modp);
        VL_RESTORER(m_genblkAbove);
        VL_RESTORER(m_genblkNum);
        VL_RESTORER(m_lifetime);
        {
            // Module: Create sim table for entire module and iterate
            cleanFileline(nodep);
            // Classes inherit from upper package
            if (m_modp && nodep->timeunit().isNone()) nodep->timeunit(m_modp->timeunit());
            m_modp = nodep;
            m_genblkAbove = 0;
            m_genblkNum = 0;
            m_valueModp = nodep;
            m_lifetime = nodep->lifetime();
            if (m_lifetime.isNone()) {
                m_lifetime = VN_IS(nodep, Class) ? VLifetime::AUTOMATIC : VLifetime::STATIC;
            }
            iterateChildren(nodep);
        }
        m_valueModp = nodep;
    }
    void visitIterateNoValueMod(AstNode* nodep) {
        // Iterate a node which shouldn't have any local variables moved to an Initial
        cleanFileline(nodep);
        {
            VL_RESTORER(m_valueModp);
            m_valueModp = nullptr;
            iterateChildren(nodep);
        }
    }
    virtual void visit(AstNodeProcedure* nodep) override { visitIterateNoValueMod(nodep); }
    virtual void visit(AstAlways* nodep) override {
        VL_RESTORER(m_inAlways);
        m_inAlways = true;
        visitIterateNoValueMod(nodep);
    }
    virtual void visit(AstCover* nodep) override { visitIterateNoValueMod(nodep); }
    virtual void visit(AstRestrict* nodep) override { visitIterateNoValueMod(nodep); }

    virtual void visit(AstBegin* nodep) override {
        V3Config::applyCoverageBlock(m_modp, nodep);
        cleanFileline(nodep);
        const AstNode* const backp = nodep->backp();
        // IEEE says directly nested item is not a new block
        // The genblk name will get attached to the if true/false LOWER begin block(s)
        const bool nestedIf = nestedIfBegin(nodep);
        // It's not FOR(BEGIN(...)) but we earlier changed it to BEGIN(FOR(...))
        if (nodep->genforp()) {
            ++m_genblkNum;
            if (nodep->name() == "") nodep->name("genblk" + cvtToStr(m_genblkNum));
        }
        if (nodep->generate() && nodep->name() == ""
            && (VN_IS(backp, CaseItem) || VN_IS(backp, GenIf)) && !nestedIf) {
            nodep->name("genblk" + cvtToStr(m_genblkAbove));
        }
        if (nodep->name() != "") {
            VL_RESTORER(m_genblkAbove);
            VL_RESTORER(m_genblkNum);
            m_genblkAbove = 0;
            m_genblkNum = 0;
            iterateChildren(nodep);
        } else {
            iterateChildren(nodep);
        }
    }
    virtual void visit(AstGenCase* nodep) override {
        ++m_genblkNum;
        cleanFileline(nodep);
        {
            VL_RESTORER(m_genblkAbove);
            VL_RESTORER(m_genblkNum);
            m_genblkAbove = m_genblkNum;
            m_genblkNum = 0;
            iterateChildren(nodep);
        }
    }
    virtual void visit(AstGenIf* nodep) override {
        cleanFileline(nodep);
        const bool nestedIf
            = (VN_IS(nodep->backp(), Begin) && nestedIfBegin(VN_CAST(nodep->backp(), Begin)));
        if (nestedIf) {
            iterateChildren(nodep);
        } else {
            ++m_genblkNum;
            VL_RESTORER(m_genblkAbove);
            VL_RESTORER(m_genblkNum);
            m_genblkAbove = m_genblkNum;
            m_genblkNum = 0;
            iterateChildren(nodep);
        }
    }
    virtual void visit(AstCase* nodep) override {
        V3Config::applyCase(nodep);
        cleanFileline(nodep);
        iterateChildren(nodep);
    }
    virtual void visit(AstPrintTimeScale* nodep) override {
        // Inlining may change hierarchy, so just save timescale where needed
        cleanFileline(nodep);
        iterateChildren(nodep);
        nodep->name(m_modp->name());
        nodep->timeunit(m_modp->timeunit());
    }
    virtual void visit(AstSFormatF* nodep) override {
        cleanFileline(nodep);
        iterateChildren(nodep);
        nodep->timeunit(m_modp->timeunit());
    }
    virtual void visit(AstTime* nodep) override {
        cleanFileline(nodep);
        iterateChildren(nodep);
        nodep->timeunit(m_modp->timeunit());
    }
    virtual void visit(AstTimeD* nodep) override {
        cleanFileline(nodep);
        iterateChildren(nodep);
        nodep->timeunit(m_modp->timeunit());
    }
    virtual void visit(AstTimeImport* nodep) override {
        cleanFileline(nodep);
        iterateChildren(nodep);
        nodep->timeunit(m_modp->timeunit());
    }
    virtual void visit(AstEventControl* nodep) override {
        cleanFileline(nodep);
        iterateChildren(nodep);
        AstAlways* const alwaysp = VN_CAST(nodep->backp(), Always);
        if (alwaysp && alwaysp->keyword() == VAlwaysKwd::ALWAYS_COMB) {
            alwaysp->v3error("Event control statements not legal under always_comb "
                             "(IEEE 1800-2017 9.2.2.2.2)\n"
                             << nodep->warnMore() << "... Suggest use a normal 'always'");
            VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
        } else if (alwaysp && !alwaysp->sensesp()) {
            // Verilator is still ony supporting SenTrees under an always,
            // so allow the parser to handle everything and shim to
            // historical AST here
            if (AstSenTree* const sensesp = nodep->sensesp()) {
                sensesp->unlinkFrBackWithNext();
                alwaysp->sensesp(sensesp);
            }
            if (nodep->stmtsp()) alwaysp->addStmtp(nodep->stmtsp()->unlinkFrBackWithNext());
            VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
        }
    }

    virtual void visit(AstNode* nodep) override {
        // Default: Just iterate
        cleanFileline(nodep);
        iterateChildren(nodep);
    }

public:
    // CONSTRUCTORS
    explicit LinkParseVisitor(AstNetlist* rootp) { iterate(rootp); }
    virtual ~LinkParseVisitor() override = default;
};

//######################################################################
// Link class functions

void V3LinkParse::linkParse(AstNetlist* rootp) {
    UINFO(4, __FUNCTION__ << ": " << endl);
    { LinkParseVisitor{rootp}; }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("linkparse", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 6);
}
