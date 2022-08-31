// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Resolve module/signal name references
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
// LinkResolve TRANSFORMATIONS:
//      Top-down traversal
//          Extracts:
//              Add SUB so that we subtract off the "base 0-start" of the array
//          SelBit: Convert to ArraySel
//              Add SUB so that we subtract off the "base 0-start" of the array
//          File operations
//              Convert normal var to FILE* type
//          SenItems: Convert pos/negedge of non-simple signals to temporaries
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3LinkResolve.h"

#include "V3Ast.h"
#include "V3Global.h"
#include "V3String.h"

#include <algorithm>
#include <map>

//######################################################################
// Link state, as a visitor of each AstNode

class LinkResolveVisitor final : public VNVisitor {
private:
    // NODE STATE
    //  Entire netlist:
    //   AstCaseItem::user2()   // bool           Moved default caseitems
    const VNUser2InUse m_inuser2;

    // STATE
    // Below state needs to be preserved between each module call.
    AstNodeModule* m_modp = nullptr;  // Current module
    AstClass* m_classp = nullptr;  // Class we're inside
    AstNodeFTask* m_ftaskp = nullptr;  // Function or task we're inside
    AstNodeCoverOrAssert* m_assertp = nullptr;  // Current assertion
    int m_senitemCvtNum = 0;  // Temporary signal counter
    bool m_underGenerate = false;  // Under GenFor/GenIf

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    // VISITs
    // TODO: Most of these visitors are here for historical reasons.
    // TODO: ExpectDecriptor can move to data type resolution, and the rest
    // TODO: could move to V3LinkParse to get them out of the way of elaboration
    virtual void visit(AstNodeModule* nodep) override {
        // Module: Create sim table for entire module and iterate
        UINFO(8, "MODULE " << nodep << endl);
        if (nodep->dead()) return;
        VL_RESTORER(m_modp);
        VL_RESTORER(m_senitemCvtNum);
        {
            m_modp = nodep;
            m_senitemCvtNum = 0;
            iterateChildren(nodep);
        }
    }
    virtual void visit(AstClass* nodep) override {
        VL_RESTORER(m_classp);
        {
            m_classp = nodep;
            iterateChildren(nodep);
        }
    }
    virtual void visit(AstInitialAutomatic* nodep) override {
        iterateChildren(nodep);
        // Initial assignments under function/tasks can just be simple
        // assignments without the initial
        if (m_ftaskp) {
            VL_DO_DANGLING(nodep->replaceWith(nodep->bodysp()->unlinkFrBackWithNext()), nodep);
        }
    }
    virtual void visit(AstNodeCoverOrAssert* nodep) override {
        if (m_assertp) nodep->v3error("Assert not allowed under another assert");
        m_assertp = nodep;
        iterateChildren(nodep);
        m_assertp = nullptr;
    }
    virtual void visit(AstVar* nodep) override {
        iterateChildren(nodep);
        if (m_classp && !nodep->isParam()) nodep->varType(VVarType::MEMBER);
        if (m_ftaskp) nodep->funcLocal(true);
        if (nodep->isSigModPublic()) {
            nodep->sigModPublic(false);  // We're done with this attribute
            m_modp->modPublic(true);  // Avoid flattening if signals are exposed
        }
    }

    virtual void visit(AstNodeVarRef* nodep) override {
        // VarRef: Resolve its reference
        if (nodep->varp()) nodep->varp()->usedParam(true);
        iterateChildren(nodep);
    }

    virtual void visit(AstNodeFTask* nodep) override {
        // NodeTask: Remember its name for later resolution
        if (m_underGenerate) nodep->underGenerate(true);
        // Remember the existing symbol table scope
        if (m_classp) {
            if (nodep->name() == "pre_randomize" || nodep->name() == "post_randomize") {
                nodep->v3warn(E_UNSUPPORTED, "Unsupported: " << nodep->prettyNameQ());
            } else if (nodep->name() == "randomize") {
                nodep->v3error(nodep->prettyNameQ()
                               << " is a predefined class method; redefinition not allowed (IEEE "
                                  "1800-2017 18.6.3)");
            }
            nodep->classMethod(true);
        }
        // V3LinkDot moved the isExternDef into the class, the extern proto was
        // checked to exist, and now isn't needed
        nodep->isExternDef(false);
        if (nodep->isExternProto()) {
            VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
            return;
        }
        {
            m_ftaskp = nodep;
            iterateChildren(nodep);
        }
        m_ftaskp = nullptr;
        if (nodep->dpiExport()) nodep->scopeNamep(new AstScopeName{nodep->fileline(), false});
    }
    virtual void visit(AstNodeFTaskRef* nodep) override {
        iterateChildren(nodep);
        if (nodep->taskp() && (nodep->taskp()->dpiContext() || nodep->taskp()->dpiExport())) {
            nodep->scopeNamep(new AstScopeName{nodep->fileline(), false});
        }
    }

    virtual void visit(AstSenItem* nodep) override {
        // Remove bit selects, and bark if it's not a simple variable
        iterateChildren(nodep);
        if (nodep->isClocked()) {
            // If it's not a simple variable wrap in a temporary
            // This is a bit unfortunate as we haven't done width resolution
            // and any width errors will look a bit odd, but it works.
            AstNode* const sensp = nodep->sensp();
            if (sensp && !VN_IS(sensp, NodeVarRef) && !VN_IS(sensp, Const)) {
                // Make a new temp wire
                const string newvarname = "__Vsenitemexpr" + cvtToStr(++m_senitemCvtNum);
                AstVar* const newvarp = new AstVar(sensp->fileline(), VVarType::MODULETEMP,
                                                   newvarname, VFlagLogicPacked(), 1);
                // We can't just add under the module, because we may be
                // inside a generate, begin, etc.
                // We know a SenItem should be under a SenTree/Always etc,
                // we we'll just hunt upwards
                AstNode* addwherep = nodep;  // Add to this element's next
                while (VN_IS(addwherep, SenItem) || VN_IS(addwherep, SenTree)) {
                    addwherep = addwherep->backp();
                }
                if (!VN_IS(addwherep, Always)) {  // Assertion perhaps?
                    sensp->v3warn(E_UNSUPPORTED,
                                  "Unsupported: Non-single-bit pos/negedge clock statement under "
                                  "some complicated block");
                    addwherep = m_modp;
                }
                addwherep->addNext(newvarp);

                sensp->replaceWith(new AstVarRef(sensp->fileline(), newvarp, VAccess::READ));
                AstAssignW* const assignp = new AstAssignW(
                    sensp->fileline(), new AstVarRef(sensp->fileline(), newvarp, VAccess::WRITE),
                    sensp);
                addwherep->addNext(assignp);
            }
        } else {  // Old V1995 sensitivity list; we'll probably mostly ignore
            bool did = true;
            while (did) {
                did = false;
                if (AstNodeSel* const selp = VN_CAST(nodep->sensp(), NodeSel)) {
                    AstNode* const fromp = selp->fromp()->unlinkFrBack();
                    selp->replaceWith(fromp);
                    VL_DO_DANGLING(selp->deleteTree(), selp);
                    did = true;
                }
                // NodeSel doesn't include AstSel....
                if (AstSel* const selp = VN_CAST(nodep->sensp(), Sel)) {
                    AstNode* const fromp = selp->fromp()->unlinkFrBack();
                    selp->replaceWith(fromp);
                    VL_DO_DANGLING(selp->deleteTree(), selp);
                    did = true;
                }
                if (AstNodePreSel* const selp = VN_CAST(nodep->sensp(), NodePreSel)) {
                    AstNode* const fromp = selp->fromp()->unlinkFrBack();
                    selp->replaceWith(fromp);
                    VL_DO_DANGLING(selp->deleteTree(), selp);
                    did = true;
                }
            }
        }
        if (!VN_IS(nodep->sensp(), NodeVarRef)
            && !VN_IS(nodep->sensp(), EnumItemRef)  // V3Const will cleanup
            && !nodep->isIllegal()) {
            if (debug()) nodep->dumpTree(cout, "-tree: ");
            nodep->v3warn(E_UNSUPPORTED, "Unsupported: Complex statement in sensitivity list");
        }
    }

    virtual void visit(AstNodePreSel* nodep) override {
        if (!nodep->attrp()) {
            iterateChildren(nodep);
            // Constification may change the fromp() to a constant, which will lose the
            // variable we're extracting from (to determine MSB/LSB/endianness/etc.)
            // So we replicate it in another node
            // Note that V3Param knows not to replace AstVarRef's under AstAttrOf's
            AstNode* const basefromp = AstArraySel::baseFromp(nodep, false);
            if (AstNodeVarRef* const varrefp
                = VN_CAST(basefromp, NodeVarRef)) {  // Maybe varxref - so need to clone
                nodep->attrp(new AstAttrOf(nodep->fileline(), VAttrType::VAR_BASE,
                                           varrefp->cloneTree(false)));
            } else if (AstUnlinkedRef* const uvxrp
                       = VN_CAST(basefromp, UnlinkedRef)) {  // Maybe unlinked - so need to clone
                nodep->attrp(new AstAttrOf(nodep->fileline(), VAttrType::VAR_BASE,
                                           uvxrp->cloneTree(false)));
            } else if (auto* const fromp = VN_CAST(basefromp, LambdaArgRef)) {
                nodep->attrp(new AstAttrOf(nodep->fileline(), VAttrType::VAR_BASE,
                                           fromp->cloneTree(false)));
            } else if (AstMemberSel* const fromp = VN_CAST(basefromp, MemberSel)) {
                nodep->attrp(new AstAttrOf(nodep->fileline(), VAttrType::MEMBER_BASE,
                                           fromp->cloneTree(false)));
            } else if (AstEnumItemRef* const fromp = VN_CAST(basefromp, EnumItemRef)) {
                nodep->attrp(new AstAttrOf(nodep->fileline(), VAttrType::ENUM_BASE,
                                           fromp->cloneTree(false)));
            } else if (VN_IS(basefromp, Replicate)) {
                // From {...}[...] syntax in IEEE 2017
                if (basefromp) UINFO(1, "    Related node: " << basefromp << endl);
            } else {
                if (basefromp) UINFO(1, "    Related node: " << basefromp << endl);
                nodep->v3fatalSrc("Illegal bit select; no signal/member being extracted from");
            }
        }
    }

    virtual void visit(AstCaseItem* nodep) override {
        // Move default caseItems to the bottom of the list
        // That saves us from having to search each case list twice, for non-defaults and defaults
        iterateChildren(nodep);
        if (!nodep->user2() && nodep->isDefault() && nodep->nextp()) {
            nodep->user2(true);
            AstNode* const nextp = nodep->nextp();
            nodep->unlinkFrBack();
            nextp->addNext(nodep);
        }
    }

    virtual void visit(AstPragma* nodep) override {
        if (nodep->pragType() == VPragmaType::HIER_BLOCK) {
            UASSERT_OBJ(m_modp, nodep, "HIER_BLOCK not under a module");
            // If this is hierarchical mode which is to lib-create,
            // sub modules do not have hier_block meta comment in the source code.
            // But .vlt files may still mark a module which is actually a lib-create wrapper
            // hier_block. AstNodeModule::hierBlock() can be true only when --hierarchical is
            // specified.
            m_modp->hierBlock(v3Global.opt.hierarchical());
            nodep->unlinkFrBack();
            VL_DO_DANGLING(pushDeletep(nodep), nodep);
        } else if (nodep->pragType() == VPragmaType::PUBLIC_MODULE) {
            UASSERT_OBJ(m_modp, nodep, "PUBLIC_MODULE not under a module");
            m_modp->modPublic(true);
            nodep->unlinkFrBack();
            VL_DO_DANGLING(pushDeletep(nodep), nodep);
        } else if (nodep->pragType() == VPragmaType::PUBLIC_TASK) {
            UASSERT_OBJ(m_ftaskp, nodep, "PUBLIC_TASK not under a task");
            m_ftaskp->taskPublic(true);
            m_modp->modPublic(true);  // Need to get to the task...
            nodep->unlinkFrBack();
            VL_DO_DANGLING(pushDeletep(nodep), nodep);
        } else if (nodep->pragType() == VPragmaType::COVERAGE_BLOCK_OFF) {
            if (!v3Global.opt.coverageLine()) {  // No need for block statements; may optimize
                                                 // better without
                nodep->unlinkFrBack();
                VL_DO_DANGLING(pushDeletep(nodep), nodep);
            }
        } else {
            iterateChildren(nodep);
        }
    }

    string expectFormat(AstNode* nodep, const string& format, AstNode* argp, bool isScan) {
        // Check display arguments, return new format string
        string newFormat;
        bool inPct = false;
        bool inIgnore = false;
        string fmt;
        for (const char ch : format) {
            if (!inPct && ch == '%') {
                inPct = true;
                inIgnore = false;
                fmt = ch;
            } else if (inPct && (isdigit(ch) || ch == '.' || ch == '-')) {
                fmt += ch;
            } else if (inPct) {
                inPct = false;
                fmt += ch;
                switch (tolower(ch)) {
                case '%':  // %% - just output a %
                    break;
                case '*':
                    inPct = true;
                    inIgnore = true;
                    break;
                case 'm':  // %m - auto insert "name"
                    if (isScan) {
                        nodep->v3warn(E_UNSUPPORTED, "Unsupported: %m in $fscanf");
                        fmt = "";
                    }
                    break;
                case 'l':  // %l - auto insert "library"
                    if (isScan) {
                        nodep->v3warn(E_UNSUPPORTED, "Unsupported: %l in $fscanf");
                        fmt = "";
                    }
                    if (m_modp) fmt = VString::quotePercent(m_modp->prettyName());
                    break;
                default:  // Most operators, just move to next argument
                    if (!V3Number::displayedFmtLegal(ch, isScan)) {
                        nodep->v3error("Unknown $display-like format code: '%" << ch << "'");
                    } else if (!inIgnore) {
                        if (!argp) {
                            nodep->v3error("Missing arguments for $display-like format");
                        } else {
                            argp = argp->nextp();
                        }
                    }
                    break;
                }  // switch
                newFormat += fmt;
            } else {
                newFormat += ch;
            }
        }

        if (argp && !isScan) {
            int skipCount = 0;  // number of args consume by any additional format strings
            while (argp) {
                if (skipCount) {
                    argp = argp->nextp();
                    --skipCount;
                    continue;
                }
                const AstConst* const constp = VN_CAST(argp, Const);
                const bool isFromString = (constp) ? constp->num().isFromString() : false;
                if (isFromString) {
                    const int numchars = argp->dtypep()->width() / 8;
                    if (!constp->num().toString().empty()) {
                        string str(numchars, ' ');
                        // now scan for % operators
                        bool inpercent = false;
                        for (int i = 0; i < numchars; i++) {
                            const int ii = numchars - i - 1;
                            const char c = constp->num().dataByte(ii);
                            str[i] = c;
                            if (!inpercent && c == '%') {
                                inpercent = true;
                            } else if (inpercent) {
                                inpercent = false;
                                switch (c) {
                                case '0':  // FALLTHRU
                                case '1':  // FALLTHRU
                                case '2':  // FALLTHRU
                                case '3':  // FALLTHRU
                                case '4':  // FALLTHRU
                                case '5':  // FALLTHRU
                                case '6':  // FALLTHRU
                                case '7':  // FALLTHRU
                                case '8':  // FALLTHRU
                                case '9':  // FALLTHRU
                                case '.': inpercent = true; break;
                                case '%': break;
                                default:
                                    if (V3Number::displayedFmtLegal(c, isScan)) ++skipCount;
                                }
                            }
                        }
                        newFormat.append(str);
                    }
                    AstNode* const nextp = argp->nextp();
                    argp->unlinkFrBack();
                    VL_DO_DANGLING(pushDeletep(argp), argp);
                    argp = nextp;
                } else {
                    newFormat.append("%?");  // V3Width to figure it out
                    argp = argp->nextp();
                }
            }
        }
        return newFormat;
    }

    static void expectDescriptor(AstNode* /*nodep*/, AstNodeVarRef* filep) {
        // This might fail on complex expressions like arrays
        // We use attrFileDescr() only for lint suppression, so that's ok
        if (filep && filep->varp()) filep->varp()->attrFileDescr(true);
    }

    virtual void visit(AstFOpen* nodep) override {
        iterateChildren(nodep);
        expectDescriptor(nodep, VN_CAST(nodep->filep(), NodeVarRef));
    }
    virtual void visit(AstFOpenMcd* nodep) override {
        iterateChildren(nodep);
        expectDescriptor(nodep, VN_CAST(nodep->filep(), NodeVarRef));
    }
    virtual void visit(AstFClose* nodep) override {
        iterateChildren(nodep);
        expectDescriptor(nodep, VN_CAST(nodep->filep(), NodeVarRef));
    }
    virtual void visit(AstFError* nodep) override {
        iterateChildren(nodep);
        expectDescriptor(nodep, VN_CAST(nodep->filep(), NodeVarRef));
    }
    virtual void visit(AstFEof* nodep) override {
        iterateChildren(nodep);
        expectDescriptor(nodep, VN_CAST(nodep->filep(), NodeVarRef));
    }
    virtual void visit(AstFRead* nodep) override {
        iterateChildren(nodep);
        expectDescriptor(nodep, VN_CAST(nodep->filep(), NodeVarRef));
    }
    virtual void visit(AstFScanF* nodep) override {
        iterateChildren(nodep);
        expectFormat(nodep, nodep->text(), nodep->exprsp(), true);
    }
    virtual void visit(AstSScanF* nodep) override {
        iterateChildren(nodep);
        expectFormat(nodep, nodep->text(), nodep->exprsp(), true);
    }
    virtual void visit(AstSFormatF* nodep) override {
        iterateChildren(nodep);
        // Cleanup old-school displays without format arguments
        if (!nodep->hasFormat()) {
            UASSERT_OBJ(nodep->text() == "", nodep,
                        "Non-format $sformatf should have \"\" format");
            if (VN_IS(nodep->exprsp(), Const)
                && VN_AS(nodep->exprsp(), Const)->num().isFromString()) {
                AstConst* const fmtp = VN_AS(nodep->exprsp()->unlinkFrBack(), Const);
                nodep->text(fmtp->num().toString());
                VL_DO_DANGLING(pushDeletep(fmtp), fmtp);
            }
            nodep->hasFormat(true);
        }
        const string newFormat = expectFormat(nodep, nodep->text(), nodep->exprsp(), false);
        nodep->text(newFormat);
        if ((VN_IS(nodep->backp(), Display)
             && VN_AS(nodep->backp(), Display)->displayType().needScopeTracking())
            || nodep->formatScopeTracking()) {
            nodep->scopeNamep(new AstScopeName{nodep->fileline(), true});
        }
    }

    virtual void visit(AstUdpTable* nodep) override {
        UINFO(5, "UDPTABLE  " << nodep << endl);
        if (!v3Global.opt.bboxUnsup()) {
            // We don't warn until V3Inst, so that UDPs that are in libraries and
            // never used won't result in any warnings.
        } else {
            // Massive hack, just tie off all outputs so our analysis can proceed
            const AstVar* varoutp = nullptr;
            for (AstNode* stmtp = m_modp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
                if (AstVar* const varp = VN_CAST(stmtp, Var)) {
                    if (varp->isReadOnly()) {
                    } else if (varp->isWritable()) {
                        if (varoutp) {
                            varp->v3error("Multiple outputs not allowed in udp modules");
                        }
                        varoutp = varp;
                        // Tie off
                        m_modp->addStmtp(
                            new AstAssignW(varp->fileline(),
                                           new AstVarRef(varp->fileline(), varp, VAccess::WRITE),
                                           new AstConst(varp->fileline(), AstConst::BitFalse())));
                    } else {
                        varp->v3error("Only inputs and outputs are allowed in udp modules");
                    }
                }
            }
            nodep->unlinkFrBack();
            VL_DO_DANGLING(pushDeletep(nodep), nodep);
        }
    }

    virtual void visit(AstScCtor* nodep) override {
        // Constructor info means the module must remain public
        m_modp->modPublic(true);
        iterateChildren(nodep);
    }
    virtual void visit(AstScDtor* nodep) override {
        // Destructor info means the module must remain public
        m_modp->modPublic(true);
        iterateChildren(nodep);
    }
    virtual void visit(AstScInt* nodep) override {
        // Special class info means the module must remain public
        m_modp->modPublic(true);
        iterateChildren(nodep);
    }

    virtual void visit(AstIfaceRefDType* nodep) override {
        // LinkDot checked modports, now remove references to them
        // Keeping them later caused problems with InstDeArray,
        // as it needed to make new modport arrays and such
        nodep->modportp(nullptr);
        iterateChildren(nodep);
    }
    // virtual void visit(AstModport* nodep) override { ... }
    // We keep Modport's themselves around for XML dump purposes

    virtual void visit(AstGenFor* nodep) override {
        VL_RESTORER(m_underGenerate);
        m_underGenerate = true;
        iterateChildren(nodep);
    }
    virtual void visit(AstGenIf* nodep) override {
        VL_RESTORER(m_underGenerate);
        m_underGenerate = true;
        iterateChildren(nodep);
    }

    virtual void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit LinkResolveVisitor(AstNetlist* rootp) { iterate(rootp); }
    virtual ~LinkResolveVisitor() override = default;
};

//######################################################################
// LinkBotupVisitor
//      Recurses cells backwards, so we can pick up those things that propagate
//      from child cells up to the top module.

class LinkBotupVisitor final : public VNVisitor {
private:
    // STATE
    AstNodeModule* m_modp = nullptr;  // Current module

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    // VISITs
    virtual void visit(AstNetlist* nodep) override {
        // Iterate modules backwards, in bottom-up order.
        iterateChildrenBackwards(nodep);
    }
    virtual void visit(AstNodeModule* nodep) override {
        VL_RESTORER(m_modp);
        {
            m_modp = nodep;
            iterateChildren(nodep);
        }
    }
    virtual void visit(AstCell* nodep) override {
        // Parent module inherits child's publicity
        if (nodep->modp()->modPublic()) m_modp->modPublic(true);
        //** No iteration for speed
    }
    virtual void visit(AstNodeMath*) override {}  // Accelerate
    virtual void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit LinkBotupVisitor(AstNetlist* rootp) { iterate(rootp); }
    virtual ~LinkBotupVisitor() override = default;
};

//######################################################################
// Link class functions

void V3LinkResolve::linkResolve(AstNetlist* rootp) {
    UINFO(4, __FUNCTION__ << ": " << endl);
    {
        const LinkResolveVisitor visitor{rootp};
        LinkBotupVisitor{rootp};
    }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("linkresolve", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 6);
}
