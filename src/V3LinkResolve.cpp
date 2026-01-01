// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Resolve module/signal name references
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

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3LinkResolve.h"

#include "V3String.h"
#include "V3Task.h"

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// Link state, as a visitor of each AstNode

class LinkResolveVisitor final : public VNVisitor {
    // NODE STATE
    //  Entire netlist:
    //   AstCaseItem::user2()   // bool     Moved default caseitems
    //   AstNodeFTaskRef::user2()  // bool  Processing - to check for recursion
    const VNUser2InUse m_inuser2;

    // STATE
    // Below state needs to be preserved between each module call.
    AstNodeModule* m_modp = nullptr;  // Current module
    AstClass* m_classp = nullptr;  // Class we're inside
    string m_randcIllegalWhy;  // Why randc illegal
    AstNode* m_randcIllegalp = nullptr;  // Node causing randc illegal
    AstNodeFTask* m_ftaskp = nullptr;  // Function or task we're inside
    int m_senitemCvtNum = 0;  // Temporary signal counter
    std::deque<AstGenFor*> m_underGenFors;  // Stack of GenFor underneath
    bool m_underGenerate = false;  // Under GenFor/GenIf
    AstNodeExpr* m_currentRandomizeSelectp = nullptr;  // fromp() of current `randomize()` call
    bool m_inRandomizeWith = false;  // If in randomize() with (and no other with afterwards)

    // VISITORS
    // TODO: Most of these visitors are here for historical reasons.
    // TODO: ExpectDescriptor can move to data type resolution, and the rest
    // TODO: could move to V3LinkParse to get them out of the way of elaboration
    void visit(AstNodeModule* nodep) override {
        // Module: Create sim table for entire module and iterate
        UINFO(8, "MODULE " << nodep);
        if (nodep->dead()) return;
        VL_RESTORER(m_modp);
        VL_RESTORER(m_senitemCvtNum);
        m_modp = nodep;
        m_senitemCvtNum = 0;
        iterateChildren(nodep);
    }
    void visit(AstClass* nodep) override {
        VL_RESTORER(m_classp);
        m_classp = nodep;
        iterateChildren(nodep);
    }
    void visit(AstConstraint* nodep) override {
        // V3LinkDot moved the isExternDef into the class, the extern proto was
        // checked to exist, and now isn't needed
        nodep->isExternDef(false);
        if (nodep->isExternProto()) {
            VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
            return;
        }
        iterateChildren(nodep);
    }
    void visit(AstConstraintBefore* nodep) override {
        VL_RESTORER(m_randcIllegalWhy);
        VL_RESTORER(m_randcIllegalp);
        m_randcIllegalWhy = "'solve before' (IEEE 1800-2023 18.5.9)";
        m_randcIllegalp = nodep;
        iterateChildrenConst(nodep);
    }
    void visit(AstDist* nodep) override {
        VL_RESTORER(m_randcIllegalWhy);
        VL_RESTORER(m_randcIllegalp);
        m_randcIllegalWhy = "'constraint dist' (IEEE 1800-2023 18.5.3)";
        m_randcIllegalp = nodep;
        iterateChildrenConst(nodep);
    }
    void visit(AstConstraintExpr* nodep) override {
        VL_RESTORER(m_randcIllegalWhy);
        VL_RESTORER(m_randcIllegalp);
        if (nodep->isSoft()) {
            m_randcIllegalWhy = "'constraint soft' (IEEE 1800-2023 18.5.13.1)";
            m_randcIllegalp = nodep;
        }
        iterateChildrenConst(nodep);
    }

    void visit(AstInitialAutomatic* nodep) override {
        iterateChildren(nodep);
        // Initial assignments under function/tasks can just be simple
        // assignments without the initial
        if (m_ftaskp) {
            nodep->replaceWith(nodep->stmtsp()->unlinkFrBackWithNext());
            VL_DO_DANGLING(pushDeletep(nodep), nodep);
        }
    }
    void visit(AstVar* nodep) override {
        iterateChildren(nodep);
        if (m_classp && !nodep->isParam()) nodep->varType(VVarType::MEMBER);
        if (m_ftaskp) nodep->funcLocal(true);
        if (nodep->isSigModPublic()) {
            nodep->sigModPublic(false);  // We're done with this attribute
            m_modp->modPublic(true);  // Avoid flattening if signals are exposed
        }
    }

    void visit(AstNodeVarRef* nodep) override {
        if (nodep->varp()) {  // Else due to dead code, might not have var pointer
            // VarRef: Resolve its reference
            nodep->varp()->usedParam(true);
            // Look for where genvar is valid
            bool ok = false;
            // cppcheck-suppress constVariablePointer
            for (AstGenFor* const forp : m_underGenFors) {
                if (ok) break;
                if (forp->initsp())
                    forp->initsp()->foreach([&](const AstVarRef* refp) {  //
                        if (refp->varp() == nodep->varp()) ok = true;
                    });
            }
            if (nodep->varp()->isGenVar() && !ok) {
                nodep->v3error("Genvar "
                               << nodep->prettyNameQ()
                               << " used outside generate for loop (IEEE 1800-2023 27.4)");
            }
            if (nodep->varp()->isRandC() && m_randcIllegalp) {
                nodep->v3error("Randc variables not allowed in "
                               << m_randcIllegalWhy << '\n'
                               << nodep->warnContextPrimary() << '\n'
                               << m_randcIllegalp->warnOther()
                               << "... Location of restricting expression\n"
                               << m_randcIllegalp->warnContextSecondary());
            }
        }
        iterateChildren(nodep);
    }

    void visit(AstNodeFTask* nodep) override {
        // Note AstLet is handled specifically elsewhere
        // NodeTask: Remember its name for later resolution
        if (m_underGenerate) nodep->underGenerate(true);
        // Remember the existing symbol table scope
        if (m_classp) nodep->classMethod(true);
        // V3LinkDot moved the isExternDef into the class, the extern proto was
        // checked to exist, and now isn't needed
        nodep->isExternDef(false);
        if (nodep->isExternProto()) {
            VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
            return;
        }
        VL_RESTORER(m_ftaskp);
        m_ftaskp = nodep;
        iterateChildren(nodep);
        if (nodep->dpiExport()) nodep->scopeNamep(new AstScopeName{nodep->fileline(), false});
    }
    void visit(AstNodeFTaskRef* nodep) override {
        VL_RESTORER(m_currentRandomizeSelectp);
        if (nodep->taskp()) {
            if (AstSequence* const seqp = VN_CAST(nodep->taskp(), Sequence))
                seqp->isReferenced(true);
        }

        if (nodep->name() == "randomize") {
            if (const AstMethodCall* const methodcallp = VN_CAST(nodep, MethodCall)) {
                if (m_inRandomizeWith) {
                    nodep->v3warn(
                        E_UNSUPPORTED,
                        "Unsupported: randomize() nested in inline randomize() constraints");
                }
                m_currentRandomizeSelectp = methodcallp->fromp();
            }
        }
        iterateChildren(nodep);
        if (AstLet* letp = VN_CAST(nodep->taskp(), Let)) {
            UINFO(7, "letSubstitute() " << nodep << " <- " << letp);
            if (letp->user2()) {
                nodep->v3error("Recursive let substitution " << letp->prettyNameQ());
                nodep->replaceWith(new AstConst{nodep->fileline(), AstConst::BitFalse{}});
                VL_DO_DANGLING(pushDeletep(nodep), nodep);
                return;
            }
            letp->user2(true);
            if (VN_IS(nodep->backp(), StmtExpr)) {
                nodep->v3error("Expected statement, not let substitution " << letp->prettyNameQ());
            }
            // UINFOTREE(1, letp, "", "let-let");
            // UINFOTREE(1, nodep, "", "let-ref");
            // cppcheck-suppress constVariablePointer
            AstStmtExpr* const letStmtp = VN_AS(letp->stmtsp(), StmtExpr);
            AstNodeExpr* const newp = letStmtp->exprp()->cloneTree(false);
            const V3TaskConnects tconnects = V3Task::taskConnects(nodep, letp->stmtsp());
            std::map<const AstVar*, AstNodeExpr*> portToExprs;
            for (const auto& tconnect : tconnects) {
                const AstVar* const portp = tconnect.first;
                const AstArg* const argp = tconnect.second;
                AstNodeExpr* const pinp = argp->exprp();
                if (!pinp) continue;  // Argument error we'll find later
                portToExprs.emplace(portp, pinp);
            }
            // Replace VarRefs of arguments with the argument values
            newp->foreach([&](AstVarRef* refp) {  //
                const auto it = portToExprs.find(refp->varp());
                if (it != portToExprs.end()) {
                    AstNodeExpr* const pinp = it->second;
                    UINFO(9, "let pin subst " << refp << " <- " << pinp);
                    // Side effects are copied into pins, to match other simulators
                    refp->replaceWith(pinp->cloneTree(false));
                    VL_DO_DANGLING(pushDeletep(refp), refp);
                }
            });
            // UINFOTREE(1, newp, "", "let-new");
            nodep->replaceWith(newp);
            VL_DO_DANGLING(pushDeletep(nodep), nodep);
            // Iterate to expand further now, so we can look for recursions
            visit(newp);
            letp->user2(false);
            return;
        }
    }

    void visit(AstCaseItem* nodep) override {
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

    void visit(AstLet* nodep) override {
        // Lets have been (or about to be) substituted, we can remove
        nodep->unlinkFrBack();
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }

    void visit(AstStmtPragma* nodep) override {
        if (nodep->pragp()->pragType() == VPragmaType::COVERAGE_BLOCK_OFF) {
            // Strip pragma if not needed, may optimize better without
            if (!v3Global.opt.coverageLine()) {
                VL_DO_DANGLING(pushDeletep(nodep->unlinkFrBack()), nodep);
                return;
            }
        }
        iterateChildren(nodep);
    }

    void visit(AstPragma* nodep) override {
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
        string parseFormat = format;
        while (!parseFormat.empty() || argp) {
            for (const char ch : parseFormat) {
                if (!inPct && ch == '%') {
                    inPct = true;
                    inIgnore = false;
                    fmt = ch;
                } else if (inPct && (std::isdigit(ch) || ch == '.' || ch == '-')) {
                    fmt += ch;
                } else if (inPct) {
                    inPct = false;
                    fmt += ch;
                    switch (std::tolower(ch)) {
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
                        if (m_modp)
                            fmt = AstNode::prettyName(m_modp->libname()) + "."
                                  + m_modp->prettyName();
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

            // Find additional arguments (without format) or additional format strings
            parseFormat = "";

            if (isScan) break;
            while (argp) {
                const AstConst* const constp = VN_CAST(argp, Const);
                const bool isFromString = (constp) ? constp->num().isFromString() : false;
                if (!isFromString) {
                    newFormat.append("%?");  // V3Width to figure it out
                    argp = argp->nextp();
                } else {  // New format string
                    parseFormat += constp->num().toString();
                    AstNode* const nextp = argp->nextp();
                    argp->unlinkFrBack();
                    VL_DO_DANGLING(pushDeletep(argp), argp);
                    argp = nextp;
                    break;  // And continue at top of parsing the new parseFormat
                }
            }
        }
        return newFormat;
    }

    static void expectDescriptor(AstNode* /*nodep*/, const AstNodeVarRef* filep) {
        // This might fail on complex expressions like arrays
        // We use attrFileDescr() only for lint suppression, so that's ok
        if (filep && filep->varp()) filep->varp()->attrFileDescr(true);
    }

    void visit(AstFClose* nodep) override {
        iterateChildren(nodep);
        expectDescriptor(nodep, VN_CAST(nodep->filep(), NodeVarRef));
    }
    void visit(AstFError* nodep) override {
        iterateChildren(nodep);
        expectDescriptor(nodep, VN_CAST(nodep->filep(), NodeVarRef));
    }
    void visit(AstFEof* nodep) override {
        iterateChildren(nodep);
        expectDescriptor(nodep, VN_CAST(nodep->filep(), NodeVarRef));
    }
    void visit(AstFRead* nodep) override {
        iterateChildren(nodep);
        expectDescriptor(nodep, VN_CAST(nodep->filep(), NodeVarRef));
    }
    void visit(AstFScanF* nodep) override {
        iterateChildren(nodep);
        expectFormat(nodep, nodep->text(), nodep->exprsp(), true);
    }
    void visit(AstSScanF* nodep) override {
        iterateChildren(nodep);
        expectFormat(nodep, nodep->text(), nodep->exprsp(), true);
    }
    void visit(AstSFormatF* nodep) override {
        if (nodep->user2SetOnce()) return;
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

    void visit(AstUdpTable* nodep) override {
        UINFO(5, "UDPTABLE  " << nodep);
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
                        AstAssignW* const ap
                            = new AstAssignW{varp->fileline(),
                                             new AstVarRef{varp->fileline(), varp, VAccess::WRITE},
                                             new AstConst{varp->fileline(), AstConst::BitFalse{}}};
                        m_modp->addStmtsp(new AstAlways{ap});
                    } else {
                        varp->v3error("Only inputs and outputs are allowed in udp modules");
                    }
                }
            }
            nodep->unlinkFrBack();
            VL_DO_DANGLING(pushDeletep(nodep), nodep);
        }
    }

    void visit(AstSystemCSection* nodep) override {
        switch (nodep->sectionType()) {
        // Constructor, desctructor or special class info means the module must remain public
        case VSystemCSectionType::CTOR:
        case VSystemCSectionType::DTOR:
        case VSystemCSectionType::INT: m_modp->modPublic(true); break;
        default: break;
        }
        // Has no children
    }

    void visit(AstIfaceRefDType* nodep) override {
        // LinkDot checked modports, now remove references to them
        // Keeping them later caused problems with InstDeArray,
        // as it needed to make new modport arrays and such
        nodep->modportp(nullptr);
        iterateChildren(nodep);
    }
    //  void visit(AstModport* nodep) override { ... }
    // We keep Modport's themselves around for JSON dump purposes

    void visit(AstGenFor* nodep) override {
        VL_RESTORER(m_underGenerate);
        m_underGenerate = true;
        m_underGenFors.emplace_back(nodep);
        iterateChildren(nodep);
        UASSERT_OBJ(!m_underGenFors.empty(), nodep, "Underflow");
        m_underGenFors.pop_back();
    }
    void visit(AstGenIf* nodep) override {
        VL_RESTORER(m_underGenerate);
        m_underGenerate = true;
        iterateChildren(nodep);
    }

    void visit(AstMemberSel* nodep) override {
        if (m_inRandomizeWith && nodep->fromp()->isSame(m_currentRandomizeSelectp)) {
            // Replace member selects to the element
            // on which the randomize() is called with LambdaArgRef
            // This allows V3Randomize to work properly when
            // constrained variables are referred using that object
            AstNodeExpr* const prevFromp = nodep->fromp();
            prevFromp->replaceWith(
                new AstLambdaArgRef{prevFromp->fileline(), prevFromp->name(), false});
            pushDeletep(prevFromp);
        }
        iterateChildren(nodep);
    }

    void visit(AstWith* nodep) override {
        VL_RESTORER(m_inRandomizeWith);
        if (const AstMethodCall* const methodCallp = VN_CAST(nodep->backp(), MethodCall)) {
            m_inRandomizeWith = methodCallp->name() == "randomize";
        } else {
            m_inRandomizeWith = false;
        }
        iterateChildren(nodep);
    }

    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit LinkResolveVisitor(AstNetlist* rootp) { iterate(rootp); }
    ~LinkResolveVisitor() override = default;
};

//######################################################################
// LinkBotupVisitor
//      Recurses cells backwards, so we can pick up those things that propagate
//      from child cells up to the top module.

class LinkBotupVisitor final : public VNVisitorConst {
    // STATE
    AstNodeModule* m_modp = nullptr;  // Current module

    // VISITORS
    void visit(AstNetlist* nodep) override {
        // Iterate modules backwards, in bottom-up order.
        iterateChildrenBackwardsConst(nodep);
    }
    void visit(AstNodeModule* nodep) override {
        VL_RESTORER(m_modp);
        m_modp = nodep;
        iterateChildrenConst(nodep);
    }
    void visit(AstCell* nodep) override {
        // Parent module inherits child's publicity
        if (nodep->modp()->modPublic()) m_modp->modPublic(true);
        //** No iteration for speed
    }
    void visit(AstNodeExpr*) override {}  // Accelerate
    void visit(AstNode* nodep) override { iterateChildrenConst(nodep); }

public:
    // CONSTRUCTORS
    explicit LinkBotupVisitor(AstNetlist* rootp) { iterateConst(rootp); }
    ~LinkBotupVisitor() override = default;
};

//######################################################################
// Link class functions

void V3LinkResolve::linkResolve(AstNetlist* rootp) {
    UINFO(4, __FUNCTION__ << ": ");
    {
        const LinkResolveVisitor visitor{rootp};
        LinkBotupVisitor{rootp};
    }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("linkresolve", 0, dumpTreeEitherLevel() >= 6);
}
