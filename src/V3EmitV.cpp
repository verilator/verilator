// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Emit Verilog from tree
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2004-2024 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "V3PchAstMT.h"

#include "V3EmitV.h"

#include "V3EmitCBase.h"

#include <vector>

VL_DEFINE_DEBUG_FUNCTIONS;

// ######################################################################
//  Emit statements and expressions

class EmitVBaseVisitorConst VL_NOT_FINAL : public EmitCBaseVisitorConst {
    // MEMBERS
    bool m_suppressSemi = false;
    const bool m_suppressUnknown = false;
    AstSenTree* m_sensesp;  // Domain for printing one a ALWAYS under a ACTIVE

    // METHODS

    virtual void puts(const string& str) = 0;
    virtual void putbs(const string& str) = 0;
    virtual void putfs(AstNode* nodep, const string& str) = 0;  // Fileline and node %% mark
    virtual void putqs(AstNode* nodep, const string& str) = 0;  // Fileline quiet w/o %% mark
    virtual void putsNoTracking(const string& str) = 0;
    virtual void putsQuoted(const string& str) {
        // Quote \ and " for use inside C programs
        // Don't use to quote a filename for #include - #include doesn't \ escape.
        // Duplicate in V3File - here so we can print to string
        putsNoTracking("\"");
        putsNoTracking(V3OutFormatter::quoteNameControls(str));
        putsNoTracking("\"");
    }

    // VISITORS
    void visit(AstNetlist* nodep) override { iterateAndNextConstNull(nodep->modulesp()); }
    void visit(AstNodeModule* nodep) override {
        putfs(nodep, nodep->verilogKwd() + " " + prefixNameProtect(nodep) + ";\n");
        iterateChildrenConst(nodep);
        putqs(nodep, "end" + nodep->verilogKwd() + "\n");
    }
    void visit(AstPort* nodep) override {}
    void visit(AstNodeFTask* nodep) override {
        putfs(nodep, nodep->isFunction() ? "function" : "task");
        puts(" ");
        puts(nodep->prettyName());
        puts(";\n");
        // Only putfs the first time for each visitor; later for same node is putqs
        iterateAndNextConstNull(nodep->stmtsp());
        putfs(nodep, nodep->isFunction() ? "endfunction\n" : "endtask\n");
    }

    void visit(AstBegin* nodep) override {
        if (nodep->name() == "") {
            putbs("begin\n");
        } else {
            putbs("begin : " + nodep->name() + "\n");
        }
        iterateChildrenConst(nodep);
        puts("end\n");
    }
    void visit(AstFork* nodep) override {
        if (nodep->name() == "") {
            putbs("fork\n");
        } else {
            putbs("fork : " + nodep->name() + "\n");
        }
        iterateChildrenConst(nodep);
        puts(nodep->joinType().verilogKwd());
        puts("\n");
    }
    void visit(AstFinal* nodep) override {
        putfs(nodep, "final begin\n");
        iterateChildrenConst(nodep);
        putqs(nodep, "end\n");
    }
    void visit(AstInitial* nodep) override {
        putfs(nodep, "initial begin\n");
        iterateChildrenConst(nodep);
        putqs(nodep, "end\n");
    }
    void visit(AstInitialAutomatic* nodep) override { iterateChildrenConst(nodep); }
    void visit(AstInitialStatic* nodep) override { iterateChildrenConst(nodep); }
    void visit(AstAlways* nodep) override {
        putfs(nodep, "always ");
        if (m_sensesp) {
            iterateAndNextConstNull(m_sensesp);
        }  // In active
        else {
            iterateAndNextConstNull(nodep->sensesp());
        }
        putbs(" begin\n");
        iterateAndNextConstNull(nodep->stmtsp());
        putqs(nodep, "end\n");
    }
    void visit(AstAlwaysPublic* nodep) override {
        putfs(nodep, "/*verilator public_flat_rw ");
        if (m_sensesp) {
            iterateAndNextConstNull(m_sensesp);
        }  // In active
        else {
            iterateAndNextConstNull(nodep->sensesp());
        }
        putqs(nodep, " ");
        iterateAndNextConstNull(nodep->stmtsp());
        putqs(nodep, "*/\n");
    }
    void visit(AstNodeAssign* nodep) override {
        if (VN_IS(nodep, AssignForce)) puts("force ");
        iterateAndNextConstNull(nodep->lhsp());
        putfs(nodep, " " + nodep->verilogKwd() + " ");
        iterateAndNextConstNull(nodep->rhsp());
        if (!m_suppressSemi) puts(";\n");
    }
    void visit(AstAssignDly* nodep) override {
        iterateAndNextConstNull(nodep->lhsp());
        putfs(nodep, " <= ");
        iterateAndNextConstNull(nodep->rhsp());
        puts(";\n");
    }
    void visit(AstAssignAlias* nodep) override {
        putbs("alias ");
        iterateAndNextConstNull(nodep->lhsp());
        putfs(nodep, " = ");
        iterateAndNextConstNull(nodep->rhsp());
        if (!m_suppressSemi) puts(";\n");
    }
    void visit(AstAssignW* nodep) override {
        putfs(nodep, "assign ");
        iterateAndNextConstNull(nodep->lhsp());
        putbs(" = ");
        iterateAndNextConstNull(nodep->rhsp());
        if (!m_suppressSemi) puts(";\n");
    }
    void visit(AstRelease* nodep) override {
        puts("release ");
        iterateAndNextConstNull(nodep->lhsp());
        if (!m_suppressSemi) puts(";\n");
    }
    void visit(AstBreak*) override {
        putbs("break");
        if (!m_suppressSemi) puts(";\n");
    }
    void visit(AstSenTree* nodep) override {
        // AstSenItem is called for dumping in isolation by V3Order
        putfs(nodep, "@(");
        for (AstNode* expp = nodep->sensesp(); expp; expp = expp->nextp()) {
            iterateConst(expp);
            if (expp->nextp()) putqs(expp->nextp(), " or ");
        }
        puts(")");
    }
    void visit(AstSenItem* nodep) override {
        putfs(nodep, "");
        puts(nodep->edgeType().verilogKwd());
        if (nodep->sensp()) puts(" ");
        iterateChildrenConst(nodep);
    }
    void visit(AstNodeCase* nodep) override {
        putfs(nodep, "");
        if (const AstCase* const casep = VN_CAST(nodep, Case)) {
            if (casep->priorityPragma()) puts("priority ");
            if (casep->uniquePragma()) puts("unique ");
            if (casep->unique0Pragma()) puts("unique0 ");
        }
        puts(nodep->verilogKwd());
        puts(" (");
        iterateAndNextConstNull(nodep->exprp());
        puts(")\n");
        if (const AstCase* const casep = VN_CAST(nodep, Case)) {
            if (casep->fullPragma() || casep->parallelPragma()) {
                puts(" // synopsys");
                if (casep->fullPragma()) puts(" full_case");
                if (casep->parallelPragma()) puts(" parallel_case");
            }
        }
        iterateAndNextConstNull(nodep->itemsp());
        putqs(nodep, "endcase\n");
    }
    void visit(AstCaseItem* nodep) override {
        if (nodep->condsp()) {
            iterateAndNextConstNull(nodep->condsp());
        } else {
            putbs("default");
        }
        putfs(nodep, ": begin ");
        iterateAndNextConstNull(nodep->stmtsp());
        putqs(nodep, "end\n");
    }
    void visit(AstComment* nodep) override {
        puts("// "s + nodep->name() + "\n");
        iterateChildrenConst(nodep);
    }
    void visit(AstContinue*) override {
        putbs("continue");
        if (!m_suppressSemi) puts(";\n");
    }
    void visit(AstCoverDecl*) override {}  // N/A
    void visit(AstCoverInc*) override {}  // N/A
    void visit(AstCoverToggle*) override {}  // N/A

    void visitNodeDisplay(AstNode* nodep, AstNode* fileOrStrgp, const string& text,
                          AstNode* exprsp) {
        putfs(nodep, nodep->verilogKwd());
        putbs("(");
        if (fileOrStrgp) {
            iterateAndNextConstNull(fileOrStrgp);
            putbs(", ");
        }
        putsQuoted(text);
        for (AstNode* expp = exprsp; expp; expp = expp->nextp()) {
            puts(", ");
            iterateAndNextConstNull(expp);
        }
        puts(");\n");
    }
    void visit(AstDisable* nodep) override { putbs("disable " + nodep->name() + ";\n"); }
    void visit(AstDisplay* nodep) override {
        visitNodeDisplay(nodep, nodep->filep(), nodep->fmtp()->text(), nodep->fmtp()->exprsp());
    }
    void visit(AstElabDisplay* nodep) override {
        visitNodeDisplay(nodep, nullptr, nodep->fmtp()->text(), nodep->fmtp()->exprsp());
    }
    void visit(AstFScanF* nodep) override {
        visitNodeDisplay(nodep, nodep->filep(), nodep->text(), nodep->exprsp());
    }
    void visit(AstSScanF* nodep) override {
        visitNodeDisplay(nodep, nodep->fromp(), nodep->text(), nodep->exprsp());
    }
    void visit(AstSFormat* nodep) override {
        visitNodeDisplay(nodep, nodep->lhsp(), nodep->fmtp()->text(), nodep->fmtp()->exprsp());
    }
    void visit(AstSFormatF* nodep) override {
        visitNodeDisplay(nodep, nullptr, nodep->text(), nodep->exprsp());
    }
    void visit(AstFOpen* nodep) override {
        putfs(nodep, nodep->verilogKwd());
        putbs("(");
        iterateAndNextConstNull(nodep->filenamep());
        putbs(", ");
        iterateAndNextConstNull(nodep->modep());
        puts(");\n");
    }
    void visit(AstFOpenMcd* nodep) override {
        putfs(nodep, nodep->verilogKwd());
        putbs("(");
        iterateAndNextConstNull(nodep->filenamep());
        puts(");\n");
    }
    void visit(AstFClose* nodep) override {
        putfs(nodep, nodep->verilogKwd());
        putbs("(");
        if (nodep->filep()) iterateAndNextConstNull(nodep->filep());
        puts(");\n");
    }
    void visit(AstFFlush* nodep) override {
        putfs(nodep, nodep->verilogKwd());
        putbs("(");
        if (nodep->filep()) iterateAndNextConstNull(nodep->filep());
        puts(");\n");
    }
    void visit(AstJumpBlock* nodep) override {
        putbs("begin : label" + cvtToStr(nodep->labelNum()) + "\n");
        if (nodep->stmtsp()) iterateAndNextConstNull(nodep->stmtsp());
        puts("end\n");
    }
    void visit(AstJumpGo* nodep) override {
        putbs("disable label" + cvtToStr(nodep->labelp()->blockp()->labelNum()) + ";\n");
    }
    void visit(AstJumpLabel* nodep) override { putbs("// " + cvtToStr(nodep->blockp()) + ":\n"); }
    void visit(AstNodeReadWriteMem* nodep) override {
        putfs(nodep, nodep->verilogKwd());
        putbs("(");
        if (nodep->filenamep()) iterateAndNextConstNull(nodep->filenamep());
        putbs(", ");
        if (nodep->memp()) iterateAndNextConstNull(nodep->memp());
        if (nodep->lsbp()) {
            putbs(", ");
            iterateAndNextConstNull(nodep->lsbp());
        }
        if (nodep->msbp()) {
            putbs(", ");
            iterateAndNextConstNull(nodep->msbp());
        }
        puts(");\n");
    }
    void visit(AstSysFuncAsTask* nodep) override {
        iterateAndNextConstNull(nodep->lhsp());
        puts(";\n");
    }
    void visit(AstSysIgnore* nodep) override {
        putfs(nodep, nodep->verilogKwd());
        putbs("(");
        iterateAndNextConstNull(nodep->exprsp());
        puts(");\n");
    }
    void visit(AstNodeFor* nodep) override {
        putfs(nodep, "for (");
        {
            VL_RESTORER(m_suppressSemi);
            m_suppressSemi = true;
            iterateAndNextConstNull(nodep->initsp());
            puts(";");
            iterateAndNextConstNull(nodep->condp());
            puts(";");
            iterateAndNextConstNull(nodep->incsp());
        }
        puts(") begin\n");
        iterateAndNextConstNull(nodep->stmtsp());
        putqs(nodep, "end\n");
    }
    void visit(AstRepeat* nodep) override {
        putfs(nodep, "repeat (");
        iterateAndNextConstNull(nodep->countp());
        puts(") begin\n");
        iterateAndNextConstNull(nodep->stmtsp());
        putfs(nodep, "end\n");
    }
    void visit(AstWhile* nodep) override {
        iterateAndNextConstNull(nodep->precondsp());
        putfs(nodep, "while (");
        iterateAndNextConstNull(nodep->condp());
        puts(") begin\n");
        iterateAndNextConstNull(nodep->stmtsp());
        iterateAndNextConstNull(nodep->incsp());
        iterateAndNextConstNull(nodep->precondsp());  // Need to recompute before next loop
        putfs(nodep, "end\n");
    }
    void visit(AstNodeIf* nodep) override {
        putfs(nodep, "");
        if (const AstIf* const ifp = VN_CAST(nodep, If)) {
            if (ifp->priorityPragma()) puts("priority ");
            if (ifp->uniquePragma()) puts("unique ");
            if (ifp->unique0Pragma()) puts("unique0 ");
        }
        puts("if (");
        iterateAndNextConstNull(nodep->condp());
        puts(") begin\n");
        iterateAndNextConstNull(nodep->thensp());
        if (nodep->elsesp()) {
            putqs(nodep, "end\n");
            putqs(nodep, "else begin\n");
            iterateAndNextConstNull(nodep->elsesp());
        }
        putqs(nodep, "end\n");
    }
    void visit(AstPast* nodep) override {
        putfs(nodep, "$past(");
        iterateAndNextConstNull(nodep->exprp());
        if (nodep->ticksp()) {
            puts(", ");
            iterateAndNextConstNull(nodep->ticksp());
        }
        puts(")");
    }
    void visit(AstReturn* nodep) override {
        putfs(nodep, "return ");
        iterateAndNextConstNull(nodep->lhsp());
        puts(";\n");
    }
    void visit(AstStop* nodep) override { putfs(nodep, "$stop;\n"); }
    void visit(AstFinish* nodep) override { putfs(nodep, "$finish;\n"); }
    void visit(AstStmtExpr* nodep) override {
        iterateConst(nodep->exprp());
        puts(";\n");
    }
    void visit(AstNodeSimpleText* nodep) override {
        if (nodep->tracking() || m_trackText) {
            puts(nodep->text());
        } else {
            putsNoTracking(nodep->text());
        }
    }
    void visit(AstTextBlock* nodep) override {
        visit(static_cast<AstNodeSimpleText*>(nodep));
        {
            VL_RESTORER(m_suppressSemi);
            m_suppressVarSemi = nodep->commas();
            for (AstNode* childp = nodep->nodesp(); childp; childp = childp->nextp()) {
                iterateConst(childp);
                if (nodep->commas() && childp->nextp()) puts(", ");
            }
        }
    }
    void visit(AstScopeName* nodep) override {}
    void visit(AstCStmt* nodep) override {
        putfs(nodep, "$_CSTMT(");
        iterateAndNextConstNull(nodep->exprsp());
        puts(");\n");
    }
    void visit(AstCExpr* nodep) override {
        putfs(nodep, "$_CEXPR(");
        iterateAndNextConstNull(nodep->exprsp());
        puts(")");
    }
    void visit(AstUCStmt* nodep) override {
        putfs(nodep, "$c(");
        iterateAndNextConstNull(nodep->exprsp());
        puts(");\n");
    }
    void visit(AstUCFunc* nodep) override {
        putfs(nodep, "$c(");
        iterateAndNextConstNull(nodep->exprsp());
        puts(")");
    }
    void visit(AstExprStmt* nodep) override {
        putfs(nodep, "$_EXPRSTMT(\n");
        iterateAndNextConstNull(nodep->stmtsp());
        putbs(", ");
        puts(");\n");
    }

    void visit(AstCMethodHard* nodep) override {
        iterateConst(nodep->fromp());
        puts("." + nodep->name() + "(");
        for (AstNode* pinp = nodep->pinsp(); pinp; pinp = pinp->nextp()) {
            if (pinp != nodep->pinsp()) puts(", ");
            iterateConst(pinp);
        }
        puts(")");
    }
    void visit(AstCMethodCall* nodep) override {
        iterateConst(nodep->fromp());
        puts("." + nodep->name() + "(");
        for (AstNode* pinp = nodep->argsp(); pinp; pinp = pinp->nextp()) {
            if (pinp != nodep->argsp()) puts(", ");
            iterateConst(pinp);
        }
        puts(")");
    }

    // Operators
    virtual void emitVerilogFormat(AstNode* nodep, const string& format, AstNode* lhsp = nullptr,
                                   AstNode* const rhsp = nullptr, AstNode* thsp = nullptr,
                                   AstNode* fhsp = nullptr) {
        // Look at emitVerilog() format for term/uni/dual/triops,
        // and write out appropriate text.
        //      %f      Potential fileline-if-change and line break
        //      %l      lhsp - if appropriate
        //      %r      rhsp - if appropriate
        //      %t      thsp - if appropriate
        //      %o      fhsp - if appropriate
        //      %d      dtypep - if appropriate
        //      %k      Potential line break
        bool inPct = false;
        putbs("");
        for (const char c : format) {
            if (c == '%') {
                inPct = true;
            } else if (!inPct) {  // Normal text
                string s;
                s += c;
                puts(s);
            } else {  // Format character
                inPct = false;
                switch (c) {
                case '%': puts("%"); break;
                case 'f': putfs(nodep, ""); break;
                case 'k': putbs(""); break;
                case 'l': {
                    UASSERT_OBJ(lhsp, nodep, "emitVerilog() references undef node");
                    iterateAndNextConstNull(lhsp);
                    break;
                }
                case 'r': {
                    UASSERT_OBJ(rhsp, nodep, "emitVerilog() references undef node");
                    iterateAndNextConstNull(rhsp);
                    break;
                }
                case 't': {
                    UASSERT_OBJ(thsp, nodep, "emitVerilog() references undef node");
                    iterateAndNextConstNull(thsp);
                    break;
                }
                case 'o': {
                    UASSERT_OBJ(thsp, nodep, "emitVerilog() references undef node");
                    iterateAndNextConstNull(fhsp);
                    break;
                }
                case 'd': {
                    UASSERT_OBJ(nodep->dtypep(), nodep, "emitVerilog() references undef node");
                    iterateAndNextConstNull(nodep->dtypep());
                    break;
                }
                default: nodep->v3fatalSrc("Unknown emitVerilog format code: %" << c); break;
                }
            }
        }
    }

    void visit(AstNodeTermop* nodep) override { emitVerilogFormat(nodep, nodep->emitVerilog()); }
    void visit(AstNodeUniop* nodep) override {
        emitVerilogFormat(nodep, nodep->emitVerilog(), nodep->lhsp());
    }
    void visit(AstNodeBiop* nodep) override {
        emitVerilogFormat(nodep, nodep->emitVerilog(), nodep->lhsp(), nodep->rhsp());
    }
    void visit(AstNodeTriop* nodep) override {
        emitVerilogFormat(nodep, nodep->emitVerilog(), nodep->lhsp(), nodep->rhsp(),
                          nodep->thsp());
    }
    void visit(AstMemberSel* nodep) override {
        iterateConst(nodep->fromp());
        puts(".");
        puts(nodep->prettyName());
    }
    void visit(AstStructSel* nodep) override {
        iterateConst(nodep->fromp());
        puts(".");
        puts(nodep->prettyName());
    }
    void visit(AstAttrOf* nodep) override {
        putfs(nodep, "$_ATTROF(");
        iterateAndNextConstNull(nodep->fromp());
        if (nodep->dimp()) {
            putbs(", ");
            iterateAndNextConstNull(nodep->dimp());
        }
        puts(")");
    }
    void visit(AstInitArray* nodep) override {
        putfs(nodep, "'{");
        int comma = 0;
        const auto& mapr = nodep->map();
        for (const auto& itr : mapr) {
            if (comma++) putbs(", ");
            puts(cvtToStr(itr.first));
            puts(":");
            AstNode* const valuep = itr.second->valuep();
            iterateConst(valuep);
        }
        puts("}");
    }
    void visit(AstNodeCond* nodep) override {
        putbs("(");
        iterateAndNextConstNull(nodep->condp());
        putfs(nodep, " ? ");
        iterateAndNextConstNull(nodep->thenp());
        putbs(" : ");
        iterateAndNextConstNull(nodep->elsep());
        puts(")");
    }
    void visit(AstRange* nodep) override {
        puts("[");
        if (VN_IS(nodep->leftp(), Const) && VN_IS(nodep->rightp(), Const)) {
            // Looks nicer if we print [1:0] rather than [32'sh1:32sh0]
            puts(cvtToStr(nodep->leftConst()));
            puts(":");
            puts(cvtToStr(nodep->rightConst()));
            puts("]");
        } else {
            iterateAndNextConstNull(nodep->leftp());
            puts(":");
            iterateAndNextConstNull(nodep->rightp());
            puts("]");
        }
    }
    void visit(AstSel* nodep) override {
        iterateAndNextConstNull(nodep->fromp());
        puts("[");
        if (VN_IS(nodep->lsbp(), Const)) {
            if (nodep->widthp()->isOne()) {
                if (VN_IS(nodep->lsbp(), Const)) {
                    puts(cvtToStr(VN_AS(nodep->lsbp(), Const)->toSInt()));
                } else {
                    iterateAndNextConstNull(nodep->lsbp());
                }
            } else {
                puts(cvtToStr(VN_AS(nodep->lsbp(), Const)->toSInt()
                              + VN_AS(nodep->widthp(), Const)->toSInt() - 1));
                puts(":");
                puts(cvtToStr(VN_AS(nodep->lsbp(), Const)->toSInt()));
            }
        } else {
            iterateAndNextConstNull(nodep->lsbp());
            putfs(nodep, "+:");
            iterateAndNextConstNull(nodep->widthp());
            puts("]");
        }
        puts("]");
    }
    void visit(AstSliceSel* nodep) override {
        iterateAndNextConstNull(nodep->fromp());
        puts(cvtToStr(nodep->declRange()));
    }
    void visit(AstTypedef* nodep) override {
        putfs(nodep, "typedef ");
        iterateAndNextConstNull(nodep->dtypep());
        puts(" ");
        puts(nodep->prettyName());
        puts(";\n");
    }
    void visit(AstBasicDType* nodep) override {
        if (nodep->isSigned()) putfs(nodep, "signed ");
        putfs(nodep, nodep->prettyName());
        if (nodep->rangep()) {
            puts(" ");
            iterateAndNextConstNull(nodep->rangep());
            puts(" ");
        } else if (nodep->isRanged()) {
            puts(" [");
            puts(cvtToStr(nodep->hi()));
            puts(":");
            puts(cvtToStr(nodep->lo()));
            puts("] ");
        }
    }
    void visit(AstConstDType* nodep) override {
        putfs(nodep, "const ");
        iterateConst(nodep->subDTypep());
    }
    void visit(AstNodeArrayDType* nodep) override {
        iterateConst(nodep->subDTypep());
        iterateAndNextConstNull(nodep->rangep());
    }
    void visit(AstRefDType* nodep) override { iterateConst(nodep->skipRefp()); }
    void visit(AstNodeUOrStructDType* nodep) override {
        puts(nodep->verilogKwd() + " ");
        if (nodep->packed()) puts("packed ");
        puts("\n");
        puts("{");
        for (AstMemberDType* itemp = nodep->membersp(); itemp;
             itemp = VN_AS(itemp->nextp(), MemberDType)) {
            iterateConst(itemp);
            puts(";");
        }
        puts("}");
    }
    void visit(AstMemberDType* nodep) override {
        iterateConst(nodep->subDTypep());
        puts(" ");
        puts(nodep->name());
    }
    void visit(AstNodeFTaskRef* nodep) override {
        if (nodep->dotted() != "") {
            putfs(nodep, nodep->dotted());
            puts(".");
            puts(nodep->prettyName());
        } else {
            putfs(nodep, nodep->prettyName());
        }
        puts("(");
        iterateAndNextConstNull(nodep->pinsp());
        puts(")");
    }
    void visit(AstCCall* nodep) override {
        puts(nodep->funcp()->name());
        puts("(");
        iterateAndNextConstNull(nodep->argsp());
        puts(")");
    }
    void visit(AstArg* nodep) override { iterateAndNextConstNull(nodep->exprp()); }
    void visit(AstPrintTimeScale* nodep) override {
        puts(nodep->verilogKwd());
        puts(";\n");
    }

    // Terminals
    void visit(AstVarRef* nodep) override {
        if (nodep->varScopep()) {
            putfs(nodep, nodep->varScopep()->prettyName());
        } else {
            if (nodep->varp()) {
                if (nodep->selfPointer().isEmpty()) {
                    putfs(nodep, nodep->varp()->prettyName());
                } else {
                    putfs(nodep, nodep->selfPointer().asString());
                    putfs(nodep, "->");
                    puts(nodep->varp()->prettyName());
                }
            } else {
                putfs(nodep, nodep->name());
            }
        }
    }
    void visit(AstVarXRef* nodep) override {
        putfs(nodep, nodep->dotted());
        puts(".");
        if (nodep->varp()) {
            puts(nodep->varp()->prettyName());
        } else {
            puts(nodep->prettyName());
        }
    }
    void visit(AstConst* nodep) override { putfs(nodep, nodep->num().ascii(true, true)); }

    // Just iterate
    void visit(AstTopScope* nodep) override { iterateChildrenConst(nodep); }
    void visit(AstScope* nodep) override { iterateChildrenConst(nodep); }
    void visit(AstVar* nodep) override {
        if (nodep->isIO()) {
            putfs(nodep, nodep->verilogKwd());
            puts(" ");
        }
        std::vector<const AstUnpackArrayDType*> unpackps;
        for (AstNodeDType* dtypep = nodep->dtypep(); dtypep;) {
            dtypep = dtypep->skipRefp();
            if (const AstUnpackArrayDType* const unpackp = VN_CAST(dtypep, UnpackArrayDType)) {
                unpackps.push_back(unpackp);
                dtypep = unpackp->subDTypep();
            } else {
                iterateConst(dtypep);
                puts(" ");
                puts(nodep->prettyName());
                dtypep = nullptr;
            }
        }
        // If nodep is an unpacked array, append unpacked dimensions
        for (const auto& unpackp : unpackps) {
            puts("[");
            puts(cvtToStr(unpackp->rangep()->leftConst()));
            puts(":");
            puts(cvtToStr(unpackp->rangep()->rightConst()));
            puts("]");
        }
        puts(m_suppressVarSemi ? "\n" : ";\n");
    }
    void visit(AstActive* nodep) override {
        m_sensesp = nodep->sensesp();
        iterateAndNextConstNull(nodep->stmtsp());
        m_sensesp = nullptr;
    }
    void visit(AstParseRef* nodep) override { puts(nodep->prettyName()); }
    void visit(AstVarScope*) override {}
    void visit(AstNodeText*) override {}
    void visit(AstTraceDecl*) override {}
    void visit(AstTraceInc*) override {}
    // NOPs
    void visit(AstPragma*) override {}
    void visit(AstCell*) override {}  // Handled outside the Visit class
    // Default
    void visit(AstNode* nodep) override {
        puts("\n???? // "s + nodep->prettyTypeName() + "\n");
        iterateChildrenConst(nodep);
        // Not v3fatalSrc so we keep processing
        if (!m_suppressUnknown) {
            nodep->v3error(
                "Internal: Unknown node type reached emitter: " << nodep->prettyTypeName());
        }
    }

public:
    bool m_suppressVarSemi = false;  // Suppress emitting semicolon for AstVars
    explicit EmitVBaseVisitorConst(bool suppressUnknown, AstSenTree* domainp)
        : m_suppressUnknown{suppressUnknown}
        , m_sensesp{domainp} {}
    ~EmitVBaseVisitorConst() override = default;
};

//######################################################################
// Emit to an output file

class EmitVFileVisitor final : public EmitVBaseVisitorConst {
    // METHODS
    void puts(const string& str) override { ofp()->puts(str); }
    void putbs(const string& str) override { ofp()->putbs(str); }
    void putfs(AstNode*, const string& str) override { putbs(str); }
    void putqs(AstNode*, const string& str) override { putbs(str); }
    void putsNoTracking(const string& str) override { ofp()->putsNoTracking(str); }

public:
    EmitVFileVisitor(AstNode* nodep, V3OutVFile* ofp, bool trackText, bool suppressUnknown)
        : EmitVBaseVisitorConst{suppressUnknown, nullptr} {
        m_ofp = ofp;
        m_trackText = trackText;
        iterateConst(nodep);
    }
    ~EmitVFileVisitor() override = default;
};

//######################################################################
// Emit to a stream (perhaps stringstream)

class EmitVStreamVisitor final : public EmitVBaseVisitorConst {
    // MEMBERS
    std::ostream& m_os;
    // METHODS
    void putsNoTracking(const string& str) override { m_os << str; }
    void puts(const string& str) override { putsNoTracking(str); }
    void putbs(const string& str) override { puts(str); }
    void putfs(AstNode*, const string& str) override { putbs(str); }
    void putqs(AstNode*, const string& str) override { putbs(str); }

public:
    EmitVStreamVisitor(const AstNode* nodep, std::ostream& os)
        : EmitVBaseVisitorConst{false, nullptr}
        , m_os(os) {  // Need () or GCC 4.8 false warning
        iterateConst(const_cast<AstNode*>(nodep));
    }
    ~EmitVStreamVisitor() override = default;
};

//######################################################################
// EmitV class functions

void V3EmitV::verilogForTree(const AstNode* nodep, std::ostream& os) {
    { EmitVStreamVisitor{nodep, os}; }
}

void V3EmitV::emitvFiles() {
    UINFO(2, __FUNCTION__ << ": " << endl);
    for (AstNodeFile* filep = v3Global.rootp()->filesp(); filep;
         filep = VN_AS(filep->nextp(), NodeFile)) {
        AstVFile* const vfilep = VN_CAST(filep, VFile);
        if (vfilep && vfilep->tblockp()) {
            V3OutVFile of{vfilep->name()};
            of.puts("// DESCR"
                    "IPTION: Verilator generated Verilog\n");
            { EmitVFileVisitor{vfilep->tblockp(), &of, true, false}; }
        }
    }
}

void V3EmitV::debugEmitV(const string& filename) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    V3OutVFile of{filename};
    { EmitVFileVisitor{v3Global.rootp(), &of, true, true}; }
}
