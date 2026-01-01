// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Emit Verilog from tree
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2004-2026 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "V3PchAstMT.h"

#include "V3EmitV.h"

#include "V3EmitCBase.h"

#include <unordered_map>
#include <vector>

VL_DEFINE_DEBUG_FUNCTIONS;

// ######################################################################
//  Emit statements and expressions

class EmitVBaseVisitorConst VL_NOT_FINAL : public VNVisitorConst {
    // STATE - across all visitors
    const bool m_suppressUnknown;  // Do not error on unknown node

    // STATE - for current visit position (use VL_RESTORER)
    AstSenTree* m_sentreep = nullptr;  // Domain for printing one a ALWAYS under a ACTIVE
    bool m_suppressSemi = false;  // Non-statement, don't print ;
    bool m_suppressVarSemi = false;  // Suppress emitting semicolon for AstVars
    bool m_suppressSampled = false;  // Suppress emitting sampled in assertion properties
    bool m_arrayPost = false;  // Print array information that goes after identifier (vs after)
    bool m_prefixed = true;  // Whether constants need to be prefixed
    std::deque<AstNodeArrayDType*> m_packedps;  // Packed arrays to print with BasicDType
    std::unordered_map<AstJumpBlock*, size_t> m_labelNumbers;  // Label numbers for JumpBlocks

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

    void iterateAndCommaConstNull(AstNode* nodep) {
        for (; nodep; nodep = nodep->nextp()) {
            iterateConst(nodep);
            if (nodep->nextp()) puts(", ");
        }
    }
    void emitPacked() {
        for (AstNodeArrayDType* packedp : m_packedps) {
            puts(" ");
            iterateConstNull(packedp->rangep());
        }
        m_packedps.clear();
    }
    void emitNodesWithText(AstNode* nodesp, bool tracking, const std::string& separator) {
        for (AstNode* nodep = nodesp; nodep; nodep = nodep->nextp()) {
            if (const AstText* const textp = VN_CAST(nodep, Text)) {
                if (tracking) {
                    puts(textp->text());
                } else {
                    putsNoTracking(textp->text());
                }
            } else {
                iterateConst(nodep);
            }
            if (nodep->nextp()) puts(separator);
        }
    }

    // VISITORS
    void visit(AstNetlist* nodep) override { iterateAndNextConstNull(nodep->modulesp()); }
    void visit(AstNodeModule* nodep) override {
        putfs(nodep, nodep->verilogKwd() + " " + EmitCUtil::prefixNameProtect(nodep) + ";\n");
        iterateChildrenConst(nodep);
        putqs(nodep, "end" + nodep->verilogKwd() + "\n");
    }
    void visit(AstPort* nodep) override {}
    void visit(AstNodeFTask* nodep) override {
        putfs(nodep, nodep->verilogKwd());
        puts(" ");
        puts(nodep->prettyName());
        puts(";\n");
        // Only putfs the first time for each visitor; later for same node is putqs
        iterateAndNextConstNull(nodep->stmtsp());
        putqs(nodep, "end" + nodep->verilogKwd() + "\n");
    }

    void visit(AstGenBlock* nodep) override {
        const std::string name = nodep->name().empty() ? "" : " : " + nodep->name();
        putbs("/* generate */ begin" + name + '\n');
        iterateChildrenConst(nodep);
        puts("end" + name + '\n');
    }
    void visit(AstGenCase* nodep) override {
        putfs(nodep, "/* generate */ case (");
        iterateAndNextConstNull(nodep->exprp());
        puts(")\n");
        iterateAndNextConstNull(nodep->itemsp());
        putqs(nodep, "endcase\n");
    }
    void visit(AstGenCaseItem* nodep) override {
        if (nodep->condsp()) {
            iterateAndNextConstNull(nodep->condsp());
        } else {
            putbs("default");
        }
        iterateAndNextConstNull(nodep->itemsp());
    }
    void visit(AstGenFor* nodep) override {
        putfs(nodep, "/* generate */ for (");
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
        iterateAndNextConstNull(nodep->itemsp());
        putqs(nodep, "end\n");
    }
    void visit(AstGenIf* nodep) override {
        putfs(nodep, "");
        puts("/* generate */ if (");
        iterateAndNextConstNull(nodep->condp());
        puts(") begin\n");
        iterateAndNextConstNull(nodep->thensp());
        if (nodep->elsesp()) {
            putqs(nodep, "end else begin\n");
            iterateAndNextConstNull(nodep->elsesp());
        }
        putqs(nodep, "end\n");
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
        if (const AstAssignW* const ap = VN_CAST(nodep->stmtsp(), AssignW)) {
            if (!ap->nextp()) {
                putfs(nodep, "assign ");
                if (AstNode* const tcp = ap->timingControlp()) {
                    iterateAndNextConstNull(tcp);
                    putbs(" ");
                }
                iterateAndNextConstNull(ap->lhsp());
                putbs(" = ");
                iterateAndNextConstNull(ap->rhsp());
                if (!m_suppressSemi) puts(";\n");
                return;
            }
        }
        putfs(nodep, "always ");
        if (m_sentreep) {
            iterateAndNextConstNull(m_sentreep);
        }  // In active
        else {
            iterateAndNextConstNull(nodep->sentreep());
        }
        putbs(" begin\n");
        iterateAndNextConstNull(nodep->stmtsp());
        putqs(nodep, "end\n");
    }
    void visit(AstAlwaysPre* nodep) override {
        putfs(nodep, "always /* PRE */ begin\n");
        iterateAndNextConstNull(nodep->stmtsp());
        putqs(nodep, "end\n");
    }
    void visit(AstAlwaysPost* nodep) override {
        putfs(nodep, "always /* POST */ begin\n");
        iterateAndNextConstNull(nodep->stmtsp());
        putqs(nodep, "end\n");
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
    void visit(AstAlias* nodep) override {
        putbs("alias ");
        iterateConst(nodep->itemsp());
        for (AstNode* itemp = nodep->itemsp()->nextp(); itemp; itemp = itemp->nextp()) {
            putfs(nodep, " = ");
            iterateConst(itemp);
        }
        if (!m_suppressSemi) puts(";\n");
    }
    void visit(AstAssignW* nodep) override {
        putfs(nodep, "continuous assign ");
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
        if (nodep->edgeType() != VEdgeType::ET_CHANGED) puts(nodep->edgeType().verilogKwd());
        if (nodep->sensp()) puts(" ");
        iterateChildrenConst(nodep);
    }
    void visit(AstCase* nodep) override {
        putfs(nodep, "");
        if (nodep->priorityPragma()) puts("priority ");
        if (nodep->uniquePragma()) puts("unique ");
        if (nodep->unique0Pragma()) puts("unique0 ");
        puts(nodep->verilogKwd());
        puts(" (");
        iterateAndNextConstNull(nodep->exprp());
        puts(")\n");
        if (nodep->fullPragma() || nodep->parallelPragma()) {
            puts(" // synopsys");
            if (nodep->fullPragma()) puts(" full_case");
            if (nodep->parallelPragma()) puts(" parallel_case");
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
    void visit(AstNodeCoverDecl*) override {}  // N/A
    void visit(AstCoverInc*) override {}  // N/A
    void visit(AstCoverToggle*) override {}  // N/A

    void visit(AstCvtPackString* nodep) override {
        putfs(nodep, "");
        if (AstConst* const lhsConstp = VN_CAST(nodep->lhsp(), Const)) {
            putsQuoted(lhsConstp->num().toString());
        } else {
            puts("string'(");
            iterateAndNextConstNull(nodep->lhsp());
            puts(")");
        }
    }
    void visit(AstTestPlusArgs* nodep) override {
        putfs(nodep, nodep->verilogKwd());
        putbs("(");
        iterateChildrenConst(nodep);
        puts(")");
    }
    void visit(AstValuePlusArgs* nodep) override {
        putfs(nodep, nodep->verilogKwd());
        putbs("(");
        iterateConstNull(nodep->searchp());
        putbs(", ");
        iterateConstNull(nodep->outp());
        puts(")");
    }
    void visitNodeDisplay(AstNode* nodep, AstNode* fileOrStrgp, const string& text,
                          AstNode* exprsp) {
        putfs(nodep, nodep->verilogKwd());
        putbs("(");
        if (fileOrStrgp) {
            iterateConstNull(fileOrStrgp);
            putbs(", ");
        }
        putsQuoted(text);
        for (AstNode* expp = exprsp; expp; expp = expp->nextp()) {
            puts(", ");
            iterateConstNull(expp);
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
    void visit(AstToStringN* nodep) override { iterateConst(nodep->lhsp()); }
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
        // Allocate label number
        const size_t n = m_labelNumbers.size();
        const bool newEntry = m_labelNumbers.emplace(nodep, n).second;
        UASSERT_OBJ(newEntry, nodep, "AstJumpBlock visited twide");
        // Emit
        putbs("begin : label" + std::to_string(n) + "\n");
        iterateAndNextConstNull(nodep->stmtsp());
        puts("end\n");
    }
    void visit(AstJumpGo* nodep) override {
        // Retrieve target label number - Sometimes EmitV is used by debug code,
        // so allow printing with an unknown target
        const auto it = m_labelNumbers.find(nodep->blockp());
        const std::string label
            = it != m_labelNumbers.end() ? "label" + std::to_string(it->second) : "<UNKNOWN>";
        putbs("disable " + label + ";\n");
    }
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
    void visit(AstSysIgnore* nodep) override {
        putfs(nodep, nodep->verilogKwd());
        putbs("(");
        iterateAndNextConstNull(nodep->exprsp());
        puts(");\n");
    }
    void visit(AstRepeat* nodep) override {
        putfs(nodep, "repeat (");
        iterateAndNextConstNull(nodep->countp());
        puts(") begin\n");
        iterateAndNextConstNull(nodep->stmtsp());
        putfs(nodep, "end\n");
    }
    void visit(AstLoop* nodep) override {
        // Special case when the AstLoopTest is first for output readability
        if (AstLoopTest* const testp = VN_CAST(nodep->stmtsp(), LoopTest)) {
            putfs(nodep, "while (");
            iterateConst(testp->condp());
            puts(") begin\n");
            iterateAndNextConstNull(testp->nextp());
            puts("end\n");
            return;
        }
        // Special case when the AstLoopTest is last for output readability
        if (AstNode* lastp = nodep->stmtsp()) {
            while (AstNode* const nextp = lastp->nextp()) lastp = nextp;
            if (AstLoopTest* const testp = VN_CAST(lastp, LoopTest)) {
                putfs(nodep, "do begin\n");
                for (AstNode* p = nodep->stmtsp(); p != lastp; p = p->nextp()) iterateConst(p);
                puts("end while (");
                iterateConst(testp->condp());
                puts(")\n");
                return;
            }
        }
        // Generic case
        putfs(nodep, "while (true) begin\n");
        iterateAndNextConstNull(nodep->stmtsp());
        iterateAndNextConstNull(nodep->contsp());
        putfs(nodep, "end\n");
    }
    void visit(AstLoopTest* nodep) override {
        putfs(nodep, "if (!(");
        iterateAndNextConstNull(nodep->condp());
        puts(")) break;\n");
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
        if (nodep->ticksp() || nodep->sentreep()) {
            puts(", ");
            iterateAndNextConstNull(nodep->ticksp());
            if (nodep->sentreep()) {
                puts(", ");
                iterateAndNextConstNull(nodep->sentreep());
            }
        }
        puts(")");
    }
    void visit(AstSampled* nodep) override {
        if (!m_suppressSampled) {
            putfs(nodep, "$sampled(");
            iterateAndNextConstNull(nodep->exprp());
            puts(")");
        }
    }
    void visit(AstRising* nodep) override {
        putfs(nodep, "$rising(");
        iterateAndNextConstNull(nodep->exprp());
        puts(")");
    }
    void visit(AstRose* nodep) override {
        putfs(nodep, "$rose(");
        iterateAndNextConstNull(nodep->exprp());
        if (nodep->sentreep()) {
            puts(", ");
            iterateAndNextConstNull(nodep->sentreep());
        }
        puts(")");
    }
    void visit(AstFell* nodep) override {
        putfs(nodep, "$fell(");
        iterateAndNextConstNull(nodep->exprp());
        if (nodep->sentreep()) {
            puts(", ");
            iterateAndNextConstNull(nodep->sentreep());
        }
        puts(")");
    }
    void visit(AstFalling* nodep) override {
        putfs(nodep, "$falling(");
        iterateAndNextConstNull(nodep->exprp());
        puts(")");
    }
    void visit(AstFuture* nodep) override {
        putfs(nodep, "$future(");
        iterateAndNextConstNull(nodep->exprp());
        puts(")");
    }
    void visit(AstStable* nodep) override {
        putfs(nodep, "$stable(");
        iterateAndNextConstNull(nodep->exprp());
        if (nodep->sentreep()) {
            puts(", ");
            iterateAndNextConstNull(nodep->sentreep());
        }
        puts(")");
    }
    void visit(AstSteady* nodep) override {
        putfs(nodep, "$steady(");
        iterateAndNextConstNull(nodep->exprp());
        puts(")");
    }
    void visit(AstReturn* nodep) override {
        putfs(nodep, "return ");
        iterateAndNextConstNull(nodep->lhsp());
        puts(";\n");
    }
    void visit(AstStop* nodep) override {
        emitVerilogFormat(nodep, nodep->emitVerilog());
        puts(";\n");
    }
    void visit(AstFinish* nodep) override { putfs(nodep, "$finish;\n"); }
    void visit(AstFinishFork* nodep) override { putfs(nodep, "$finish;\n"); }
    void visit(AstStmtExpr* nodep) override {
        iterateConst(nodep->exprp());
        puts(";\n");
    }

    // Nodes involing AstText
    void visit(AstText* nodep) override {
        // All Text should be under TextBlock/CStmt/CStmtUser/CExpr/CExprUser
        nodep->v3fatalSrc("Text node in unexpected position");
    }
    void visit(AstTextBlock* nodep) override {
        VL_RESTORER(m_suppressVarSemi);
        m_suppressVarSemi = !nodep->separator().empty();
        puts(nodep->prefix());
        emitNodesWithText(nodep->nodesp(), true, nodep->separator());
        puts(nodep->suffix());
    }
    void visit(AstCStmt* nodep) override {
        putfs(nodep, "$_CSTMT(");
        emitNodesWithText(nodep->nodesp(), true, "");
        puts(");\n");
    }
    void visit(AstCExpr* nodep) override {
        putfs(nodep, "$_CEXPR(");
        emitNodesWithText(nodep->nodesp(), true, "");
        puts(")");
    }
    void visit(AstCStmtUser* nodep) override {
        putfs(nodep, "$c(");
        emitNodesWithText(nodep->nodesp(), false, "");
        puts(");\n");
    }
    void visit(AstCExprUser* nodep) override {
        putfs(nodep, "$c(");
        emitNodesWithText(nodep->nodesp(), false, "");
        puts(")");
    }

    void visit(AstScopeName* nodep) override {}
    void visit(AstExprStmt* nodep) override {
        putfs(nodep, "$_EXPRSTMT(\n");
        iterateAndNextConstNull(nodep->stmtsp());
        putbs(", ");
        puts(");\n");
    }

    void visit(AstCMethodHard* nodep) override {
        iterateConst(nodep->fromp());
        puts("." + nodep->name() + "(");
        iterateAndCommaConstNull(nodep->pinsp());
        puts(")");
    }
    void visit(AstCMethodCall* nodep) override {
        iterateConst(nodep->fromp());
        puts("." + nodep->name() + "(");
        iterateAndCommaConstNull(nodep->argsp());
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
            if (!inPct && c == '%') {
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
    void visit(AstNodeQuadop* nodep) override {
        emitVerilogFormat(nodep, nodep->emitVerilog(), nodep->lhsp(), nodep->rhsp(), nodep->thsp(),
                          nodep->fhsp());
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
    void visit(AstCond* nodep) override {
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
        } else {
            iterateAndNextConstNull(nodep->leftp());
            puts(":");
            iterateAndNextConstNull(nodep->rightp());
        }
        puts("]");
    }
    void visit(AstRand* nodep) override {
        emitVerilogFormat(nodep, nodep->emitVerilog(), nodep->seedp());
    }
    void visit(AstSel* nodep) override {
        iterateAndNextConstNull(nodep->fromp());
        int offset = 0;
        AstNodeDType* const dtypep = nodep->fromp()->dtypep();
        if (VN_IS(dtypep, BasicDType)) {
            AstBasicDType* const basicDtypep = VN_AS(dtypep, BasicDType);
            offset = basicDtypep->lo();
        }
        puts("[");
        if (VN_IS(nodep->lsbp(), Const)) {
            if (nodep->widthConst() == 1) {
                puts(cvtToStr(VN_AS(nodep->lsbp(), Const)->toSInt() + offset));
            } else {
                puts(cvtToStr(VN_AS(nodep->lsbp(), Const)->toSInt() + nodep->widthConst() + offset
                              - 1));
                puts(":");
                puts(cvtToStr(VN_AS(nodep->lsbp(), Const)->toSInt() + offset));
            }
        } else {
            iterateAndNextConstNull(nodep->lsbp());
            if (offset != 0) {
                puts(" + ");
                puts(cvtToStr(offset));
            }
            putfs(nodep, "+:");
            puts(cvtToStr(nodep->widthConst()));
        }
        puts("]");
    }
    void visit(AstSliceSel* nodep) override {
        iterateAndNextConstNull(nodep->fromp());
        puts(cvtToStr(nodep->declRange()));
    }
    void visit(AstThisRef* nodep) override { puts("this"); }
    void visit(AstTypedef* nodep) override {
        putfs(nodep, "typedef ");
        iterateConstNull(nodep->subDTypep());
        puts(" ");
        puts(nodep->prettyName());
        puts(";\n");
    }
    void visit(AstNodeCoverOrAssert* nodep) override {
        putfs(nodep, nodep->verilogKwd() + " ");
        if (nodep->type() == VAssertType::OBSERVED_DEFERRED_IMMEDIATE) {
            puts("#0 ");
        } else if (nodep->type() == VAssertType::FINAL_DEFERRED_IMMEDIATE) {
            puts("final ");
        } else if (nodep->type() == VAssertType::CONCURRENT) {
            puts("property ");
        }
        iterateConstNull(nodep->sentreep());
        puts("(");
        if (AstSampled* const sampledp = VN_CAST(nodep->propp(), Sampled)) {
            iterateAndNextConstNull(sampledp->exprp());
        } else {
            iterateAndNextConstNull(nodep->propp());
        }
        if (!VN_IS(nodep, Restrict)) {
            puts(") begin\n");
            iterateAndNextConstNull(nodep->passsp());
            puts("end\n");
        } else {
            puts(");\n");
        }

        if (const AstAssert* const assertp = VN_CAST(nodep, Assert)) {
            puts("else begin\n");
            iterateAndNextConstNull(assertp->failsp());
            puts("end\n");
        } else if (const AstAssertIntrinsic* const assertp = VN_CAST(nodep, AssertIntrinsic)) {
            puts("else begin\n");
            iterateAndNextConstNull(assertp->failsp());
            puts("end\n");
        }
    }
    void visit(AstAssocArrayDType* nodep) override {
        if (!m_arrayPost) {
            iterateConst(nodep->subDTypep());
        } else {
            VL_RESTORER(m_arrayPost);
            m_arrayPost = false;
            puts("[");
            iterateConst(nodep->keyDTypep());
            puts("]");
            m_arrayPost = true;
            iterateConst(nodep->subDTypep());  // For post's key
        }
    }
    void visit(AstBasicDType* nodep) override {
        if (m_arrayPost) return;
        putfs(nodep, nodep->prettyName());
        if (nodep->isSigned() && !nodep->keyword().isDouble()) putfs(nodep, " signed");
        // Do not emit ranges for integer atoms.
        if (nodep->keyword().isIntNumeric() && !nodep->keyword().isBitLogic()) return;
        emitPacked();
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
        if (m_arrayPost) return;
        putfs(nodep, "const ");
        iterateConst(nodep->subDTypep());
    }
    void visit(AstDynArrayDType* nodep) override {
        if (!m_arrayPost) {
            iterateConst(nodep->subDTypep());
        } else {
            puts("[]");
            iterateConst(nodep->subDTypep());  // For post's key
        }
    }
    void visit(AstEnumDType* nodep) override {
        if (m_arrayPost) return;
        putfs(nodep, "enum ");
        iterateConst(nodep->subDTypep());
        puts("{\n");
        iterateAndNextConstNull(nodep->itemsp());
        puts("}");
    }
    void visit(AstEnumItemRef* nodep) override {
        if (AstNodeModule* const classOrPackagep = nodep->classOrPackagep()) {
            putfs(nodep, classOrPackagep->prettyName());
            puts("::");
        }
        putfs(nodep, nodep->name());
    }
    void visit(AstEnumItem* nodep) override {
        putfs(nodep, nodep->name());
        iterateConstNull(nodep->rangep());
        puts(" = ");
        iterateConstNull(nodep->valuep());
        if (nodep->nextp()) puts(",");
        puts("\n");
    }
    void visit(AstNodeArrayDType* nodep) override {
        if (!m_arrayPost) {
            if (VN_IS(nodep, PackArrayDType)) {
                // Unpacked ranges handled in BasicDType, as they print "backwards"
                m_packedps.push_back(nodep);
            }
            iterateConst(nodep->subDTypep());
        } else {
            if (VN_IS(nodep, UnpackArrayDType)) {
                VL_RESTORER(m_arrayPost);
                m_arrayPost = false;
                iterateAndNextConstNull(nodep->rangep());
                m_arrayPost = true;
            }
            iterateConst(nodep->subDTypep());  // For post's key
        }
    }
    void visit(AstIfaceRefDType* nodep) override {
        if (m_arrayPost) {
            puts(" (");
            if (nodep->cellp()) {
                iterateConst(nodep->cellp());
            } else {
                puts("????");
            }
            puts(")");
            return;
        }
        puts(nodep->ifaceName());
    }
    void visit(AstRefDType* nodep) override {
        if (nodep->subDTypep()) {
            iterateConst(nodep->skipRefp());
        } else {
            puts("\n???? // "s + nodep->prettyTypeName() + " -> UNLINKED\n");
        }
    }
    void visit(AstRequireDType* nodep) override { iterateConst(nodep->lhsp()); }
    void visit(AstModport* nodep) override {
        puts(nodep->verilogKwd());
        puts(" ");
        puts(nodep->prettyName());
        puts(" (\n");
        if (nodep->varsp()) {
            iterateConst(nodep->varsp());
        } else {
            puts("????");
        }
        puts(");\n");
    }
    void visit(AstModportVarRef* nodep) override {
        puts(nodep->direction().verilogKwd());
        puts(" ");
        if (nodep->varp()) {
            VL_RESTORER(m_suppressVarSemi);
            m_suppressVarSemi = true;
            iterateConst(nodep->varp());
        } else {
            puts(nodep->prettyName());
        }
        if (nodep->nextp()) puts(", ");
    }
    void visit(AstNodeUOrStructDType* nodep) override {
        if (m_arrayPost) return;
        puts(nodep->verilogKwd() + " ");
        if (nodep->packed()) puts("packed ");
        {
            puts("{\n");
            VL_RESTORER(m_packedps);
            m_packedps.clear();
            for (AstMemberDType* itemp = nodep->membersp(); itemp;
                 itemp = VN_AS(itemp->nextp(), MemberDType)) {
                iterateConst(itemp);
            }
            puts("}");
        }
        emitPacked();
    }
    void visit(AstMemberDType* nodep) override {
        if (m_arrayPost) return;
        iterateConst(nodep->subDTypep());
        puts(" ");
        puts(nodep->name());
        puts(";\n");
    }
    void visit(AstQueueDType* nodep) override {
        if (!m_arrayPost) {
            iterateConst(nodep->subDTypep());
        } else {
            VL_RESTORER(m_arrayPost);
            m_arrayPost = false;
            puts("[$");
            if (nodep->boundp()) {
                puts(":");
                iterateConst(nodep->boundp());
            }
            puts("]");
            m_arrayPost = true;
            iterateConst(nodep->subDTypep());  // For post's key
        }
    }
    void visit(AstNodeFTaskRef* nodep) override {
        if (nodep->dotted() != "") {
            putfs(nodep, nodep->dotted());
            puts(".");
            puts(nodep->prettyName());
        } else {
            putfs(nodep, nodep->prettyName());
        }
        if (!VN_IS(nodep->taskp(), Property)) {
            puts("(");
            iterateAndNextConstNull(nodep->pinsp());
            puts(")");
        }
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
    void visit(AstPropSpec* nodep) override {
        if (!VN_IS(nodep->propp(), FuncRef)) {
            // Same dumping as in AstSenTree
            putfs(nodep, "@(");
            for (AstNode* expp = nodep->sensesp(); expp; expp = expp->nextp()) {
                iterateConst(expp);
                if (expp->nextp()) putqs(expp->nextp(), " or ");
            }
            puts(")");
        }
        if (nodep->disablep()) {
            puts(" disable iff ");
            iterateConst(nodep->disablep());
        }

        puts(" ");
        iterateConstNull(nodep->propp());
        puts("\n");
    }
    void visit(AstPExpr* nodep) override { iterateConst(nodep->bodyp()); }
    void visit(AstSExpr* nodep) override {
        iterateConstNull(nodep->preExprp());
        {
            VL_RESTORER(m_suppressSemi);
            m_suppressSemi = true;
            iterateConst(nodep->delayp());
        }
        iterateConst(nodep->exprp());
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
        putfs(nodep, nodep->prettyName(nodep->dotted()));
        puts(".");
        if (nodep->varp()) {
            puts(nodep->varp()->prettyName());
        } else {
            puts(nodep->prettyName());
        }
    }
    void visit(AstConst* nodep) override { putfs(nodep, nodep->num().ascii(m_prefixed, true)); }

    // Just iterate
    void visit(AstTopScope* nodep) override { iterateChildrenConst(nodep); }
    void visit(AstScope* nodep) override { iterateChildrenConst(nodep); }
    void visit(AstVar* nodep) override {
        if (nodep->isIO()) {
            putfs(nodep, nodep->verilogKwd());
            puts(" ");
        }
        VL_RESTORER(m_arrayPost);
        m_arrayPost = false;
        iterateConstNull(nodep->dtypep());  // Dtype part before identifier
        puts(" ");
        puts(nodep->prettyName());
        m_arrayPost = true;
        iterateConstNull(nodep->dtypep());  // Dtype part after identifier
        puts(m_suppressVarSemi ? "\n" : ";\n");
    }
    void visit(AstActive* nodep) override {
        VL_RESTORER(m_sentreep);
        m_sentreep = nodep->sentreep();
        iterateAndNextConstNull(nodep->stmtsp());
    }
    void visit(AstDelay* nodep) override {
        puts("");  // this is for proper alignment
        if (nodep->isCycleDelay()) {
            puts("##");
        } else {
            puts("#");
        }
        VL_RESTORER(m_prefixed);
        m_prefixed = false;
        iterateConst(nodep->lhsp());
        if (!m_suppressSemi) {
            puts(";\n");
        } else {
            puts(" ");
        }
        iterateAndNextConstNull(nodep->stmtsp());
    }
    void visit(AstCAwait* nodep) override {
        AstCMethodHard* methodp = VN_CAST(nodep->exprp(), CMethodHard);
        UASSERT_OBJ(methodp, nodep, "AstCAwait expression must be an AstCMethodHard");
        puts("");  // this is for proper alignment
        puts("#");
        iterateConst(methodp->pinsp());
    }
    void visit(AstParseRef* nodep) override { puts(nodep->prettyName()); }
    void visit(AstVarScope*) override {}
    void visit(AstTraceDecl*) override {}
    void visit(AstTraceInc*) override {}
    // NOPs
    void visit(AstPragma*) override {}
    void visit(AstStmtPragma*) override {}
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
    explicit EmitVBaseVisitorConst(bool suppressUnknown)
        : m_suppressUnknown{suppressUnknown} {}
    ~EmitVBaseVisitorConst() override = default;
};

//######################################################################
// Emit to an output file

class EmitVFileVisitor final : public EmitVBaseVisitorConst {
    // STATE
    V3OutVFile& m_of;  // The output file
    // METHODS
    void putsNoTracking(const string& str) override { m_of.putsNoTracking(str); }
    void puts(const string& str) override { m_of.puts(str); }
    void putbs(const string& str) override { m_of.putbs(str); }
    void putfs(AstNode*, const string& str) override { putbs(str); }
    void putqs(AstNode*, const string& str) override { putbs(str); }

public:
    EmitVFileVisitor(AstNode* nodep, V3OutVFile& of, bool suppressUnknown)
        : EmitVBaseVisitorConst{suppressUnknown}
        , m_of{of} {
        iterateConst(nodep);
    }
    ~EmitVFileVisitor() override = default;
};

//######################################################################
// Emit to a stream (perhaps stringstream)

class EmitVStreamVisitor final : public EmitVBaseVisitorConst {
    // STATE
    V3OutStream m_os;  // The output stream formatter
    const bool m_tracking;  // Use line tracking
    // METHODS
    void putsNoTracking(const string& str) override { m_os.putsNoTracking(str); }
    void puts(const string& str) override {
        m_tracking ? m_os.puts(str) : m_os.putsNoTracking(str);
    }
    void putbs(const string& str) override {
        m_tracking ? m_os.putbs(str) : m_os.putsNoTracking(str);
    }
    void putfs(AstNode*, const string& str) override { putbs(str); }
    void putqs(AstNode*, const string& str) override { putbs(str); }

public:
    EmitVStreamVisitor(const AstNode* nodep, std::ostream& os, bool tracking, bool suppressUnknown)
        : EmitVBaseVisitorConst{suppressUnknown}
        , m_os{os, V3OutFormatter::LA_VERILOG}
        , m_tracking{tracking} {
        iterateConst(const_cast<AstNode*>(nodep));
    }
    ~EmitVStreamVisitor() override = default;
};

//######################################################################
// EmitV class functions

void V3EmitV::verilogForTree(const AstNode* nodep, std::ostream& os) {
    { EmitVStreamVisitor{nodep, os, /* tracking: */ false, false}; }
}

void V3EmitV::debugVerilogForTree(const AstNode* nodep, std::ostream& os) {
    { EmitVStreamVisitor{nodep, os, /* tracking: */ true, true}; }
}

void V3EmitV::emitvFiles() {
    UINFO(2, __FUNCTION__ << ":");
    for (AstNodeFile* filep = v3Global.rootp()->filesp(); filep;
         filep = VN_AS(filep->nextp(), NodeFile)) {
        AstVFile* const vfilep = VN_CAST(filep, VFile);
        if (vfilep && vfilep->tblockp()) {
            V3OutVFile of{vfilep->name()};
            of.puts("// DESCRIPTION: Verilator generated Verilog\n");
            EmitVFileVisitor{vfilep->tblockp(), of, false};
        }
    }
}

void V3EmitV::debugEmitV(const string& filename) {
    UINFO(2, __FUNCTION__ << ":");
    V3OutVFile of{filename};
    EmitVFileVisitor{v3Global.rootp(), of, true};
}
