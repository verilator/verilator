// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Emit Verilog from tree
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2004-2021 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3Global.h"
#include "V3EmitV.h"
#include "V3EmitCBase.h"

#include <algorithm>
#include <map>
#include <vector>

//######################################################################
// Emit statements and math operators

class EmitVBaseVisitor VL_NOT_FINAL : public EmitCBaseVisitor {
    // MEMBERS
    bool m_suppressSemi = false;
    bool m_suppressUnknown = false;
    AstSenTree* m_sensesp;  // Domain for printing one a ALWAYS under a ACTIVE

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

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
    virtual void visit(AstNetlist* nodep) override { iterateAndNextNull(nodep->modulesp()); }
    virtual void visit(AstNodeModule* nodep) override {
        putfs(nodep, nodep->verilogKwd() + " " + prefixNameProtect(nodep) + ";\n");
        iterateChildren(nodep);
        putqs(nodep, "end" + nodep->verilogKwd() + "\n");
    }
    virtual void visit(AstPort* nodep) override {}
    virtual void visit(AstNodeFTask* nodep) override {
        putfs(nodep, nodep->isFunction() ? "function" : "task");
        puts(" ");
        puts(nodep->prettyName());
        puts(";\n");
        // Only putfs the first time for each visitor; later for same node is putqs
        putqs(nodep, "begin\n");
        iterateAndNextNull(nodep->stmtsp());
        putqs(nodep, "end\n");
    }

    virtual void visit(AstBegin* nodep) override {
        if (nodep->name() == "") {
            putbs("begin\n");
        } else {
            putbs("begin : " + nodep->name() + "\n");
        }
        iterateChildren(nodep);
        puts("end\n");
    }
    virtual void visit(AstFork* nodep) override {
        if (nodep->name() == "") {
            putbs("fork\n");
        } else {
            putbs("fork : " + nodep->name() + "\n");
        }
        iterateChildren(nodep);
        puts(nodep->joinType().verilogKwd());
        puts("\n");
    }
    virtual void visit(AstFinal* nodep) override {
        putfs(nodep, "final begin\n");
        iterateChildren(nodep);
        putqs(nodep, "end\n");
    }
    virtual void visit(AstInitial* nodep) override {
        putfs(nodep, "initial begin\n");
        iterateChildren(nodep);
        putqs(nodep, "end\n");
    }
    virtual void visit(AstAlways* nodep) override {
        putfs(nodep, "always ");
        if (m_sensesp) {
            iterateAndNextNull(m_sensesp);
        }  // In active
        else {
            iterateAndNextNull(nodep->sensesp());
        }
        putbs(" begin\n");
        iterateAndNextNull(nodep->bodysp());
        putqs(nodep, "end\n");
    }
    virtual void visit(AstAlwaysPublic* nodep) override {
        putfs(nodep, "/*verilator public_flat_rw ");
        if (m_sensesp) {
            iterateAndNextNull(m_sensesp);
        }  // In active
        else {
            iterateAndNextNull(nodep->sensesp());
        }
        putqs(nodep, " ");
        iterateAndNextNull(nodep->bodysp());
        putqs(nodep, "*/\n");
    }
    virtual void visit(AstNodeAssign* nodep) override {
        iterateAndNextNull(nodep->lhsp());
        putfs(nodep, " " + nodep->verilogKwd() + " ");
        iterateAndNextNull(nodep->rhsp());
        if (!m_suppressSemi) puts(";\n");
    }
    virtual void visit(AstAssignDly* nodep) override {
        iterateAndNextNull(nodep->lhsp());
        putfs(nodep, " <= ");
        iterateAndNextNull(nodep->rhsp());
        puts(";\n");
    }
    virtual void visit(AstAssignAlias* nodep) override {
        putbs("alias ");
        iterateAndNextNull(nodep->lhsp());
        putfs(nodep, " = ");
        iterateAndNextNull(nodep->rhsp());
        if (!m_suppressSemi) puts(";\n");
    }
    virtual void visit(AstAssignW* nodep) override {
        putfs(nodep, "assign ");
        iterateAndNextNull(nodep->lhsp());
        putbs(" = ");
        iterateAndNextNull(nodep->rhsp());
        if (!m_suppressSemi) puts(";\n");
    }
    virtual void visit(AstBreak*) override {
        putbs("break");
        if (!m_suppressSemi) puts(";\n");
    }
    virtual void visit(AstSenTree* nodep) override {
        // AstSenItem is called for dumping in isolation by V3Order
        putfs(nodep, "@(");
        for (AstNode* expp = nodep->sensesp(); expp; expp = expp->nextp()) {
            iterate(expp);
            if (expp->nextp()) putqs(expp->nextp(), " or ");
        }
        puts(")");
    }
    virtual void visit(AstSenItem* nodep) override {
        putfs(nodep, "");
        puts(nodep->edgeType().verilogKwd());
        if (nodep->sensp()) puts(" ");
        iterateChildren(nodep);
    }
    virtual void visit(AstNodeCase* nodep) override {
        putfs(nodep, "");
        if (const AstCase* casep = VN_CAST(nodep, Case)) {
            if (casep->priorityPragma()) puts("priority ");
            if (casep->uniquePragma()) puts("unique ");
            if (casep->unique0Pragma()) puts("unique0 ");
        }
        puts(nodep->verilogKwd());
        puts(" (");
        iterateAndNextNull(nodep->exprp());
        puts(")\n");
        if (const AstCase* casep = VN_CAST(nodep, Case)) {
            if (casep->fullPragma() || casep->parallelPragma()) {
                puts(" // synopsys");
                if (casep->fullPragma()) puts(" full_case");
                if (casep->parallelPragma()) puts(" parallel_case");
            }
        }
        iterateAndNextNull(nodep->itemsp());
        putqs(nodep, "endcase\n");
    }
    virtual void visit(AstCaseItem* nodep) override {
        if (nodep->condsp()) {
            iterateAndNextNull(nodep->condsp());
        } else {
            putbs("default");
        }
        putfs(nodep, ": begin ");
        iterateAndNextNull(nodep->bodysp());
        putqs(nodep, "end\n");
    }
    virtual void visit(AstComment* nodep) override {
        puts(string("// ") + nodep->name() + "\n");
        iterateChildren(nodep);
    }
    virtual void visit(AstContinue*) override {
        putbs("continue");
        if (!m_suppressSemi) puts(";\n");
    }
    virtual void visit(AstCoverDecl*) override {}  // N/A
    virtual void visit(AstCoverInc*) override {}  // N/A
    virtual void visit(AstCoverToggle*) override {}  // N/A

    void visitNodeDisplay(AstNode* nodep, AstNode* fileOrStrgp, const string& text,
                          AstNode* exprsp) {
        putfs(nodep, nodep->verilogKwd());
        putbs("(");
        if (fileOrStrgp) {
            iterateAndNextNull(fileOrStrgp);
            putbs(", ");
        }
        putsQuoted(text);
        for (AstNode* expp = exprsp; expp; expp = expp->nextp()) {
            puts(", ");
            iterateAndNextNull(expp);
        }
        puts(");\n");
    }
    virtual void visit(AstDisable* nodep) override { putbs("disable " + nodep->name() + ";\n"); }
    virtual void visit(AstDisplay* nodep) override {
        visitNodeDisplay(nodep, nodep->filep(), nodep->fmtp()->text(), nodep->fmtp()->exprsp());
    }
    virtual void visit(AstElabDisplay* nodep) override {
        visitNodeDisplay(nodep, nullptr, nodep->fmtp()->text(), nodep->fmtp()->exprsp());
    }
    virtual void visit(AstFScanF* nodep) override {
        visitNodeDisplay(nodep, nodep->filep(), nodep->text(), nodep->exprsp());
    }
    virtual void visit(AstSScanF* nodep) override {
        visitNodeDisplay(nodep, nodep->fromp(), nodep->text(), nodep->exprsp());
    }
    virtual void visit(AstSFormat* nodep) override {
        visitNodeDisplay(nodep, nodep->lhsp(), nodep->fmtp()->text(), nodep->fmtp()->exprsp());
    }
    virtual void visit(AstSFormatF* nodep) override {
        visitNodeDisplay(nodep, nullptr, nodep->text(), nodep->exprsp());
    }
    virtual void visit(AstFOpen* nodep) override {
        putfs(nodep, nodep->verilogKwd());
        putbs("(");
        iterateAndNextNull(nodep->filenamep());
        putbs(", ");
        iterateAndNextNull(nodep->modep());
        puts(");\n");
    }
    virtual void visit(AstFOpenMcd* nodep) override {
        putfs(nodep, nodep->verilogKwd());
        putbs("(");
        iterateAndNextNull(nodep->filenamep());
        puts(");\n");
    }
    virtual void visit(AstFClose* nodep) override {
        putfs(nodep, nodep->verilogKwd());
        putbs("(");
        if (nodep->filep()) iterateAndNextNull(nodep->filep());
        puts(");\n");
    }
    virtual void visit(AstFFlush* nodep) override {
        putfs(nodep, nodep->verilogKwd());
        putbs("(");
        if (nodep->filep()) iterateAndNextNull(nodep->filep());
        puts(");\n");
    }
    virtual void visit(AstJumpBlock* nodep) override {
        putbs("begin : label" + cvtToStr(nodep->labelNum()) + "\n");
        if (nodep->stmtsp()) iterateAndNextNull(nodep->stmtsp());
        puts("end\n");
    }
    virtual void visit(AstJumpGo* nodep) override {
        putbs("disable label" + cvtToStr(nodep->labelp()->blockp()->labelNum()) + ";\n");
    }
    virtual void visit(AstJumpLabel* nodep) override {
        putbs("// " + cvtToStr(nodep->blockp()) + ":\n");
    }
    virtual void visit(AstNodeReadWriteMem* nodep) override {
        putfs(nodep, nodep->verilogKwd());
        putbs("(");
        if (nodep->filenamep()) iterateAndNextNull(nodep->filenamep());
        putbs(", ");
        if (nodep->memp()) iterateAndNextNull(nodep->memp());
        if (nodep->lsbp()) {
            putbs(", ");
            iterateAndNextNull(nodep->lsbp());
        }
        if (nodep->msbp()) {
            putbs(", ");
            iterateAndNextNull(nodep->msbp());
        }
        puts(");\n");
    }
    virtual void visit(AstSysFuncAsTask* nodep) override {
        iterateAndNextNull(nodep->lhsp());
        puts(";\n");
    }
    virtual void visit(AstSysIgnore* nodep) override {
        putfs(nodep, nodep->verilogKwd());
        putbs("(");
        iterateAndNextNull(nodep->exprsp());
        puts(");\n");
    }
    virtual void visit(AstNodeFor* nodep) override {
        putfs(nodep, "for (");
        {
            VL_RESTORER(m_suppressSemi);
            m_suppressSemi = true;
            iterateAndNextNull(nodep->initsp());
            puts(";");
            iterateAndNextNull(nodep->condp());
            puts(";");
            iterateAndNextNull(nodep->incsp());
        }
        puts(") begin\n");
        iterateAndNextNull(nodep->bodysp());
        putqs(nodep, "end\n");
    }
    virtual void visit(AstRepeat* nodep) override {
        putfs(nodep, "repeat (");
        iterateAndNextNull(nodep->countp());
        puts(") begin\n");
        iterateAndNextNull(nodep->bodysp());
        putfs(nodep, "end\n");
    }
    virtual void visit(AstWhile* nodep) override {
        iterateAndNextNull(nodep->precondsp());
        putfs(nodep, "while (");
        iterateAndNextNull(nodep->condp());
        puts(") begin\n");
        iterateAndNextNull(nodep->bodysp());
        iterateAndNextNull(nodep->incsp());
        iterateAndNextNull(nodep->precondsp());  // Need to recompute before next loop
        putfs(nodep, "end\n");
    }
    virtual void visit(AstNodeIf* nodep) override {
        putfs(nodep, "");
        if (const AstIf* ifp = VN_CAST(nodep, If)) {
            if (ifp->priorityPragma()) puts("priority ");
            if (ifp->uniquePragma()) puts("unique ");
            if (ifp->unique0Pragma()) puts("unique0 ");
        }
        puts("if (");
        iterateAndNextNull(nodep->condp());
        puts(") begin\n");
        iterateAndNextNull(nodep->ifsp());
        if (nodep->elsesp()) {
            putqs(nodep, "end\n");
            putqs(nodep, "else begin\n");
            iterateAndNextNull(nodep->elsesp());
        }
        putqs(nodep, "end\n");
    }
    virtual void visit(AstPast* nodep) override {
        putfs(nodep, "$past(");
        iterateAndNextNull(nodep->exprp());
        if (nodep->ticksp()) {
            puts(", ");
            iterateAndNextNull(nodep->ticksp());
        }
        puts(")");
    }
    virtual void visit(AstReturn* nodep) override {
        putfs(nodep, "return ");
        iterateAndNextNull(nodep->lhsp());
        puts(";\n");
    }
    virtual void visit(AstStop* nodep) override { putfs(nodep, "$stop;\n"); }
    virtual void visit(AstFinish* nodep) override { putfs(nodep, "$finish;\n"); }
    virtual void visit(AstNodeSimpleText* nodep) override {
        if (nodep->tracking() || m_trackText) {
            puts(nodep->text());
        } else {
            putsNoTracking(nodep->text());
        }
    }
    virtual void visit(AstTextBlock* nodep) override {
        visit(VN_CAST(nodep, NodeSimpleText));
        {
            VL_RESTORER(m_suppressSemi);
            m_suppressVarSemi = nodep->commas();
            for (AstNode* childp = nodep->nodesp(); childp; childp = childp->nextp()) {
                iterate(childp);
                if (nodep->commas() && childp->nextp()) puts(", ");
            }
        }
    }
    virtual void visit(AstScopeName* nodep) override {}
    virtual void visit(AstCStmt* nodep) override {
        putfs(nodep, "$_CSTMT(");
        iterateAndNextNull(nodep->bodysp());
        puts(");\n");
    }
    virtual void visit(AstCMath* nodep) override {
        putfs(nodep, "$_CMATH(");
        iterateAndNextNull(nodep->bodysp());
        puts(");\n");
    }
    virtual void visit(AstUCStmt* nodep) override {
        putfs(nodep, "$c(");
        iterateAndNextNull(nodep->bodysp());
        puts(");\n");
    }
    virtual void visit(AstUCFunc* nodep) override {
        putfs(nodep, "$c(");
        iterateAndNextNull(nodep->bodysp());
        puts(")");
    }

    // Operators
    virtual void emitVerilogFormat(AstNode* nodep, const string& format, AstNode* lhsp = nullptr,
                                   AstNode* rhsp = nullptr, AstNode* thsp = nullptr,
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
                    iterateAndNextNull(lhsp);
                    break;
                }
                case 'r': {
                    UASSERT_OBJ(rhsp, nodep, "emitVerilog() references undef node");
                    iterateAndNextNull(rhsp);
                    break;
                }
                case 't': {
                    UASSERT_OBJ(thsp, nodep, "emitVerilog() references undef node");
                    iterateAndNextNull(thsp);
                    break;
                }
                case 'o': {
                    UASSERT_OBJ(thsp, nodep, "emitVerilog() references undef node");
                    iterateAndNextNull(fhsp);
                    break;
                }
                case 'd': {
                    UASSERT_OBJ(nodep->dtypep(), nodep, "emitVerilog() references undef node");
                    iterateAndNextNull(nodep->dtypep());
                    break;
                }
                default: nodep->v3fatalSrc("Unknown emitVerilog format code: %" << c); break;
                }
            }
        }
    }

    virtual void visit(AstNodeTermop* nodep) override {
        emitVerilogFormat(nodep, nodep->emitVerilog());
    }
    virtual void visit(AstNodeUniop* nodep) override {
        emitVerilogFormat(nodep, nodep->emitVerilog(), nodep->lhsp());
    }
    virtual void visit(AstNodeBiop* nodep) override {
        emitVerilogFormat(nodep, nodep->emitVerilog(), nodep->lhsp(), nodep->rhsp());
    }
    virtual void visit(AstNodeTriop* nodep) override {
        emitVerilogFormat(nodep, nodep->emitVerilog(), nodep->lhsp(), nodep->rhsp(),
                          nodep->thsp());
    }
    virtual void visit(AstAttrOf* nodep) override {
        putfs(nodep, "$_ATTROF(");
        iterateAndNextNull(nodep->fromp());
        if (nodep->dimp()) {
            putbs(", ");
            iterateAndNextNull(nodep->dimp());
        }
        puts(")");
    }
    virtual void visit(AstInitArray* nodep) override {
        putfs(nodep, "'{");
        int comma = 0;
        const AstInitArray::KeyItemMap& mapr = nodep->map();
        for (const auto& itr : mapr) {
            if (comma++) putbs(", ");
            puts(cvtToStr(itr.first));
            puts(":");
            AstNode* valuep = itr.second->valuep();
            iterate(valuep);
        }
        puts("}");
    }
    virtual void visit(AstNodeCond* nodep) override {
        putbs("(");
        iterateAndNextNull(nodep->condp());
        putfs(nodep, " ? ");
        iterateAndNextNull(nodep->expr1p());
        putbs(" : ");
        iterateAndNextNull(nodep->expr2p());
        puts(")");
    }
    virtual void visit(AstRange* nodep) override {
        puts("[");
        if (VN_IS(nodep->leftp(), Const) && VN_IS(nodep->rightp(), Const)) {
            // Looks nicer if we print [1:0] rather than [32'sh1:32sh0]
            puts(cvtToStr(nodep->leftConst()));
            puts(":");
            puts(cvtToStr(nodep->rightConst()));
            puts("]");
        } else {
            iterateAndNextNull(nodep->leftp());
            puts(":");
            iterateAndNextNull(nodep->rightp());
            puts("]");
        }
    }
    virtual void visit(AstSel* nodep) override {
        iterateAndNextNull(nodep->fromp());
        puts("[");
        if (VN_IS(nodep->lsbp(), Const)) {
            if (nodep->widthp()->isOne()) {
                if (VN_IS(nodep->lsbp(), Const)) {
                    puts(cvtToStr(VN_CAST(nodep->lsbp(), Const)->toSInt()));
                } else {
                    iterateAndNextNull(nodep->lsbp());
                }
            } else {
                puts(cvtToStr(VN_CAST(nodep->lsbp(), Const)->toSInt()
                              + VN_CAST(nodep->widthp(), Const)->toSInt() - 1));
                puts(":");
                puts(cvtToStr(VN_CAST(nodep->lsbp(), Const)->toSInt()));
            }
        } else {
            iterateAndNextNull(nodep->lsbp());
            putfs(nodep, "+:");
            iterateAndNextNull(nodep->widthp());
            puts("]");
        }
        puts("]");
    }
    virtual void visit(AstSliceSel* nodep) override {
        iterateAndNextNull(nodep->fromp());
        puts(cvtToStr(nodep->declRange()));
    }
    virtual void visit(AstTypedef* nodep) override {
        putfs(nodep, "typedef ");
        iterateAndNextNull(nodep->dtypep());
        puts(" ");
        puts(nodep->prettyName());
        puts(";\n");
    }
    virtual void visit(AstBasicDType* nodep) override {
        if (nodep->isSigned()) putfs(nodep, "signed ");
        putfs(nodep, nodep->prettyName());
        if (nodep->rangep()) {
            puts(" ");
            iterateAndNextNull(nodep->rangep());
            puts(" ");
        } else if (nodep->isRanged()) {
            puts(" [");
            puts(cvtToStr(nodep->hi()));
            puts(":0] ");
        }
    }
    virtual void visit(AstConstDType* nodep) override {
        putfs(nodep, "const ");
        iterate(nodep->subDTypep());
    }
    virtual void visit(AstNodeArrayDType* nodep) override {
        iterate(nodep->subDTypep());
        iterateAndNextNull(nodep->rangep());
    }
    virtual void visit(AstNodeUOrStructDType* nodep) override {
        puts(nodep->verilogKwd() + " ");
        if (nodep->packed()) puts("packed ");
        puts("\n");
        iterateAndNextNull(nodep->membersp());
        puts("}");
    }
    virtual void visit(AstMemberDType* nodep) override {
        iterate(nodep->subDTypep());
        puts(" ");
        puts(nodep->name());
        puts("}");
    }
    virtual void visit(AstNodeFTaskRef* nodep) override {
        if (nodep->dotted() != "") {
            putfs(nodep, nodep->dotted());
            puts(".");
            puts(nodep->prettyName());
        } else {
            putfs(nodep, nodep->prettyName());
        }
        puts("(");
        iterateAndNextNull(nodep->pinsp());
        puts(")");
    }
    virtual void visit(AstArg* nodep) override { iterateAndNextNull(nodep->exprp()); }
    virtual void visit(AstPrintTimeScale* nodep) override {
        puts(nodep->verilogKwd());
        puts(";\n");
    }

    // Terminals
    virtual void visit(AstVarRef* nodep) override {
        if (nodep->varScopep()) {
            putfs(nodep, nodep->varScopep()->prettyName());
        } else {
            if (nodep->selfPointer().empty()) {
                putfs(nodep, nodep->varp()->prettyName());
            } else {
                putfs(nodep, nodep->selfPointer() + "->");
                puts(nodep->varp()->prettyName());
            }
        }
    }
    virtual void visit(AstVarXRef* nodep) override {
        putfs(nodep, nodep->dotted());
        puts(".");
        puts(nodep->varp()->prettyName());
    }
    virtual void visit(AstConst* nodep) override { putfs(nodep, nodep->num().ascii(true, true)); }

    // Just iterate
    virtual void visit(AstTopScope* nodep) override { iterateChildren(nodep); }
    virtual void visit(AstScope* nodep) override { iterateChildren(nodep); }
    virtual void visit(AstVar* nodep) override {
        if (nodep->isIO()) {
            putfs(nodep, nodep->verilogKwd());
            puts(" ");
        }
        std::vector<const AstUnpackArrayDType*> unpackps;
        for (AstNodeDType* dtypep = nodep->dtypep(); dtypep;) {
            dtypep = dtypep->skipRefp();
            if (AstUnpackArrayDType* unpackp = VN_CAST(dtypep, UnpackArrayDType)) {
                unpackps.push_back(unpackp);
                dtypep = unpackp->subDTypep();
            } else {
                iterate(dtypep);
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
    virtual void visit(AstActive* nodep) override {
        m_sensesp = nodep->sensesp();
        iterateAndNextNull(nodep->stmtsp());
        m_sensesp = nullptr;
    }
    virtual void visit(AstVarScope*) override {}
    virtual void visit(AstNodeText*) override {}
    virtual void visit(AstTraceDecl*) override {}
    virtual void visit(AstTraceInc*) override {}
    // NOPs
    virtual void visit(AstPragma*) override {}
    virtual void visit(AstCell*) override {}  // Handled outside the Visit class
    // Default
    virtual void visit(AstNode* nodep) override {
        puts(string("\n???? // ") + nodep->prettyTypeName() + "\n");
        iterateChildren(nodep);
        // Not v3fatalSrc so we keep processing
        if (!m_suppressUnknown) {
            nodep->v3error(
                "Internal: Unknown node type reached emitter: " << nodep->prettyTypeName());
        }
    }

public:
    bool m_suppressVarSemi = false;  // Suppress emitting semicolon for AstVars
    explicit EmitVBaseVisitor(bool suppressUnknown, AstSenTree* domainp)
        : m_suppressUnknown{suppressUnknown}
        , m_sensesp{domainp} {}
    virtual ~EmitVBaseVisitor() override = default;
};

//######################################################################
// Emit to an output file

class EmitVFileVisitor final : public EmitVBaseVisitor {
    // MEMBERS
    V3OutFile* m_ofp;
    // METHODS
    V3OutFile* ofp() const { return m_ofp; }
    virtual void puts(const string& str) override { ofp()->puts(str); }
    virtual void putbs(const string& str) override { ofp()->putbs(str); }
    virtual void putfs(AstNode*, const string& str) override { putbs(str); }
    virtual void putqs(AstNode*, const string& str) override { putbs(str); }
    virtual void putsNoTracking(const string& str) override { ofp()->putsNoTracking(str); }

public:
    EmitVFileVisitor(AstNode* nodep, V3OutFile* ofp, bool trackText, bool suppressUnknown)
        : EmitVBaseVisitor{suppressUnknown, nullptr} {
        m_ofp = ofp;
        m_trackText = trackText;
        iterate(nodep);
    }
    virtual ~EmitVFileVisitor() override = default;
};

//######################################################################
// Emit to a stream (perhaps stringstream)

class EmitVStreamVisitor final : public EmitVBaseVisitor {
    // MEMBERS
    std::ostream& m_os;
    // METHODS
    virtual void putsNoTracking(const string& str) override { m_os << str; }
    virtual void puts(const string& str) override { putsNoTracking(str); }
    virtual void putbs(const string& str) override { puts(str); }
    virtual void putfs(AstNode*, const string& str) override { putbs(str); }
    virtual void putqs(AstNode*, const string& str) override { putbs(str); }

public:
    EmitVStreamVisitor(AstNode* nodep, std::ostream& os)
        : EmitVBaseVisitor{false, nullptr}
        , m_os(os) {  // Need () or GCC 4.8 false warning
        iterate(nodep);
    }
    virtual ~EmitVStreamVisitor() override = default;
};

//######################################################################
// Emit to a stream (perhaps stringstream)

class EmitVPrefixedFormatter final : public V3OutFormatter {
    std::ostream& m_os;
    string m_prefix;  // What to print at beginning of each line
    int m_flWidth;  // Padding of fileline
    int m_column;  // Rough location; need just zero or non-zero
    FileLine* m_prefixFl;
    // METHODS
    virtual void putcOutput(char chr) override {
        if (chr == '\n') {
            m_column = 0;
            m_os << chr;
        } else {
            if (m_column == 0) {
                m_column = 10;
                m_os << m_prefixFl->ascii() + ":";
                m_os << V3OutFile::indentSpaces(m_flWidth - (m_prefixFl->ascii().length() + 1));
                m_os << " ";
                m_os << m_prefix;
            }
            m_column++;
            m_os << chr;
        }
    }

public:
    void prefixFl(FileLine* fl) { m_prefixFl = fl; }
    FileLine* prefixFl() const { return m_prefixFl; }
    int column() const { return m_column; }
    EmitVPrefixedFormatter(std::ostream& os, const string& prefix, int flWidth)
        : V3OutFormatter{"__STREAM", V3OutFormatter::LA_VERILOG}
        , m_os(os)  // Need () or GCC 4.8 false warning
        , m_prefix{prefix}
        , m_flWidth{flWidth} {
        m_column = 0;
        m_prefixFl = v3Global.rootp()->fileline();  // NETLIST's fileline instead of nullptr to
                                                    // avoid nullptr checks
    }
    virtual ~EmitVPrefixedFormatter() override {
        if (m_column) puts("\n");
    }
};

class EmitVPrefixedVisitor final : public EmitVBaseVisitor {
    // MEMBERS
    EmitVPrefixedFormatter m_formatter;  // Special verilog formatter (Way down the
                                         // inheritance is another unused V3OutFormatter)
    // METHODS
    virtual void putsNoTracking(const string& str) override { m_formatter.putsNoTracking(str); }
    virtual void puts(const string& str) override { m_formatter.puts(str); }
    // We don't use m_formatter's putbs because the tokens will change filelines
    // and insert returns at the proper locations
    virtual void putbs(const string& str) override { m_formatter.puts(str); }
    virtual void putfs(AstNode* nodep, const string& str) override { putfsqs(nodep, str, false); }
    virtual void putqs(AstNode* nodep, const string& str) override { putfsqs(nodep, str, true); }
    void putfsqs(AstNode* nodep, const string& str, bool quiet) {
        if (m_formatter.prefixFl() != nodep->fileline()) {
            m_formatter.prefixFl(nodep->fileline());
            if (m_formatter.column()) puts("\n");  // This in turn will print the m_prefixFl
        }
        if (!quiet && nodep->user3()) puts("%%");
        putbs(str);
    }

public:
    EmitVPrefixedVisitor(AstNode* nodep, std::ostream& os, const string& prefix, int flWidth,
                         AstSenTree* domainp, bool user3mark)
        : EmitVBaseVisitor{false, domainp}
        , m_formatter{os, prefix, flWidth} {
        if (user3mark) AstUser3InUse::check();
        iterate(nodep);
    }
    virtual ~EmitVPrefixedVisitor() override = default;
};

//######################################################################
// EmitV class functions

void V3EmitV::verilogForTree(AstNode* nodep, std::ostream& os) { EmitVStreamVisitor(nodep, os); }

void V3EmitV::verilogPrefixedTree(AstNode* nodep, std::ostream& os, const string& prefix,
                                  int flWidth, AstSenTree* domainp, bool user3mark) {
    EmitVPrefixedVisitor(nodep, os, prefix, flWidth, domainp, user3mark);
}

void V3EmitV::emitvFiles() {
    UINFO(2, __FUNCTION__ << ": " << endl);
    for (AstNodeFile* filep = v3Global.rootp()->filesp(); filep;
         filep = VN_CAST(filep->nextp(), NodeFile)) {
        AstVFile* vfilep = VN_CAST(filep, VFile);
        if (vfilep && vfilep->tblockp()) {
            V3OutVFile of(vfilep->name());
            of.puts("// DESCR"
                    "IPTION: Verilator generated Verilog\n");
            EmitVFileVisitor visitor(vfilep->tblockp(), &of, true, false);
        }
    }
}

void V3EmitV::debugEmitV(const string& stage) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    const string filename
        = v3Global.opt.makeDir() + "/" + v3Global.opt.prefix() + "__" + stage + ".v";
    V3OutVFile of(filename);
    EmitVFileVisitor visitor(v3Global.rootp(), &of, true, true);
}
