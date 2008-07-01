//*************************************************************************
// DESCRIPTION: Verilator: Emit Verilog from tree
//
// Code available from: http://www.veripool.org/verilator
//
// AUTHORS: Wilson Snyder with Paul Wasson, Duane Gabli
//
//*************************************************************************
//
// Copyright 2004-2008 by Wilson Snyder.  This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// General Public License or the Perl Artistic License.
//
// Verilator is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"
#include <cstdio>
#include <cstdarg>
#include <unistd.h>
#include <cmath>
#include <map>
#include <vector>
#include <algorithm>

#include "V3Global.h"
#include "V3EmitV.h"
#include "V3EmitCBase.h"

//######################################################################
// Emit statements and math operators

class EmitVImp : public EmitCBaseVisitor {
private:
    bool	m_suppressSemi;
    AstModule*	m_modp;
public:
    //int debug() { return 9; }

    // METHODS

    // VISITORS
    virtual void visit(AstNetlist* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
    }
    virtual void visit(AstModule* nodep, AstNUser*) {
	m_modp = nodep;
	putbs("module "+modClassName(nodep)+";\n");
	nodep->iterateChildren(*this);
	puts("endmodule\n");
    }
    virtual void visit(AstNodeFTask* nodep, AstNUser*) {
	putbs(nodep->castTask() ? "task ":"function ");
	puts(nodep->name());
	puts(";\n");
	putbs("begin\n");
	nodep->stmtsp()->iterateAndNext(*this);
	puts("end\n");
    }

    virtual void visit(AstBegin* nodep, AstNUser*) {
	putbs("begin\n");
	nodep->iterateChildren(*this);
	puts("end\n");
    }
    virtual void visit(AstGenerate* nodep, AstNUser*) {
	putbs("generate\n");
	nodep->iterateChildren(*this);
	puts("end\n");
    }
    virtual void visit(AstFinal* nodep, AstNUser*) {
	putbs("final begin\n");
	nodep->iterateChildren(*this);
	puts("end\n");
    }
    virtual void visit(AstInitial* nodep, AstNUser*) {
	putbs("initial begin\n");
	nodep->iterateChildren(*this);
	puts("end\n");
    }
    virtual void visit(AstAlways* nodep, AstNUser*) {
	putbs("always ");
	nodep->sensesp()->iterateAndNext(*this);
	putbs("begin\n");
	nodep->bodysp()->iterateAndNext(*this);
	puts("end\n");
    }
    virtual void visit(AstNodeAssign* nodep, AstNUser*) {
	nodep->lhsp()->iterateAndNext(*this);
	putbs(" "+nodep->verilogKwd()+" ");
	nodep->rhsp()->iterateAndNext(*this);
	if (!m_suppressSemi) puts(";\n");
    }
    virtual void visit(AstAssignDly* nodep, AstNUser*) {
	nodep->lhsp()->iterateAndNext(*this);
	putbs(" <= ");
	nodep->rhsp()->iterateAndNext(*this);
	puts(";\n");
    }
    virtual void visit(AstAssignAlias* nodep, AstNUser*) {
	putbs("assign ");
	nodep->lhsp()->iterateAndNext(*this);
	putbs(" = ");
	nodep->rhsp()->iterateAndNext(*this);
	if (!m_suppressSemi) puts(";\n");
    }
    virtual void visit(AstAssignW* nodep, AstNUser*) {
	putbs("assign ");
	nodep->lhsp()->iterateAndNext(*this);
	putbs(" = ");
	nodep->rhsp()->iterateAndNext(*this);
	if (!m_suppressSemi) puts(";\n");
    }
    virtual void visit(AstSenTree* nodep, AstNUser*) {
	putbs("@(");
	nodep->iterateChildren(*this);
	puts(") ");
    }
    virtual void visit(AstSenItem* nodep, AstNUser*) {
	putbs("");
	if (nodep->backp()->castSenItem()) puts(" or ");
	puts(nodep->edgeType().verilogKwd());
	puts(" ");
	nodep->iterateChildren(*this);
	puts(" ");
    }
    virtual void visit(AstNodeCase* nodep, AstNUser*) {
	putbs(nodep->verilogKwd());
	puts(" (");
	nodep->exprp()->iterateAndNext(*this);
	puts(")\n");
	if (AstCase* casep = nodep->castCase()) {
	    if (casep->fullPragma() || casep->parallelPragma()) {
		puts(" // synopsys");
		if (casep->fullPragma()) puts(" full_case");
		if (casep->parallelPragma()) puts(" parallel_case");
	    }
	}
	nodep->itemsp()->iterateAndNext(*this);
	putbs("endcase");
	puts("\n");
    }
    virtual void visit(AstCaseItem* nodep, AstNUser*) {
	if (nodep->condsp()) {
	    nodep->condsp()->iterateAndNext(*this);
	} else putbs("default");
	putbs(": begin ");
	nodep->bodysp()->iterateAndNext(*this);
	puts("end\n");
    }
    virtual void visit(AstComment* nodep, AstNUser*) {
	puts((string)"// "+nodep->name()+"\n");
	nodep->iterateChildren(*this);
    }
    virtual void visit(AstCoverDecl*, AstNUser*) {
	// N/A
    }
    virtual void visit(AstCoverInc*, AstNUser*) {
	// N/A
    }

    void visitNodeDisplay(AstNode* nodep, AstNode* filep, const string& text, AstNode* exprsp) {
	putbs(nodep->verilogKwd());
	putbs(" (");
	if (filep) { filep->iterateAndNext(*this); putbs(","); }
	puts("\"");
	ofp()->putsNoTracking(text);
	puts("\"");
	for (AstNode* expp=exprsp; expp; expp = expp->nextp()) {
	    puts(",");
	    expp->iterateAndNext(*this);
	}
	puts(");\n");
    }
    virtual void visit(AstDisplay* nodep, AstNUser*) {
	visitNodeDisplay(nodep, nodep->filep(), nodep->text(), nodep->exprsp());
    }
    virtual void visit(AstFScanF* nodep, AstNUser*) {
	visitNodeDisplay(nodep, nodep->filep(), nodep->text(), nodep->exprsp());
    }
    virtual void visit(AstSScanF* nodep, AstNUser*) {
	visitNodeDisplay(nodep, nodep->fromp(), nodep->text(), nodep->exprsp());
    }

    virtual void visit(AstFOpen* nodep, AstNUser*) {
	putbs(nodep->verilogKwd());
	putbs(" (");
	if (nodep->filep()) nodep->filep()->iterateChildren(*this);
	putbs(",");
	if (nodep->filenamep()) nodep->filenamep()->iterateChildren(*this);
	putbs(",");
	if (nodep->modep()) nodep->modep()->iterateChildren(*this);
	puts(");\n");
    }
    virtual void visit(AstFClose* nodep, AstNUser*) {
	putbs(nodep->verilogKwd());
	putbs(" (");
	if (nodep->filep()) nodep->filep()->iterateChildren(*this);
	puts(");\n");
    }
    virtual void visit(AstFFlush* nodep, AstNUser*) {
	putbs(nodep->verilogKwd());
	putbs(" (");
	if (nodep->filep()) nodep->filep()->iterateChildren(*this);
	puts(");\n");
    }
    virtual void visit(AstReadMem* nodep, AstNUser*) {
	putbs(nodep->verilogKwd());
	putbs(" (");
	if (nodep->filenamep()) nodep->filenamep()->iterateChildren(*this);
	putbs(",");
	if (nodep->memp()) nodep->memp()->iterateChildren(*this);
	if (nodep->lsbp()) { putbs(","); nodep->lsbp()->iterateChildren(*this); }
	if (nodep->msbp()) { putbs(","); nodep->msbp()->iterateChildren(*this); }
	puts(");\n");
    }
    virtual void visit(AstNodeFor* nodep, AstNUser*) {
	puts("for (");
	m_suppressSemi = true;
	nodep->initsp()->iterateAndNext(*this);
	puts(";");
	nodep->condp()->iterateAndNext(*this);
	puts(";");
	nodep->incsp()->iterateAndNext(*this);
	m_suppressSemi = false;
	puts(") {\n");
	nodep->bodysp()->iterateAndNext(*this);
	puts("}\n");
    }
    virtual void visit(AstWhile* nodep, AstNUser*) {
	nodep->precondsp()->iterateAndNext(*this);
	puts("while (");
	nodep->condp()->iterateAndNext(*this);
	puts(") {\n");
	nodep->bodysp()->iterateAndNext(*this);
	nodep->precondsp()->iterateAndNext(*this);  // Need to recompute before next loop
	puts("}\n");
    }
    virtual void visit(AstNodeIf* nodep, AstNUser*) {
	puts("if (");
	nodep->condp()->iterateAndNext(*this);
	puts(") begin\n");
	nodep->ifsp()->iterateAndNext(*this);
	if (nodep->elsesp()) {
	    puts("end\n");
	    puts("else begin\n");
	    nodep->elsesp()->iterateAndNext(*this);
	}
	puts("end\n");
    }
    virtual void visit(AstStop*, AstNUser*) {
	putbs("$stop;\n");
    }
    virtual void visit(AstFinish*, AstNUser*) {
	putbs("$finish;\n");
    }
    virtual void visit(AstText* nodep, AstNUser*) {
	ofp()->putsNoTracking(nodep->text());
    }
    virtual void visit(AstScopeName* nodep, AstNUser*) {
    }
    virtual void visit(AstCStmt* nodep, AstNUser*) {
	putbs("$_CSTMT(");
	nodep->bodysp()->iterateAndNext(*this);
	puts(");\n");
    }
    virtual void visit(AstCMath* nodep, AstNUser*) {
	putbs("$_CMATH(");
	nodep->bodysp()->iterateAndNext(*this);
	puts(");\n");
    }
    virtual void visit(AstUCStmt* nodep, AstNUser*) {
	putbs("$c(");
	nodep->bodysp()->iterateAndNext(*this);
	puts(");\n");
    }
    virtual void visit(AstUCFunc* nodep, AstNUser*) {
	putbs("$c(");
	nodep->bodysp()->iterateAndNext(*this); puts(")\n");
    }

    // Operators
    virtual void emitVerilogFormat(AstNode* nodep, const string& format,
				   AstNode* lhsp=NULL, AstNode* rhsp=NULL, AstNode* thsp=NULL) {
	// Look at emitVerilog() format for term/uni/dual/triops,
	// and write out appropriate text.
	//	%l	lhsp - if appropriate
	//	%r	rhsp - if appropriate
	//	%t	thsp - if appropriate
	//	%k	Potential line break
	bool inPct = false;
	putbs("");
	for (string::const_iterator pos = format.begin(); pos != format.end(); ++pos) {
	    if (pos[0]=='%') {
		inPct = true;
	    } else if (!inPct) {   // Normal text
		string s; s+=pos[0]; puts(s);
	    } else { // Format character
		inPct = false;
		switch (*pos) {
		case '%': puts("%");  break;
		case 'k': putbs("");  break;
		case 'l': {
		    if (!lhsp) { nodep->v3fatalSrc("emitVerilog() references undef node"); }
		    else lhsp->iterateAndNext(*this);
		    break;
		}
		case 'r': {
		    if (!rhsp) { nodep->v3fatalSrc("emitVerilog() references undef node"); }
		    else rhsp->iterateAndNext(*this);
		    break;
		}
		case 't': {
		    if (!thsp) { nodep->v3fatalSrc("emitVerilog() references undef node"); }
		    else thsp->iterateAndNext(*this);
		    break;
		}
		default:
		    nodep->v3fatalSrc("Unknown emitVerilog format code: %"<<pos[0]);
		    break;
		}
            }
        }
    }

    virtual void visit(AstNodeTermop* nodep, AstNUser*) {
	emitVerilogFormat(nodep, nodep->emitVerilog());
    }
    virtual void visit(AstNodeUniop* nodep, AstNUser*) {
	emitVerilogFormat(nodep, nodep->emitVerilog(), nodep->lhsp());
    }
    virtual void visit(AstNodeBiop* nodep, AstNUser*) {
	emitVerilogFormat(nodep, nodep->emitVerilog(), nodep->lhsp(), nodep->rhsp());
    }
    virtual void visit(AstNodeTriop* nodep, AstNUser*) {
	emitVerilogFormat(nodep, nodep->emitVerilog(), nodep->lhsp(), nodep->rhsp(), nodep->thsp());
    }
    virtual void visit(AstAttrOf* nodep, AstNUser*) {
	puts("$_ATTROF(");
	nodep->fromp()->iterateAndNext(*this);
	puts(")");
    }
    virtual void visit(AstNodeCond* nodep, AstNUser*) {
	putbs("(");
	nodep->condp()->iterateAndNext(*this); putbs(" ? ");
	nodep->expr1p()->iterateAndNext(*this); putbs(" : ");
	nodep->expr2p()->iterateAndNext(*this); puts(")");
    }
    virtual void visit(AstRange* nodep, AstNUser*) {
	puts("[");
	nodep->msbp()->iterateAndNext(*this); puts(":");
	nodep->lsbp()->iterateAndNext(*this); puts("]");
    }
    virtual void visit(AstSel* nodep, AstNUser*) {
	nodep->fromp()->iterateAndNext(*this); puts("[");
	if (nodep->lsbp()->castConst()) {
	    if (nodep->widthp()->isOne()) {
		nodep->lsbp()->iterateAndNext(*this);
	    } else {
		puts(cvtToStr(nodep->lsbp()->castConst()->asInt()
			      +nodep->widthp()->castConst()->asInt()
			      -1));
		puts(":");
		nodep->lsbp()->iterateAndNext(*this);
	    }
	} else {
	    nodep->lsbp()->iterateAndNext(*this); puts("+:");
	    nodep->widthp()->iterateAndNext(*this); puts("]");
	}
	puts("]");
    }
    virtual void visit(AstNodeFTaskRef* nodep, AstNUser*) {
	if (nodep->dotted()!="") { puts(nodep->dotted()); puts("."); }
	puts(nodep->name());
	puts("(");
	nodep->pinsp()->iterateAndNext(*this);
	puts(")");
    }
    // Terminals
    virtual void visit(AstVarRef* nodep, AstNUser*) {
	puts(nodep->hiername());
	puts(nodep->varp()->name());
    }
    virtual void visit(AstVarXRef* nodep, AstNUser*) {
	puts(nodep->dotted());
	puts(".");
	puts(nodep->varp()->name());
    }
    virtual void visit(AstConst* nodep, AstNUser*) {
	puts(nodep->num().ascii(true,true));
    }

    // Just iterate
    virtual void visit(AstTopScope* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
    }
    virtual void visit(AstScope* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
    }
    virtual void visit(AstVar* nodep, AstNUser*) {
	puts(nodep->verilogKwd());
	puts(" ");
	if (nodep->isSigned()) puts("signed ");
	if (nodep->rangep()) {
	    puts("["+cvtToStr(nodep->msb())
		 +":"+cvtToStr(nodep->lsb())
		 +"] ");
	}
	puts(nodep->name());
	for (AstRange* arrayp=nodep->arraysp(); arrayp; arrayp = arrayp->nextp()->castRange()) {
	    puts(" ["+cvtToStr(arrayp->msbConst())
		 +":"+cvtToStr(arrayp->lsbConst())
		 +"]");
	}
	puts(";\n");
    }
    virtual void visit(AstNodeText*, AstNUser*) {}
    virtual void visit(AstTraceDecl*, AstNUser*) {}
    virtual void visit(AstTraceInc*, AstNUser*) {}
    // NOPs
    virtual void visit(AstPragma*, AstNUser*) {}
    virtual void visit(AstCell*, AstNUser*) {}		// Handled outside the Visit class
    // Default
    virtual void visit(AstNode* nodep, AstNUser*) {
	puts((string)"\n???? // "+nodep->typeName()+"\n");
	nodep->iterateChildren(*this);
	nodep->v3fatalSrc("Unknown node type reached emitter: "<<nodep->typeName());
    }

public:
    EmitVImp() {
	m_suppressSemi = false;
	m_modp = NULL;
    }
    void main(AstNode* nodep, V3OutCFile* ofp);
    virtual ~EmitVImp() {}
};

//######################################################################

void EmitVImp::main(AstNode* modp, V3OutCFile* ofp) {
    // Output a module, or overall netlist
    m_ofp = ofp;
    modp->accept(*this);
}

//######################################################################
// EmitV class functions

void V3EmitV::emitv() {
    UINFO(2,__FUNCTION__<<": "<<endl);
    if (1) {
	// All-in-one file
	V3OutVFile of (v3Global.opt.makeDir()+"/"+v3Global.opt.prefix()+"__Vout.v");
	of.putsHeader();
	EmitVImp imp;
	imp.main(v3Global.rootp(), &of);
    } else {
	// Process each module in turn
	for (AstModule* modp = v3Global.rootp()->modulesp(); modp; modp=modp->nextp()->castModule()) {
	    EmitVImp imp;
	    V3OutVFile of (v3Global.opt.makeDir()+"/"+imp.modClassName(modp)+"__Vout.v");
	    of.putsHeader();
	    imp.main(modp, &of);
	}
    }
}
