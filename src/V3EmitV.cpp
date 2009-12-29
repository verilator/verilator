//*************************************************************************
// DESCRIPTION: Verilator: Emit Verilog from tree
//
// Code available from: http://www.veripool.org/verilator
//
// AUTHORS: Wilson Snyder with Paul Wasson, Duane Gabli
//
//*************************************************************************
//
// Copyright 2004-2009 by Wilson Snyder.  This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
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

class EmitVBaseVisitor : public EmitCBaseVisitor {
    // MEMBERS
    bool	m_suppressSemi;
    AstSenTree*	m_sensesp;

    // METHODS
    static int debug() {
	static int level = -1;
	if (VL_UNLIKELY(level < 0)) level = v3Global.opt.debugSrcLevel(__FILE__);
	return level;
    }

    virtual void puts(const string& str) = 0;
    virtual void putbs(const string& str) = 0;
    virtual void putfs(AstNode* nodep, const string& str) = 0;
    virtual void putsNoTracking(const string& str) = 0;
    virtual void putsQuoted(const string& str) {
	// Quote \ and " for use inside C programs
	// Don't use to quote a filename for #include - #include doesn't \ escape.
	// Duplicate in V3File - here so we can print to string
	putsNoTracking("\"");
	putsNoTracking(AstNode::quoteName(str));
	putsNoTracking("\"");
    }
    
    // VISITORS
    virtual void visit(AstNetlist* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
    }
    virtual void visit(AstModule* nodep, AstNUser*) {
	putfs(nodep, "module "+modClassName(nodep)+";\n");
	nodep->iterateChildren(*this);
	putfs(nodep, "endmodule\n");
    }
    virtual void visit(AstNodeFTask* nodep, AstNUser*) {
	putfs(nodep, nodep->isFunction() ? "function":"task");
	puts(" ");
	puts(nodep->name());
	puts(";\n");
	putfs(nodep, "begin\n");
	nodep->stmtsp()->iterateAndNext(*this);
	putfs(nodep, "end\n");
    }

    virtual void visit(AstBegin* nodep, AstNUser*) {
	putbs("begin\n");
	nodep->iterateChildren(*this);
	puts("end\n");
    }
    virtual void visit(AstGenerate* nodep, AstNUser*) {
	putfs(nodep, "generate\n");
	nodep->iterateChildren(*this);
	putfs(nodep, "end\n");
    }
    virtual void visit(AstFinal* nodep, AstNUser*) {
	putfs(nodep, "final begin\n");
	nodep->iterateChildren(*this);
	putfs(nodep, "end\n");
    }
    virtual void visit(AstInitial* nodep, AstNUser*) {
	putfs(nodep,"initial begin\n");
	nodep->iterateChildren(*this);
	putfs(nodep, "end\n");
    }
    virtual void visit(AstAlways* nodep, AstNUser*) {
	putfs(nodep,"always ");
	if (m_sensesp) m_sensesp->iterateAndNext(*this);  // In active
	else nodep->sensesp()->iterateAndNext(*this);
	putbs(" begin\n");
	nodep->bodysp()->iterateAndNext(*this);
	putfs(nodep,"end\n");
    }
    virtual void visit(AstNodeAssign* nodep, AstNUser*) {
	nodep->lhsp()->iterateAndNext(*this);
	putfs(nodep," "+nodep->verilogKwd()+" ");
	nodep->rhsp()->iterateAndNext(*this);
	if (!m_suppressSemi) puts(";\n");
    }
    virtual void visit(AstAssignDly* nodep, AstNUser*) {
	nodep->lhsp()->iterateAndNext(*this);
	putfs(nodep," <= ");
	nodep->rhsp()->iterateAndNext(*this);
	puts(";\n");
    }
    virtual void visit(AstAssignAlias* nodep, AstNUser*) {
	putbs("alias ");
	nodep->lhsp()->iterateAndNext(*this);
	putfs(nodep," = ");
	nodep->rhsp()->iterateAndNext(*this);
	if (!m_suppressSemi) puts(";\n");
    }
    virtual void visit(AstAssignW* nodep, AstNUser*) {
	putfs(nodep,"assign ");
	nodep->lhsp()->iterateAndNext(*this);
	putbs(" = ");
	nodep->rhsp()->iterateAndNext(*this);
	if (!m_suppressSemi) puts(";\n");
    }
    virtual void visit(AstSenTree* nodep, AstNUser*) {
	// AstSenItem is called for dumping in isolation by V3Order
	putfs(nodep,"@(");
	for (AstNode* expp=nodep->sensesp(); expp; expp = expp->nextp()) {
	    expp->accept(*this);
	    if (expp->nextp()) putfs(expp->nextp()," or ");
	}
	puts(")");
    }
    virtual void visit(AstSenGate* nodep, AstNUser*) {
	emitVerilogFormat(nodep, nodep->emitVerilog(), nodep->sensesp(), nodep->rhsp());
    }
    virtual void visit(AstSenItem* nodep, AstNUser*) {
	putfs(nodep,"");
	puts(nodep->edgeType().verilogKwd());
	if (nodep->sensp()) puts(" ");
	nodep->iterateChildren(*this);
    }
    virtual void visit(AstNodeCase* nodep, AstNUser*) {
	putfs(nodep,nodep->verilogKwd());
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
	putfs(nodep,"endcase\n");
    }
    virtual void visit(AstCaseItem* nodep, AstNUser*) {
	if (nodep->condsp()) {
	    nodep->condsp()->iterateAndNext(*this);
	} else putbs("default");
	putfs(nodep,": begin ");
	nodep->bodysp()->iterateAndNext(*this);
	putfs(nodep,"end\n");
    }
    virtual void visit(AstComment* nodep, AstNUser*) {
	puts((string)"// "+nodep->name()+"\n");
	nodep->iterateChildren(*this);
    }
    virtual void visit(AstCoverDecl*, AstNUser*) {}  // N/A
    virtual void visit(AstCoverInc*, AstNUser*) {}  // N/A
    virtual void visit(AstCoverToggle*, AstNUser*) {}  // N/A

    void visitNodeDisplay(AstNode* nodep, AstNode* fileOrStrgp, const string& text, AstNode* exprsp) {
	putfs(nodep,nodep->verilogKwd());
	putbs(" (");
	if (fileOrStrgp) { fileOrStrgp->iterateAndNext(*this); putbs(","); }
	putsQuoted(text);
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
    virtual void visit(AstSFormat* nodep, AstNUser*) {
	visitNodeDisplay(nodep, nodep->lhsp(), nodep->text(), nodep->exprsp());
    }
    virtual void visit(AstValuePlusArgs* nodep, AstNUser*) {
	visitNodeDisplay(nodep, NULL, nodep->text(), nodep->exprsp());
    }

    virtual void visit(AstFOpen* nodep, AstNUser*) {
	putfs(nodep,nodep->verilogKwd());
	putbs(" (");
	if (nodep->filep()) nodep->filep()->iterateChildren(*this);
	putbs(",");
	if (nodep->filenamep()) nodep->filenamep()->iterateChildren(*this);
	putbs(",");
	if (nodep->modep()) nodep->modep()->iterateChildren(*this);
	puts(");\n");
    }
    virtual void visit(AstFClose* nodep, AstNUser*) {
	putfs(nodep,nodep->verilogKwd());
	putbs(" (");
	if (nodep->filep()) nodep->filep()->iterateChildren(*this);
	puts(");\n");
    }
    virtual void visit(AstFFlush* nodep, AstNUser*) {
	putfs(nodep,nodep->verilogKwd());
	putbs(" (");
	if (nodep->filep()) nodep->filep()->iterateChildren(*this);
	puts(");\n");
    }
    virtual void visit(AstReadMem* nodep, AstNUser*) {
	putfs(nodep,nodep->verilogKwd());
	putbs(" (");
	if (nodep->filenamep()) nodep->filenamep()->iterateChildren(*this);
	putbs(",");
	if (nodep->memp()) nodep->memp()->iterateChildren(*this);
	if (nodep->lsbp()) { putbs(","); nodep->lsbp()->iterateChildren(*this); }
	if (nodep->msbp()) { putbs(","); nodep->msbp()->iterateChildren(*this); }
	puts(");\n");
    }
    virtual void visit(AstNodeFor* nodep, AstNUser*) {
	putfs(nodep,"for (");
	m_suppressSemi = true;
	nodep->initsp()->iterateAndNext(*this);
	puts(";");
	nodep->condp()->iterateAndNext(*this);
	puts(";");
	nodep->incsp()->iterateAndNext(*this);
	m_suppressSemi = false;
	puts(") begin\n");
	nodep->bodysp()->iterateAndNext(*this);
	putfs(nodep,"end\n");
    }
    virtual void visit(AstRepeat* nodep, AstNUser*) {
	putfs(nodep,"repeat (");
	nodep->countp()->iterateAndNext(*this);
	puts(") begin\n");
	nodep->bodysp()->iterateAndNext(*this);
	putfs(nodep,"end\n");
    }
    virtual void visit(AstWhile* nodep, AstNUser*) {
	nodep->precondsp()->iterateAndNext(*this);
	putfs(nodep,"while (");
	nodep->condp()->iterateAndNext(*this);
	puts(") begin\n");
	nodep->bodysp()->iterateAndNext(*this);
	nodep->precondsp()->iterateAndNext(*this);  // Need to recompute before next loop
	putfs(nodep,"end\n");
    }
    virtual void visit(AstNodeIf* nodep, AstNUser*) {
	putfs(nodep,"if (");
	nodep->condp()->iterateAndNext(*this);
	puts(") begin\n");
	nodep->ifsp()->iterateAndNext(*this);
	if (nodep->elsesp()) {
	    putfs(nodep,"end\n");
	    putfs(nodep,"else begin\n");
	    nodep->elsesp()->iterateAndNext(*this);
	}
	putfs(nodep,"end\n");
    }
    virtual void visit(AstStop* nodep, AstNUser*) {
	putfs(nodep,"$stop;\n");
    }
    virtual void visit(AstFinish* nodep, AstNUser*) {
	putfs(nodep,"$finish;\n");
    }
    virtual void visit(AstText* nodep, AstNUser*) {
	putsNoTracking(nodep->text());
    }
    virtual void visit(AstScopeName* nodep, AstNUser*) {
    }
    virtual void visit(AstCStmt* nodep, AstNUser*) {
	putfs(nodep,"$_CSTMT(");
	nodep->bodysp()->iterateAndNext(*this);
	puts(");\n");
    }
    virtual void visit(AstCMath* nodep, AstNUser*) {
	putfs(nodep,"$_CMATH(");
	nodep->bodysp()->iterateAndNext(*this);
	puts(");\n");
    }
    virtual void visit(AstUCStmt* nodep, AstNUser*) {
	putfs(nodep,"$c(");
	nodep->bodysp()->iterateAndNext(*this);
	puts(");\n");
    }
    virtual void visit(AstUCFunc* nodep, AstNUser*) {
	putfs(nodep,"$c(");
	nodep->bodysp()->iterateAndNext(*this); puts(")\n");
    }

    // Operators
    virtual void emitVerilogFormat(AstNode* nodep, const string& format,
				   AstNode* lhsp=NULL, AstNode* rhsp=NULL, AstNode* thsp=NULL) {
	// Look at emitVerilog() format for term/uni/dual/triops,
	// and write out appropriate text.
	//	%f	Potential fileline-if-change and line break
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
		case 'f': putfs(nodep,"");  break;
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
	putfs(nodep,"$_ATTROF(");
	nodep->fromp()->iterateAndNext(*this);
	puts(")");
    }
    virtual void visit(AstNodeCond* nodep, AstNUser*) {
	putbs("(");
	nodep->condp()->iterateAndNext(*this); putfs(nodep," ? ");
	nodep->expr1p()->iterateAndNext(*this); putbs(" : ");
	nodep->expr2p()->iterateAndNext(*this); puts(")");
    }
    virtual void visit(AstRange* nodep, AstNUser*) {
	puts("[");
	if (nodep->msbp()->castConst() && nodep->lsbp()->castConst()) {
	    // Looks nicer if we print [1:0] rather than [32'sh1:32sh0]
	    puts(cvtToStr(nodep->msbEndianedp()->castConst()->toSInt())); puts(":");
	    puts(cvtToStr(nodep->lsbEndianedp()->castConst()->toSInt())); puts("]");
	} else {
	    nodep->msbEndianedp()->iterateAndNext(*this); puts(":");
	    nodep->lsbEndianedp()->iterateAndNext(*this); puts("]");
	}
    }
    virtual void visit(AstSel* nodep, AstNUser*) {
	nodep->fromp()->iterateAndNext(*this); puts("[");
	if (nodep->lsbp()->castConst()) {
	    if (nodep->widthp()->isOne()) {
		if (nodep->lsbp()->castConst()) {
		    puts(cvtToStr(nodep->lsbp()->castConst()->toSInt()));
		} else {
		    nodep->lsbp()->iterateAndNext(*this);
		}
	    } else {
		puts(cvtToStr(nodep->lsbp()->castConst()->toSInt()
			      +nodep->widthp()->castConst()->toSInt()
			      -1));
		puts(":");
		puts(cvtToStr(nodep->lsbp()->castConst()->toSInt()));
	    }
	} else {
	    nodep->lsbp()->iterateAndNext(*this); putfs(nodep,"+:");
	    nodep->widthp()->iterateAndNext(*this); puts("]");
	}
	puts("]");
    }
    virtual void visit(AstTypedef* nodep, AstNUser*) {
	putfs(nodep,"typedef ");
	nodep->dtypep()->iterateAndNext(*this); puts(" ");
	puts(nodep->name());
	puts(";\n");
    }
    virtual void visit(AstBasicDType* nodep, AstNUser*) {
	if (nodep->isSigned()) putfs(nodep,"signed ");
	putfs(nodep,nodep->prettyName());
	if (nodep->rangep()) { nodep->rangep()->iterateAndNext(*this); puts(" "); }
    }
    virtual void visit(AstNodeFTaskRef* nodep, AstNUser*) {
	if (nodep->dotted()!="") { putfs(nodep,nodep->dotted()); puts("."); puts(nodep->name()); }
	else { putfs(nodep,nodep->name()); }
	puts("(");
	nodep->pinsp()->iterateAndNext(*this);
	puts(")");
    }
    // Terminals
    virtual void visit(AstVarRef* nodep, AstNUser*) {
	putfs(nodep,nodep->hiername());
	puts(nodep->varp()->name());
    }
    virtual void visit(AstVarXRef* nodep, AstNUser*) {
	putfs(nodep,nodep->dotted());
	puts(".");
	puts(nodep->varp()->name());
    }
    virtual void visit(AstConst* nodep, AstNUser*) {
	putfs(nodep,nodep->num().ascii(true,true));
    }

    // Just iterate
    virtual void visit(AstTopScope* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
    }
    virtual void visit(AstScope* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
    }
    virtual void visit(AstVar* nodep, AstNUser*) {
	putfs(nodep,nodep->verilogKwd());
	puts(" ");
	nodep->dtypep()->iterateChildren(*this); puts(" ");
	puts(nodep->name());
	puts(";\n");
    }
    virtual void visit(AstActive* nodep, AstNUser*) {
	m_sensesp = nodep->sensesp();
	nodep->iterateChildren(*this);
	m_sensesp = NULL;
    }
    virtual void visit(AstVarScope*, AstNUser*) {}
    virtual void visit(AstNodeText*, AstNUser*) {}
    virtual void visit(AstTraceDecl*, AstNUser*) {}
    virtual void visit(AstTraceInc*, AstNUser*) {}
    // NOPs
    virtual void visit(AstPragma*, AstNUser*) {}
    virtual void visit(AstCell*, AstNUser*) {}		// Handled outside the Visit class
    // Default
    virtual void visit(AstNode* nodep, AstNUser*) {
	puts((string)"\n???? // "+nodep->prettyTypeName()+"\n");
	nodep->iterateChildren(*this);
	// Not v3fatalSrc so we keep processing
	nodep->v3error("Internal: Unknown node type reached emitter: "<<nodep->prettyTypeName());
    }

public:
    EmitVBaseVisitor() {
	m_suppressSemi = false;
	m_sensesp = NULL;
    }
    virtual ~EmitVBaseVisitor() {}
};

//######################################################################
// Emit to an output file

class EmitVFileVisitor : public EmitVBaseVisitor {
    // MEMBERS
    V3OutFile*	m_ofp;
    // METHODS
    V3OutFile*	ofp() const { return m_ofp; }
    virtual void puts(const string& str) { ofp()->puts(str); }
    virtual void putbs(const string& str) { ofp()->putbs(str); }
    virtual void putfs(AstNode*, const string& str) { putbs(str); }
    virtual void putsNoTracking(const string& str) { ofp()->putsNoTracking(str); }
    
public:
    EmitVFileVisitor(AstNode* nodep, V3OutFile* ofp) {
	m_ofp = ofp;
	nodep->accept(*this);
    }
    virtual ~EmitVFileVisitor() {}
};

//######################################################################
// Emit to a stream (perhaps stringstream)

class EmitVStreamVisitor : public EmitVBaseVisitor {
    // MEMBERS
    ostream&	m_os;
    // METHODS
    virtual void puts(const string& str) { m_os<<str; }
    virtual void putbs(const string& str) { m_os<<str; }
    virtual void putfs(AstNode*, const string& str) { putbs(str); }
    virtual void putsNoTracking(const string& str) { m_os<<str; }
    
public:
    EmitVStreamVisitor(AstNode* nodep, ostream& os)
	: m_os(os) {
	nodep->accept(*this);
    }
    virtual ~EmitVStreamVisitor() {}
};

//######################################################################
// EmitV class functions

void V3EmitV::emitv() {
    UINFO(2,__FUNCTION__<<": "<<endl);
    if (1) {
	// All-in-one file
	V3OutVFile of (v3Global.opt.makeDir()+"/"+v3Global.opt.prefix()+"__Vout.v");
	of.putsHeader();
	of.puts("# DESCR" "IPTION: Verilator output: Verilog representation of internal tree for debug\n");
	EmitVFileVisitor visitor (v3Global.rootp(), &of);
    } else {
	// Process each module in turn
	for (AstNodeModule* modp = v3Global.rootp()->modulesp(); modp; modp=modp->nextp()->castNodeModule()) {
	    V3OutVFile of (v3Global.opt.makeDir()
			   +"/"+EmitCBaseVisitor::modClassName(modp)+"__Vout.v");
	    of.putsHeader();
	    EmitVFileVisitor visitor (modp, &of);
	}
    }
}

void V3EmitV::verilogForTree(AstNode* nodep, ostream& os) {
    EmitVStreamVisitor(nodep, os);
}
