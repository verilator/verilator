// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Emit Verilog from tree
//
// Code available from: http://www.veripool.org/verilator
//
//*************************************************************************
//
// Copyright 2004-2019 by Wilson Snyder.  This program is free software; you can
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

#include "V3Global.h"
#include "V3EmitV.h"
#include "V3EmitCBase.h"

#include <algorithm>
#include <cmath>
#include <cstdarg>
#include <map>
#include <vector>

//######################################################################
// Emit statements and math operators

class EmitVBaseVisitor : public EmitCBaseVisitor {
    // MEMBERS
    bool	m_suppressSemi;
    AstSenTree*	m_sensesp;

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
	putsNoTracking(V3Number::quoteNameControls(str));
	putsNoTracking("\"");
    }

    // VISITORS
    virtual void visit(AstNetlist* nodep) {
        iterateChildren(nodep);
    }
    virtual void visit(AstNodeModule* nodep) {
	putfs(nodep, nodep->verilogKwd()+" "+modClassName(nodep)+";\n");
        iterateChildren(nodep);
	putqs(nodep, "end"+nodep->verilogKwd()+"\n");
    }
    virtual void visit(AstNodeFTask* nodep) {
	putfs(nodep, nodep->isFunction() ? "function":"task");
	puts(" ");
	puts(nodep->prettyName());
	puts(";\n");
	putqs(nodep, "begin\n");  // Only putfs the first time for each visitor; later for same node is putqs
        iterateAndNextNull(nodep->stmtsp());
	putqs(nodep, "end\n");
    }

    virtual void visit(AstBegin* nodep) {
	if (nodep->unnamed()) {
	    putbs("begin\n");
	} else {
	    putbs("begin : "+nodep->name()+"\n");
	}
        iterateChildren(nodep);
	puts("end\n");
    }
    virtual void visit(AstGenerate* nodep) {
	putfs(nodep, "generate\n");
        iterateChildren(nodep);
	putqs(nodep, "end\n");
    }
    virtual void visit(AstFinal* nodep) {
	putfs(nodep, "final begin\n");
        iterateChildren(nodep);
	putqs(nodep, "end\n");
    }
    virtual void visit(AstInitial* nodep) {
	putfs(nodep,"initial begin\n");
        iterateChildren(nodep);
	putqs(nodep, "end\n");
    }
    virtual void visit(AstAlways* nodep) {
	putfs(nodep,"always ");
        if (m_sensesp) iterateAndNextNull(m_sensesp);  // In active
        else iterateAndNextNull(nodep->sensesp());
	putbs(" begin\n");
        iterateAndNextNull(nodep->bodysp());
	putqs(nodep,"end\n");
    }
    virtual void visit(AstAlwaysPublic* nodep) {
	putfs(nodep,"/*verilator public_flat_rw ");
        if (m_sensesp) iterateAndNextNull(m_sensesp);  // In active
        else iterateAndNextNull(nodep->sensesp());
	putqs(nodep," ");
        iterateAndNextNull(nodep->bodysp());
	putqs(nodep,"*/\n");
    }
    virtual void visit(AstNodeAssign* nodep) {
        iterateAndNextNull(nodep->lhsp());
	putfs(nodep," "+nodep->verilogKwd()+" ");
        iterateAndNextNull(nodep->rhsp());
	if (!m_suppressSemi) puts(";\n");
    }
    virtual void visit(AstAssignDly* nodep) {
        iterateAndNextNull(nodep->lhsp());
	putfs(nodep," <= ");
        iterateAndNextNull(nodep->rhsp());
	puts(";\n");
    }
    virtual void visit(AstAssignAlias* nodep) {
	putbs("alias ");
        iterateAndNextNull(nodep->lhsp());
	putfs(nodep," = ");
        iterateAndNextNull(nodep->rhsp());
	if (!m_suppressSemi) puts(";\n");
    }
    virtual void visit(AstAssignW* nodep) {
	putfs(nodep,"assign ");
        iterateAndNextNull(nodep->lhsp());
	putbs(" = ");
        iterateAndNextNull(nodep->rhsp());
	if (!m_suppressSemi) puts(";\n");
    }
    virtual void visit(AstBreak* nodep) {
	putbs("break");
	if (!m_suppressSemi) puts(";\n");
    }
    virtual void visit(AstSenTree* nodep) {
	// AstSenItem is called for dumping in isolation by V3Order
	putfs(nodep,"@(");
	for (AstNode* expp=nodep->sensesp(); expp; expp = expp->nextp()) {
            iterate(expp);
	    if (expp->nextp()) putqs(expp->nextp()," or ");
	}
	puts(")");
    }
    virtual void visit(AstSenGate* nodep) {
	emitVerilogFormat(nodep, nodep->emitVerilog(), nodep->sensesp(), nodep->rhsp());
    }
    virtual void visit(AstSenItem* nodep) {
	putfs(nodep,"");
	puts(nodep->edgeType().verilogKwd());
	if (nodep->sensp()) puts(" ");
        iterateChildren(nodep);
    }
    virtual void visit(AstNodeCase* nodep) {
	putfs(nodep,"");
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
	putqs(nodep,"endcase\n");
    }
    virtual void visit(AstCaseItem* nodep) {
	if (nodep->condsp()) {
            iterateAndNextNull(nodep->condsp());
	} else putbs("default");
	putfs(nodep,": begin ");
        iterateAndNextNull(nodep->bodysp());
	putqs(nodep,"end\n");
    }
    virtual void visit(AstComment* nodep) {
        puts(string("// ")+nodep->name()+"\n");
        iterateChildren(nodep);
    }
    virtual void visit(AstContinue* nodep) {
	putbs("continue");
	if (!m_suppressSemi) puts(";\n");
    }
    virtual void visit(AstCoverDecl*) {}  // N/A
    virtual void visit(AstCoverInc*) {}  // N/A
    virtual void visit(AstCoverToggle*) {}  // N/A

    void visitNodeDisplay(AstNode* nodep, AstNode* fileOrStrgp, const string& text, AstNode* exprsp) {
	putfs(nodep,nodep->verilogKwd());
	putbs(" (");
        if (fileOrStrgp) { iterateAndNextNull(fileOrStrgp); putbs(","); }
	putsQuoted(text);
	for (AstNode* expp=exprsp; expp; expp = expp->nextp()) {
	    puts(",");
            iterateAndNextNull(expp);
	}
	puts(");\n");
    }
    virtual void visit(AstDisable* nodep) {
	putbs("disable "+nodep->name()+";\n");
    }
    virtual void visit(AstDisplay* nodep) {
	visitNodeDisplay(nodep, nodep->filep(), nodep->fmtp()->text(), nodep->fmtp()->exprsp());
    }
    virtual void visit(AstFScanF* nodep) {
	visitNodeDisplay(nodep, nodep->filep(), nodep->text(), nodep->exprsp());
    }
    virtual void visit(AstSScanF* nodep) {
	visitNodeDisplay(nodep, nodep->fromp(), nodep->text(), nodep->exprsp());
    }
    virtual void visit(AstSFormat* nodep) {
	visitNodeDisplay(nodep, nodep->lhsp(), nodep->fmtp()->text(), nodep->fmtp()->exprsp());
    }
    virtual void visit(AstSFormatF* nodep) {
	visitNodeDisplay(nodep, NULL, nodep->text(), nodep->exprsp());
    }
    virtual void visit(AstFOpen* nodep) {
	putfs(nodep,nodep->verilogKwd());
	putbs(" (");
        if (nodep->filep()) iterateAndNextNull(nodep->filep());
	putbs(",");
        if (nodep->filenamep()) iterateAndNextNull(nodep->filenamep());
	putbs(",");
        if (nodep->modep()) iterateAndNextNull(nodep->modep());
	puts(");\n");
    }
    virtual void visit(AstFClose* nodep) {
	putfs(nodep,nodep->verilogKwd());
	putbs(" (");
        if (nodep->filep()) iterateAndNextNull(nodep->filep());
	puts(");\n");
    }
    virtual void visit(AstFFlush* nodep) {
	putfs(nodep,nodep->verilogKwd());
	putbs(" (");
        if (nodep->filep()) iterateAndNextNull(nodep->filep());
	puts(");\n");
    }
    virtual void visit(AstJumpGo* nodep) {
        putbs("disable "+cvtToHex(nodep->labelp())+";\n");
    }
    virtual void visit(AstJumpLabel* nodep) {
        putbs("begin : "+cvtToHex(nodep)+"\n");
        if (nodep->stmtsp()) iterateAndNextNull(nodep->stmtsp());
	puts("end\n");
    }
    virtual void visit(AstNodeReadWriteMem* nodep) {
	putfs(nodep,nodep->verilogKwd());
	putbs(" (");
        if (nodep->filenamep()) iterateAndNextNull(nodep->filenamep());
	putbs(",");
        if (nodep->memp()) iterateAndNextNull(nodep->memp());
        if (nodep->lsbp()) { putbs(","); iterateAndNextNull(nodep->lsbp()); }
        if (nodep->msbp()) { putbs(","); iterateAndNextNull(nodep->msbp()); }
	puts(");\n");
    }
    virtual void visit(AstSysFuncAsTask* nodep) {
        iterateAndNextNull(nodep->lhsp());
        puts(";\n");
    }
    virtual void visit(AstSysIgnore* nodep) {
	putfs(nodep,nodep->verilogKwd());
	putbs(" (");
        iterateAndNextNull(nodep->exprsp());
	puts(");\n");
    }
    virtual void visit(AstNodeFor* nodep) {
	putfs(nodep,"for (");
	m_suppressSemi = true;
        iterateAndNextNull(nodep->initsp());
	puts(";");
        iterateAndNextNull(nodep->condp());
	puts(";");
        iterateAndNextNull(nodep->incsp());
	m_suppressSemi = false;
	puts(") begin\n");
        iterateAndNextNull(nodep->bodysp());
	putqs(nodep,"end\n");
    }
    virtual void visit(AstRepeat* nodep) {
	putfs(nodep,"repeat (");
        iterateAndNextNull(nodep->countp());
	puts(") begin\n");
        iterateAndNextNull(nodep->bodysp());
	putfs(nodep,"end\n");
    }
    virtual void visit(AstWhile* nodep) {
        iterateAndNextNull(nodep->precondsp());
	putfs(nodep,"while (");
        iterateAndNextNull(nodep->condp());
	puts(") begin\n");
        iterateAndNextNull(nodep->bodysp());
        iterateAndNextNull(nodep->incsp());
        iterateAndNextNull(nodep->precondsp());  // Need to recompute before next loop
	putfs(nodep,"end\n");
    }
    virtual void visit(AstNodeIf* nodep) {
	putfs(nodep,"");
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
	    putqs(nodep,"end\n");
	    putqs(nodep,"else begin\n");
            iterateAndNextNull(nodep->elsesp());
	}
	putqs(nodep,"end\n");
    }
    virtual void visit(AstPast* nodep) {
        putfs(nodep, "$past(");
        iterateAndNextNull(nodep->exprp());
        if (nodep->ticksp()) {
            puts(",");
            iterateAndNextNull(nodep->ticksp());
        }
        puts(")");
    }
    virtual void visit(AstReturn* nodep) {
	putfs(nodep,"return ");
        iterateAndNextNull(nodep->lhsp());
	puts(";\n");
    }
    virtual void visit(AstStop* nodep) {
	putfs(nodep,"$stop;\n");
    }
    virtual void visit(AstFinish* nodep) {
	putfs(nodep,"$finish;\n");
    }
    virtual void visit(AstText* nodep) {
	putsNoTracking(nodep->text());
    }
    virtual void visit(AstScopeName* nodep) {
    }
    virtual void visit(AstCStmt* nodep) {
	putfs(nodep,"$_CSTMT(");
        iterateAndNextNull(nodep->bodysp());
	puts(");\n");
    }
    virtual void visit(AstCMath* nodep) {
	putfs(nodep,"$_CMATH(");
        iterateAndNextNull(nodep->bodysp());
	puts(");\n");
    }
    virtual void visit(AstUCStmt* nodep) {
	putfs(nodep,"$c(");
        iterateAndNextNull(nodep->bodysp());
	puts(");\n");
    }
    virtual void visit(AstUCFunc* nodep) {
	putfs(nodep,"$c(");
        iterateAndNextNull(nodep->bodysp());
	puts(")");
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
	//	%d	dtypep - if appropriate
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
                    else iterateAndNextNull(lhsp);
		    break;
		}
		case 'r': {
		    if (!rhsp) { nodep->v3fatalSrc("emitVerilog() references undef node"); }
                    else iterateAndNextNull(rhsp);
		    break;
		}
		case 't': {
		    if (!thsp) { nodep->v3fatalSrc("emitVerilog() references undef node"); }
                    else iterateAndNextNull(thsp);
		    break;
		}
		case 'd': {
		    if (!nodep->dtypep()) { nodep->v3fatalSrc("emitVerilog() references undef node"); }
                    else iterateAndNextNull(nodep->dtypep());
		    break;
		}
		default:
		    nodep->v3fatalSrc("Unknown emitVerilog format code: %"<<pos[0]);
		    break;
		}
            }
        }
    }

    virtual void visit(AstNodeTermop* nodep) {
	emitVerilogFormat(nodep, nodep->emitVerilog());
    }
    virtual void visit(AstNodeUniop* nodep) {
	emitVerilogFormat(nodep, nodep->emitVerilog(), nodep->lhsp());
    }
    virtual void visit(AstNodeBiop* nodep) {
	emitVerilogFormat(nodep, nodep->emitVerilog(), nodep->lhsp(), nodep->rhsp());
    }
    virtual void visit(AstNodeTriop* nodep) {
	emitVerilogFormat(nodep, nodep->emitVerilog(), nodep->lhsp(), nodep->rhsp(), nodep->thsp());
    }
    virtual void visit(AstAttrOf* nodep) {
	putfs(nodep,"$_ATTROF(");
        iterateAndNextNull(nodep->fromp());
	if (nodep->dimp()) {
	    putbs(",");
            iterateAndNextNull(nodep->dimp());
	}
	puts(")");
    }
    virtual void visit(AstInitArray* nodep) {
	putfs(nodep,"`{");
	int pos = 0;
	for (AstNode* itemp = nodep->initsp(); itemp; ++pos, itemp=itemp->nextp()) {
	    int index = nodep->posIndex(pos);
	    puts(cvtToStr(index));
	    puts(":");
            iterate(itemp);
	    if (itemp->nextp()) putbs(",");
	}
	puts("}");
    }
    virtual void visit(AstNodeCond* nodep) {
	putbs("(");
        iterateAndNextNull(nodep->condp()); putfs(nodep," ? ");
        iterateAndNextNull(nodep->expr1p()); putbs(" : ");
        iterateAndNextNull(nodep->expr2p()); puts(")");
    }
    virtual void visit(AstRange* nodep) {
	puts("[");
        if (VN_IS(nodep->msbp(), Const) && VN_IS(nodep->lsbp(), Const)) {
	    // Looks nicer if we print [1:0] rather than [32'sh1:32sh0]
            puts(cvtToStr(VN_CAST(nodep->leftp(), Const)->toSInt())); puts(":");
            puts(cvtToStr(VN_CAST(nodep->rightp(), Const)->toSInt())); puts("]");
	} else {
            iterateAndNextNull(nodep->leftp()); puts(":");
            iterateAndNextNull(nodep->rightp()); puts("]");
	}
    }
    virtual void visit(AstSel* nodep) {
        iterateAndNextNull(nodep->fromp()); puts("[");
        if (VN_IS(nodep->lsbp(), Const)) {
	    if (nodep->widthp()->isOne()) {
                if (VN_IS(nodep->lsbp(), Const)) {
                    puts(cvtToStr(VN_CAST(nodep->lsbp(), Const)->toSInt()));
		} else {
                    iterateAndNextNull(nodep->lsbp());
		}
	    } else {
                puts(cvtToStr(VN_CAST(nodep->lsbp(), Const)->toSInt()
                              + VN_CAST(nodep->widthp(), Const)->toSInt()
                              - 1));
		puts(":");
                puts(cvtToStr(VN_CAST(nodep->lsbp(), Const)->toSInt()));
	    }
	} else {
            iterateAndNextNull(nodep->lsbp()); putfs(nodep,"+:");
            iterateAndNextNull(nodep->widthp()); puts("]");
	}
	puts("]");
    }
    virtual void visit(AstSliceSel* nodep) {
        iterateAndNextNull(nodep->fromp());
        puts(cvtToStr(nodep->declRange()));
    }
    virtual void visit(AstTypedef* nodep) {
	putfs(nodep,"typedef ");
        iterateAndNextNull(nodep->dtypep()); puts(" ");
	puts(nodep->prettyName());
	puts(";\n");
    }
    virtual void visit(AstBasicDType* nodep) {
	if (nodep->isSigned()) putfs(nodep,"signed ");
	putfs(nodep,nodep->prettyName());
        if (nodep->rangep()) { puts(" "); iterateAndNextNull(nodep->rangep()); puts(" "); }
	else if (nodep->isRanged()) { puts(" ["); puts(cvtToStr(nodep->msb())); puts(":0] "); }
    }
    virtual void visit(AstConstDType* nodep) {
	putfs(nodep,"const ");
        iterate(nodep->subDTypep());
    }
    virtual void visit(AstNodeArrayDType* nodep) {
        iterate(nodep->subDTypep());
        iterateAndNextNull(nodep->rangep());
    }
    virtual void visit(AstNodeClassDType* nodep) {
	puts(nodep->verilogKwd()+" ");
	if (nodep->packed()) puts("packed ");
	puts("\n");
        iterateAndNextNull(nodep->membersp());
	puts("}");
    }
    virtual void visit(AstMemberDType* nodep) {
        iterate(nodep->subDTypep());
	puts(" ");
	puts(nodep->name());
	puts("}");
    }
    virtual void visit(AstNodeFTaskRef* nodep) {
	if (nodep->dotted()!="") { putfs(nodep,nodep->dotted()); puts("."); puts(nodep->prettyName()); }
	else { putfs(nodep,nodep->prettyName()); }
	puts("(");
        iterateAndNextNull(nodep->pinsp());
	puts(")");
    }
    virtual void visit(AstArg* nodep) {
        iterateAndNextNull(nodep->exprp());
    }
    // Terminals
    virtual void visit(AstVarRef* nodep) {
        if (nodep->varScopep()) {
	    putfs(nodep,nodep->varScopep()->prettyName());
        } else {
	    putfs(nodep,nodep->hiername());
	    puts(nodep->varp()->prettyName());
	}
    }
    virtual void visit(AstVarXRef* nodep) {
	putfs(nodep,nodep->dotted());
	puts(".");
	puts(nodep->varp()->prettyName());
    }
    virtual void visit(AstConst* nodep) {
	putfs(nodep,nodep->num().ascii(true,true));
    }

    // Just iterate
    virtual void visit(AstTopScope* nodep) {
        iterateChildren(nodep);
    }
    virtual void visit(AstScope* nodep) {
        iterateChildren(nodep);
    }
    virtual void visit(AstVar* nodep) {
	putfs(nodep,nodep->verilogKwd());
	puts(" ");
        iterate(nodep->dtypep()); puts(" ");
	puts(nodep->prettyName());
	puts(";\n");
    }
    virtual void visit(AstActive* nodep) {
	m_sensesp = nodep->sensesp();
        iterateAndNextNull(nodep->stmtsp());
	m_sensesp = NULL;
    }
    virtual void visit(AstVarScope*) {}
    virtual void visit(AstNodeText*) {}
    virtual void visit(AstTraceDecl*) {}
    virtual void visit(AstTraceInc*) {}
    // NOPs
    virtual void visit(AstPragma*) {}
    virtual void visit(AstCell*) {}		// Handled outside the Visit class
    // Default
    virtual void visit(AstNode* nodep) {
        puts(string("\n???? // ")+nodep->prettyTypeName()+"\n");
        iterateChildren(nodep);
	// Not v3fatalSrc so we keep processing
	nodep->v3error("Internal: Unknown node type reached emitter: "<<nodep->prettyTypeName());
    }

public:
    explicit EmitVBaseVisitor(AstSenTree* domainp=NULL) {   // Domain for printing one a ALWAYS under a ACTIVE
	m_suppressSemi = false;
	m_sensesp = domainp;
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
    virtual void putqs(AstNode*, const string& str) { putbs(str); }
    virtual void putsNoTracking(const string& str) { ofp()->putsNoTracking(str); }
public:
    EmitVFileVisitor(AstNode* nodep, V3OutFile* ofp) {
	m_ofp = ofp;
        iterate(nodep);
    }
    virtual ~EmitVFileVisitor() {}
};

//######################################################################
// Emit to a stream (perhaps stringstream)

class EmitVStreamVisitor : public EmitVBaseVisitor {
    // MEMBERS
    std::ostream&       m_os;
    // METHODS
    virtual void putsNoTracking(const string& str) { m_os<<str; }
    virtual void puts(const string& str) { putsNoTracking(str); }
    virtual void putbs(const string& str) { puts(str); }
    virtual void putfs(AstNode*, const string& str) { putbs(str); }
    virtual void putqs(AstNode*, const string& str) { putbs(str); }
public:
    EmitVStreamVisitor(AstNode* nodep, std::ostream& os)
	: m_os(os) {
        iterate(nodep);
    }
    virtual ~EmitVStreamVisitor() {}
};

//######################################################################
// Emit to a stream (perhaps stringstream)

class EmitVPrefixedFormatter : public V3OutFormatter {
    std::ostream&       m_os;
    string	m_prefix;	// What to print at beginning of each line
    int		m_flWidth;	// Padding of fileline
    int		m_column;	// Rough location; need just zero or non-zero
    FileLine*	m_prefixFl;
    // METHODS
    virtual void putcOutput(char chr) {
	if (chr == '\n') {
	    m_column = 0;
	    m_os<<chr;
	} else {
	    if (m_column == 0) {
		m_column = 10;
		m_os<<m_prefixFl->ascii()+":";
		m_os<<V3OutFile::indentSpaces(m_flWidth-(m_prefixFl->ascii().length()+1));
		m_os<<" ";
		m_os<<m_prefix;
	    }
	    m_column++;
	    m_os<<chr;
	}
    }
public:
    void prefixFl(FileLine* fl) { m_prefixFl = fl; }
    FileLine* prefixFl() const { return m_prefixFl; }
    int column() const { return m_column; }
    EmitVPrefixedFormatter(std::ostream& os, const string& prefix, int flWidth)
	: V3OutFormatter("__STREAM", V3OutFormatter::LA_VERILOG)
	, m_os(os), m_prefix(prefix), m_flWidth(flWidth) {
	m_column = 0;
	m_prefixFl = v3Global.rootp()->fileline();  // NETLIST's fileline instead of NULL to avoid NULL checks
    }
    virtual ~EmitVPrefixedFormatter() {
	if (m_column) puts("\n");
    }
};

class EmitVPrefixedVisitor : public EmitVBaseVisitor {
    // MEMBERS
    EmitVPrefixedFormatter m_formatter; // Special verilog formatter (Way down the inheritance is another unused V3OutFormatter)
    // METHODS
    virtual void putsNoTracking(const string& str) { m_formatter.putsNoTracking(str); }
    virtual void puts(const string& str) { m_formatter.puts(str); }
    // We don't use m_formatter's putbs because the tokens will change filelines
    // and insert returns at the proper locations
    virtual void putbs(const string& str) { m_formatter.puts(str); }
    virtual void putfs(AstNode* nodep, const string& str) { putfsqs(nodep,str,false); }
    virtual void putqs(AstNode* nodep, const string& str) { putfsqs(nodep,str,true); }
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
	: EmitVBaseVisitor(domainp), m_formatter(os, prefix, flWidth) {
	if (user3mark) { AstUser3InUse::check(); }
        iterate(nodep);
    }
    virtual ~EmitVPrefixedVisitor() {}
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
        for (AstNodeModule* modp = v3Global.rootp()->modulesp(); modp; modp=VN_CAST(modp->nextp(), NodeModule)) {
	    V3OutVFile of (v3Global.opt.makeDir()
			   +"/"+EmitCBaseVisitor::modClassName(modp)+"__Vout.v");
	    of.putsHeader();
	    EmitVFileVisitor visitor (modp, &of);
	}
    }
}

void V3EmitV::verilogForTree(AstNode* nodep, std::ostream& os) {
    EmitVStreamVisitor(nodep, os);
}

void V3EmitV::verilogPrefixedTree(AstNode* nodep, std::ostream& os, const string& prefix, int flWidth,
				  AstSenTree* domainp, bool user3mark) {
    EmitVPrefixedVisitor(nodep, os, prefix, flWidth, domainp, user3mark);
}
