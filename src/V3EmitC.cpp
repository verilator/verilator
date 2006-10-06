// $Id$
//*************************************************************************
// DESCRIPTION: Verilator: Emit C++ for tree
//
// Code available from: http://www.veripool.com/verilator
//
// AUTHORS: Wilson Snyder with Paul Wasson, Duane Gabli
//
//*************************************************************************
//
// Copyright 2003-2006 by Wilson Snyder.  This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// General Public License or the Perl Artistic License.
//
// Verilator is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
//*************************************************************************

#include "config.h"
#include <stdio.h>
#include <stdarg.h>
#include <unistd.h>
#include <math.h>
#include <map>
#include <vector>
#include <algorithm>

#include "V3Global.h"
#include "V3EmitC.h"
#include "V3EmitCBase.h"

#define VL_VALUE_STRING_MAX_WIDTH 1024	// We use a static char array in VL_VALUE_STRING

//######################################################################
// Coverage ID tracking

class EmitCoverIds {
    // TYPES
    typedef map<AstCoverDecl*,int> CoverIdMap;
    // MEMBERS
    CoverIdMap	m_coverIds;	// Remapping of coverage IDs to per-module value
    int		m_coverIdsSize;	// Size of m_coverIds (to avoid O(n^2) insert)
    // METHODS
public:
    void clear() {
	m_coverIds.clear();
	m_coverIdsSize = 0;
    }
    int size() const { return m_coverIdsSize; }
    int remap(AstCoverDecl* declp) {
	// Make cover ID for this point, unique on this module
	CoverIdMap::iterator it = m_coverIds.find(declp);
	if (it == m_coverIds.end()) {
	    m_coverIds.insert(make_pair(declp,m_coverIdsSize++));	// Remapping of coverage IDs to per-module value
	    return m_coverIdsSize-1;
	} else {
	    return it->second;
	}
    }
    EmitCoverIds() : m_coverIdsSize(0) {}
    ~EmitCoverIds() {}
};

//######################################################################
// Emit statements and math operators

class EmitCStmts : public EmitCBaseVisitor {
private:
    bool	m_suppressSemi;
    AstVarRef*	m_wideTempRefp;		// Variable that _WW macros should be setting
    vector<AstVar*>		m_ctorVarsVec;		// All variables in constructor order
public:
    EmitCoverIds m_coverIds;	// Coverage ID remapping
public:
    //int debug() { return 9; }

    // METHODS
    void displayEmit(AstDisplay* nodep);
    string displayFormat(AstNode* widthNode, string in, 
			 char fmtLetter, bool padZero, bool reallyString);
    void displayArg(AstDisplay* dispp, AstNode** elistp, string fmt, char fmtLetter); 

    void emitVarDecl(AstVar* nodep, const string& prefixIfImp);
    typedef enum {EVL_IO, EVL_SIG, EVL_TEMP, EVL_STATIC, EVL_ALL} EisWhich;
    void emitVarList(AstNode* firstp, EisWhich which, const string& prefixIfImp);
    void emitVarCtors();
    bool emitSimpleOk(AstNodeMath* nodep);
    void emitIQW(AstNode* nodep) {
	puts (nodep->isWide()?"W":(nodep->isQuad()?"Q":"I"));
    }
    void emitOpName(AstNode* nodep, const string& name);

    string cFuncArgs(AstCFunc* nodep) {
	// Return argument list for given C function
	string args = nodep->argTypes();
	if (args=="") {
	    // Might be a user function with argument list.
	    for (AstNode* stmtp = nodep->argsp(); stmtp; stmtp=stmtp->nextp()) {
		if (AstVar* portp = stmtp->castVar()) {
		    if (portp->isIO() && !portp->isFuncReturn()) {
			if (args != "") args+= ", ";
			if (portp->isWide()) {
			    if (portp->isInOnly()) args += "const ";
			    args += portp->cType();
			    args += " (& "+portp->name();
			    args += ")["+cvtToStr(portp->widthWords())+"]";
			} else {
			    args += portp->cType();
			    if (portp->isOutput()) args += "&";
			    args += " "+portp->name();
			}
		    }
		}
	    }
	}
	return args;
    }

    // VISITORS
    virtual void visit(AstNodeAssign* nodep, AstNUser*) {
	bool paren = true;  bool decind = false;
	if (AstSel* selp=nodep->lhsp()->castSel()) {
	    if (selp->widthMin()==1) {
		putbs("VL_ASSIGNBIT_");
		emitIQW(selp->fromp());
		if (nodep->rhsp()->isAllOnesV()) {
		    putbs("O(");
		} else {
		    putbs("I(");
		}
		puts(cvtToStr(nodep->widthMin())+",");
		selp->lsbp()->iterateAndNext(*this); puts(", ");
		selp->fromp()->iterateAndNext(*this); puts(", ");
	    } else {
		putbs("VL_ASSIGNSEL_");
		emitIQW (selp->fromp());
		putbs("II");
		emitIQW(nodep->rhsp());
		puts("(");
		puts(cvtToStr(nodep->widthMin())+",");
		selp->lsbp()->iterateAndNext(*this); puts(", ");
		selp->fromp()->iterateAndNext(*this); puts(", ");
	    }
	} else if (nodep->lhsp()->castVarRef()
		   && nodep->lhsp()->castVarRef()->varp()->isSc()) {
	    putbs("VL_ASSIGN_"); 	// Set a systemC variable
	    if (nodep->lhsp()->castVarRef()->varp()->isScQuad()) puts("SQ");
	    else  puts("S");
	    emitIQW(nodep);
	    puts("(");
	    puts(cvtToStr(nodep->widthMin())+",");
	    nodep->lhsp()->iterateAndNext(*this); puts(", ");
	} else if (nodep->rhsp()->castVarRef()
		   && nodep->rhsp()->castVarRef()->varp()->isSc()) {
	    putbs("VL_ASSIGN_"); 	// Get a systemC variable
	    emitIQW(nodep);
	    if (nodep->rhsp()->castVarRef()->varp()->isScQuad()) puts("SQ(");
	    else puts("S(");
	    puts(cvtToStr(nodep->widthMin())+",");
	    nodep->lhsp()->iterateAndNext(*this); puts(", ");
	} else if (nodep->isWide()
		   && nodep->lhsp()->castVarRef()
		   && !nodep->rhsp()->castVarRef()
		   && !nodep->rhsp()->castArraySel()) {
	    // Wide functions assign into the array directly, don't need separate assign statement
	    m_wideTempRefp = nodep->lhsp()->castVarRef();
	    paren = false;
	} else if (nodep->isWide()) {
	    putbs("VL_ASSIGN_W(");
	    puts(cvtToStr(nodep->widthMin())+",");
	    nodep->lhsp()->iterateAndNext(*this); puts(", ");
	} else {
	    paren = false;
	    nodep->lhsp()->iterateAndNext(*this);
	    puts(" ");
	    ofp()->blockInc(); decind = true;
	    if (!nodep->rhsp()->castConst()) ofp()->putBreak();
	    puts("= ");
	}
	nodep->rhsp()->iterateAndNext(*this);
	if (paren) puts(")");
	if (decind) ofp()->blockDec();
	if (!m_suppressSemi) puts(";\n");
    }
    virtual void visit(AstCCall* nodep, AstNUser*) {
	puts(nodep->hiername());
	puts(nodep->funcp()->name());
	puts("(");
	puts(nodep->argTypes());
	bool comma = (nodep->argTypes() != "");
	for (AstNode* subnodep=nodep->argsp(); subnodep; subnodep = subnodep->nextp()) {
	    if (comma) puts(", ");
	    subnodep->accept(*this);
	    comma = true;
	}
	if (nodep->backp()->castNodeMath() || nodep->backp()->castCReturn()) {
	    // We should have a separate CCall for math and statement usage, but...
	    puts(")");
	} else {
	    puts(");\n");
	}
    }
    virtual void visit(AstNodeCase* nodep, AstNUser*) {
	// In V3Case...
	nodep->v3fatalSrc("Case statements should have been reduced out\n");
    }
    virtual void visit(AstComment* nodep, AstNUser*) {
	puts((string)"// "+nodep->name()+" at "+nodep->fileline()->ascii()+"\n");
	nodep->iterateChildren(*this);
    }
    virtual void visit(AstCoverDecl* nodep, AstNUser*) {
	puts("__vlCoverInsert(");	// As Declared in emitCoverageDecl
	puts("&__Vcoverage["); 	
	puts(cvtToStr(m_coverIds.remap(nodep))); puts("]");
	puts(", \"");	puts(nodep->fileline()->filebasename()); puts("\"");
	puts(", ");	puts(cvtToStr(nodep->fileline()->lineno()));
	puts(", ");	puts(cvtToStr(nodep->column()));
	puts(", \"");	puts(nodep->hier()); puts("\"");
	puts(", \"");	puts(nodep->typeText()); puts("\"");
	puts(", \"");	puts(nodep->comment()); puts("\"");
	puts(");\n");
    }
    virtual void visit(AstCoverInc* nodep, AstNUser*) {
	puts("++this->__Vcoverage[");
	puts(cvtToStr(m_coverIds.remap(nodep->declp()))); puts("];\n");
    }
    virtual void visit(AstCReturn* nodep, AstNUser*) {
	puts("return (");
	nodep->lhsp()->iterateAndNext(*this);
	puts(");\n");
    }
    virtual void visit(AstDisplay* nodep, AstNUser*);  // BELOW
    virtual void visit(AstFOpen* nodep, AstNUser*) {
	nodep->filep()->iterateAndNext(*this);
	puts(" = VL_FOPEN_");
	emitIQW(nodep->filenamep());
	emitIQW(nodep->modep());
	if (nodep->modep()->width()>4*8) nodep->modep()->v3error("$fopen mode should be <= 4 characters");
	puts("(");
	if (nodep->filenamep()->isWide()) puts(cvtToStr(nodep->filenamep()->widthWords()));
	if (nodep->filenamep()->widthWords() > VL_TO_STRING_MAX_WORDS) {
	    nodep->v3error("String of "<<nodep->filenamep()->width()<<" bits exceeds hardcoded limit VL_TO_STRING_MAX_WORDS in verilatedos.h\n");
	}
	putbs(", ");
	nodep->filenamep()->iterateAndNext(*this);
	putbs(", ");
	nodep->modep()->iterateAndNext(*this);
	puts(");\n");
    }
    virtual void visit(AstFClose* nodep, AstNUser*) {
	puts("if (");
	nodep->filep()->iterateAndNext(*this);
	puts(") { fclose (VL_CVT_Q_FP(");
	nodep->filep()->iterateAndNext(*this);
	puts(")); ");
	nodep->filep()->iterateAndNext(*this);	// For saftey, so user doesn't later WRITE with it.
	puts("=0; }\n");
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
	if (nodep->branchPred() != AstBranchPred::UNKNOWN) {
	    puts(nodep->branchPred().ascii()); puts("(");
	}
	nodep->condp()->iterateAndNext(*this);
	if (nodep->branchPred() != AstBranchPred::UNKNOWN) puts(")");
	puts(") {\n");
	nodep->ifsp()->iterateAndNext(*this);
	if (nodep->elsesp()) {
	    puts("} else {\n");
	    nodep->elsesp()->iterateAndNext(*this);
	}
	puts("}\n");
    }
    virtual void visit(AstStop* nodep, AstNUser*) {
	puts("vl_stop(\"");
	puts(nodep->fileline()->filename());
	puts("\",");
	puts(cvtToStr(nodep->fileline()->lineno()));
	puts(",\"\");\n");
    }
    virtual void visit(AstFinish* nodep, AstNUser*) {
	puts("vl_finish(\"");
	puts(nodep->fileline()->filename());
	puts("\",");
	puts(cvtToStr(nodep->fileline()->lineno()));
	puts(",\"\");\n");
    }
    virtual void visit(AstText* nodep, AstNUser*) {
	ofp()->putsNoTracking(nodep->text());
    }
    virtual void visit(AstCStmt* nodep, AstNUser*) {
	nodep->bodysp()->iterateAndNext(*this);
    }
    virtual void visit(AstCMath* nodep, AstNUser*) {
	nodep->bodysp()->iterateAndNext(*this);
    }
    virtual void visit(AstUCStmt* nodep, AstNUser*) {
	puts("// $c statement at "+nodep->fileline()->ascii()+"\n");
	nodep->bodysp()->iterateAndNext(*this);
	puts("\n");
    }
    virtual void visit(AstUCFunc* nodep, AstNUser*) {
	puts("\n");
	puts("// $c function at "+nodep->fileline()->ascii()+"\n");
	nodep->bodysp()->iterateAndNext(*this);
	puts("\n");
    }

    // Operators
    virtual void visit(AstNodeTermop* nodep, AstNUser*) {
	emitOpName(nodep,nodep->emitOperator());
	puts(")");
    }
    virtual void visit(AstNodeUniop* nodep, AstNUser*) {
	if (emitSimpleOk(nodep)) {
	    putbs("("); puts(nodep->emitSimpleOperator()); puts(" ");
	} else {
	    emitOpName(nodep,nodep->emitOperator());
	}
	nodep->lhsp()->iterateAndNext(*this); puts(")");
    }
    virtual void visit(AstNodeBiop* nodep, AstNUser*) {
	if (emitSimpleOk(nodep)) {
	    putbs("("); nodep->lhsp()->iterateAndNext(*this);
	    puts(" "); putbs(nodep->emitSimpleOperator()); puts(" ");
	} else {
	    emitOpName(nodep,nodep->emitOperator());
	    nodep->lhsp()->iterateAndNext(*this); puts(", ");
	}
	nodep->rhsp()->iterateAndNext(*this); puts(")");
    }
    virtual void visit(AstRedXor* nodep, AstNUser* vup) {
	if (nodep->lhsp()->isWide()) {
	    visit(nodep->castNodeUniop(), vup);
	} else {
	    putbs("VL_REDXOR_");
	    puts(cvtToStr(nodep->lhsp()->widthPow2()));
	    puts("(");
	    nodep->lhsp()->iterateAndNext(*this);
	    puts(")");
	}
    }
    virtual void visit(AstMulS* nodep, AstNUser* vup) {
	if (nodep->widthWords() > VL_MULS_MAX_WORDS) {
	    nodep->v3error("Signed multiply of "<<nodep->width()<<" bits exceeds hardcoded limit VL_MULS_MAX_WORDS in verilatedos.h\n");
	}
	visit(nodep->castNodeBiop(), vup);
    }
    virtual void visit(AstCast* nodep, AstNUser*) {
	// Extending a value of the same word width is just a NOP.
	if (nodep->size()>VL_WORDSIZE) {
	    puts("(QData)(");
	} else {
	    puts("(IData)(");
	}
	nodep->lhsp()->iterateAndNext(*this);
	puts(")");
    }
    virtual void visit(AstNodeCond* nodep, AstNUser*) {
	// Widths match up already, so we'll just use C++'s operator w/o any temps.
	if (nodep->expr1p()->isWide()) {
	    emitOpName(nodep,nodep->emitOperator());
	    nodep->condp()->iterateAndNext(*this); puts(", ");
	    nodep->expr1p()->iterateAndNext(*this); puts(", ");
	    nodep->expr2p()->iterateAndNext(*this); puts(")");
	} else {
	    putbs("(");
	    nodep->condp()->iterateAndNext(*this); putbs(" ? ");
	    nodep->expr1p()->iterateAndNext(*this); putbs(" : ");
	    nodep->expr2p()->iterateAndNext(*this); puts(")");
	}
    }
    virtual void visit(AstSel* nodep, AstNUser*) {
	// Note ASSIGN checks for this on a LHS
	if (nodep->widthp()->isOne()) {
	    emitOpName(nodep,"VL_BITSEL");
	    nodep->fromp()->iterateAndNext(*this); puts(", ");
	    nodep->lsbp()->iterateAndNext(*this); puts(")");
	} else {
	    emitOpName(nodep,"VL_SEL");
	    nodep->fromp()->iterateAndNext(*this); puts(", ");
	    nodep->lsbp()->iterateAndNext(*this); puts(", ");
	    nodep->widthp()->iterateAndNext(*this); puts(")");
	}
    }
    virtual void visit(AstReplicate* nodep, AstNUser*) {
	if (nodep->lhsp()->widthMin() == 1 && !nodep->isWide()) {
	    if (((int)nodep->rhsp()->castConst()->asInt()
		     * nodep->lhsp()->widthMin()) != nodep->widthMin())
		nodep->v3fatalSrc("Replicate non-constant or width miscomputed");
	    puts("VL_REPLICATE_");
	    emitIQW(nodep);
	    puts("OI(");
	    puts(cvtToStr(nodep->widthMin()));
	    if (nodep->lhsp()) { puts(","+cvtToStr(nodep->lhsp()->widthMin())); }
	    if (nodep->rhsp()) { puts(","+cvtToStr(nodep->rhsp()->widthMin())); }
	    puts(",");
	} else {
	    emitOpName(nodep,nodep->emitOperator());
	}
	nodep->lhsp()->iterateAndNext(*this); puts(", ");
	nodep->rhsp()->iterateAndNext(*this); puts(")");
    }
    virtual void visit(AstArraySel* nodep, AstNUser*) {
	nodep->fromp()->iterateAndNext(*this); putbs("[");
	nodep->bitp()->iterateAndNext(*this); puts("]");
    }
    virtual void visit(AstWordSel* nodep, AstNUser*) {
	nodep->fromp()->iterateAndNext(*this); puts("["); // Not putbs, as usually it's a small constant next
	nodep->bitp()->iterateAndNext(*this); puts("]");
    }
    // Terminals
    virtual void visit(AstVarRef* nodep, AstNUser*) {
	puts(nodep->hiername());
 	puts(nodep->varp()->name());
    }
    void emitConstant(AstConst* nodep, AstVarRef* assigntop, const string& assignString) {
	// Put out constant set to the specified variable, or given variable in a string
	if (nodep->num().isFourState()) {
	    nodep->v3error("Unsupported: 4-state numbers in this context");
	} else if (nodep->isWide()) {
	    putbs("VL_CONST_W_");
	    puts(cvtToStr(VL_WORDS_I(nodep->num().minWidth())));
	    puts("X(");
	    puts(cvtToStr(nodep->widthMin()));
	    puts(",");
	    if (!assigntop) {
		puts(assignString);
	    } else if (assigntop->castVarRef()) {
		puts(assigntop->hiername());
		puts(assigntop->varp()->name());
	    } else {
		assigntop->iterateAndNext(*this);
	    }
	    for (int word=VL_WORDS_I(nodep->num().minWidth())-1; word>0; word--) {
		ofp()->printf(",0x%08x", nodep->num().dataWord(word));
	    }
	    ofp()->printf(",0x%08x)", nodep->num().dataWord(0));
	} else if (nodep->isQuad()) {
	    vluint64_t num = nodep->asQuad();
	    if (num<10) ofp()->printf("VL_ULL(%lld)", (long long)num);
	    else ofp()->printf("VL_ULL(0x%llx)", (long long)num);
	} else {
	    uint32_t num = nodep->asInt();
	    if (num<10) puts(cvtToStr(num));
	    else ofp()->printf("0x%x", num);
	    //Unneeded-Causes %lx format warnings:
	    //  if (!nodep->num().isSigned() && (num & (1UL<<31))) puts("U");
	}
    }
    void emitSetVarConstant(const string& assignString, AstConst* constp) {
	if (!constp->isWide()) {
	    puts(assignString);
	    puts(" = ");
	}
	emitConstant(constp, NULL, assignString);
	puts(";\n");
    }
    virtual void visit(AstConst* nodep, AstNUser*) {
	if (nodep->isWide()) {
	    if (!m_wideTempRefp) nodep->v3fatalSrc("Wide Constant w/ no temp");
	    emitConstant(nodep, m_wideTempRefp, "");
	    m_wideTempRefp = NULL;   // We used it, barf if set it a second time
	} else {
	    emitConstant(nodep, NULL, "");
	}
    }

    // Just iterate
    virtual void visit(AstTopScope* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
    }
    virtual void visit(AstScope* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
    }
    // NOPs
    virtual void visit(AstPragma*, AstNUser*) {}
    virtual void visit(AstCell*, AstNUser*) {}		// Handled outside the Visit class
    virtual void visit(AstVar*, AstNUser*) {}		// Handled outside the Visit class
    virtual void visit(AstNodeText*, AstNUser*) {}	// Handled outside the Visit class
    virtual void visit(AstTraceDecl*, AstNUser*) {}	// Handled outside the Visit class
    virtual void visit(AstTraceInc*, AstNUser*) {}	// Handled outside the Visit class
    // Default
    virtual void visit(AstNode* nodep, AstNUser*) {
	puts((string)"\n???? // "+nodep->typeName()+"\n");
	nodep->iterateChildren(*this);
	nodep->v3fatalSrc("Unknown node type reached emitter: "<<nodep->typeName());
    }

public:
    EmitCStmts() {
	m_suppressSemi = false;
	m_wideTempRefp = NULL;
    }
    virtual ~EmitCStmts() {}
};

//######################################################################
// Internal EmitC implementation

class EmitCImp : EmitCStmts {
    // MEMBERS
    AstModule*	m_modp;
    vector<AstChangeDet*>	m_blkChangeDetVec;	// All encountered changes in block
    bool	m_slow;		// Creating __Slow file
    bool	m_fast;		// Creating non __Slow file (or both)
    int		m_splitSize;	// # of cfunc nodes placed into output file
    int		m_splitFilenum;	// File number being created, 0 = primary

    //---------------------------------------
    // METHODS

    void doubleOrDetect(AstChangeDet* changep, bool& gotOne) {
	static int addDoubleOr = 10;	// Determined experimentally as best
	if (!changep->rhsp()) {
	    if (!gotOne) gotOne = true;
	    else puts(" | ");
	    changep->lhsp()->iterateAndNext(*this);
	}
	else {
	    AstVarRef* lhsp = changep->lhsp()->castVarRef();
	    AstVarRef* rhsp = changep->rhsp()->castVarRef();
	    if (!lhsp) changep->v3fatalSrc("Not ref?");
	    if (!rhsp) changep->v3fatalSrc("Not ref?");
	    for (int word=0; word<changep->lhsp()->widthWords(); word++) {
		if (!gotOne) {
		    gotOne = true;
		    addDoubleOr = 10;	// Determined experimentally as best
		    puts("(");
		} else if (--addDoubleOr == 0) {
		    puts("|| (");
		    addDoubleOr = 10;
		} else {
		    puts(" | (");
		}
		changep->lhsp()->iterateAndNext(*this);
		if (changep->isWide()) puts("["+cvtToStr(word)+"]");
		puts(" ^ ");
		changep->rhsp()->iterateAndNext(*this);
		if (changep->isWide()) puts("["+cvtToStr(word)+"]");
		puts(")");
	    }
	}
    }

    V3OutCFile* newOutCFile(AstModule* modp, bool slow, bool source, int filenum=0) {
	string filenameNoExt = v3Global.opt.makeDir()+"/"+ modClassName(modp);
	if (filenum) filenameNoExt += "__"+cvtToStr(filenum);
	filenameNoExt += (slow ? "__Slow":"");
	V3OutCFile* ofp = NULL;
	if (optSystemPerl()) {
	    string filename = filenameNoExt+".sp";
	    newCFile(filename, slow, source);
	    ofp = new V3OutSpFile (filename);
	}
	else if (optSystemC()) {
	    string filename = filenameNoExt+(source?".cpp":".h");
	    newCFile(filename, slow, source);
	    ofp = new V3OutScFile (filename);
	}
	else {
	    string filename = filenameNoExt+(source?".cpp":".h");
	    newCFile(filename, slow, source);
	    ofp = new V3OutCFile  (filename);
	}
	ofp->putsHeader();
	return ofp;
    }

    //---------------------------------------
    // VISITORS
    virtual void visit(AstCFunc* nodep, AstNUser*) {
	if (nodep->funcType() == AstCFuncType::TRACE_INIT
	    || nodep->funcType() == AstCFuncType::TRACE_FULL
	    || nodep->funcType() == AstCFuncType::TRACE_CHANGE) {
	    return;  // Handled specially
	}
	if (!(nodep->slow() ? m_slow : m_fast)) return;

	m_blkChangeDetVec.clear();

	m_splitSize += EmitCBaseCounterVisitor(nodep).count();

	puts("\n");
	puts(nodep->rtnTypeVoid()); puts(" ");
	puts(modClassName(m_modp)+"::"+nodep->name()
	     +"("+cFuncArgs(nodep)+") {\n");

	puts("VL_DEBUG_IF(cout<<\"  "); 
	for (int i=0;i<m_modp->level();i++) { puts("  "); }
	puts(modClassName(m_modp)+"::"+nodep->name()
	     +"\"<<endl; );\n");

	if (nodep->symProlog()) puts(EmitCBaseVisitor::symTopAssign()+"\n");

	if (nodep->initsp()) puts("// Variables\n");
	ofp()->putAlign(V3OutFile::AL_AUTO, 4);
	for (AstNode* subnodep=nodep->argsp(); subnodep; subnodep = subnodep->nextp()) {
	    if (AstVar* varp=subnodep->castVar()) {
		if (varp->isFuncReturn()) emitVarDecl(varp, "");
	    }
	}
	emitVarList(nodep->initsp(), EVL_ALL, "");
	ofp()->putAlign(V3OutFile::AL_AUTO, 4);
	emitVarList(nodep->stmtsp(), EVL_ALL, "");
	ofp()->putAlign(V3OutFile::AL_AUTO, 4);

	nodep->initsp()->iterateAndNext(*this);

	if (nodep->stmtsp()) puts("// Body\n");
	nodep->stmtsp()->iterateAndNext(*this);
#ifndef NEW_ORDERING
	if (!m_blkChangeDetVec.empty()) emitChangeDet();
#endif

	if (nodep->finalsp()) puts("// Final\n");
	nodep->finalsp()->iterateAndNext(*this);
	//

	if (!m_blkChangeDetVec.empty()) puts("return __req;\n");

//	puts("__Vm_activity = true;\n");
	puts("}\n");
    }

    void emitChangeDet() {
	puts("// Change detection\n");
	puts("IData __req = false;  // Logically a bool\n");  // But not because it results in faster code
	bool gotOne = false;
	for (vector<AstChangeDet*>::iterator it = m_blkChangeDetVec.begin();
	     it != m_blkChangeDetVec.end(); ++it) {
	    AstChangeDet* changep = *it;
	    if (changep->lhsp()) {
		if (!gotOne) {  // Not a clocked block
		    puts("__req |= (");
		}
		else puts("\n");
		doubleOrDetect(changep, gotOne);
	    }
	}
	if (gotOne) {
	    puts(");\n");
	    //puts("VL_DEBUG_IF( if (__req) cout<<\"\tCLOCKREQ );");
	}
    }

    virtual void visit(AstChangeDet* nodep, AstNUser*) {
	m_blkChangeDetVec.push_back(nodep);
    }

    //---------------------------------------
    // ACCESSORS

    // METHODS
    // Low level
    void emitVarResets(AstModule* modp);
    void emitCellCtors(AstModule* modp);
    void emitSensitives();
    // Medium level
    void emitCtorImp(AstModule* modp);
    void emitConfigureImp(AstModule* modp);
    void emitCoverageDecl(AstModule* modp);
    void emitCoverageImp(AstModule* modp);
    void emitDestructorImp(AstModule* modp);
    void emitTextSection(AstType type);
    void emitIntFuncDecls(AstModule* modp);
    // High level
    void emitImp(AstModule* modp);
    void emitImpBottom(AstModule* modp);
    void emitStaticDecl(AstModule* modp);
    void emitWrapEval(AstModule* modp);
    void emitInt(AstModule* modp);
    void writeMakefile(string filename);

public:
    EmitCImp() {
	m_modp = NULL;
	m_splitSize = 0;
	m_splitFilenum = 0;
    }
    virtual ~EmitCImp() {}
    void main(AstModule* modp, bool slow, bool fast);
    void mainDoFunc(AstCFunc* nodep) {
	nodep->accept(*this);
    }
    int splitSize() { return m_splitSize; }
};

//######################################################################
// Internal EmitCStmts

void EmitCStmts::emitVarDecl(AstVar* nodep, const string& prefixIfImp) {
    if (nodep->isIO()) {
	if (nodep->isSc()) {
	    m_ctorVarsVec.push_back(nodep);
	    ofp()->putAlign(nodep->isStatic(), 4);	// sc stuff is a structure, so bigger alignment
	    if (nodep->attrScClocked() && nodep->isInput()) {
		puts("sc_in_clk\t");
	    } else {
		if (nodep->isInout()) puts("sc_inout<");
		else if (nodep->isInput()) puts("sc_in<");
		else if (nodep->isOutput()) puts("sc_out<");
		else nodep->v3fatalSrc("Unknown type");

		puts(nodep->scType());
		puts(">\t");
	    }
	    puts(nodep->name());
	    puts(";\n");
	} else { // C++ signals
	    ofp()->putAlign(nodep->isStatic(), nodep->widthAlignBytes());
	    if (nodep->isInout()) puts("VL_INOUT");
	    else if (nodep->isInput()) puts("VL_IN");
	    else if (nodep->isOutput()) puts("VL_OUT");
	    else nodep->v3fatalSrc("Unknown type");

	    if (nodep->isQuad()) puts("64");
	    else if (nodep->widthMin() <= 8) puts("8");
	    else if (nodep->widthMin() <= 16) puts("16");

	    if (!nodep->isWide())
		puts("("+nodep->name()
		     +","+cvtToStr(nodep->msb())
		     +","+cvtToStr(nodep->lsb()));
	    else puts("W("+nodep->name()
		      +","+cvtToStr(nodep->msb())
		      +","+cvtToStr(nodep->lsb())
		      +","+cvtToStr(nodep->widthWords()));
	    puts(");\n");
	}
    } else {
	// Arrays need a small alignment, but may need different padding after.
	// For example three VL_SIG8's needs alignment 1 but size 3.
	ofp()->putAlign(nodep->isStatic(), nodep->widthAlignBytes(), nodep->arrayElements()*nodep->widthAlignBytes());
	if (nodep->isStatic() && prefixIfImp=="") puts("static ");
	if (nodep->isStatic()) puts("VL_ST_"); else puts("VL_");
	if (nodep->widthMin() <= 8) {
	    puts("SIG8(");
	} else if (nodep->widthMin() <= 16) {
	    puts("SIG16(");
	} else if (nodep->isQuad()) {
	    puts("SIG64(");
	} else if (!nodep->isWide()) {
	    puts("SIG(");
	} else {
	    puts("SIGW(");
	}
	if (prefixIfImp!="") { puts(prefixIfImp); puts("::"); }
	puts(nodep->name());
	for (AstRange* arrayp=nodep->arraysp(); arrayp; arrayp = arrayp->nextp()->castRange()) {
	    puts("["+cvtToStr(arrayp->elementsConst())+"]");
	}
	puts(","+cvtToStr(nodep->msb())+","+cvtToStr(nodep->lsb()));
	if (nodep->isWide()) puts(","+cvtToStr(nodep->widthWords()));
	puts(");\n");
    }
}

void EmitCStmts::emitVarCtors() {
    ofp()->indentInc();
    bool first = true;
    for (vector<AstVar*>::iterator it = m_ctorVarsVec.begin(); it != m_ctorVarsVec.end(); ++it) {
	if (first) {
	    first=false;
	    puts("\n");
	    puts("#if (SYSTEMC_VERSION>20011000)\n");  // SystemC 2.0.1 and newer
	    puts("  : ");
	}
	else puts(", ");
	if (ofp()->exceededWidth()) puts("\n  ");
	puts((*it)->name()); puts("(\"");
	puts((*it)->name()); puts("\")");
    }
    if (!first) puts ("\n#endif\n");
    ofp()->indentDec();
}

bool EmitCStmts::emitSimpleOk(AstNodeMath* nodep) {
    // Can we put out a simple (A + B) instead of VL_ADD_III(A,B)?
    if (nodep->emitSimpleOperator() == "") return false;
    if (nodep->isWide()) return false;
    if (nodep->op1p()) { if (nodep->op1p()->isWide()) return false; }
    if (nodep->op2p()) { if (nodep->op2p()->isWide()) return false; }
    if (nodep->op3p()) { if (nodep->op3p()->isWide()) return false; }
    return true;
}

void EmitCStmts::emitOpName(AstNode* nodep, const string& opname) {
    putbs(opname+"_");
    if (nodep->emitWordForm()) {
	emitIQW(nodep->op1p());
	puts("(");
	if (nodep->op1p()->isWide()) {
	    puts(cvtToStr(nodep->op1p()->widthWords()));
	    puts(", ");
	}
    } else {
	emitIQW(nodep);
	if (nodep->op1p()) { emitIQW(nodep->op1p()); }
	if (nodep->op2p()) { emitIQW(nodep->op2p()); }
	if (nodep->op3p()) { emitIQW(nodep->op3p()); }
	puts("(");
	puts(cvtToStr(nodep->widthMin()));
	if (nodep->op1p()) { puts(","+cvtToStr(nodep->op1p()->widthMin())); }
	if (nodep->op2p()) { puts(","+cvtToStr(nodep->op2p()->widthMin())); }
	if (nodep->op3p()) { puts(","+cvtToStr(nodep->op3p()->widthMin())); }
	if (nodep->op1p() || nodep->isWide()) puts(", ");
    }
    if (nodep->isWide()) {
	if (!m_wideTempRefp) nodep->v3fatalSrc("Wide Op w/ no temp, perhaps missing op in V3EmitC?");
	puts(m_wideTempRefp->hiername());
	puts(m_wideTempRefp->varp()->name());
	m_wideTempRefp = NULL;
	if (nodep->op1p()) puts(", ");
    }
}

//----------------------------------------------------------------------
// Mid level - VISITS

// We only do one display at once, so can just use static state

struct EmitDispState {
    bool		m_wide;		// Put out a wide func that needs string buffer
    string		m_format;	// "%s" and text from user
    vector<AstNode*>	m_argsp;	// Each argument to be printed
    vector<string>	m_argsFunc;	// Function before each argument to be printed
    EmitDispState() { clear(); }
    void clear() {
	m_wide = false;
	m_format = "";
	m_argsp.clear();
	m_argsFunc.clear();
    }
    void pushFormat(const string& fmt) { m_format += fmt; }
    void pushFormat(char fmt) { m_format += fmt; }
    void pushArg(AstNode* nodep, const string& func) {
	m_argsp.push_back(nodep); m_argsFunc.push_back(func);
    }
} emitDispState;

void EmitCStmts::displayEmit(AstDisplay* nodep) {
    if (emitDispState.m_format != "") {
	// Format
	if (nodep->filep()) {
	    puts("if (");
	    nodep->filep()->iterate(*this);	// Check if closed, to avoid core dump
	    puts(") fprintf(VL_CVT_Q_FP(");
	    nodep->filep()->iterate(*this);
	    puts("),\"");
	} else {
	    puts("VL_PRINTF(\"");
	}
	ofp()->putsNoTracking(emitDispState.m_format);
	puts("\"");
	// Arguments
	for (unsigned i=0; i < emitDispState.m_argsp.size(); i++) {
	    puts(",");
	    AstNode* argp = emitDispState.m_argsp[i];
	    string   func = emitDispState.m_argsFunc[i];
	    ofp()->indentInc();
	    ofp()->putbs("");
	    if (func!="") puts(func);
	    if (argp) argp->iterate(*this);
	    if (func!="") puts(")");
	    ofp()->indentDec();
	}
        // End
	puts(");\n");
	// Prep for next
	emitDispState.clear();
    }
}

string EmitCStmts::displayFormat(AstNode* widthNodep, string in,
				 char fmtLetter, bool padZero, bool reallyString) {
    if (fmtLetter=='s') padZero = false;
    if (widthNodep && widthNodep->isWide()
	&& (fmtLetter=='d'||fmtLetter=='u')) {
	widthNodep->v3error("Unsupported: $display of dec format of > 64 bit results (use hex format instead)");
    }
    if (widthNodep && widthNodep->widthMin()>8 && fmtLetter=='c') {
	widthNodep->v3error("$display of char format of > 8 bit result");
    }
    string fmt;
    if (in == "") {
	// Size naturally
	if (widthNodep == NULL) fmt="";  // Out of args, will get error
	if (fmtLetter=='u' || fmtLetter=='d') { // Decimal.  Spec says leading spaces, not zeros
	    double mantissabits = widthNodep->widthMin() - ((fmtLetter=='d')?1:0);
	    double maxval = pow(2.0, mantissabits);
	    double dchars = log10(maxval)+1.0;
	    if (fmtLetter=='d') dchars++;  // space for sign
	    int nchars = int(dchars);
	    fmt=cvtToStr(nchars);
	} else if (fmtLetter!='s' && fmtLetter!='c') {  // Strings/chars don't get padding
	    int bitsPerChar = (fmtLetter=='b'?1 : fmtLetter=='o'?3 : 4);
	    int nchars = (widthNodep->widthMin() + bitsPerChar-1)/bitsPerChar;
	    if (padZero) fmt=(string)("0")+cvtToStr(nchars);
	    else fmt=cvtToStr(nchars);
	}
    } else if (in == "0") {
	fmt="";	// No width
    } else {
	fmt=in;
    }
    return fmt;
}

void EmitCStmts::displayArg(AstDisplay* dispp, AstNode** elistp, string fmt, char fmtLetter) {
    // Print display argument, edits elistp
    if (!*elistp) {
	dispp->v3error("Missing arguments for $display format");
	return;
    }
    if ((*elistp)->widthMin() > VL_VALUE_STRING_MAX_WIDTH) {
	dispp->v3error("Exceeded limit of 1024 bits for any display arguments");
    }

    if ((*elistp)->isWide()	// Have to use our own function for wide,
	|| fmtLetter=='s'	// ... Verilog strings
	|| fmtLetter=='b'	// ... binary, no printf %b in C
	|| fmtLetter=='d') {	// ... Signed decimal
	// We use a single static string, so must only have one call per VL_PRINT
	if (emitDispState.m_wide) { displayEmit(dispp); }
	emitDispState.m_wide = true;
	string nfmt = displayFormat(*elistp, fmt, fmtLetter, false, true);
	string pfmt = "%"+nfmt+"s";
	string func = "VL_VALUE_FORMATTED_";
	func += ((*elistp)->isWide()) ? "W(" : ((*elistp)->isQuad()) ? "Q(" : "I(";
	func += (cvtToStr((*elistp)->widthMin())
		 +",'"+fmtLetter+"'"
		 +","+(fmt=="0"?"true":"false")+",");
	emitDispState.pushFormat(pfmt);
	emitDispState.pushArg(*elistp,func);
    } else {
	string func;
	string nfmt = displayFormat(*elistp, fmt, fmtLetter, true, false);
	// We don't need to check for fmtLetter=='d', as it is above.
	if ((*elistp)->isQuad() && (fmtLetter=='u'||fmtLetter=='o'||fmtLetter=='x')) {
	    nfmt+="ll";
	    func="(unsigned long long)(";  // Must match %ull to avoid warnings
	}
	string pfmt = "%"+nfmt+fmtLetter;

	emitDispState.pushFormat(pfmt);
	emitDispState.pushArg(*elistp,func);
    }
    // Next parameter
    *elistp = (*elistp)->nextp();
}

void EmitCStmts::visit(AstDisplay* nodep, AstNUser*) {
    string vformat = nodep->text();
    bool addNewline = (nodep->newline() == '\n');
    AstNode* elistp = nodep->exprsp();

    // Convert Verilog display to C printf formats
    // 		"%0t" becomes "%d"
    emitDispState.clear();
    string fmt = "";
    string::iterator pos = vformat.begin();
    if (*pos == '"') pos++;
    bool inPct = false;
    for (; pos != vformat.end(); ++pos) {
	if (pos[0]=='"' && (pos+1)==vformat.end()) break;
	if (inPct && pos[0]=='%') {
	    emitDispState.pushFormat("%%");  // We're printf'ing it, so need to quote the %
	    inPct = false;
	} else if (pos[0]=='%') {
	    inPct = true;
	    fmt = "";
	} else if (!inPct) {   // Normal text
	    //char text[2]; text[0]=*pos; text[1]='\0';
	    emitDispState.pushFormat(*pos);
	} else { // Format character
	    if (isdigit(pos[0])) {
		// Digits, like %5d, etc.
		fmt += pos[0];
	    } else {
		inPct = false;
		switch (tolower(pos[0])) {
		// Special codes
		case '~': displayArg(nodep,&elistp,fmt,'d'); break;  // Signed decimal
		// Spec: h d o b c l
		case 'b': displayArg(nodep,&elistp,fmt,'b'); break;
		case 'c': displayArg(nodep,&elistp,fmt,'c'); break;
		case 'd': displayArg(nodep,&elistp,fmt,'u'); break;  // Unsigned decimal
		case 'o': displayArg(nodep,&elistp,fmt,'o'); break;
		case 'h':
		case 'x': displayArg(nodep,&elistp,fmt,'x'); break;
		case 's': displayArg(nodep,&elistp,fmt,'s'); break;
		case 't': displayArg(nodep,&elistp,fmt,'u'); break;
		case 'm': {
		    emitDispState.pushFormat("%s");
		    emitDispState.pushArg(NULL, "vlSymsp->name(");
		    for (AstText* textp=nodep->scopeTextp(); textp; textp=textp->nextp()->castText()) {
			emitDispState.pushFormat(textp->text());
		    }
		    break;
		}
		case 'u':
		case 'z':
		case 'l':
		case 'v':
		    nodep->v3error("Unsupported: $display format code: %"<<pos[0]);
		    break;
		default:
		    nodep->v3error("Unknown $display format code: %"<<pos[0]);
		    break;
		}
	    }
	}
    }
    if (elistp != NULL) {
	nodep->v3error("Extra arguments for $display format\n");
    }
    if (addNewline) emitDispState.pushFormat("\\n");
    displayEmit(nodep);
}

//######################################################################
// Internal EmitC

void EmitCImp::emitVarResets(AstModule* modp) {
    puts("// Reset internal values\n");
    if (modp->isTop()) {
	if (v3Global.opt.inhibitSim()) puts("__Vm_inhibitSim = false;\n");
	puts("\n");
    }

    puts("// Reset structure values\n");
    for (AstNode* nodep=modp->stmtsp(); nodep; nodep = nodep->nextp()) {
	if (AstVar* varp = nodep->castVar()) {
	    if (varp->isIO() && modp->isTop() && optSystemC()) {
		// System C top I/O doesn't need loading, as the lower level subinst code does it.
	    }
	    else if (varp->isParam()) {
		if (!varp->hasSimpleInit()) nodep->v3fatalSrc("No init for a param?");
		//puts("// parameter "+varp->name()+" = "+varp->initp()->name()+"\n");
	    }
	    else if (AstInitArray* initarp = varp->initp()->castInitArray()) {
		AstConst* constsp = initarp->initsp()->castConst();
		if (!varp->arraysp()) varp->v3fatalSrc("InitArray under non-arrayed var");
		for (int i=0; i<varp->arraysp()->elementsConst(); i++) {
		    if (!constsp) initarp->v3fatalSrc("Not enough values in array initalizement");
		    emitSetVarConstant(varp->name()+"["+cvtToStr(i)+"]", constsp);
		    constsp = constsp->nextp()->castConst();
		}
	    }
	    else {
		int vects = 0;
		for (AstRange* arrayp=varp->arraysp(); arrayp; arrayp = arrayp->nextp()->castRange()) {
		    int vecnum = vects++;
		    if (arrayp->msbConst() < arrayp->lsbConst()) varp->v3fatalSrc("Should have swapped msb & lsb earlier.");
		    string ivar = string("__Vi")+cvtToStr(vecnum);
		    // MSVC++ pre V7 doesn't support 'for (int ...)', so declare in sep block
		    puts("{ int __Vi"+cvtToStr(vecnum)+"="+cvtToStr(0)+";");
		    puts(" for (; "+ivar+"<"+cvtToStr(arrayp->elementsConst()));
		    puts("; ++"+ivar+") {\n");
		}
		bool zeroit = (varp->attrFileDescr() // Zero it out, so we don't core dump if never call $fopen
			       || (varp->name().c_str()[0]=='_' && v3Global.opt.underlineZero()));
		if (varp->isWide()) {
		    // DOCUMENT: We randomize everything.  If the user wants a _var to be zero,
		    // there should be a initial statement.  (Different from verilator2.)
		    if (zeroit) puts("VL_ZERO_RESET_W(");
		    else puts("VL_RAND_RESET_W(");
		    puts(cvtToStr(varp->widthMin()));
		    puts(",");
		    puts(varp->name());
		    for (int v=0; v<vects; ++v) puts( "[__Vi"+cvtToStr(v)+"]");
		    puts(");\n");
		} else {
		    puts(varp->name());
		    for (int v=0; v<vects; ++v) puts( "[__Vi"+cvtToStr(v)+"]");
		    if (zeroit) {
			puts("= 0;\n");
		    } else {
			puts(" = VL_RAND_RESET_");
			emitIQW(varp);
			puts("(");
			puts(cvtToStr(varp->widthMin()));
			puts(");\n");
		    }
		}
		for (int v=0; v<vects; ++v) puts( "}}\n");
	    }
	}
    }
}

void EmitCImp::emitCoverageDecl(AstModule* modp) {
    m_coverIds.clear();
    for (AstNode* nodep=modp->stmtsp(); nodep; nodep = nodep->nextp()) {
	if (AstCoverDecl* declp = nodep->castCoverDecl()) {
	    m_coverIds.remap(declp);
	}
    }
    if (m_coverIds.size()) {
	ofp()->putsPrivate(true);
	puts("// Coverage\n");
	puts("SpZeroed<uint32_t>\t__Vcoverage["); puts(cvtToStr(m_coverIds.size())); puts("];\n");
	ofp()->putAlign(V3OutFile::AL_AUTO, sizeof(uint32_t)*m_coverIds.size());
	puts("void __vlCoverInsert(SpZeroed<uint32_t>* countp, const char* filename, int lineno, int column,\n");
	puts(  	"const char* hier, const char* type, const char* comment);\n");
    }
}

void EmitCImp::emitCtorImp(AstModule* modp) {
    puts("\n");
    if (optSystemPerl() && modp->isTop()) {
	puts("SP_CTOR_IMP("+modClassName(modp)+")");
    } else if (optSystemC() && modp->isTop()) {
	puts("VL_SC_CTOR_IMP("+modClassName(modp)+")");
    } else {
	puts("VL_CTOR_IMP("+modClassName(modp)+")");
    }
    emitVarCtors();
    puts(" {\n");

    emitCellCtors(modp);
    emitSensitives();
    emitVarResets(modp);
    emitTextSection(AstType::SCCTOR);
    if (optSystemPerl()) puts("SP_AUTO_CTOR;\n");
    puts("}\n");
}

void EmitCImp::emitConfigureImp(AstModule* modp) {
    puts("\nvoid "+modClassName(modp)+"::__Vconfigure("+symClassName()+"* symsp) {\n");
    puts(   "__VlSymsp = symsp;\n");  // First, as later stuff needs it.
    bool first=true;
    for (AstNode* nodep=modp->stmtsp(); nodep; nodep = nodep->nextp()) {
	if (nodep->castCoverDecl()) {
	    if (first) {
		first = false;
		puts("// Coverage Declarations\n");
	    }
	    nodep->accept(*this);
	}
    }
    puts("}\n");
}

void EmitCImp::emitCoverageImp(AstModule* modp) {
    if (m_coverIds.size()) {
	puts("\n// Coverage\n");
	// Rather then putting out SP_COVER_INSERT calls directly, we do it via this function
	// This gets around gcc slowness constructing all of the template arguments
	puts("void "+modClassName(m_modp)+"::__vlCoverInsert(SpZeroed<uint32_t>* countp, const char* filename, int lineno, int column,\n");
	puts(  	"const char* hier, const char* type, const char* comment) {\n");
	puts(   "SP_COVER_INSERT(countp,");
	puts(	"  \"filename\",filename,");
	puts(	"  \"lineno\",lineno,");
	puts(	"  \"column\",column,\n");
	//puts(	"\"hier\",string(__VlSymsp->name())+hier,");  // Need to move hier into scopes and back out if do this
	puts(	"\"hier\",string(name())+hier,");
	puts(	"  \"type\",type,");
	puts(	"  \"comment\",comment);\n");
	puts("}\n");
    }
}

void EmitCImp::emitDestructorImp(AstModule* modp) {
    puts("\n");
    puts(modClassName(modp)+"::~"+modClassName(modp)+"() {\n");
    emitTextSection(AstType::SCDTOR);
    if (modp->isTop()) puts("delete __VlSymsp; __VlSymsp=NULL;\n");
    puts("}\n");
}

void EmitCImp::emitStaticDecl(AstModule* modp) {
    // Need implementation here.  Be careful of alignment code; needs to be uniquified
    // with module name to avoid multiple symbols.
    //emitVarList(modp->stmtsp(), EVL_ALL, modp->name());
}

void EmitCImp::emitTextSection(AstType type) {
    int last_line = -999;
    for (AstNode* nodep = m_modp->stmtsp(); nodep != NULL; nodep = nodep->nextp()) {
	if (AstNodeText* textp = nodep->castNodeText()) {
	    if (nodep->type() == type) {
		if (last_line != nodep->fileline()->lineno()) {
		    if (last_line < 0) {
			puts("\n//*** Below code from `systemc in Verilog file\n");
		    }
		    ofp()->putsNoTracking("//#line "+cvtToStr(nodep->fileline()->lineno())
					  +" \""+nodep->fileline()->filename()+"\"\n");
		    last_line = nodep->fileline()->lineno();
		}
		ofp()->putsNoTracking(textp->text());
		last_line++;
	    }
	}
    }
    if (last_line > 0) {
	puts("//*** Above code from `systemc in Verilog file\n\n");
    }
}

void EmitCImp::emitCellCtors(AstModule* modp) {
    if (modp->isTop()) {
	// Must be before other constructors, as __vlCoverInsert calls it
	puts(EmitCBaseVisitor::symClassVar()+" = __VlSymsp = new "+symClassName()+"(this, name());\n");
	puts(EmitCBaseVisitor::symTopAssign()+"\n");
    }
    for (AstNode* nodep=modp->stmtsp(); nodep; nodep = nodep->nextp()) {
	if (AstCell* cellp=nodep->castCell()) {
	    puts("VL_CELL ("+cellp->name()+", "+modClassName(cellp->modp())+");\n");
	}
    }
}

void EmitCImp::emitSensitives() {
    // Create sensitivity list for when to evaluate the model.
    // If C++ code, the user must call this routine themself.
    if (m_modp->isTop() && optSystemC()) {
	puts("// Sensitivities on all clocks and combo inputs\n");
	puts("SC_METHOD(eval);\n");
	for (AstNode* nodep=m_modp->stmtsp(); nodep; nodep = nodep->nextp()) {
	    if (AstVar* varp = nodep->castVar()) {
		if (varp->isInput() && (varp->isScSensitive() || varp->isUsedClock())) {
		    puts("sensitive("+varp->name()+");\n");
		}
	    }
	}
	puts("\n");
    }
}

void EmitCImp::emitWrapEval(AstModule* modp) {
    puts("\nvoid "+modClassName(modp)+"::eval() {\n");
    puts(EmitCBaseVisitor::symClassVar()+" = this->__VlSymsp; // Setup global symbol table\n");
    puts(EmitCBaseVisitor::symTopAssign()+"\n");
    puts("// Initialize\n");
    puts("if (VL_UNLIKELY(!vlSymsp->__Vm_didInit)) _eval_initial_loop(vlSymsp);\n");
    if (v3Global.opt.inhibitSim()) {
	puts("if (VL_UNLIKELY(__Vm_inhibitSim)) return;\n");
    }
    puts("// Evaluate till stable\n");
    puts("VL_DEBUG_IF(cout<<\"\\n----TOP Evaluate "+modClassName(modp)+"::eval\"<<endl; );\n");
#ifndef NEW_ORDERING
    puts("int __VclockLoop = 0;\n");
    puts("IData __Vchange=1;\n");
    puts("while (VL_LIKELY(__Vchange)) {\n");
    puts(    "VL_DEBUG_IF(cout<<\" Clock loop\"<<endl;);\n");
#endif
    puts(    "vlSymsp->__Vm_activity = true;\n");
    puts(    "_eval(vlSymsp);\n");
#ifndef NEW_ORDERING
    puts(    "__Vchange = _change_request(vlSymsp);\n");
    puts(    "if (++__VclockLoop > 100) vl_fatal(__FILE__,__LINE__,__FILE__,\"Verilated model didn't converge\");\n");
    puts("}\n");
#endif
    puts("}\n");

    //
    puts("\nvoid "+modClassName(modp)+"::_eval_initial_loop("+EmitCBaseVisitor::symClassVar()+") {\n");
    puts("vlSymsp->__Vm_didInit = true;\n");
    puts("_eval_initial(vlSymsp);\n");
#ifndef NEW_ORDERING
    puts(    "vlSymsp->__Vm_activity = true;\n");
    puts(    "int __VclockLoop = 0;\n");
    puts(    "IData __Vchange=1;\n");
    puts(    "while (VL_LIKELY(__Vchange)) {\n");
#endif
    puts(        "_eval_settle(vlSymsp);\n");
    puts(        "_eval(vlSymsp);\n");
#ifndef NEW_ORDERING
    puts(	 "__Vchange = _change_request(vlSymsp);\n");
    puts(        "if (++__VclockLoop > 100) vl_fatal(__FILE__,__LINE__,__FILE__,\"Verilated model didn't DC converge\");\n");
    puts(    "}\n");
#endif
    puts("}\n");
}

//----------------------------------------------------------------------
// Top interface/ implementation

void EmitCStmts::emitVarList(AstNode* firstp, EisWhich which, const string& prefixIfImp) {
    // Put out a list of signal declarations
    // in order of 0:clocks, 1:vluint8, 2:vluint16, 4:vluint32, 5:vluint64, 6:wide, 7:arrays
    // This aids cache packing and locality
    // Largest->smallest reduces the number of pad variables.
    // But for now, Smallest->largest makes it more likely a small offset will allow access to the signal.
    for (int isstatic=1; isstatic>=0; isstatic--) {
	if (prefixIfImp!="" && !isstatic) continue;
	for (int size=0; size<8; size++) {
	    if (size==3) continue;
	    for (AstNode* nodep=firstp; nodep; nodep = nodep->nextp()) {
		if (AstVar* varp = nodep->castVar()) {
		    bool doit = true;
		    switch (which) {
		    case EVL_ALL:  doit = true; break;
		    case EVL_IO:   doit = varp->isIO(); break;
		    case EVL_SIG:  doit = (varp->isSignal() && !varp->isIO()); break;
		    case EVL_TEMP: doit = varp->isTemp(); break;
		    default: v3fatalSrc("Bad Case");
		    }
		    if (varp->isStatic() ? !isstatic : isstatic) doit=false;
		    if (doit) {
			int sigbytes = varp->widthAlignBytes();
			if (varp->isUsedClock() && varp->widthMin()==1) sigbytes = 0;
			else if (varp->arraysp()) sigbytes=7;
			else if (varp->isScWide()) sigbytes=6;
			else if (sigbytes==8) sigbytes=5;
			else if (sigbytes==4) sigbytes=4;
			else if (sigbytes==2) sigbytes=2;
			else if (sigbytes==1) sigbytes=1;
			if (size==sigbytes) {
			    emitVarDecl(varp, prefixIfImp);
			}
		    }
		}
	    }
	}
	ofp()->putAlign(isstatic, 4, 0, prefixIfImp.c_str());
    }
}

struct CmpName {
    inline bool operator () (const AstNode* lhsp, const AstNode* rhsp) const {
	return lhsp->name() < rhsp->name();
    }
};

void EmitCImp::emitIntFuncDecls(AstModule* modp) {
    vector<AstCFunc*> funcsp;

    for (AstNode* nodep=modp->stmtsp(); nodep; nodep = nodep->nextp()) {
	if (AstCFunc* funcp = nodep->castCFunc()) {
	    if (!funcp->skipDecl()) {
		funcsp.push_back(funcp);
	    }
	}
    }

    sort(funcsp.begin(), funcsp.end(), CmpName());

    for (vector<AstCFunc*>::iterator it = funcsp.begin(); it != funcsp.end(); ++it) {
	AstCFunc* funcp = *it;
	ofp()->putsPrivate(funcp->declPrivate());
	if (funcp->isStatic()) puts("static ");
	puts(funcp->rtnTypeVoid()); puts("\t");
	puts(funcp->name()); puts("("+cFuncArgs(funcp)+");\n");
    }
}

void EmitCImp::emitInt(AstModule* modp) {
    // Always have this first; gcc has short circuiting if #ifdef is first in a file
    if (!optSystemPerl()) {  // else done for us automatically
	puts("#ifndef _"+modClassName(modp)+"_H_\n");
	puts("#define _"+modClassName(modp)+"_H_\n");
	puts("\n");
    }

    ofp()->putsIntTopInclude();
    puts("#include \"verilated.h\"\n");
    if (v3Global.opt.coverage()) {
	puts("#include \"SpCoverage.h\"\n");
    }

    // Declare foreign instances up front to make C++ happy
    puts("class "+symClassName()+";\n");
    for (AstNode* nodep=modp->stmtsp(); nodep; nodep = nodep->nextp()) {
	if (AstCell* cellp=nodep->castCell()) {
	    puts("class "+modClassName(cellp->modp())+";\n");
	}
    }

    puts("\n//----------\n\n");
    emitTextSection(AstType::SCHDR);

    if (optSystemC() && modp->isTop()) {
	puts("SC_MODULE("+modClassName(modp)+") {\n");
    } else {
	puts("VL_MODULE("+modClassName(modp)+") {\n");
    }
    if (optSystemPerl()) puts("/*AUTOATTR(verilated)*/\n\n");
    ofp()->resetPrivate();
    ofp()->putsPrivate(false);  // public:

    // Instantiated modules
    if (optSystemPerl()) {
	puts("/*AUTOSUBCELLS*/\n\n");
    } else {
	puts("// CELLS\n");
	for (AstNode* nodep=modp->stmtsp(); nodep; nodep = nodep->nextp()) {
	    if (AstCell* cellp=nodep->castCell()) {
		ofp()->putsCellDecl(modClassName(cellp->modp()), cellp->name());
	    }
	}
    }

    puts("\n// PORTS\n");
    emitVarList(modp->stmtsp(), EVL_IO, "");

    puts("\n// LOCAL SIGNALS\n");
    emitVarList(modp->stmtsp(), EVL_SIG, "");

    puts("\n// LOCAL VARIABLES\n");
    emitVarList(modp->stmtsp(), EVL_TEMP, "");

    puts("\n// INTERNAL VARIABLES\n");
    ofp()->putsPrivate(!modp->isTop());  // private: unless top
    ofp()->putAlign(V3OutFile::AL_AUTO, 8);
    puts(symClassName()+"*\t__VlSymsp;\t\t// Symbol table\n");
    ofp()->putsPrivate(false);  // public:
    if (modp->isTop()) {
	if (v3Global.opt.inhibitSim()) {
	    ofp()->putAlign(V3OutFile::AL_AUTO, sizeof(bool));
	    puts("bool\t__Vm_inhibitSim;\t///< Set true to disable evaluation of module\n");
	}
    }
    ofp()->putAlign(V3OutFile::AL_AUTO, 8);
    emitCoverageDecl(modp);	// may flip public/private
    ofp()->putAlign(V3OutFile::AL_AUTO, 8);

    puts("\n// PARAMETERS\n");
    ofp()->putsPrivate(false);  // public:
    for (AstNode* nodep=modp->stmtsp(); nodep; nodep = nodep->nextp()) {
	if (AstVar* varp = nodep->castVar()) {
	    if (varp->isParam() && (varp->isUsedParam() || varp->isSigPublic())) {
		if (!varp->initp()) nodep->v3fatalSrc("No init for a param?");
		// These should be static const values, however microsloth VC++ doesn't
		// support them.  They also cause problems with GDB under GCC2.95.
		if (varp->isScWide()) {   // Unsupported for output
		    puts("// enum WData "+varp->name()+"  //wide");
		} else if (!varp->initp()->castConst()) {   // Unsupported for output
		    puts("// enum IData "+varp->name()+"  //not simple value");
		} else {
		    puts("enum ");
		    puts(varp->isQuad()?"_QData":"_IData");
		    puts(""+varp->name()+" { "+varp->name()+" = ");
		    varp->initp()->iterateAndNext(*this);
		    puts("};");
		}
		puts("\n");
	    }
	}
    }

    puts("\n// METHODS\n");
    ofp()->resetPrivate();
    // We don't need a private copy constructor, as VerilatedModule has one for us.
    ofp()->putsPrivate(true);
    puts(modClassName(modp)+"& operator= (const "+modClassName(modp)+"&);\t///< Copying not allowed\n");
    puts(modClassName(modp)+"(const "+modClassName(modp)+"&);\t///< Copying not allowed\n");

    ofp()->putsPrivate(false);  // public:
    if (optSystemC() && modp->isTop()) {
	puts("SC_CTOR("+modClassName(modp)+");\n");
	puts("virtual ~"+modClassName(modp)+"();\n");
    } else if (optSystemC()) {
	puts("VL_CTOR("+modClassName(modp)+");\n");
	puts("~"+modClassName(modp)+"();\n");
    } else {
	puts(modClassName(modp)+"(const char* name=\"TOP\");\n");
	puts("~"+modClassName(modp)+"();\n");
	if (v3Global.opt.trace()) {
	    puts("void\ttrace (SpTraceVcdCFile* tfp, int levels, int options=0);\n");
	}
    }
    puts("void\t__Vconfigure("+symClassName()+"* symsp);\n");
    if (optSystemPerl()) puts("/*AUTOMETHODS*/\n");

    emitTextSection(AstType::SCINT);

    puts("\n// Sensitivity blocks\n");
    if (modp->isTop()) {
	puts("void\tfinal();\t///< Function to call when simulation completed\n");
	if (optSystemC()) ofp()->putsPrivate(true);	///< eval() is invoked by our sensitive() calls.
	puts("void\teval();\t///< Main function to call from calling app when inputs change\n");
	if (v3Global.opt.inhibitSim()) {
	    puts("void\tinhibitSim(bool flag) { __Vm_inhibitSim=flag; }\t///< Set true to disable evaluation of module\n");
	}
	ofp()->putsPrivate(true);  // private:
	puts("static void _eval_initial_loop("+EmitCBaseVisitor::symClassVar()+");\n");
    }

    emitIntFuncDecls(modp);

    if (!optSystemPerl() && v3Global.opt.trace()) {
	ofp()->putsPrivate(false);  // public:
	puts("static void traceInit (SpTraceVcd* vcdp, void* userthis, uint32_t code);\n");
	puts("static void traceFull (SpTraceVcd* vcdp, void* userthis, uint32_t code);\n");
	puts("static void traceChg  (SpTraceVcd* vcdp, void* userthis, uint32_t code);\n");
    }

    puts("} VL_ATTR_ALIGNED(64);\n");
    puts("\n");

    // finish up h-file
    if (!optSystemPerl()) {
	puts("#endif  /*guard*/\n");
    }
}

//----------------------------------------------------------------------

void EmitCImp::emitImp(AstModule* modp) {
    if (optSystemPerl()) {
	puts("//############################################################\n");
	puts("#sp implementation\n");
    }
    ofp()->printf("#include \"%-20s // For This\n",
		  (modClassName(modp)+".h\"").c_str());

    // Us
    puts("#include \""+ symClassName() +".h\"\n");

    if (optSystemPerl() && (m_splitFilenum || !m_fast)) {
	puts("\n");
	puts("SP_MODULE_CONTINUED("+modClassName(modp)+");\n");
    }

    emitTextSection(AstType::SCIMPHDR);

    if (m_slow && m_splitFilenum==0) {
	puts("\n//--------------------\n");
	puts("// STATIC VARIABLES\n\n");
	emitVarList(modp->stmtsp(), EVL_ALL, modClassName(modp));
    }

    if (m_fast && m_splitFilenum==0) {
	emitTextSection(AstType::SCIMP);
	emitStaticDecl(modp);
    }

    if (m_slow && m_splitFilenum==0) {
	puts("\n//--------------------\n");
	emitCtorImp(modp);
	emitConfigureImp(modp);
	emitDestructorImp(modp);
	emitCoverageImp(modp);
    }

    if (m_fast && m_splitFilenum==0) {
	if (modp->isTop()) {
	    emitStaticDecl(modp);
	    puts("\n//--------------------\n");
	    puts("\n");
	    emitWrapEval(modp);
	}
    }

    if (m_fast && m_splitFilenum==0) {
	if (v3Global.opt.trace() && optSystemC() && m_modp->isTop()) {
	    puts("\n");
	    puts("\n/*AUTOTRACE(__MODULE__,recurse,activity,exists)*/\n\n");
	}
    }

    // Blocks
    puts("\n//--------------------\n");
    puts("// Internal Methods\n");
}

void EmitCImp::emitImpBottom(AstModule* modp) {
}

//######################################################################

void EmitCImp::main(AstModule* modp, bool slow, bool fast) {
    // Output a module
    m_modp = modp;
    m_slow = slow;
    m_fast = fast;
    string filenameNoExt = v3Global.opt.makeDir()+"/"+ modClassName(modp)+(m_fast ? "" : "__Slow");

    if (debug()>=5) {
	for (int i=0;i<modp->level();i++) { cout<<"  "; }
	UINFONL(0,"  Emitting "<<modClassName(modp)<<endl);
    }

    if (optSystemPerl()) {
	m_ofp = newOutCFile(modp, !m_fast, true);

	if (m_fast) {
	    puts("#sp interface\n");
	    emitInt (modp);
	}
    }
    else if (optSystemC()) {
	if (m_fast) {
	    m_ofp = newOutCFile (modp, !m_fast, false/*source*/);
	    emitInt (modp);
	    delete m_ofp; m_ofp=NULL;
	}

	m_ofp = newOutCFile (modp, !m_fast, true/*source*/);
    }
    else {
	if (m_fast) {
	    m_ofp = newOutCFile (modp, !m_fast, false/*source*/);
	    emitInt (modp);
	    delete m_ofp; m_ofp=NULL;
	}

	m_ofp = newOutCFile (modp, !m_fast, true/*source*/);
    }

    emitImp (modp);
	 
    for (AstNode* nodep=modp->stmtsp(); nodep; nodep = nodep->nextp()) {
	if (AstCFunc* funcp = nodep->castCFunc()) {
	    if (v3Global.opt.outputSplit() > 1 && splitSize()
		&& v3Global.opt.outputSplit() < splitSize()) {
		// Close old file
		emitImpBottom (modp);
		delete m_ofp; m_ofp=NULL;

		// Open a new file
		m_splitSize = 0;
		m_ofp = newOutCFile (modp, !m_fast, true/*source*/, ++m_splitFilenum);
		emitImp (modp);
	    }
	    mainDoFunc(funcp);
	}
    }

    emitImpBottom (modp);
    delete m_ofp; m_ofp=NULL;
}

//######################################################################
// Tracing routines

class EmitCTrace : EmitCStmts {
    AstCFunc*	m_funcp;	// Function we're in now
    bool	m_slow;		// Making slow file
    // METHODS
    void emitTraceHeader() {
	// Includes
	if (optSystemC()) {
	    puts("#include \"SpTraceVcd.h\"\n");
	}
	puts("#include \"SpTraceVcdC.h\"\n");
	puts("#include \""+ symClassName() +".h\"\n");
	puts("\n");
    }

    void emitTraceSlow() {
	puts("\n//======================\n\n");

	puts("void "+topClassName()+"::trace (");
	if (optSystemC()) {
	    puts("SpTraceFile* tfp, int, int) {\n");
	} else {
	    puts("SpTraceVcdCFile* tfp, int, int) {\n");
	}
	puts(  "tfp->spTrace()->addCallback ("
	       "&"+topClassName()+"::traceInit"
	       +", &"+topClassName()+"::traceFull"
	       +", &"+topClassName()+"::traceChg, this);\n");
	puts("}\n");

	puts("void "+topClassName()+"::traceInit(SpTraceVcd* vcdp, void* userthis, uint32_t code) {\n");
	puts("// Callback from vcd->open()\n");
	puts(topClassName()+"* t=("+topClassName()+"*)userthis;\n");
	puts(EmitCBaseVisitor::symClassVar()+" = t->__VlSymsp; // Setup global symbol table\n");
	puts("if (!Verilated::calcUnusedSigs()) vl_fatal(__FILE__,__LINE__,__FILE__,\"Turning on wave traces requires Verilated::traceEverOn(true) call before time 0.\");\n");
	puts("t->traceInitThis (vlSymsp, vcdp, code);\n");
	puts("}\n");
    
	puts("void "+topClassName()+"::traceFull(SpTraceVcd* vcdp, void* userthis, uint32_t code) {\n");
	puts("// Callback from vcd->dump()\n");
	puts(topClassName()+"* t=("+topClassName()+"*)userthis;\n");
	puts(EmitCBaseVisitor::symClassVar()+" = t->__VlSymsp; // Setup global symbol table\n");
	puts("t->traceFullThis (vlSymsp, vcdp, code);\n");
	puts("}\n");

	puts("\n//======================\n\n");
    }

    void emitTraceFast() {
	puts("\n//======================\n\n");

	puts("void "+topClassName()+"::traceChg(SpTraceVcd* vcdp, void* userthis, uint32_t code) {\n");
	puts("// Callback from vcd->dump()\n");
	puts(topClassName()+"* t=("+topClassName()+"*)userthis;\n");
	puts(EmitCBaseVisitor::symClassVar()+" = t->__VlSymsp; // Setup global symbol table\n");
	puts("if (vlSymsp->getClearActivity()) {\n");
	puts("t->traceChgThis (vlSymsp, vcdp, code);\n");
	puts("}\n");
	puts("}\n");

	puts("\n//======================\n\n");
    }

    bool emitTraceIsScWide(AstTraceInc* nodep) {
	AstVarRef* varrefp = nodep->valuep()->castVarRef();
	if (!varrefp) return false;
	AstVar* varp = varrefp->varp();
	return varp->isSc() && varp->isScWide();
    }
    void emitTraceInitOne(AstTraceDecl* nodep) {
	if (nodep->isWide()) {
	    puts("vcdp->declArray");
	} else if (nodep->isQuad()) {
	    puts("vcdp->declQuad ");
	} else if (nodep->msb() || nodep->lsb()) {
	    puts("vcdp->declBus  ");
	} else {
	    puts("vcdp->declBit  ");
	}
	puts("(c+"+cvtToStr(nodep->code()));
	if (nodep->arrayWidth()) puts("+i*"+cvtToStr(nodep->widthWords()));
	puts(",\""+nodep->showname()+"\"");
	if (nodep->arrayWidth()) {
	    puts(",(i+"+cvtToStr(nodep->arrayLsb())+")");
	} else {
	    puts(",-1");
	}
	if (nodep->msb() || nodep->lsb()) {
	    puts(","+cvtToStr(nodep->msb())+","+cvtToStr(nodep->lsb()));
	}
	puts(");");
    }

    void emitTraceChangeOne(AstTraceInc* nodep, int arrayindex) {
	nodep->precondsp()->iterateAndNext(*this);
	string full = (m_funcp->funcType() == AstCFuncType::TRACE_FULL) ? "full":"chg";
	if (nodep->isWide() || emitTraceIsScWide(nodep)) {
	    puts("vcdp->"+full+"Array");
	} else if (nodep->isQuad()) {
	    puts("vcdp->"+full+"Quad ");
	} else if (nodep->declp()->msb() || nodep->declp()->lsb()) {
	    puts("vcdp->"+full+"Bus  ");
	} else {
	    puts("vcdp->"+full+"Bit  ");
	}
	puts("(c+"+cvtToStr(nodep->declp()->code()
			    + ((arrayindex<0) ? 0 : (arrayindex*nodep->declp()->widthWords()))));
	puts(",");
	emitTraceValue(nodep, arrayindex);
	if (nodep->declp()->msb() || nodep->declp()->lsb()) {
	    puts(","+cvtToStr(nodep->declp()->widthMin()));
	}
	puts(");\n");
    }
    void emitTraceValue(AstTraceInc* nodep, int arrayindex) {
	if (nodep->valuep()->castVarRef()) {
	    AstVarRef* varrefp = nodep->valuep()->castVarRef();
	    AstVar* varp = varrefp->varp();
	    if (emitTraceIsScWide(nodep)) puts("(uint32_t*)");
	    puts("(");
	    varrefp->iterate(*this);	// Put var name out
	    if (varp->arraysp()) {
		if (arrayindex==-2) puts("[i]");
		else if (arrayindex==-1) puts("[0]");
		else puts("["+cvtToStr(arrayindex)+"]");
	    }
	    if (varp->isSc()) puts(".read()");
	    if (emitTraceIsScWide(nodep)) puts(".get_datap()");
	    puts(")");
	} else {
	    puts("(");
	    nodep->valuep()->iterate(*this);
	    puts(")");
	}
    }

    // VISITORS
    virtual void visit(AstNetlist* nodep, AstNUser*) {
	// Top module only
	nodep->topModulep()->accept(*this);
    }
    virtual void visit(AstModule* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
    }
    virtual void visit(AstCFunc* nodep, AstNUser*) {
	if (nodep->slow() != m_slow) return;
	if (nodep->funcType() == AstCFuncType::TRACE_INIT
	    || nodep->funcType() == AstCFuncType::TRACE_FULL
	    || nodep->funcType() == AstCFuncType::TRACE_CHANGE) {
	    m_funcp = nodep;

	    puts("\n");
	    puts(nodep->rtnTypeVoid()); puts(" ");
	    puts(topClassName()+"::"+nodep->name()
		 +"("+cFuncArgs(nodep)+") {\n");

	    if (nodep->symProlog()) puts(EmitCBaseVisitor::symTopAssign()+"\n");

	    puts("int c=code;\n");
	    puts("if (0 && vcdp && c) {}  // Prevent unused\n");
	    if (nodep->funcType() == AstCFuncType::TRACE_INIT) {
		puts("vcdp->module(vlSymsp->name()); // Setup signal names\n");
	    } else if (nodep->funcType() == AstCFuncType::TRACE_FULL) {
	    } else if (nodep->funcType() == AstCFuncType::TRACE_CHANGE) {
	    } else nodep->v3fatalSrc("Bad Case");

	    if (nodep->initsp()) puts("// Variables\n");
	    emitVarList(nodep->initsp(), EVL_ALL, "");
	    nodep->initsp()->iterateAndNext(*this);
	    ofp()->putAlign(V3OutFile::AL_AUTO, 4);

	    puts("// Body\n");
	    puts("{\n");
	    // Do the statements  Note not from this node, but the TRACE_INIT's.
	    // That saved us from having 3 copies of all of the TRACEs
	    nodep->stmtsp()->iterateAndNext(*this);
	    puts("}\n");
	    if (nodep->finalsp()) puts("// Final\n");
	    nodep->finalsp()->iterateAndNext(*this);
	    puts("}\n");
	}
	m_funcp = NULL;
    }
    virtual void visit(AstTraceDecl* nodep, AstNUser*) {
	if (nodep->arrayWidth()) {
	    puts("{int i; for (i=0; i<"+cvtToStr(nodep->arrayWidth())+"; i++) {\n");
	    emitTraceInitOne(nodep);
	    puts("}}\n");
	} else {
	    emitTraceInitOne(nodep);
	    puts("\n");
	}
    }
    virtual void visit(AstTraceInc* nodep, AstNUser*) {
	if (nodep->declp()->arrayWidth()) {
	    // It traces faster if we unroll the loop
	    for (unsigned i=0; i<nodep->declp()->arrayWidth(); i++) {
		emitTraceChangeOne(nodep, i);
	    }
	} else {
	    emitTraceChangeOne(nodep, -1);
	}
    }
    virtual void visit(AstCoverDecl* nodep, AstNUser*) {
    }
    virtual void visit(AstCoverInc* nodep, AstNUser*) {
    }
    
public:
    EmitCTrace(bool slow) {
	m_funcp = NULL;
	m_slow = slow;
    }
    virtual ~EmitCTrace() {}
    void main() {
	// Put out the file
	string filename = (v3Global.opt.makeDir()+"/"+ topClassName()
			   + (m_slow?"__Trace__Slow.cpp":"__Trace.cpp"));
	AstCFile* cfilep = newCFile(filename, m_slow, true/*source*/);
	cfilep->support(true);

	V3OutCFile of (filename);
	of.putsHeader();
	m_ofp = &of;

	emitTraceHeader();

	if (m_slow) emitTraceSlow();
	else emitTraceFast();

	v3Global.rootp()->accept(*this);

	m_ofp = NULL;
    }
};

//######################################################################
// EmitC class functions

void V3EmitC::emitc() {
    UINFO(2,__FUNCTION__<<": "<<endl);
    // Process each module in turn
    for (AstModule* nodep = v3Global.rootp()->modulesp(); nodep; nodep=nodep->nextp()->castModule()) {
	if (v3Global.opt.outputSplit()) {
	    { EmitCImp imp; imp.main(nodep, false, true); }
	    { EmitCImp imp; imp.main(nodep, true, false); }
	} else {
	    { EmitCImp imp; imp.main(nodep, true, true); }
	}
    }
}

void V3EmitC::emitcTrace() {
    UINFO(2,__FUNCTION__<<": "<<endl);
    if (v3Global.opt.trace()) {
	{ EmitCTrace trace (true);  trace.main(); }
	{ EmitCTrace trace (false); trace.main(); }
    }
}
