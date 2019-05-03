// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Emit C++ for tree
//
// Code available from: http://www.veripool.org/verilator
//
//*************************************************************************
//
// Copyright 2003-2019 by Wilson Snyder.  This program is free software; you can
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
#include "V3String.h"
#include "V3EmitC.h"
#include "V3EmitCBase.h"
#include "V3Number.h"
#include "V3PartitionGraph.h"
#include "V3TSP.h"

#include <algorithm>
#include <cmath>
#include <cstdarg>
#include <map>
#include <vector>
#include VL_INCLUDE_UNORDERED_SET

#define VL_VALUE_STRING_MAX_WIDTH 8192	// We use a static char array in VL_VALUE_STRING

#define EMITC_NUM_CONSTW	8	// Number of VL_CONST_W_*X's in verilated.h (IE VL_CONST_W_8X is last)

//######################################################################
// Emit statements and math operators

class EmitCStmts : public EmitCBaseVisitor {
private:
    typedef std::vector<const AstVar*> VarVec;
    typedef std::map<int, VarVec> VarSortMap;  // Map size class to VarVec

    bool	m_suppressSemi;
    AstVarRef*	m_wideTempRefp;		// Variable that _WW macros should be setting
    VarVec      m_ctorVarsVec;  // All variables in constructor order
    int		m_splitSize;	// # of cfunc nodes placed into output file
    int		m_splitFilenum;	// File number being created, 0 = primary

public:
    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    // ACCESSORS
    int	splitFilenum() const { return m_splitFilenum; }
    int	splitFilenumInc() { m_splitSize = 0; return ++m_splitFilenum; }
    int splitSize() const { return m_splitSize; }
    void splitSizeInc(int count) { m_splitSize += count; }
    void splitSizeInc(AstNode* nodep) { splitSizeInc(EmitCBaseCounterVisitor(nodep).count()); }
    bool splitNeeded() { return (splitSize() && v3Global.opt.outputSplit()
				 && v3Global.opt.outputSplit() < splitSize()); }

    // METHODS
    void displayNode(AstNode* nodep, AstScopeName* scopenamep,
		     const string& vformat, AstNode* exprsp, bool isScan);
    void displayEmit(AstNode* nodep, bool isScan);
    void displayArg(AstNode* dispp, AstNode** elistp, bool isScan,
		    const string& vfmt, char fmtLetter);

    void emitVarDecl(const AstVar* nodep, const string& prefixIfImp);
    typedef enum {EVL_CLASS_IO, EVL_CLASS_SIG, EVL_CLASS_TEMP, EVL_CLASS_PAR, EVL_CLASS_ALL,
                  EVL_FUNC_ALL} EisWhich;
    void emitVarList(AstNode* firstp, EisWhich which, const string& prefixIfImp);
    static void emitVarSort(const VarSortMap& vmap, VarVec* sortedp);
    void emitSortedVarList(const VarVec& anons,
                           const VarVec& nonanons, const string& prefixIfImp);
    void emitVarCtors(bool* firstp);
    void emitCtorSep(bool* firstp);
    bool emitSimpleOk(AstNodeMath* nodep);
    void emitIQW(AstNode* nodep) {
        // Other abbrevs: "C"har, "S"hort, "F"loat, "D"ouble, stri"N"g
        puts(nodep->dtypep()->charIQWN());
    }
    void emitScIQW(AstVar* nodep) {
	if (!nodep->isSc()) nodep->v3fatalSrc("emitting SystemC operator on non-SC variable");
        puts(nodep->isScBigUint() ? "SB"
             : nodep->isScUint()  ? "SU"
             : nodep->isScBv()    ? "SW"
             : (nodep->isScQuad() ? "SQ" : "SI"));
    }
    void emitOpName(AstNode* nodep, const string& format,
		    AstNode* lhsp, AstNode* rhsp, AstNode* thsp);
    void emitDeclArrayBrackets(const AstVar* nodep) {
	// This isn't very robust and may need cleanup for other data types
        for (const AstUnpackArrayDType* arrayp=VN_CAST_CONST(nodep->dtypeSkipRefp(), UnpackArrayDType); arrayp;
             arrayp = VN_CAST_CONST(arrayp->subDTypep()->skipRefp(), UnpackArrayDType)) {
	    puts("["+cvtToStr(arrayp->elementsConst())+"]");
	}
    }
    void emitVarCmtChg(const AstVar* varp, string* curVarCmtp) {
        string newVarCmt = varp->mtasksString();
        if (*curVarCmtp != newVarCmt) {
            *curVarCmtp = newVarCmt;
            puts("// Begin mtask footprint "+*curVarCmtp+"\n");
        }
    }
    void emitTypedefs(AstNode* firstp) {
	bool first = true;
	for (AstNode* loopp=firstp; loopp; loopp = loopp->nextp()) {
            if (const AstTypedef* nodep = VN_CAST(loopp, Typedef)) {
		if (nodep->attrPublic()) {
		    if (first) {
			first = false;
			puts("\n// TYPEDEFS\n");
			puts("// That were declared public\n");
		    } else {
			puts("\n");
		    }
                    if (const AstEnumDType* adtypep = VN_CAST(nodep->dtypep()->skipRefToEnump(), EnumDType)) {
			if (adtypep->width()>64) {
			    putsDecoration("// enum "+nodep->name()+" // Ignored: Too wide for C++\n");
			} else {
			    puts("enum "+nodep->name()+" {\n");
                            for (AstEnumItem* itemp = adtypep->itemsp(); itemp; itemp=VN_CAST(itemp->nextp(), EnumItem)) {
				puts(itemp->name());
				puts(" = ");
                                iterateAndNextNull(itemp->valuep());
                                if (VN_IS(itemp->nextp(), EnumItem)) puts(",");
				puts("\n");
			    }
			    puts("};\n");
			}
		    }
		}
	    }
	}
    }

    // VISITORS
    virtual void visit(AstNodeAssign* nodep) {
	bool paren = true;  bool decind = false;
        if (AstSel* selp=VN_CAST(nodep->lhsp(), Sel)) {
	    if (selp->widthMin()==1) {
		putbs("VL_ASSIGNBIT_");
		emitIQW(selp->fromp());
		if (nodep->rhsp()->isAllOnesV()) {
		    puts("O(");
		} else {
		    puts("I(");
		}
		puts(cvtToStr(nodep->widthMin())+",");
                iterateAndNextNull(selp->lsbp()); puts(", ");
                iterateAndNextNull(selp->fromp()); puts(", ");
	    } else {
		putbs("VL_ASSIGNSEL_");
                emitIQW(selp->fromp());
		puts("II");
		emitIQW(nodep->rhsp());
		puts("(");
		puts(cvtToStr(nodep->widthMin())+",");
                iterateAndNextNull(selp->lsbp()); puts(", ");
                iterateAndNextNull(selp->fromp()); puts(", ");
	    }
	} else if (AstVar* varp = AstVar::scVarRecurse(nodep->lhsp())) {
	    putbs("VL_ASSIGN_"); 	// Set a systemC variable
	    emitScIQW(varp);
	    emitIQW(nodep);
	    puts("(");
	    puts(cvtToStr(nodep->widthMin())+",");
            iterateAndNextNull(nodep->lhsp()); puts(", ");
	} else if (AstVar* varp = AstVar::scVarRecurse(nodep->rhsp())) {
	    putbs("VL_ASSIGN_"); 	// Get a systemC variable
	    emitIQW(nodep);
	    emitScIQW(varp);
	    puts("(");
	    puts(cvtToStr(nodep->widthMin())+",");
            iterateAndNextNull(nodep->lhsp()); puts(", ");
	} else if (nodep->isWide()
                   && VN_IS(nodep->lhsp(), VarRef)
                   && !VN_IS(nodep->rhsp(), CMath)
                   && !VN_IS(nodep->rhsp(), VarRef)
                   && !VN_IS(nodep->rhsp(), ArraySel)) {
	    // Wide functions assign into the array directly, don't need separate assign statement
            m_wideTempRefp = VN_CAST(nodep->lhsp(), VarRef);
	    paren = false;
	} else if (nodep->isWide()) {
	    putbs("VL_ASSIGN_W(");
	    puts(cvtToStr(nodep->widthMin())+",");
            iterateAndNextNull(nodep->lhsp()); puts(", ");
	} else {
	    paren = false;
            iterateAndNextNull(nodep->lhsp());
	    puts(" ");
	    ofp()->blockInc(); decind = true;
            if (!VN_IS(nodep->rhsp(), Const)) ofp()->putBreak();
	    puts("= ");
	}
        iterateAndNextNull(nodep->rhsp());
	if (paren) puts(")");
	if (decind) ofp()->blockDec();
	if (!m_suppressSemi) puts(";\n");
    }
    virtual void visit(AstAlwaysPublic*) {
    }
    virtual void visit(AstCCall* nodep) {
	puts(nodep->hiername());
	puts(nodep->funcp()->name());
	puts("(");
	puts(nodep->argTypes());
	bool comma = (nodep->argTypes() != "");
	for (AstNode* subnodep=nodep->argsp(); subnodep; subnodep = subnodep->nextp()) {
	    if (comma) puts(", ");
            iterate(subnodep);
	    comma = true;
	}
        if (VN_IS(nodep->backp(), NodeMath) || VN_IS(nodep->backp(), CReturn)) {
	    // We should have a separate CCall for math and statement usage, but...
	    puts(")");
	} else {
	    puts(");\n");
	}
    }
    virtual void visit(AstNodeCase* nodep) {
	// In V3Case...
	nodep->v3fatalSrc("Case statements should have been reduced out");
    }
    virtual void visit(AstComment* nodep) {
        putsDecoration(string("// ")+nodep->name()+" at "+nodep->fileline()->ascii()+"\n");
        iterateChildren(nodep);
    }
    virtual void visit(AstCoverDecl* nodep) {
	puts("__vlCoverInsert(");	// As Declared in emitCoverageDecl
	puts("&(vlSymsp->__Vcoverage[");
	puts(cvtToStr(nodep->dataDeclThisp()->binNum())); puts("])");
	// If this isn't the first instantiation of this module under this
	// design, don't really count the bucket, and rely on verilator_cov to
	// aggregate counts.  This is because Verilator combines all
	// hiearchies itself, and if verilator_cov also did it, you'd end up
	// with (number-of-instant) times too many counts in this bin.
	puts(", first");  // Enable, passed from __Vconfigure parameter
	puts(", ");	putsQuoted(nodep->fileline()->filename());
	puts(", ");	puts(cvtToStr(nodep->fileline()->lineno()));
	puts(", ");	puts(cvtToStr(nodep->column()));
	puts(", ");	putsQuoted((nodep->hier()!=""?".":"")+nodep->hier());
	puts(", ");	putsQuoted(nodep->page());
	puts(", ");	putsQuoted(nodep->comment());
	puts(");\n");
    }
    virtual void visit(AstCoverInc* nodep) {
	puts("++(vlSymsp->__Vcoverage[");
	puts(cvtToStr(nodep->declp()->dataDeclThisp()->binNum()));
	puts("]);\n");
    }
    virtual void visit(AstCReturn* nodep) {
	puts("return (");
        iterateAndNextNull(nodep->lhsp());
	puts(");\n");
    }
    virtual void visit(AstDisplay* nodep) {
	string text = nodep->fmtp()->text();
	if (nodep->addNewline()) text += "\n";
	displayNode(nodep, nodep->fmtp()->scopeNamep(), text, nodep->fmtp()->exprsp(), false);
    }
    virtual void visit(AstScopeName* nodep) {
	// For use under AstCCalls for dpiImports.  ScopeNames under displays are handled in AstDisplay
	if (!nodep->dpiExport()) {
	    // this is where the DPI import context scope is set
	    string scope = nodep->scopeDpiName();
	    putbs("(&(vlSymsp->__Vscope_"+scope+"))");
	}
    }
    virtual void visit(AstSFormat* nodep) {
	displayNode(nodep, nodep->fmtp()->scopeNamep(), nodep->fmtp()->text(), nodep->fmtp()->exprsp(), false);
    }
    virtual void visit(AstSFormatF* nodep) {
	displayNode(nodep, nodep->scopeNamep(), nodep->text(), nodep->exprsp(), false);
    }
    virtual void visit(AstFScanF* nodep) {
	displayNode(nodep, NULL, nodep->text(), nodep->exprsp(), true);
    }
    virtual void visit(AstSScanF* nodep) {
	displayNode(nodep, NULL, nodep->text(), nodep->exprsp(), true);
    }
    virtual void visit(AstValuePlusArgs* nodep) {
	puts("VL_VALUEPLUSARGS_IN");
	emitIQW(nodep->outp());
	puts("(");
	puts(cvtToStr(nodep->outp()->widthMin()));
	puts(",");
	emitCvtPackStr(nodep->searchp());
	puts(",");
	putbs("");
        iterateAndNextNull(nodep->outp());
	puts(")");
    }
    virtual void visit(AstTestPlusArgs* nodep) {
	puts("VL_TESTPLUSARGS_I(");
	putsQuoted(nodep->text());
	puts(")");
    }
    virtual void visit(AstFGetS* nodep) {
	checkMaxWords(nodep);
	emitOpName(nodep, nodep->emitC(), nodep->lhsp(), nodep->rhsp(), NULL);
    }

    void checkMaxWords(AstNode* nodep) {
	if (nodep->widthWords() > VL_TO_STRING_MAX_WORDS) {
	    nodep->v3error("String of "<<nodep->width()<<" bits exceeds hardcoded limit VL_TO_STRING_MAX_WORDS in verilatedos.h");
	}
    }
    virtual void visit(AstFOpen* nodep) {
        iterateAndNextNull(nodep->filep());
	puts(" = VL_FOPEN_");
	emitIQW(nodep->filenamep());
	emitIQW(nodep->modep());
	if (nodep->modep()->width()>4*8) nodep->modep()->v3error("$fopen mode should be <= 4 characters");
	puts("(");
	if (nodep->filenamep()->isWide()) {
	    puts(cvtToStr(nodep->filenamep()->widthWords()));
	    putbs(", ");
	}
	checkMaxWords(nodep->filenamep());
        iterateAndNextNull(nodep->filenamep());
	putbs(", ");
        iterateAndNextNull(nodep->modep());
	puts(");\n");
    }
    virtual void visit(AstNodeReadWriteMem* nodep) {
        puts(nodep->cFuncPrefixp());
	emitIQW(nodep->filenamep());
        puts("(");  // We take a void* rather than emitIQW(nodep->memp());
	puts(nodep->isHex()?"true":"false");
	putbs(",");
	puts(cvtToStr(nodep->memp()->widthMin()));  // Need real storage width
	putbs(",");
	uint32_t array_lsb = 0;
	{
            const AstVarRef* varrefp = VN_CAST(nodep->memp(), VarRef);
            if (!varrefp) { nodep->v3error(nodep->verilogKwd() << " loading non-variable"); }
            else if (const AstUnpackArrayDType* adtypep = VN_CAST(varrefp->varp()->dtypeSkipRefp(), UnpackArrayDType)) {
		puts(cvtToStr(varrefp->varp()->dtypep()->arrayUnpackedElements()));
		array_lsb = adtypep->lsb();
	    }
	    else {
		nodep->v3error(nodep->verilogKwd()
                               << " loading other than unpacked-array variable");
	    }
	}
	putbs(", ");
	puts(cvtToStr(array_lsb));
	putbs(",");
        if (!nodep->filenamep()->dtypep()->isString()) {
            puts(cvtToStr(nodep->filenamep()->widthWords()));
            checkMaxWords(nodep->filenamep());
            putbs(", ");
        }
        iterateAndNextNull(nodep->filenamep());
	putbs(", ");
        iterateAndNextNull(nodep->memp());
        putbs(","); if (nodep->lsbp()) { iterateAndNextNull(nodep->lsbp()); }
	else puts(cvtToStr(array_lsb));
        putbs(","); if (nodep->msbp()) { iterateAndNextNull(nodep->msbp()); } else puts("~0");
	puts(");\n");
    }
    virtual void visit(AstFClose* nodep) {
	puts("VL_FCLOSE_I(");
        iterateAndNextNull(nodep->filep());
	puts("); ");
        iterateAndNextNull(nodep->filep());  // For saftey, so user doesn't later WRITE with it.
	puts("=0;\n");
    }
    virtual void visit(AstFFlush* nodep) {
	if (!nodep->filep()) {
            puts("fflush(stdout);\n");
	} else {
	    puts("if (");
            iterateAndNextNull(nodep->filep());
            puts(") { fflush(VL_CVT_I_FP(");
            iterateAndNextNull(nodep->filep());
	    puts(")); }\n");
	}
    }
    virtual void visit(AstFRead* nodep) {
        puts("VL_FREAD_I(");
        puts(cvtToStr(nodep->memp()->widthMin()));  // Need real storage width
        putbs(",");
        bool memory = false;
        uint32_t array_lsb = 0;
        uint32_t array_size = 0;
        {
            const AstVarRef* varrefp = VN_CAST(nodep->memp(), VarRef);
            if (!varrefp) { nodep->v3error(nodep->verilogKwd() << " loading non-variable"); }
            else if (VN_CAST(varrefp->varp()->dtypeSkipRefp(), BasicDType)) { }
            else if (const AstUnpackArrayDType* adtypep
                     = VN_CAST(varrefp->varp()->dtypeSkipRefp(), UnpackArrayDType)) {
                memory = true;
                array_lsb = adtypep->lsb();
                array_size = adtypep->elementsConst();
            }
            else {
                nodep->v3error(nodep->verilogKwd()
                               << " loading other than unpacked-array variable");
            }
        }
        puts(cvtToStr(array_lsb));
        putbs(",");
        puts(cvtToStr(array_size));
        putbs(", ");
        if (!memory) puts("&(");
        iterateAndNextNull(nodep->memp());
        if (!memory) puts(")");
        putbs(", ");
        iterateAndNextNull(nodep->filep());
        putbs(", ");
        if (nodep->startp()) iterateAndNextNull(nodep->startp());
        else puts(cvtToStr(array_lsb));
        putbs(", ");
        if (nodep->countp()) iterateAndNextNull(nodep->countp());
        else puts(cvtToStr(array_size));
        puts(");\n");
    }
    virtual void visit(AstSysFuncAsTask* nodep) {
        if (!nodep->lhsp()->isWide()) puts("(void)");
        iterateAndNextNull(nodep->lhsp());
        if (!nodep->lhsp()->isWide()) puts(";");
    }
    virtual void visit(AstSystemT* nodep) {
	puts("(void)VL_SYSTEM_I");
	emitIQW(nodep->lhsp());
	puts("(");
	if (nodep->lhsp()->isWide()) {
	    puts(cvtToStr(nodep->lhsp()->widthWords()));
	    putbs(", ");
	}
	checkMaxWords(nodep->lhsp());
        iterateAndNextNull(nodep->lhsp());
	puts(");\n");
    }
    virtual void visit(AstSystemF* nodep) {
	puts("VL_SYSTEM_I");
	emitIQW(nodep->lhsp());
	puts("(");
	if (nodep->lhsp()->isWide()) {
	    puts(cvtToStr(nodep->lhsp()->widthWords()));
	    putbs(", ");
	}
	checkMaxWords(nodep->lhsp());
        iterateAndNextNull(nodep->lhsp());
	puts(")");
    }
    virtual void visit(AstJumpGo* nodep) {
	puts("goto __Vlabel"+cvtToStr(nodep->labelp()->labelNum())+";\n");
    }
    virtual void visit(AstJumpLabel* nodep) {
	puts("{\n");
        iterateAndNextNull(nodep->stmtsp());
	puts("}\n");
	puts("__Vlabel"+cvtToStr(nodep->labelNum())+": ;\n");
    }
    virtual void visit(AstWhile* nodep) {
        iterateAndNextNull(nodep->precondsp());
	puts("while (");
        iterateAndNextNull(nodep->condp());
	puts(") {\n");
        iterateAndNextNull(nodep->bodysp());
        iterateAndNextNull(nodep->incsp());
        iterateAndNextNull(nodep->precondsp());  // Need to recompute before next loop
	puts("}\n");
    }
    virtual void visit(AstNodeIf* nodep) {
	puts("if (");
	if (nodep->branchPred() != AstBranchPred::BP_UNKNOWN) {
	    puts(nodep->branchPred().ascii()); puts("(");
	}
        iterateAndNextNull(nodep->condp());
	if (nodep->branchPred() != AstBranchPred::BP_UNKNOWN) puts(")");
	puts(") {\n");
        iterateAndNextNull(nodep->ifsp());
	if (nodep->elsesp()) {
	    puts("} else {\n");
            iterateAndNextNull(nodep->elsesp());
	}
	puts("}\n");
    }
    virtual void visit(AstStop* nodep) {
	puts("VL_STOP_MT(");
	putsQuoted(nodep->fileline()->filename());
	puts(",");
	puts(cvtToStr(nodep->fileline()->lineno()));
	puts(",\"\");\n");
    }
    virtual void visit(AstFinish* nodep) {
	puts("VL_FINISH_MT(");
	putsQuoted(nodep->fileline()->filename());
	puts(",");
	puts(cvtToStr(nodep->fileline()->lineno()));
	puts(",\"\");\n");
    }
    virtual void visit(AstText* nodep) {
	if (nodep->tracking()) {
	    puts(nodep->text());
	} else {
	    ofp()->putsNoTracking(nodep->text());
	}
    }
    virtual void visit(AstCStmt* nodep) {
	putbs("");
        iterateAndNextNull(nodep->bodysp());
    }
    virtual void visit(AstCMath* nodep) {
	putbs("");
        iterateAndNextNull(nodep->bodysp());
    }
    virtual void visit(AstUCStmt* nodep) {
	putsDecoration("// $c statement at "+nodep->fileline()->ascii()+"\n");
        iterateAndNextNull(nodep->bodysp());
	puts("\n");
    }
    virtual void visit(AstUCFunc* nodep) {
	puts("\n");
	putsDecoration("// $c function at "+nodep->fileline()->ascii()+"\n");
        iterateAndNextNull(nodep->bodysp());
	puts("\n");
    }

    // Operators
    virtual void visit(AstNodeTermop* nodep) {
	emitOpName(nodep, nodep->emitC(), NULL, NULL, NULL);
    }
    virtual void visit(AstNodeUniop* nodep) {
	if (emitSimpleOk(nodep)) {
	    putbs("("); puts(nodep->emitSimpleOperator()); puts(" ");
            iterateAndNextNull(nodep->lhsp()); puts(")");
	} else {
	    emitOpName(nodep, nodep->emitC(), nodep->lhsp(), NULL, NULL);
	}
    }
    virtual void visit(AstNodeBiop* nodep) {
	if (emitSimpleOk(nodep)) {
            putbs("("); iterateAndNextNull(nodep->lhsp());
	    puts(" "); putbs(nodep->emitSimpleOperator()); puts(" ");
            iterateAndNextNull(nodep->rhsp()); puts(")");
	} else {
	    emitOpName(nodep, nodep->emitC(), nodep->lhsp(), nodep->rhsp(), NULL);
	}
    }
    virtual void visit(AstRedXor* nodep) {
	if (nodep->lhsp()->isWide()) {
            visit(VN_CAST(nodep, NodeUniop));
	} else {
	    putbs("VL_REDXOR_");
	    puts(cvtToStr(nodep->lhsp()->dtypep()->widthPow2()));
	    puts("(");
            iterateAndNextNull(nodep->lhsp());
	    puts(")");
	}
    }
    virtual void visit(AstMulS* nodep) {
	if (nodep->widthWords() > VL_MULS_MAX_WORDS) {
            nodep->v3error("Unsupported: Signed multiply of "<<nodep->width()
                           <<" bits exceeds hardcoded limit VL_MULS_MAX_WORDS in verilatedos.h");
	}
        visit(VN_CAST(nodep, NodeBiop));
    }
    virtual void visit(AstPow* nodep) {
	if (nodep->widthWords() > VL_MULS_MAX_WORDS) {
            nodep->v3error("Unsupported: Power of "<<nodep->width()
                           <<" bits exceeds hardcoded limit VL_MULS_MAX_WORDS in verilatedos.h");
	}
        visit(VN_CAST(nodep, NodeBiop));
    }
    virtual void visit(AstPowSS* nodep) {
	if (nodep->widthWords() > VL_MULS_MAX_WORDS) {
            nodep->v3error("Unsupported: Power of "<<nodep->width()
                           <<" bits exceeds hardcoded limit VL_MULS_MAX_WORDS in verilatedos.h");
	}
        visit(VN_CAST(nodep, NodeBiop));
    }
    virtual void visit(AstPowSU* nodep) {
	if (nodep->widthWords() > VL_MULS_MAX_WORDS) {
            nodep->v3error("Unsupported: Power of "<<nodep->width()
                           <<" bits exceeds hardcoded limit VL_MULS_MAX_WORDS in verilatedos.h");
	}
        visit(VN_CAST(nodep, NodeBiop));
    }
    virtual void visit(AstPowUS* nodep) {
	if (nodep->widthWords() > VL_MULS_MAX_WORDS) {
            nodep->v3error("Unsupported: Power of "<<nodep->width()
                           <<" bits exceeds hardcoded limit VL_MULS_MAX_WORDS in verilatedos.h");
	}
        visit(VN_CAST(nodep, NodeBiop));
    }
    virtual void visit(AstCCast* nodep) {
	// Extending a value of the same word width is just a NOP.
	if (nodep->size()>VL_WORDSIZE) {
	    puts("(QData)(");
	} else {
	    puts("(IData)(");
	}
        iterateAndNextNull(nodep->lhsp());
	puts(")");
    }
    virtual void visit(AstNodeCond* nodep) {
	// Widths match up already, so we'll just use C++'s operator w/o any temps.
	if (nodep->expr1p()->isWide()) {
	    emitOpName(nodep, nodep->emitC(), nodep->condp(), nodep->expr1p(), nodep->expr2p());
	} else {
	    putbs("(");
            iterateAndNextNull(nodep->condp()); putbs(" ? ");
            iterateAndNextNull(nodep->expr1p()); putbs(" : ");
            iterateAndNextNull(nodep->expr2p()); puts(")");
	}
    }
    virtual void visit(AstSel* nodep) {
	// Note ASSIGN checks for this on a LHS
	emitOpName(nodep, nodep->emitC(), nodep->fromp(), nodep->lsbp(), nodep->thsp());
    }
    virtual void visit(AstReplicate* nodep) {
	if (nodep->lhsp()->widthMin() == 1 && !nodep->isWide()) {
            if ((static_cast<int>(VN_CAST(nodep->rhsp(), Const)->toUInt())
                 * nodep->lhsp()->widthMin()) != nodep->widthMin())
		nodep->v3fatalSrc("Replicate non-constant or width miscomputed");
	    puts("VL_REPLICATE_");
	    emitIQW(nodep);
	    puts("OI(");
	    puts(cvtToStr(nodep->widthMin()));
	    if (nodep->lhsp()) { puts(","+cvtToStr(nodep->lhsp()->widthMin())); }
	    if (nodep->rhsp()) { puts(","+cvtToStr(nodep->rhsp()->widthMin())); }
	    puts(",");
            iterateAndNextNull(nodep->lhsp()); puts(", ");
            iterateAndNextNull(nodep->rhsp()); puts(")");
	} else {
	    emitOpName(nodep, nodep->emitC(), nodep->lhsp(), nodep->rhsp(), NULL);
	}
    }
    virtual void visit(AstStreamL* nodep) {
	// Attempt to use a "fast" stream function for slice size = power of 2
	if (!nodep->isWide()) {
            uint32_t isPow2 = VN_CAST(nodep->rhsp(), Const)->num().countOnes() == 1;
            uint32_t sliceSize = VN_CAST(nodep->rhsp(), Const)->toUInt();
	    if (isPow2 && sliceSize <= (nodep->isQuad() ? sizeof(uint64_t) : sizeof(uint32_t))) {
		puts("VL_STREAML_FAST_");
		emitIQW(nodep);
		emitIQW(nodep->lhsp());
		puts("I(");
		puts(cvtToStr(nodep->widthMin()));
		puts(","+cvtToStr(nodep->lhsp()->widthMin()));
		puts(","+cvtToStr(nodep->rhsp()->widthMin()));
		puts(",");
                iterateAndNextNull(nodep->lhsp()); puts(", ");
                uint32_t rd_log2 = V3Number::log2b(VN_CAST(nodep->rhsp(), Const)->toUInt());
		puts(cvtToStr(rd_log2)+")");
		return;
	    }
	}
	emitOpName(nodep, "VL_STREAML_%nq%lq%rq(%nw,%lw,%rw, %P, %li, %ri)", nodep->lhsp(), nodep->rhsp(), NULL);
    }
    // Terminals
    virtual void visit(AstVarRef* nodep) {
	puts(nodep->hiername());
	puts(nodep->varp()->name());
    }
    void emitCvtPackStr(AstNode* nodep) {
        if (const AstConst* constp = VN_CAST(nodep, Const)) {
	    putbs("std::string(");
	    putsQuoted(constp->num().toString());
	    puts(")");
	} else {
	    putbs("VL_CVT_PACK_STR_N");
	    emitIQW(nodep);
	    puts("(");
	    if (nodep->isWide()) {
		puts(cvtToStr(nodep->widthWords()));  // Note argument width, not node width (which is always 32)
		puts(",");
	    }
            iterateAndNextNull(nodep);
	    puts(")");
	}
    }
    void emitConstant(AstConst* nodep, AstVarRef* assigntop, const string& assignString) {
	// Put out constant set to the specified variable, or given variable in a string
	if (nodep->num().isFourState()) {
	    nodep->v3error("Unsupported: 4-state numbers in this context");
	} else if (nodep->num().isString()) {
	    putbs("std::string(");
	    putsQuoted(nodep->num().toString());
	    puts(")");
	} else if (nodep->isWide()) {
	    int upWidth = nodep->num().widthMin();
	    int chunks = 0;
	    if (upWidth > EMITC_NUM_CONSTW*VL_WORDSIZE) {
		// Output e.g. 8 words in groups of e.g. 8
		chunks = (upWidth-1) / (EMITC_NUM_CONSTW*VL_WORDSIZE);
		upWidth %= (EMITC_NUM_CONSTW*VL_WORDSIZE);
		if (upWidth == 0) upWidth = (EMITC_NUM_CONSTW*VL_WORDSIZE);
	    }
	    {	// Upper e.g. 8 words
		if (chunks) {
		    putbs("VL_CONSTHI_W_");
		    puts(cvtToStr(VL_WORDS_I(upWidth)));
		    puts("X(");
		    puts(cvtToStr(nodep->widthMin()));
		    puts(",");
		    puts(cvtToStr(chunks*EMITC_NUM_CONSTW*VL_WORDSIZE));
		} else {
		    putbs("VL_CONST_W_");
		    puts(cvtToStr(VL_WORDS_I(upWidth)));
		    puts("X(");
		    puts(cvtToStr(nodep->widthMin()));
		}
		puts(",");
		if (!assigntop) {
		    puts(assignString);
                } else if (VN_IS(assigntop, VarRef)) {
		    puts(assigntop->hiername());
		    puts(assigntop->varp()->name());
		} else {
                    iterateAndNextNull(assigntop);
		}
		for (int word=VL_WORDS_I(upWidth)-1; word>=0; word--) {
		    // Only 32 bits - llx + long long here just to appease CPP format warning
                    ofp()->printf(",0x%08" VL_PRI64 "x",
                                  static_cast<vluint64_t>(nodep->num().dataWord
                                                          (word+chunks*EMITC_NUM_CONSTW)));
		}
		puts(")");
	    }
	    for (chunks--; chunks >= 0; chunks--) {
		puts(";\n");
		putbs("VL_CONSTLO_W_");
		puts(cvtToStr(EMITC_NUM_CONSTW));
		puts("X(");
		puts(cvtToStr(chunks*EMITC_NUM_CONSTW*VL_WORDSIZE));
		puts(",");
		if (!assigntop) {
		    puts(assignString);
                } else if (VN_IS(assigntop, VarRef)) {
		    puts(assigntop->hiername());
		    puts(assigntop->varp()->name());
		} else {
                    iterateAndNextNull(assigntop);
		}
		for (int word=EMITC_NUM_CONSTW-1; word>=0; word--) {
		    // Only 32 bits - llx + long long here just to appease CPP format warning
                    ofp()->printf(",0x%08" VL_PRI64 "x",
                                  static_cast<vluint64_t>(nodep->num().dataWord
                                                          (word+chunks*EMITC_NUM_CONSTW)));
		}
		puts(")");
	    }
	} else if (nodep->isDouble()) {
	    if (int(nodep->num().toDouble()) == nodep->num().toDouble()
		&& nodep->num().toDouble() < 1000
		&& nodep->num().toDouble() > -1000) {
		ofp()->printf("%3.1f", nodep->num().toDouble());  // Force decimal point
	    } else {
		// Not %g as will not always put in decimal point, so not obvious to compiler
		// is a real number
		ofp()->printf("%.17e", nodep->num().toDouble());
	    }
	} else if (nodep->isQuad()) {
	    vluint64_t num = nodep->toUQuad();
	    if (num<10) ofp()->printf("VL_ULL(%" VL_PRI64 "u)", num);
	    else ofp()->printf("VL_ULL(0x%" VL_PRI64 "x)", num);
	} else {
	    uint32_t num = nodep->toUInt();
	    // Only 32 bits - llx + long long here just to appease CPP format warning
	    if (num<10) puts(cvtToStr(num));
            else ofp()->printf("0x%" VL_PRI64 "x", static_cast<vluint64_t>(num));
	    // If signed, we'll do our own functions
	    // But must be here, or <= comparisons etc may end up signed
	    puts("U");
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
    virtual void visit(AstConst* nodep) {
	if (nodep->isWide()) {
	    if (!m_wideTempRefp) nodep->v3fatalSrc("Wide Constant w/ no temp");
	    emitConstant(nodep, m_wideTempRefp, "");
	    m_wideTempRefp = NULL;   // We used it, barf if set it a second time
	} else {
	    emitConstant(nodep, NULL, "");
	}
    }

    // Just iterate
    virtual void visit(AstNetlist* nodep) {
        iterateChildren(nodep);
    }
    virtual void visit(AstTopScope* nodep) {
        iterateChildren(nodep);
    }
    virtual void visit(AstScope* nodep) {
        iterateChildren(nodep);
    }
    // NOPs
    virtual void visit(AstTypedef*) {}
    virtual void visit(AstPragma*) {}
    virtual void visit(AstCell*) {}		// Handled outside the Visit class
    virtual void visit(AstVar*) {}		// Handled outside the Visit class
    virtual void visit(AstNodeText*) {}	// Handled outside the Visit class
    virtual void visit(AstTraceDecl*) {}	// Handled outside the Visit class
    virtual void visit(AstTraceInc*) {}	// Handled outside the Visit class
    virtual void visit(AstCFile*) {}		// Handled outside the Visit class
    // Default
    virtual void visit(AstNode* nodep) {
        puts(string("\n???? // ")+nodep->prettyTypeName()+"\n");
        iterateChildren(nodep);
	nodep->v3fatalSrc("Unknown node type reached emitter: "<<nodep->prettyTypeName());
    }

public:
    EmitCStmts() {
	m_suppressSemi = false;
	m_wideTempRefp = NULL;
	m_splitSize = 0;
	m_splitFilenum = 0;
    }
    virtual ~EmitCStmts() {}
};

//######################################################################
// Establish mtask variable sort order in mtasks mode

class EmitVarTspSorter : public V3TSP::TspStateBase {
private:
    // MEMBERS
    const MTaskIdSet& m_mtaskIds;  // Mtask we're ordering
    static unsigned m_serialNext;  // Unique ID to establish serial order
    unsigned m_serial;  // Serial ordering
public:
    // CONSTRUCTORS
    explicit EmitVarTspSorter(const MTaskIdSet& mtaskIds)
        : m_mtaskIds(mtaskIds),
          m_serial(++m_serialNext) {}
    virtual ~EmitVarTspSorter() {}
    // METHODS
    bool operator<(const TspStateBase& other) const {
        return operator<(dynamic_cast<const EmitVarTspSorter&>(other));
    }
    bool operator<(const EmitVarTspSorter& other) const {
        return m_serial < other.m_serial;
    }
    const MTaskIdSet& mtaskIds() const { return m_mtaskIds; }
    virtual int cost(const TspStateBase* otherp) const {
        return cost(dynamic_cast<const EmitVarTspSorter*>(otherp));
    }
    virtual int cost(const EmitVarTspSorter* otherp) const {
        int cost = diffs(m_mtaskIds, otherp->m_mtaskIds);
        cost += diffs(otherp->m_mtaskIds, m_mtaskIds);
        return cost;
    }
    // Returns the number of elements in set_a that don't appear in set_b
    static int diffs(const MTaskIdSet& set_a, const MTaskIdSet& set_b) {
        int diffs = 0;
        for (MTaskIdSet::iterator it = set_a.begin();
             it != set_a.end(); ++it) {
            if (set_b.find(*it) == set_b.end()) ++diffs;
        }
        return diffs;
    }
};

unsigned EmitVarTspSorter::m_serialNext = 0;

//######################################################################
// Internal EmitC implementation

class EmitCImp : EmitCStmts {
    // MEMBERS
    AstNodeModule*	m_modp;
    std::vector<AstChangeDet*> m_blkChangeDetVec;  // All encountered changes in block
    bool	m_slow;		// Creating __Slow file
    bool	m_fast;		// Creating non __Slow file (or both)

    //---------------------------------------
    // METHODS

    void doubleOrDetect(AstChangeDet* changep, bool& gotOne) {
        static int s_addDoubleOr = 10;  // Determined experimentally as best
	if (!changep->rhsp()) {
	    if (!gotOne) gotOne = true;
	    else puts(" | ");
            iterateAndNextNull(changep->lhsp());
	}
	else {
	    AstNode* lhsp = changep->lhsp();
	    AstNode* rhsp = changep->rhsp();
            if (!VN_IS(lhsp, VarRef) && !VN_IS(lhsp, ArraySel)) changep->v3fatalSrc("Not ref?");
            if (!VN_IS(rhsp, VarRef) && !VN_IS(rhsp, ArraySel)) changep->v3fatalSrc("Not ref?");
            for (int word=0;
                 word < (changep->lhsp()->isWide() ? changep->lhsp()->widthWords() : 1);
                 ++word) {
		if (!gotOne) {
		    gotOne = true;
                    s_addDoubleOr = 10;
		    puts("(");
                } else if (--s_addDoubleOr == 0) {
		    puts("|| (");
                    s_addDoubleOr = 10;
		} else {
		    puts(" | (");
		}
                iterateAndNextNull(changep->lhsp());
		if (changep->lhsp()->isWide()) puts("["+cvtToStr(word)+"]");
		if (changep->lhsp()->isDouble()) puts(" != ");
		else puts(" ^ ");
                iterateAndNextNull(changep->rhsp());
		if (changep->lhsp()->isWide()) puts("["+cvtToStr(word)+"]");
		puts(")");
	    }
	}
    }

    V3OutCFile* newOutCFile(AstNodeModule* modp, bool slow, bool source, int filenum=0) {
	string filenameNoExt = v3Global.opt.makeDir()+"/"+ modClassName(modp);
	if (filenum) filenameNoExt += "__"+cvtToStr(filenum);
	filenameNoExt += (slow ? "__Slow":"");
	V3OutCFile* ofp = NULL;
	if (v3Global.opt.lintOnly()) {
	    // Unfortunately we have some lint checks here, so we can't just skip processing.
	    // We should move them to a different stage.
	    string filename = VL_DEV_NULL;
	    newCFile(filename, slow, source);
            ofp = new V3OutCFile(filename);
	}
	else if (optSystemC()) {
	    string filename = filenameNoExt+(source?".cpp":".h");
	    newCFile(filename, slow, source);
            ofp = new V3OutScFile(filename);
	}
	else {
	    string filename = filenameNoExt+(source?".cpp":".h");
	    newCFile(filename, slow, source);
            ofp = new V3OutCFile(filename);
	}

	ofp->putsHeader();
	if (modp->isTop() && !source) {
	    ofp->puts("// DESCR" "IPTION: Verilator output: Primary design header\n");
	    ofp->puts("//\n");
	    ofp->puts("// This header should be included by all source files instantiating the design.\n");
	    ofp->puts("// The class here is then constructed to instantiate the design.\n");
	    ofp->puts("// See the Verilator manual for examples.\n");
	} else {
	    if (source) {
		ofp->puts("// DESCR" "IPTION: Verilator output: Design implementation internals\n");
	    } else {
		ofp->puts("// DESCR" "IPTION: Verilator output: Design internal header\n");
	    }
	    ofp->puts("// See "+v3Global.opt.prefix()+".h for the primary calling header\n");
	}
	ofp->puts("\n");

	return ofp;
    }

    // Returns the number of cross-thread dependencies into mtaskp.
    // If >0, mtaskp must test whether its prereqs are done before starting,
    // and may need to block.
    static uint32_t packedMTaskMayBlock(const ExecMTask* mtaskp) {
        uint32_t result = 0;
        for (V3GraphEdge* edgep = mtaskp->inBeginp(); edgep; edgep = edgep->inNextp()) {
            const ExecMTask* prevp = dynamic_cast<ExecMTask*>(edgep->fromp());
            if (prevp->thread() != mtaskp->thread()) {
                ++result;
            }
        }
        return result;
    }

    void emitMTaskBody(AstMTaskBody* nodep) {
        ExecMTask* curExecMTaskp = nodep->execMTaskp();
        if (packedMTaskMayBlock(curExecMTaskp)) {
            puts("vlTOPp->__Vm_mt_" + cvtToStr(curExecMTaskp->id())
                 + ".waitUntilUpstreamDone(even_cycle);\n");
        }

        string recName;
        if (v3Global.opt.profThreads()) {
            recName = "__Vprfthr_" + cvtToStr(curExecMTaskp->id());
            puts("VlProfileRec* " + recName + " = NULL;\n");
            // Leave this if() here, as don't want to call VL_RDTSC_Q unless profiling
            puts("if (VL_UNLIKELY(vlTOPp->__Vm_profile_cycle_start)) {\n");
            puts(  recName + " = vlTOPp->__Vm_threadPoolp->profileAppend();\n");
            puts(  recName + "->startRecord(VL_RDTSC_Q() - vlTOPp->__Vm_profile_cycle_start,");
            puts(               " "+cvtToStr(curExecMTaskp->id())+ ",");
            puts(               " "+cvtToStr(curExecMTaskp->cost())+");\n");
            puts("}\n");
        }
        puts("Verilated::mtaskId(" + cvtToStr(curExecMTaskp->id()) + ");\n");

        // The actual body of calls to leaf functions
        iterateAndNextNull(nodep->stmtsp());

        if (v3Global.opt.profThreads()) {
            // Leave this if() here, as don't want to call VL_RDTSC_Q unless profiling
            puts("if (VL_UNLIKELY("+recName+")) {\n");
            puts(  recName + "->endRecord(VL_RDTSC_Q() - vlTOPp->__Vm_profile_cycle_start);\n");
            puts("}\n");
        }

        // Flush message queue
        puts("Verilated::endOfThreadMTask(vlSymsp->__Vm_evalMsgQp);\n");

        // For any downstream mtask that's on another thread, bump its
        // counter and maybe notify it.
        for (V3GraphEdge* edgep = curExecMTaskp->outBeginp();
             edgep; edgep = edgep->outNextp()) {
            const ExecMTask* nextp = dynamic_cast<ExecMTask*>(edgep->top());
            if (nextp->thread() != curExecMTaskp->thread()) {
                puts("vlTOPp->__Vm_mt_"+cvtToStr(nextp->id())
                     + ".signalUpstreamDone(even_cycle);\n");
            }
        }

        // Run the next mtask inline
        const ExecMTask* nextp = curExecMTaskp->packNextp();
        if (nextp) {
            emitMTaskBody(nextp->bodyp());
        } else {
            // Unblock the fake "final" mtask
            puts("vlTOPp->__Vm_mt_final.signalUpstreamDone(even_cycle);\n");
        }
    }

    virtual void visit(AstMTaskBody* nodep) {
        ExecMTask* mtp = nodep->execMTaskp();
        puts("\n");
        puts("void ");
        puts(modClassName(m_modp)+"::"+mtp->cFuncName());
        puts("(bool even_cycle, void* symtab) {\n");

        // Declare and set vlSymsp
        puts(EmitCBaseVisitor::symClassVar() + " = ("
             + EmitCBaseVisitor::symClassName() + "*)symtab;\n");
        puts(EmitCBaseVisitor::symTopAssign()+"\n");

        emitMTaskBody(nodep);
        puts("}\n");
    }

    //---------------------------------------
    // VISITORS
    using EmitCStmts::visit;  // Suppress hidden overloaded virtual function warning
    virtual void visit(AstCFunc* nodep) {
	// TRACE_* and DPI handled elsewhere
	if (nodep->funcType().isTrace()) return;
	if (nodep->dpiImport()) return;
	if (!(nodep->slow() ? m_slow : m_fast)) return;

	m_blkChangeDetVec.clear();

	splitSizeInc(nodep);

	puts("\n");
	if (nodep->ifdef()!="") puts("#ifdef "+nodep->ifdef()+"\n");
	if (nodep->isInline()) puts("VL_INLINE_OPT ");
	puts(nodep->rtnTypeVoid()); puts(" ");
	puts(modClassName(m_modp)+"::"+nodep->name()
	     +"("+cFuncArgs(nodep)+") {\n");

	// "+" in the debug indicates a print from the model
	puts("VL_DEBUG_IF(VL_DBG_MSGF(\"+  ");
	for (int i=0;i<m_modp->level();i++) { puts("  "); }
	puts(modClassName(m_modp)+"::"+nodep->name()
	     +"\\n\"); );\n");

        // Declare and set vlTOPp
	if (nodep->symProlog()) puts(EmitCBaseVisitor::symTopAssign()+"\n");

	if (nodep->initsp()) putsDecoration("// Variables\n");
	for (AstNode* subnodep=nodep->argsp(); subnodep; subnodep = subnodep->nextp()) {
            if (AstVar* varp=VN_CAST(subnodep, Var)) {
		if (varp->isFuncReturn()) emitVarDecl(varp, "");
	    }
	}
        emitVarList(nodep->initsp(), EVL_FUNC_ALL, "");
        emitVarList(nodep->stmtsp(), EVL_FUNC_ALL, "");

        iterateAndNextNull(nodep->initsp());

	if (nodep->stmtsp()) putsDecoration("// Body\n");
        iterateAndNextNull(nodep->stmtsp());
	if (!m_blkChangeDetVec.empty()) emitChangeDet();

	if (nodep->finalsp()) putsDecoration("// Final\n");
        iterateAndNextNull(nodep->finalsp());
	//

	if (!m_blkChangeDetVec.empty()) puts("return __req;\n");

	//puts("__Vm_activity = true;\n");
	puts("}\n");
	if (nodep->ifdef()!="") puts("#endif // "+nodep->ifdef()+"\n");
    }

    void emitChangeDet() {
	putsDecoration("// Change detection\n");
	puts("QData __req = false;  // Logically a bool\n");  // But not because it results in faster code
	bool gotOne = false;
        for (std::vector<AstChangeDet*>::iterator it = m_blkChangeDetVec.begin();
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
            //puts("VL_DEBUG_IF( if (__req) cout<<\"- CLOCKREQ );");
            for (std::vector<AstChangeDet*>::iterator it = m_blkChangeDetVec.begin();
		 it != m_blkChangeDetVec.end(); ++it) {
		AstChangeDet* nodep = *it;
		if (nodep->lhsp()) {
		    puts("VL_DEBUG_IF( if(__req && (");
		    bool gotOneIgnore = false;
		    doubleOrDetect(nodep, gotOneIgnore);
		    string varname;
                    if (VN_IS(nodep->lhsp(), VarRef)) {
                        varname = ": "+VN_CAST(nodep->lhsp(), VarRef)->varp()->prettyName();
		    }
		    puts(")) VL_DBG_MSGF(\"        CHANGE: "+nodep->fileline()->ascii()
			 +varname+"\\n\"); );\n");
		}
	    }
	}
    }

    virtual void visit(AstChangeDet* nodep) {
	m_blkChangeDetVec.push_back(nodep);
    }

    virtual void visit(AstCReset* nodep) {
	AstVar* varp = nodep->varrefp()->varp();
	emitVarReset(varp);
    }

    virtual void visit(AstExecGraph* nodep) {
        if (nodep != v3Global.rootp()->execGraphp()) {
            nodep->v3fatalSrc("ExecGraph should be a singleton!");
        }
        // The location of the AstExecGraph within the containing _eval()
        // function is where we want to invoke the graph and wait for it to
        // complete. Do that now.
        //
        // Don't recurse to children -- this isn't the place to emit
        // function definitions for the nested CFuncs. We'll do that at the
        // end.
        puts("vlTOPp->__Vm_even_cycle = !vlTOPp->__Vm_even_cycle;\n");

        // Build the list of initial mtasks to start
        std::vector<const ExecMTask*> execMTasks;

        // Start each root mtask
        for (const V3GraphVertex* vxp = nodep->depGraphp()->verticesBeginp();
             vxp; vxp = vxp->verticesNextp()) {
            const ExecMTask* etp = dynamic_cast<const ExecMTask*>(vxp);
            if (etp->threadRoot()) execMTasks.push_back(etp);
        }
        if (execMTasks.size() >
            static_cast<unsigned>(v3Global.opt.threads())) {
            nodep->v3fatalSrc("More root mtasks than available threads");
        }

        if (!execMTasks.empty()) {
            for (uint32_t i = 0; i < execMTasks.size(); ++i) {
                bool runInline = (i == execMTasks.size() - 1);
                if (runInline) {
                    // The thread calling eval() will run this mtask inline,
                    // along with its packed successors.
                    puts(execMTasks[i]->cFuncName()
                         + "(vlTOPp->__Vm_even_cycle, vlSymsp);\n");
                    puts("Verilated::mtaskId(0);\n");
                } else {
                    // The other N-1 go to the thread pool.
                    puts("vlTOPp->__Vm_threadPoolp->workerp("
                         + cvtToStr(i)+")->addTask("
                         + execMTasks[i]->cFuncName()
                         + ", vlTOPp->__Vm_even_cycle, vlSymsp);\n");
                }
            }
            puts("vlTOPp->__Vm_mt_final.waitUntilUpstreamDone(vlTOPp->__Vm_even_cycle);\n");
        }
    }

    //---------------------------------------
    // ACCESSORS

    // METHODS
    // Low level
    void emitVarReset(AstVar* varp);
    void emitCellCtors(AstNodeModule* modp);
    void emitSensitives();
    // Medium level
    void emitCtorImp(AstNodeModule* modp);
    void emitConfigureImp(AstNodeModule* modp);
    void emitCoverageDecl(AstNodeModule* modp);
    void emitCoverageImp(AstNodeModule* modp);
    void emitDestructorImp(AstNodeModule* modp);
    void emitSavableImp(AstNodeModule* modp);
    void emitTextSection(AstType type);
    void emitIntFuncDecls(AstNodeModule* modp);
    // High level
    void emitImp(AstNodeModule* modp);
    void emitStaticDecl(AstNodeModule* modp);
    void emitSettleLoop(const std::string& eval_call, bool initial);
    void emitWrapEval(AstNodeModule* modp);
    void emitMTaskState();
    void emitMTaskVertexCtors(bool* firstp);
    void emitInt(AstNodeModule* modp);
    void maybeSplit(AstNodeModule* modp);

public:
    EmitCImp() {
	m_modp = NULL;
	m_slow = false;
	m_fast = false;
    }
    virtual ~EmitCImp() {}
    void main(AstNodeModule* modp, bool slow, bool fast);
    void mainDoFunc(AstCFunc* nodep) {
        iterate(nodep);
    }
};

//######################################################################
// Internal EmitCStmts

void EmitCStmts::emitVarDecl(const AstVar* nodep, const string& prefixIfImp) {
    AstBasicDType* basicp = nodep->basicp();  if (!basicp) nodep->v3fatalSrc("Unimplemented: Outputting this data type");
    if (nodep->isIO()) {
	if (nodep->isSc()) {
	    m_ctorVarsVec.push_back(nodep);
            if (nodep->attrScClocked() && nodep->isReadOnly()) {
                puts("sc_in_clk ");
            } else {
                if (nodep->isInoutish()) puts("sc_inout<");
                else if (nodep->isWritable()) puts("sc_out<");
                else if (nodep->isNonOutput()) puts("sc_in<");
                else nodep->v3fatalSrc("Unknown type");

		puts(nodep->scType());
		puts("> ");
	    }
	    puts(nodep->name());
	    emitDeclArrayBrackets(nodep);
	    puts(";\n");
	} else if (basicp && basicp->isOpaque()) {
	    // strings and other fundamental c types; no VL_ macro can be used
	    puts(nodep->vlArgType(true,false,false));
	    emitDeclArrayBrackets(nodep);
	    puts(";\n");
        } else {  // C++ signals
            if (nodep->isInoutish()) puts("VL_INOUT");
            else if (nodep->isWritable()) puts("VL_OUT");
            else if (nodep->isNonOutput()) puts("VL_IN");
            else nodep->v3fatalSrc("Unknown type");

	    if (nodep->isQuad()) puts("64");
	    else if (nodep->widthMin() <= 8) puts("8");
	    else if (nodep->widthMin() <= 16) puts("16");
	    else if (nodep->isWide()) puts("W");

	    puts("("+nodep->name());
	    emitDeclArrayBrackets(nodep);
	    // If it's a packed struct/array then nodep->width is the whole thing, msb/lsb is just lowest dimension
	    puts(","+cvtToStr(basicp->lsb()+nodep->width()-1)
		 +","+cvtToStr(basicp->lsb()));
	    if (nodep->isWide()) puts(","+cvtToStr(nodep->widthWords()));
	    puts(");\n");
	}
    } else if (basicp && basicp->isOpaque()) {
	// strings and other fundamental c types
	puts(nodep->vlArgType(true,false,false));
	emitDeclArrayBrackets(nodep);
	puts(";\n");
    } else {
	// Arrays need a small alignment, but may need different padding after.
	// For example three VL_SIG8's needs alignment 1 but size 3.
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
	emitDeclArrayBrackets(nodep);
	// If it's a packed struct/array then nodep->width is the whole thing, msb/lsb is just lowest dimension
	puts(","+cvtToStr(basicp->lsb()+nodep->width()-1)
	     +","+cvtToStr(basicp->lsb()));
	if (nodep->isWide()) puts(","+cvtToStr(nodep->widthWords()));
	puts(");\n");
    }
}

void EmitCStmts::emitCtorSep(bool* firstp) {
    if (*firstp) {
        puts("  : "); *firstp = false;
    } else {
        puts(", ");
    }
    if (ofp()->exceededWidth()) puts("\n  ");
}

void EmitCStmts::emitVarCtors(bool* firstp) {
    if (!m_ctorVarsVec.empty()) {
	ofp()->indentInc();
	puts("\n");
	puts("#if (SYSTEMC_VERSION>20011000)\n");  // SystemC 2.0.1 and newer
        for (VarVec::iterator it = m_ctorVarsVec.begin(); it != m_ctorVarsVec.end(); ++it) {
            const AstVar* varp = *it;
            bool isArray = !VN_CAST(varp->dtypeSkipRefp(), BasicDType);
	    if (isArray) {
		puts("// Skipping array: ");
		puts(varp->name());
		puts("\n");
	    } else {
                emitCtorSep(firstp);
		puts(varp->name());
		puts("("); putsQuoted(varp->name()); puts(")");
	    }
	}
        puts("\n#endif\n");
	ofp()->indentDec();
    }
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

void EmitCStmts::emitOpName(AstNode* nodep, const string& format,
			    AstNode* lhsp, AstNode* rhsp, AstNode* thsp) {
    // Look at emitOperator() format for term/uni/dual/triops,
    // and write out appropriate text.
    //  %n*	node
    //   %nq	  emitIQW on the [node]
    //   %nw	  width in bits
    //   %nW	  width in words
    //   %ni	  iterate
    //	%l*	lhsp - if appropriate, then second char as above
    //	%r*	rhsp - if appropriate, then second char as above
    //	%t*	thsp - if appropriate, then second char as above
    //	%k	Potential line break
    //  %P	Wide temporary name
    //	,	Commas suppressed if the previous field is suppressed
    string nextComma;
    bool needComma = false;
#define COMMA { if (!nextComma.empty()) { puts(nextComma); nextComma=""; } }

    putbs("");
    for (string::const_iterator pos = format.begin(); pos != format.end(); ++pos) {
	if (pos[0]==',') {
	    // Remember we need to add one, but don't do yet to avoid ",)"
	    if (needComma) {
		if (pos[1]==' ') { nextComma=", "; }
		else nextComma = ",";
		needComma = false;
	    }
	    if (pos[1]==' ') { ++pos; } // Must do even if no nextComma
	}
	else if (pos[0]=='%') {
	    ++pos;
	    bool detail = false;
	    AstNode* detailp = NULL;
	    switch (pos[0]) {
	    case '%': puts("%");  break;
	    case 'k': putbs("");  break;
	    case 'n': detail = true; detailp = nodep; break;
	    case 'l': detail = true; detailp = lhsp; break;
	    case 'r': detail = true; detailp = rhsp; break;
	    case 't': detail = true; detailp = thsp; break;
	    case 'P':
		if (nodep->isWide()) {
		    if (!m_wideTempRefp) nodep->v3fatalSrc("Wide Op w/ no temp, perhaps missing op in V3EmitC?");
		    COMMA;
		    puts(m_wideTempRefp->hiername());
		    puts(m_wideTempRefp->varp()->name());
		    m_wideTempRefp = NULL;
		    needComma = true;
		}
		break;
	    default:
		nodep->v3fatalSrc("Unknown emitOperator format code: %"<<pos[0]);
		break;
	    }
	    if (detail) {
		// Get next letter of %[nlrt]
		++pos;
		switch (pos[0]) {
		case 'q': emitIQW(detailp); break;
		case 'w':
		    COMMA;
		    puts(cvtToStr(detailp->widthMin()));
		    needComma = true;
		    break;
		case 'W':
		    if (lhsp->isWide()) {
			COMMA;
			puts(cvtToStr(lhsp->widthWords()));
			needComma = true;
		    }
		    break;
		case 'i':
		    COMMA;
		    if (!detailp) { nodep->v3fatalSrc("emitOperator() references undef node"); }
                    else iterateAndNextNull(detailp);
		    needComma = true;
		    break;
		default:
		    nodep->v3fatalSrc("Unknown emitOperator format code: %[nlrt]"<<pos[0]);
		    break;
		}
	    }
	} else if (pos[0] == ')') {
	    nextComma=""; puts(")");
	} else if (pos[0] == '(') {
	    COMMA; needComma = false; puts("(");
	} else {
	    // Normal text
	    if (isalnum(pos[0])) needComma = true;
	    COMMA;
	    string s; s+=pos[0]; puts(s);
	}
    }
}

//----------------------------------------------------------------------
// Mid level - VISITS

// We only do one display at once, so can just use static state

struct EmitDispState {
    string		m_format;	// "%s" and text from user
    std::vector<char>   m_argsChar;     // Format of each argument to be printed
    std::vector<AstNode*> m_argsp;      // Each argument to be printed
    std::vector<string> m_argsFunc;     // Function before each argument to be printed
    EmitDispState() { clear(); }
    void clear() {
	m_format = "";
	m_argsChar.clear();
	m_argsp.clear();
	m_argsFunc.clear();
    }
    void pushFormat(const string& fmt) { m_format += fmt; }
    void pushFormat(char fmt) { m_format += fmt; }
    void pushArg(char fmtChar, AstNode* nodep, const string& func) {
	m_argsChar.push_back(fmtChar);
	m_argsp.push_back(nodep); m_argsFunc.push_back(func);
    }
} emitDispState;

void EmitCStmts::displayEmit(AstNode* nodep, bool isScan) {
    if (emitDispState.m_format == ""
        && VN_IS(nodep, Display)) {  // not fscanf etc, as they need to return value
	// NOP
    } else {
	// Format
	bool isStmt = false;
        if (const AstFScanF* dispp = VN_CAST(nodep, FScanF)) {
	    isStmt = false;
	    puts("VL_FSCANF_IX(");
            iterate(dispp->filep());
	    puts(",");
        } else if (const AstSScanF* dispp = VN_CAST(nodep, SScanF)) {
	    isStmt = false;
	    checkMaxWords(dispp->fromp());
	    puts("VL_SSCANF_I"); emitIQW(dispp->fromp()); puts("X(");
	    puts(cvtToStr(dispp->fromp()->widthMin()));
	    puts(",");
            iterate(dispp->fromp());
	    puts(",");
        } else if (const AstDisplay* dispp = VN_CAST(nodep, Display)) {
	    isStmt = true;
	    if (dispp->filep()) {
		puts("VL_FWRITEF(");
                iterate(dispp->filep());
		puts(",");
	    } else {
		puts("VL_WRITEF(");
	    }
        } else if (const AstSFormat* dispp = VN_CAST(nodep, SFormat)) {
	    isStmt = true;
	    puts("VL_SFORMAT_X(");
	    puts(cvtToStr(dispp->lhsp()->widthMin()));
	    putbs(",");
            iterate(dispp->lhsp());
	    putbs(",");
        } else if (const AstSFormatF* dispp = VN_CAST(nodep, SFormatF)) {
	    isStmt = false;
	    if (dispp) {}
	    puts("VL_SFORMATF_NX(");
	} else {
	    nodep->v3fatalSrc("Unknown displayEmit node type");
	}
	ofp()->putsQuoted(emitDispState.m_format);
	// Arguments
	for (unsigned i=0; i < emitDispState.m_argsp.size(); i++) {
	    puts(",");
	    char     fmt  = emitDispState.m_argsChar[i];
	    AstNode* argp = emitDispState.m_argsp[i];
	    string   func = emitDispState.m_argsFunc[i];
	    ofp()->indentInc();
	    ofp()->putbs("");
	    if (func!="") puts(func);
	    if (argp) {
		if (isScan) puts("&(");
		else if (fmt == '@') puts("&(");
                iterate(argp);
		if (isScan) puts(")");
		else if (fmt == '@') puts(")");
	    }
	    ofp()->indentDec();
	}
        // End
	puts(")");
	if (isStmt) puts(";\n");
	else puts(" ");
	// Prep for next
	emitDispState.clear();
    }
}

void EmitCStmts::displayArg(AstNode* dispp, AstNode** elistp, bool isScan,
			    const string& vfmt, char fmtLetter) {
    // Print display argument, edits elistp
    AstNode* argp = *elistp;
    if (!argp) {
	// expectDisplay() checks this first, so internal error if found here
	dispp->v3error("Internal: Missing arguments for $display-like format");
	return;
    }
    if (argp->widthMin() > VL_VALUE_STRING_MAX_WIDTH) {
	dispp->v3error("Exceeded limit of "+cvtToStr(VL_VALUE_STRING_MAX_WIDTH)+" bits for any $display-like arguments");
    }
    if (argp && argp->widthMin()>8 && fmtLetter=='c') {
	// Technically legal, but surely not what the user intended.
	argp->v3warn(WIDTH,dispp->verilogKwd()<<"of %c format of > 8 bit value");
    }

    //string pfmt = "%"+displayFormat(argp, vfmt, fmtLetter)+fmtLetter;
    string pfmt;
    if ((fmtLetter=='#' || fmtLetter=='d' || fmtLetter=='t')
	&& !isScan
	&& vfmt == "") { // Size decimal output.  Spec says leading spaces, not zeros
	double mantissabits = argp->widthMin() - ((fmtLetter=='d')?1:0);
	double maxval = pow(2.0, mantissabits);
	double dchars = log10(maxval)+1.0;
	if (fmtLetter=='d') dchars++;  // space for sign
	int nchars = int(dchars);
	pfmt = string("%") + cvtToStr(nchars) + fmtLetter;
    } else {
	pfmt = string("%") + vfmt + fmtLetter;
    }
    emitDispState.pushFormat(pfmt);
    emitDispState.pushArg(' ',NULL,cvtToStr(argp->widthMin()));
    emitDispState.pushArg(fmtLetter,argp,"");

    // Next parameter
    *elistp = (*elistp)->nextp();
}

void EmitCStmts::displayNode(AstNode* nodep, AstScopeName* scopenamep,
			     const string& vformat, AstNode* exprsp,
			     bool isScan) {
    AstNode* elistp = exprsp;

    // Convert Verilog display to C printf formats
    // 		"%0t" becomes "%d"
    emitDispState.clear();
    string vfmt;
    string::const_iterator pos = vformat.begin();
    bool inPct = false;
    for (; pos != vformat.end(); ++pos) {
        //UINFO(1,"Parse '"<<*pos<<"'  IP"<<inPct<<" List "<<cvtToHex(elistp)<<endl);
	if (!inPct && pos[0]=='%') {
	    inPct = true;
	    vfmt = "";
	} else if (!inPct) {   // Normal text
	    emitDispState.pushFormat(*pos);
	} else { // Format character
	    inPct = false;
	    switch (tolower(pos[0])) {
	    case '0': case '1': case '2': case '3': case '4':
	    case '5': case '6': case '7': case '8': case '9':
	    case '.':
		// Digits, like %5d, etc.
		vfmt += pos[0];
		inPct = true;  // Get more digits
		break;
	    case '%':
		emitDispState.pushFormat("%%");  // We're printf'ing it, so need to quote the %
		break;
	    // Special codes
	    case '~': displayArg(nodep,&elistp,isScan, vfmt,'d'); break;  // Signed decimal
	    case '@': displayArg(nodep,&elistp,isScan, vfmt,'@'); break;  // Packed string
	    // Spec: h d o b c l
	    case 'b': displayArg(nodep,&elistp,isScan, vfmt,'b'); break;
	    case 'c': displayArg(nodep,&elistp,isScan, vfmt,'c'); break;
	    case 't': displayArg(nodep,&elistp,isScan, vfmt,'t'); break;
	    case 'd': displayArg(nodep,&elistp,isScan, vfmt,'#'); break;  // Unsigned decimal
	    case 'o': displayArg(nodep,&elistp,isScan, vfmt,'o'); break;
	    case 'h': //FALLTHRU
	    case 'x': displayArg(nodep,&elistp,isScan, vfmt,'x'); break;
	    case 's': displayArg(nodep,&elistp,isScan, vfmt,'s'); break;
	    case 'e': displayArg(nodep,&elistp,isScan, vfmt,'e'); break;
	    case 'f': displayArg(nodep,&elistp,isScan, vfmt,'f'); break;
	    case 'g': displayArg(nodep,&elistp,isScan, vfmt,'g'); break;
	    case 'v': displayArg(nodep,&elistp,isScan, vfmt,'v'); break;
	    case 'm': {
		if (!scopenamep) nodep->v3fatalSrc("Display with %m but no AstScopeName");
		string suffix = scopenamep->scopePrettySymName();
		if (suffix=="") emitDispState.pushFormat("%S");
		else emitDispState.pushFormat("%N");  // Add a . when needed
		emitDispState.pushArg(' ',NULL, "vlSymsp->name()");
		emitDispState.pushFormat(suffix);
		break;
	    }
	    case 'l': {
                // Better than not compiling
		emitDispState.pushFormat("----");
		break;
	    }
	    default:
		nodep->v3error("Unknown $display-like format code: %"<<pos[0]);
		break;
	    }
	}
    }
    if (elistp != NULL) {
	// expectFormat also checks this, and should have found it first, so internal
	elistp->v3error("Internal: Extra arguments for $display-like format");
    }
    displayEmit(nodep, isScan);
}

//######################################################################
// Internal EmitC

void EmitCImp::emitVarReset(AstVar* varp) {
    if (varp->isIO() && m_modp->isTop() && optSystemC()) {
	// System C top I/O doesn't need loading, as the lower level subinst code does it.}
    } else if (varp->isParam()) {
	if (!varp->valuep()) varp->v3fatalSrc("No init for a param?");
	// If a simple CONST value we initialize it using an enum
	// If an ARRAYINIT we initialize it using an initial block similar to a signal
	//puts("// parameter "+varp->name()+" = "+varp->valuep()->name()+"\n");
    }
    else if (AstInitArray* initarp = VN_CAST(varp->valuep(), InitArray)) {
        if (AstUnpackArrayDType* arrayp = VN_CAST(varp->dtypeSkipRefp(), UnpackArrayDType)) {
	    if (initarp->defaultp()) {
		// MSVC++ pre V7 doesn't support 'for (int ...)', so declare in sep block
		puts("{ int __Vi=0;");
		puts(" for (; __Vi<"+cvtToStr(arrayp->elementsConst()));
		puts("; ++__Vi) {\n");
                emitSetVarConstant(varp->name()+"[__Vi]", VN_CAST(initarp->defaultp(), Const));
		puts("}}\n");
	    }
	    int pos = 0;
	    for (AstNode* itemp = initarp->initsp(); itemp; ++pos, itemp=itemp->nextp()) {
		int index = initarp->posIndex(pos);
		if (!initarp->defaultp() && index!=pos) initarp->v3fatalSrc("Not enough values in array initalizement");
                emitSetVarConstant(varp->name()+"["+cvtToStr(index)+"]", VN_CAST(itemp, Const));
	    }
	} else {
	    varp->v3fatalSrc("InitArray under non-arrayed var");
	}
    }
    else if (varp->basicp() && varp->basicp()->keyword() == AstBasicDTypeKwd::STRING) {
	// Constructor deals with it
    }
    else {
	int vects = 0;
	// This isn't very robust and may need cleanup for other data types
        for (AstUnpackArrayDType* arrayp=VN_CAST(varp->dtypeSkipRefp(), UnpackArrayDType);
             arrayp;
             arrayp = VN_CAST(arrayp->subDTypep()->skipRefp(), UnpackArrayDType)) {
	    int vecnum = vects++;
	    if (arrayp->msb() < arrayp->lsb()) varp->v3fatalSrc("Should have swapped msb & lsb earlier.");
	    string ivar = string("__Vi")+cvtToStr(vecnum);
	    // MSVC++ pre V7 doesn't support 'for (int ...)', so declare in sep block
	    puts("{ int __Vi"+cvtToStr(vecnum)+"="+cvtToStr(0)+";");
	    puts(" for (; "+ivar+"<"+cvtToStr(arrayp->elementsConst()));
	    puts("; ++"+ivar+") {\n");
	}
	bool zeroit = (varp->attrFileDescr() // Zero it out, so we don't core dump if never call $fopen
		       || (varp->basicp() && varp->basicp()->isZeroInit())
                       || (v3Global.opt.underlineZero()
                           && !varp->name().empty() && varp->name()[0]=='_')
		       || (v3Global.opt.xInitial() == "fast" || v3Global.opt.xInitial() == "0"));
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
	    // If --x-initial-edge is set, we want to force an initial
	    // edge on uninitialized clocks (from 'X' to whatever the
	    // first value is). Since the class is instantiated before
	    // initial blocks are evaluated, this should not clash
	    // with any initial block settings.
	    if (zeroit || (v3Global.opt.xInitialEdge() && varp->isUsedClock())) {
		puts(" = 0;\n");
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
    splitSizeInc(1);
}

void EmitCImp::emitCoverageDecl(AstNodeModule* modp) {
    if (v3Global.opt.coverage()) {
	ofp()->putsPrivate(true);
	putsDecoration("// Coverage\n");
	puts("void __vlCoverInsert(uint32_t* countp, bool enable, const char* filenamep, int lineno, int column,\n");
	puts(  	"const char* hierp, const char* pagep, const char* commentp);\n");
    }
}

void EmitCImp::emitMTaskVertexCtors(bool* firstp) {
    AstExecGraph* execGraphp = v3Global.rootp()->execGraphp();
    if (!execGraphp) v3Global.rootp()->v3fatalSrc("Should have an execGraphp");
    const V3Graph* depGraphp = execGraphp->depGraphp();

    unsigned finalEdgesInCt = 0;
    for (const V3GraphVertex* vxp = depGraphp->verticesBeginp();
         vxp; vxp = vxp->verticesNextp()) {
        const ExecMTask* mtp = dynamic_cast<const ExecMTask*>(vxp);
        unsigned edgesInCt = packedMTaskMayBlock(mtp);
        if (packedMTaskMayBlock(mtp) > 0) {
            emitCtorSep(firstp);
            puts("__Vm_mt_"+cvtToStr(mtp->id())+"("+cvtToStr(edgesInCt)+")");
        }
        // Each mtask with no packed successor will become a dependency
        // for the final node:
        if (!mtp->packNextp()) ++finalEdgesInCt;
    }

    emitCtorSep(firstp);
    puts("__Vm_mt_final(" + cvtToStr(finalEdgesInCt) + ")");

    // This will flip to 'true' before the start of the 0th cycle.
    emitCtorSep(firstp); puts("__Vm_threadPoolp(NULL)");
    if (v3Global.opt.profThreads()) {
        emitCtorSep(firstp); puts("__Vm_profile_cycle_start(0)");
    }
    emitCtorSep(firstp); puts("__Vm_even_cycle(false)");
}

void EmitCImp::emitCtorImp(AstNodeModule* modp) {
    puts("\n");
    bool first = true;
    if (optSystemC() && modp->isTop()) {
	puts("VL_SC_CTOR_IMP("+modClassName(modp)+")");
    } else {
        puts("VL_CTOR_IMP("+modClassName(modp)+")");
        first = false;  // VL_CTOR_IMP includes the first ':'
    }
    emitVarCtors(&first);
    if (modp->isTop() && v3Global.opt.mtasks()) {
        emitMTaskVertexCtors(&first);
    }
    puts(" {\n");
    emitCellCtors(modp);
    emitSensitives();

    putsDecoration("// Reset internal values\n");
    if (modp->isTop()) {
	if (v3Global.opt.inhibitSim()) puts("__Vm_inhibitSim = false;\n");
	puts("\n");
    }
    putsDecoration("// Reset structure values\n");
    puts("_ctor_var_reset();\n");
    emitTextSection(AstType::atScCtor);

    if (modp->isTop() && v3Global.opt.mtasks()) {
        // TODO-- For now each top module creates its own ThreadPool here,
        // and deletes it in the destructor. If A and B are each top level
        // modules, each creates a separate thread pool.  This allows
        // A.eval() and B.eval() to run concurrently without any
        // interference -- so long as the physical machine has enough cores
        // to support both pools and all testbench threads.
        //
        // In the future, we might want to let the client provide a
        // threadpool to the constructor. This would allow two or more
        // models to share a single threadpool.
        //
        // For example: suppose models A and B are each compiled to run on
        // 4 threads. The client might create a single thread pool with 3
        // threads and pass it to both models. If the client can ensure tht
        // A.eval() and B.eval() do NOT run concurrently, there will be no
        // contention for the threads. This mode is missing for now.  (Is
        // there demand for such a setup?)
        puts("__Vm_threadPoolp = new VlThreadPool("
             // Note we create N-1 threads in the thread pool. The thread
             // that calls eval() becomes the final Nth thread for the
             // duration of the eval call.
             + cvtToStr(v3Global.opt.threads() - 1)
             + ", " + cvtToStr(v3Global.opt.profThreads())
             + ");\n");

        if (v3Global.opt.profThreads()) {
            puts("__Vm_profile_cycle_start = 0;\n");
            puts("__Vm_profile_time_finished = 0;\n");
            puts("__Vm_profile_window_ct = 0;");
        }
    }
    puts("}\n");
}

void EmitCImp::emitConfigureImp(AstNodeModule* modp) {
    puts("\nvoid "+modClassName(modp)+"::__Vconfigure("+symClassName()+"* vlSymsp, bool first) {\n");
    puts(   "if (0 && first) {}  // Prevent unused\n");
    puts(   "this->__VlSymsp = vlSymsp;\n");  // First, as later stuff needs it.
    if (v3Global.opt.coverage() ) {
	puts("this->_configure_coverage(vlSymsp, first);\n");
    }
    puts("}\n");
    splitSizeInc(10);
}

void EmitCImp::emitCoverageImp(AstNodeModule* modp) {
    if (v3Global.opt.coverage() ) {
	puts("\n// Coverage\n");
	// Rather than putting out VL_COVER_INSERT calls directly, we do it via this function
	// This gets around gcc slowness constructing all of the template arguments.
        puts("void "+modClassName(m_modp)+"::__vlCoverInsert(uint32_t* countp, bool enable,"
             " const char* filenamep, int lineno, int column,\n");
	puts(  	"const char* hierp, const char* pagep, const char* commentp) {\n");
	puts(   "static uint32_t fake_zero_count = 0;\n");  // static doesn't need save-restore as constant
	puts(   "if (!enable) countp = &fake_zero_count;\n");  // Used for second++ instantiation of identical bin
	puts(   "*countp = 0;\n");
	puts(   "VL_COVER_INSERT(countp,");
	puts(	"  \"filename\",filenamep,");
	puts(	"  \"lineno\",lineno,");
	puts(	"  \"column\",column,\n");
	//puts(	"\"hier\",std::string(__VlSymsp->name())+hierp,");  // Need to move hier into scopes and back out if do this
	puts(	"\"hier\",std::string(name())+hierp,");
	puts(	"  \"page\",pagep,");
	puts(	"  \"comment\",commentp);\n");
	puts("}\n");
	splitSizeInc(10);
    }
}

void EmitCImp::emitDestructorImp(AstNodeModule* modp) {
    puts("\n");
    puts(modClassName(modp)+"::~"+modClassName(modp)+"() {\n");
    if (modp->isTop() && v3Global.opt.mtasks()) {
        puts("delete __Vm_threadPoolp; __Vm_threadPoolp = NULL;\n");
    }
    emitTextSection(AstType::atScDtor);
    if (modp->isTop()) puts("delete __VlSymsp; __VlSymsp=NULL;\n");
    puts("}\n");
    splitSizeInc(10);
}

void EmitCImp::emitSavableImp(AstNodeModule* modp) {
    if (v3Global.opt.savable() ) {
	puts("\n// Savable\n");
	for (int de=0; de<2; ++de) {
	    string classname = de ? "VerilatedDeserialize" : "VerilatedSerialize";
	    string funcname = de ? "__Vdeserialize" : "__Vserialize";
	    string writeread = de ? "read" : "write";
	    string op = de ? ">>" : "<<";
            // NOLINTNEXTLINE(performance-inefficient-string-concatenation)
	    puts("void "+modClassName(modp)+"::"+funcname+"("+classname+"& os) {\n");
	    // Place a computed checksum to insure proper structure save/restore formatting
	    // OK if this hash includes some things we won't dump, since just looking for loading the wrong model
	    VHashSha1 hash;
	    for (AstNode* nodep=modp->stmtsp(); nodep; nodep = nodep->nextp()) {
                if (const AstVar* varp = VN_CAST(nodep, Var)) {
		    hash.insert(varp->name());
		    hash.insert(varp->dtypep()->width());
		}
	    }
	    ofp()->printf(   "vluint64_t __Vcheckval = VL_ULL(0x%" VL_PRI64 "x);\n",
                             static_cast<vluint64_t>(hash.digestUInt64()));
	    if (de) {
		puts("os.readAssert(__Vcheckval);\n");
	    } else {
		puts("os<<__Vcheckval;\n");
	    }

	    // Save all members
	    if (v3Global.opt.inhibitSim()) puts("os"+op+"__Vm_inhibitSim;\n");
	    for (AstNode* nodep=modp->stmtsp(); nodep; nodep = nodep->nextp()) {
                if (const AstVar* varp = VN_CAST(nodep, Var)) {
		    if (varp->isIO() && modp->isTop() && optSystemC()) {
			// System C top I/O doesn't need loading, as the lower level subinst code does it.
		    }
		    else if (varp->isParam()) {}
		    else if (varp->isStatic() && varp->isConst()) {}
		    else {
			int vects = 0;
			// This isn't very robust and may need cleanup for other data types
                        for (AstUnpackArrayDType* arrayp=VN_CAST(varp->dtypeSkipRefp(), UnpackArrayDType);
                             arrayp;
                             arrayp = VN_CAST(arrayp->subDTypep()->skipRefp(), UnpackArrayDType)) {
			    int vecnum = vects++;
			    if (arrayp->msb() < arrayp->lsb()) varp->v3fatalSrc("Should have swapped msb & lsb earlier.");
			    string ivar = string("__Vi")+cvtToStr(vecnum);
			    // MSVC++ pre V7 doesn't support 'for (int ...)', so declare in sep block
			    puts("{ int __Vi"+cvtToStr(vecnum)+"="+cvtToStr(0)+";");
			    puts(" for (; "+ivar+"<"+cvtToStr(arrayp->elementsConst()));
			    puts("; ++"+ivar+") {\n");
			}
			if (varp->basicp() && (varp->basicp()->keyword() == AstBasicDTypeKwd::STRING
					       || !varp->basicp()->isWide())) {
			    puts("os"+op+varp->name());
			    for (int v=0; v<vects; ++v) puts( "[__Vi"+cvtToStr(v)+"]");
			    puts(";\n");
			} else {
			    puts("os."+writeread+"(&"+varp->name());
			    for (int v=0; v<vects; ++v) puts( "[__Vi"+cvtToStr(v)+"]");
			    puts(",sizeof("+varp->name());
			    for (int v=0; v<vects; ++v) puts( "[__Vi"+cvtToStr(v)+"]");
			    puts("));\n");
			}
			for (int v=0; v<vects; ++v) puts( "}}\n");
		    }
		}
	    }

	    if (modp->isTop()) {  // Save the children
		puts(   "__VlSymsp->"+funcname+"(os);\n");
	    }
	    puts("}\n");
	}
    }
}

void EmitCImp::emitStaticDecl(AstNodeModule* modp) {
    // Need implementation here.  Be careful of alignment code; needs to be uniquified
    // with module name to avoid multiple symbols.
    //emitVarList(modp->stmtsp(), EVL_FUNC_ALL, modp->name());
    puts("");  // NOP for cppcheck, otherwise const function
}

void EmitCImp::emitTextSection(AstType type) {
    int last_line = -999;
    for (AstNode* nodep = m_modp->stmtsp(); nodep != NULL; nodep = nodep->nextp()) {
        if (const AstNodeText* textp = VN_CAST(nodep, NodeText)) {
	    if (nodep->type() == type) {
		if (last_line != nodep->fileline()->lineno()) {
		    if (last_line < 0) {
			puts("\n//*** Below code from `systemc in Verilog file\n");
		    }
		    ofp()->putsNoTracking("//#line "+cvtToStr(nodep->fileline()->lineno())
					  +" ");
		    ofp()->putsQuoted(nodep->fileline()->filename());
		    ofp()->putsNoTracking("\n");
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

void EmitCImp::emitCellCtors(AstNodeModule* modp) {
    if (modp->isTop()) {
	// Must be before other constructors, as __vlCoverInsert calls it
	puts(EmitCBaseVisitor::symClassVar()+" = __VlSymsp = new "+symClassName()+"(this, name());\n");
	puts(EmitCBaseVisitor::symTopAssign()+"\n");
    }
    for (AstNode* nodep=modp->stmtsp(); nodep; nodep = nodep->nextp()) {
        if (AstCell* cellp=VN_CAST(nodep, Cell)) {
            puts("VL_CELL("+cellp->name()+", "+modClassName(cellp->modp())+");\n");
	}
    }
}

void EmitCImp::emitSensitives() {
    // Create sensitivity list for when to evaluate the model.
    // If C++ code, the user must call this routine themself.
    if (m_modp->isTop() && optSystemC()) {
	putsDecoration("// Sensitivities on all clocks and combo inputs\n");
	puts("SC_METHOD(eval);\n");
	for (AstNode* nodep=m_modp->stmtsp(); nodep; nodep = nodep->nextp()) {
            if (const AstVar* varp = VN_CAST(nodep, Var)) {
                if (varp->isNonOutput() && (varp->isScSensitive()
                                            || varp->isUsedClock())) {
                    int vects = 0;
                    // This isn't very robust and may need cleanup for other data types
                    for (AstUnpackArrayDType* arrayp=VN_CAST(varp->dtypeSkipRefp(), UnpackArrayDType);
                         arrayp;
                         arrayp = VN_CAST(arrayp->subDTypep()->skipRefp(), UnpackArrayDType)) {
			int vecnum = vects++;
			if (arrayp->msb() < arrayp->lsb()) varp->v3fatalSrc("Should have swapped msb & lsb earlier.");
			string ivar = string("__Vi")+cvtToStr(vecnum);
			// MSVC++ pre V7 doesn't support 'for (int ...)', so declare in sep block
			puts("{ int __Vi"+cvtToStr(vecnum)+"="+cvtToStr(arrayp->lsb())+";");
			puts(" for (; "+ivar+"<="+cvtToStr(arrayp->msb()));
			puts("; ++"+ivar+") {\n");
		    }
		    puts("sensitive << "+varp->name());
		    for (int v=0; v<vects; ++v) puts( "[__Vi"+cvtToStr(v)+"]");
		    puts(";\n");
		    for (int v=0; v<vects; ++v) puts( "}}\n");
		}
	    }
	}
	puts("\n");
    }
}

void EmitCImp::emitSettleLoop(const std::string& eval_call, bool initial) {
    putsDecoration("// Evaluate till stable\n");
    puts("int __VclockLoop = 0;\n");
    puts("QData __Vchange = 1;\n");
    puts("do {\n");
    puts(    eval_call + "\n");
    puts(    "if (VL_UNLIKELY(++__VclockLoop > "+cvtToStr(v3Global.opt.convergeLimit())
             +")) {\n");
    puts(        "// About to fail, so enable debug to see what's not settling.\n");
    puts(        "// Note you must run make with OPT=-DVL_DEBUG for debug prints.\n");
    puts(        "int __Vsaved_debug = Verilated::debug();\n");
    puts(        "Verilated::debug(1);\n");
    puts(        "__Vchange = _change_request(vlSymsp);\n");
    puts(        "Verilated::debug(__Vsaved_debug);\n");
    puts(        "VL_FATAL_MT(__FILE__,__LINE__,__FILE__,\"Verilated model didn't ");
    if (initial) puts ("DC ");
    puts(        "converge\");\n");
    puts(    "} else {\n");
    puts(        "__Vchange = _change_request(vlSymsp);\n");
    puts(    "}\n");
    puts("} while (VL_UNLIKELY(__Vchange));\n");
}

void EmitCImp::emitWrapEval(AstNodeModule* modp) {
    puts("\nvoid "+modClassName(modp)+"::eval() {\n");
    puts("VL_DEBUG_IF(VL_DBG_MSGF(\"+++++TOP Evaluate "+modClassName(modp)+"::eval\\n\"); );\n");
    puts(EmitCBaseVisitor::symClassVar()+" = this->__VlSymsp;  // Setup global symbol table\n");
    puts(EmitCBaseVisitor::symTopAssign()+"\n");
    puts("#ifdef VL_DEBUG\n");
    putsDecoration("// Debug assertions\n");
    puts("_eval_debug_assertions();\n");
    puts("#endif // VL_DEBUG\n");
    putsDecoration("// Initialize\n");
    puts("if (VL_UNLIKELY(!vlSymsp->__Vm_didInit)) _eval_initial_loop(vlSymsp);\n");
    if (v3Global.opt.inhibitSim()) {
	puts("if (VL_UNLIKELY(__Vm_inhibitSim)) return;\n");
    }

    if (v3Global.opt.threads() == 1) {
	uint32_t mtaskId = 0;
	putsDecoration("// MTask "+cvtToStr(mtaskId)+" start\n");
        puts("VL_DEBUG_IF(VL_DBG_MSGF(\"MTask"+cvtToStr(mtaskId)+" starting\\n\"););\n");
	puts("Verilated::mtaskId("+cvtToStr(mtaskId)+");\n");
    }

    if (v3Global.opt.mtasks()
        && v3Global.opt.profThreads()) {
        puts("if (VL_UNLIKELY((Verilated::profThreadsStart() != __Vm_profile_time_finished)\n");
        puts(                 " && (VL_TIME_Q() > Verilated::profThreadsStart())\n");
        puts(                 " && (Verilated::profThreadsWindow() >= 1))) {\n");
        // Within a profile (either starting, middle, or end)
        puts(    "if (vlTOPp->__Vm_profile_window_ct == 0) {\n");  // Opening file?
        // Start profile on this cycle. We'll capture a window worth, then
        // only analyze the next window worth. The idea is that the first window
        // capture will hit some cache-cold stuff (eg printf) but it'll be warm
        // by the time we hit the second window, we hope.
        puts(        "vlTOPp->__Vm_profile_cycle_start = VL_RDTSC_Q();\n");
        // "* 2" as first half is warmup, second half is collection
        puts(        "vlTOPp->__Vm_profile_window_ct = Verilated::profThreadsWindow() * 2 + 1;\n");
        puts(    "}\n");
        puts(    "--vlTOPp->__Vm_profile_window_ct;\n");
        puts(    "if (vlTOPp->__Vm_profile_window_ct == (Verilated::profThreadsWindow())) {\n");
        // This barrier record in every threads' profile demarcates the
        // cache-warm-up cycles before the barrier from the actual profile
        // cycles afterward.
        puts(        "vlTOPp->__Vm_threadPoolp->profileAppendAll(");
        puts(                       "VlProfileRec(VlProfileRec::Barrier()));\n");
        puts(        "vlTOPp->__Vm_profile_cycle_start = VL_RDTSC_Q();\n");
        puts(    "}\n");
        puts(    "else if (vlTOPp->__Vm_profile_window_ct == 0) {\n");
        // Ending file.
        puts(        "vluint64_t elapsed = VL_RDTSC_Q() - vlTOPp->__Vm_profile_cycle_start;\n");
        puts(        "vlTOPp->__Vm_threadPoolp->profileDump(Verilated::profThreadsFilenamep(), elapsed);\n");
        // This turns off the test to enter the profiling code, but still
        // allows the user to collect another profile by changing
        // profThreadsStart
        puts(        "__Vm_profile_time_finished = Verilated::profThreadsStart();\n");
        puts(        "vlTOPp->__Vm_profile_cycle_start = 0;\n");
        puts(    "}\n");
        puts("}\n");
    }

    emitSettleLoop(
        (string("VL_DEBUG_IF(VL_DBG_MSGF(\"+ Clock loop\\n\"););\n")
         + (v3Global.opt.trace() ? "vlSymsp->__Vm_activity = true;\n" : "")
         + "_eval(vlSymsp);"), false);
    if (v3Global.opt.threads() == 1) {
	puts("Verilated::endOfThreadMTask(vlSymsp->__Vm_evalMsgQp);\n");
    }
    if (v3Global.opt.threads()) {
	puts("Verilated::endOfEval(vlSymsp->__Vm_evalMsgQp);\n");
    }
    puts("}\n");
    splitSizeInc(10);

    //
    puts("\nvoid "+modClassName(modp)+"::_eval_initial_loop("+EmitCBaseVisitor::symClassVar()+") {\n");
    puts("vlSymsp->__Vm_didInit = true;\n");
    puts("_eval_initial(vlSymsp);\n");
    if (v3Global.opt.trace()) {
	puts("vlSymsp->__Vm_activity = true;\n");
    }
    emitSettleLoop((string("_eval_settle(vlSymsp);\n")
                    +"_eval(vlSymsp);"), true);
    puts("}\n");
    splitSizeInc(10);
}

//----------------------------------------------------------------------
// Top interface/ implementation

void EmitCStmts::emitVarList(AstNode* firstp, EisWhich which, const string& prefixIfImp) {
    // Put out a list of signal declarations
    // in order of 0:clocks, 1:vluint8, 2:vluint16, 4:vluint32, 5:vluint64, 6:wide, 7:arrays
    // This aids cache packing and locality
    //
    // Largest->smallest reduces the number of pad variables.  Also
    // experimented with alternating between large->small and small->large
    // on successive Mtask groups, but then when a new mtask gets added may
    // cause a huge delta.
    //
    // TODO: Move this sort to an earlier visitor stage.
    VarSortMap varAnonMap;
    VarSortMap varNonanonMap;

    for (int isstatic=1; isstatic>=0; isstatic--) {
        if (prefixIfImp!="" && !isstatic) continue;
        for (AstNode* nodep=firstp; nodep; nodep = nodep->nextp()) {
            if (const AstVar* varp = VN_CAST(nodep, Var)) {
                bool doit = true;
                switch (which) {
                case EVL_CLASS_IO:   doit = varp->isIO(); break;
                case EVL_CLASS_SIG:  doit = (varp->isSignal() && !varp->isIO()); break;
                case EVL_CLASS_TEMP: doit = (varp->isTemp() && !varp->isIO()); break;
                case EVL_CLASS_PAR:  doit = (varp->isParam() && !VN_IS(varp->valuep(), Const)); break;
                case EVL_CLASS_ALL:  doit = true; break;
                case EVL_FUNC_ALL:  doit = true; break;
                default: v3fatalSrc("Bad Case");
                }
                if (varp->isStatic() ? !isstatic : isstatic) doit=false;
                if (doit) {
                    int sigbytes = varp->dtypeSkipRefp()->widthAlignBytes();
                    int sortbytes = 9;
                    if (varp->isUsedClock() && varp->widthMin()==1) sortbytes = 0;
                    else if (VN_IS(varp->dtypeSkipRefp(), UnpackArrayDType)) sortbytes=8;
                    else if (varp->basicp() && varp->basicp()->isOpaque()) sortbytes=7;
                    else if (varp->isScBv() || varp->isScBigUint()) sortbytes=6;
                    else if (sigbytes==8) sortbytes=5;
                    else if (sigbytes==4) sortbytes=4;
                    else if (sigbytes==2) sortbytes=2;
                    else if (sigbytes==1) sortbytes=1;

                    bool anonOk = (v3Global.opt.compLimitMembers() != 0  // Enabled
                                   && !varp->isStatic()
                                   && !varp->isIO()  // Confusing to user
                                   && !varp->isSc()  // Aggregates can't be anon
                                   && (varp->basicp() && !varp->basicp()->isOpaque())  // Aggregates can't be anon
                                   && which != EVL_FUNC_ALL);  // Anon not legal in funcs, and gcc bug free there anyhow
                    if (anonOk) {
                        varAnonMap[sortbytes].push_back(varp);
                    } else {
                        varNonanonMap[sortbytes].push_back(varp);
                    }
                }
            }
        }
    }

    VarVec anons;
    VarVec nonanons;
    emitVarSort(varAnonMap, &anons);
    emitVarSort(varNonanonMap, &nonanons);
    emitSortedVarList(anons, nonanons, prefixIfImp);
}

void EmitCStmts::emitVarSort(const VarSortMap& vmap, VarVec* sortedp) {
    UASSERT(sortedp->empty(), "Sorted should be initially empty");
    if (!v3Global.opt.mtasks()) {
        // Plain old serial mode. Sort by size, from small to large,
        // to optimize for both packing and small offsets in code.
        for (VarSortMap::const_iterator it = vmap.begin();
             it != vmap.end(); ++it) {
            for (VarVec::const_iterator jt = it->second.begin();
                 jt != it->second.end(); ++jt) {
                sortedp->push_back(*jt);
            }
        }
        return;
    }

    // MacroTask mode.  Sort by MTask-affinity group first, size second.
    typedef std::map<MTaskIdSet, VarSortMap> MTaskVarSortMap;
    MTaskVarSortMap m2v;
    for (VarSortMap::const_iterator it = vmap.begin(); it != vmap.end(); ++it) {
        int size_class = it->first;
        const VarVec& vec = it->second;
        for (VarVec::const_iterator jt = vec.begin(); jt != vec.end(); ++jt) {
            const AstVar* varp = *jt;
            m2v[varp->mtaskIds()][size_class].push_back(varp);
        }
    }

    // Create a TSP sort state for each MTaskIdSet footprint
    V3TSP::StateVec states;
    for (MTaskVarSortMap::iterator it = m2v.begin(); it != m2v.end(); ++it) {
        states.push_back(new EmitVarTspSorter(it->first));
    }

    // Do the TSP sort
    V3TSP::StateVec sorted_states;
    V3TSP::tspSort(states, &sorted_states);

    for (V3TSP::StateVec::iterator it = sorted_states.begin();
         it != sorted_states.end(); ++it) {
        const EmitVarTspSorter* statep = dynamic_cast<const EmitVarTspSorter*>(*it);
        const VarSortMap& localVmap = m2v[statep->mtaskIds()];
        // use rbegin/rend to sort size large->small
        for (VarSortMap::const_reverse_iterator jt = localVmap.rbegin();
             jt != localVmap.rend(); ++jt) {
            const VarVec& vec = jt->second;
            for (VarVec::const_iterator kt = vec.begin();
                 kt != vec.end(); ++kt) {
                sortedp->push_back(*kt);
            }
        }
        delete statep; VL_DANGLING(statep);
    }
}

void EmitCStmts::emitSortedVarList(const VarVec& anons,
                                   const VarVec& nonanons,
                                   const string& prefixIfImp) {
    string curVarCmt;
    // Output anons
    {
        int anonMembers = anons.size();
        int lim = v3Global.opt.compLimitMembers();
        int anonL3s = 1;
        int anonL2s = 1;
        int anonL1s = 1;
        if (anonMembers > (lim*lim*lim)) {
            anonL3s = (anonMembers + (lim*lim*lim) - 1) / (lim*lim*lim);
            anonL2s = lim;
            anonL1s = lim;
        } else if (anonMembers > (lim*lim)) {
            anonL2s = (anonMembers + (lim*lim) - 1) / (lim*lim);
            anonL1s = lim;
        } else if (anonMembers > lim) {
            anonL1s = (anonMembers + lim - 1) / lim;
        }
        if (anonL1s != 1) puts("// Anonymous structures to workaround compiler member-count bugs\n");
        VarVec::const_iterator it = anons.begin();
        for (int l3=0; l3<anonL3s && it != anons.end(); ++l3) {
            if (anonL3s != 1) puts("struct {\n");
            for (int l2=0; l2<anonL2s && it != anons.end(); ++l2) {
                if (anonL2s != 1) puts("struct {\n");
                for (int l1=0; l1<anonL1s && it != anons.end(); ++l1) {
                    if (anonL1s != 1) puts("struct {\n");
                    for (int l0=0; l0<lim && it != anons.end(); ++l0) {
                        const AstVar* varp = *it;
                        emitVarCmtChg(varp, &curVarCmt);
                        emitVarDecl(varp, prefixIfImp);
                        ++it;
                    }
                    if (anonL1s != 1) puts("};\n");
                }
                if (anonL2s != 1) puts("};\n");
            }
            if (anonL3s != 1) puts("};\n");
        }
        // Leftovers, just in case off by one error somewhere above
        for (; it != anons.end(); ++it) {
            const AstVar* varp = *it;
            emitVarCmtChg(varp, &curVarCmt);
            emitVarDecl(varp, prefixIfImp);
        }
    }
    // Output nonanons
    for (VarVec::const_iterator it = nonanons.begin(); it != nonanons.end(); ++it) {
        const AstVar* varp = *it;
        emitVarCmtChg(varp, &curVarCmt);
        emitVarDecl(varp, prefixIfImp);
    }
}

struct CmpName {
    inline bool operator() (const AstNode* lhsp, const AstNode* rhsp) const {
	return lhsp->name() < rhsp->name();
    }
};

void EmitCImp::emitIntFuncDecls(AstNodeModule* modp) {
    typedef std::vector<const AstCFunc*> FuncVec;
    FuncVec funcsp;

    for (AstNode* nodep=modp->stmtsp(); nodep; nodep = nodep->nextp()) {
        if (const AstCFunc* funcp = VN_CAST(nodep, CFunc)) {
	    if (!funcp->skipDecl()) {
		funcsp.push_back(funcp);
	    }
	}
    }

    stable_sort(funcsp.begin(), funcsp.end(), CmpName());

    for (FuncVec::iterator it = funcsp.begin(); it != funcsp.end(); ++it) {
        const AstCFunc* funcp = *it;
	if (!funcp->dpiImport()) {  // DPI is prototyped in __Dpi.h
	    ofp()->putsPrivate(funcp->declPrivate());
            if (funcp->ifdef()!="") puts("#ifdef "+funcp->ifdef()+"\n");
            if (funcp->isStatic().trueU()) puts("static ");
            puts(funcp->rtnTypeVoid()); puts(" ");
	    puts(funcp->name()); puts("("+cFuncArgs(funcp)+");\n");
	    if (funcp->ifdef()!="") puts("#endif // "+funcp->ifdef()+"\n");
	}
    }

    if (modp->isTop() && v3Global.opt.mtasks()) {
        // Emit the mtask func prototypes.
        AstExecGraph* execGraphp = v3Global.rootp()->execGraphp();
        if (!execGraphp) v3Global.rootp()->v3fatalSrc("Root should have an execGraphp");
        const V3Graph* depGraphp = execGraphp->depGraphp();
        for (const V3GraphVertex* vxp = depGraphp->verticesBeginp();
             vxp; vxp = vxp->verticesNextp()) {
            const ExecMTask* mtp = dynamic_cast<const ExecMTask*>(vxp);
            if (mtp->threadRoot()) {
                // Emit function declaration for this mtask
                ofp()->putsPrivate(true);
                puts("static void "); puts(mtp->cFuncName());
                puts("(bool even_cycle, void* symtab);\n");
            }
        }
        // No AstCFunc for this one, as it's synthetic. Just write it:
        puts("static void __Vmtask__final(bool even_cycle, void* symtab);\n");
    }
}

void EmitCImp::emitMTaskState() {
    ofp()->putsPrivate(true);
    AstExecGraph* execGraphp = v3Global.rootp()->execGraphp();
    if (!execGraphp) v3Global.rootp()->v3fatalSrc("Root should have an execGraphp");

    const V3Graph* depGraphp = execGraphp->depGraphp();
    for (const V3GraphVertex* vxp = depGraphp->verticesBeginp();
         vxp; vxp = vxp->verticesNextp()) {
        const ExecMTask* mtp = dynamic_cast<const ExecMTask*>(vxp);
        if (packedMTaskMayBlock(mtp) > 0) {
            puts("VlMTaskVertex __Vm_mt_" + cvtToStr(mtp->id()) + ";\n");
        }
    }
    // This fake mtask depends on all the real ones.  We use it to block
    // eval() until all mtasks are done.
    //
    // In the future we might allow _eval() to return before the graph is
    // fully done executing, for "half wave" scheduling. For now we wait
    // for all mtasks though.
    puts("VlMTaskVertex __Vm_mt_final;\n");
    puts("VlThreadPool* __Vm_threadPoolp;\n");

    if (v3Global.opt.profThreads()) {
        // rdtsc() at current cycle start
        puts("vluint64_t __Vm_profile_cycle_start;\n");
        // Time we finished analysis
        puts("vluint64_t __Vm_profile_time_finished;\n");
        // Track our position in the cache warmup and actual profile window
        puts("vluint32_t __Vm_profile_window_ct;\n");
    }

    puts("bool __Vm_even_cycle;\n");
}

void EmitCImp::emitInt(AstNodeModule* modp) {
    // Always have this first; gcc has short circuiting if #ifdef is first in a file
    puts("#ifndef _"+modClassName(modp)+"_H_\n");
    puts("#define _"+modClassName(modp)+"_H_\n");
    puts("\n");

    ofp()->putsIntTopInclude();
    if (v3Global.needHeavy()) {
	puts("#include \"verilated_heavy.h\"\n");
    } else {
	puts("#include \"verilated.h\"\n");
    }
    if (v3Global.opt.mtasks()) {
        puts("#include \"verilated_threads.h\"\n");
    }
    if (v3Global.opt.savable()) {
	puts("#include \"verilated_save.h\"\n");
    }
    if (v3Global.opt.coverage()) {
	puts("#include \"verilated_cov.h\"\n");
	if (v3Global.opt.savable()) v3error("--coverage and --savable not supported together");
    }
    if (v3Global.needHInlines()) {   // Set by V3EmitCInlines; should have been called before us
	puts("#include \""+topClassName()+"__Inlines.h\"\n");
    }
    if (v3Global.dpi()) {
	// do this before including our main .h file so that any references to
	// types defined in svdpi.h are available
	puts("#include \""+ topClassName() +"__Dpi.h\"\n");
    }
    puts("\n");

    // Declare foreign instances up front to make C++ happy
    puts("class "+symClassName()+";\n");
    vl_unordered_set<string> didClassName;
    for (AstNode* nodep=modp->stmtsp(); nodep; nodep = nodep->nextp()) {
        if (AstCell* cellp=VN_CAST(nodep, Cell)) {
	    string className = modClassName(cellp->modp());
	    if (didClassName.find(className)==didClassName.end()) {
		puts("class "+className+";\n");
		didClassName.insert(className);
	    }
	}
    }
    if (v3Global.opt.trace()) {
	puts("class "+v3Global.opt.traceClassBase()+";\n");
    }

    puts("\n//----------\n\n");
    emitTextSection(AstType::atScHdr);

    if (optSystemC() && modp->isTop()) {
	puts("SC_MODULE("+modClassName(modp)+") {\n");
    } else {
	puts("VL_MODULE("+modClassName(modp)+") {\n");
    }
    ofp()->resetPrivate();
    ofp()->putsPrivate(false);  // public:

    {  // Instantiated cells
	bool did = false;
	for (AstNode* nodep=modp->stmtsp(); nodep; nodep = nodep->nextp()) {
            if (AstCell* cellp=VN_CAST(nodep, Cell)) {
		if (!did) {
		    did = true;
		    putsDecoration("// CELLS\n");
		    if (modp->isTop()) puts("// Public to allow access to /*verilator_public*/ items;\n");
		    if (modp->isTop()) puts("// otherwise the application code can consider these internals.\n");
		}
		ofp()->putsCellDecl(modClassName(cellp->modp()), cellp->name());
	    }
	}
    }

    emitTypedefs(modp->stmtsp());

    puts("\n// PORTS\n");
    if (modp->isTop()) puts("// The application code writes and reads these signals to\n");
    if (modp->isTop()) puts("// propagate new values into/out from the Verilated model.\n");
    emitVarList(modp->stmtsp(), EVL_CLASS_IO, "");

    puts("\n// LOCAL SIGNALS\n");
    if (modp->isTop()) puts("// Internals; generally not touched by application code\n");
    emitVarList(modp->stmtsp(), EVL_CLASS_SIG, "");

    puts("\n// LOCAL VARIABLES\n");
    if (modp->isTop()) puts("// Internals; generally not touched by application code\n");
    emitVarList(modp->stmtsp(), EVL_CLASS_TEMP, "");

    puts("\n// INTERNAL VARIABLES\n");
    if (modp->isTop()) puts("// Internals; generally not touched by application code\n");
    ofp()->putsPrivate(!modp->isTop());  // private: unless top
    puts(symClassName()+"* __VlSymsp;  // Symbol table\n");
    ofp()->putsPrivate(false);  // public:
    if (modp->isTop()) {
	if (v3Global.opt.inhibitSim()) {
	    puts("bool __Vm_inhibitSim;  ///< Set true to disable evaluation of module\n");
	}
    }
    if (modp->isTop() && v3Global.opt.mtasks()) {
        emitMTaskState();
    }
    emitCoverageDecl(modp);	// may flip public/private

    puts("\n// PARAMETERS\n");
    if (modp->isTop()) puts("// Parameters marked /*verilator public*/ for use by application code\n");
    ofp()->putsPrivate(false);  // public:
    emitVarList(modp->stmtsp(), EVL_CLASS_PAR, "");  // Only those that are non-CONST
    for (AstNode* nodep=modp->stmtsp(); nodep; nodep = nodep->nextp()) {
        if (const AstVar* varp = VN_CAST(nodep, Var)) {
	    if (varp->isParam() && (varp->isUsedParam() || varp->isSigPublic())) {
		if (!varp->valuep()) nodep->v3fatalSrc("No init for a param?");
		// These should be static const values, however microsloth VC++ doesn't
		// support them.  They also cause problems with GDB under GCC2.95.
		if (varp->isWide()) {   // Unsupported for output
		    putsDecoration("// enum WData "+varp->name()+"  //wide");
                } else if (!VN_IS(varp->valuep(), Const)) {  // Unsupported for output
		    //putsDecoration("// enum ..... "+varp->name()+"  //not simple value, see variable above instead");
                } else if (VN_IS(varp->dtypep(), BasicDType)
                           && VN_CAST(varp->dtypep(), BasicDType)->isOpaque()) {  // Can't put out e.g. doubles
		} else {
		    puts("enum ");
		    puts(varp->isQuad()?"_QData":"_IData");
		    puts(""+varp->name()+" { "+varp->name()+" = ");
                    iterateAndNextNull(varp->valuep());
		    puts("};");
		}
		puts("\n");
	    }
	}
    }

    puts("\n// CONSTRUCTORS\n");
    ofp()->resetPrivate();
    // We don't need a private copy constructor, as VerilatedModule has one for us.
    ofp()->putsPrivate(true);
    puts("VL_UNCOPYABLE("+modClassName(modp)+");  ///< Copying not allowed\n");

    ofp()->putsPrivate(false);  // public:
    if (optSystemC() && modp->isTop()) {
	puts("SC_CTOR("+modClassName(modp)+");\n");
	puts("virtual ~"+modClassName(modp)+"();\n");
    } else if (optSystemC()) {
	puts("VL_CTOR("+modClassName(modp)+");\n");
	puts("~"+modClassName(modp)+"();\n");
    } else {
	if (modp->isTop()) {
	    puts("/// Construct the model; called by application code\n");
	    puts("/// The special name "" may be used to make a wrapper with a\n");
	    puts("/// single model invisible with respect to DPI scope names.\n");
	}
	puts(modClassName(modp)+"(const char* name=\"TOP\");\n");
	if (modp->isTop()) puts("/// Destroy the model; called (often implicitly) by application code\n");
	puts("~"+modClassName(modp)+"();\n");
    }
    if (v3Global.opt.trace()) {
	if (modp->isTop()) puts("/// Trace signals in the model; called by application code\n");
        puts("void trace("+v3Global.opt.traceClassBase()+"C* tfp, int levels, int options=0);\n");
	if (modp->isTop() && optSystemC()) {
	    puts("/// SC tracing; avoid overloaded virtual function lint warning\n");
            puts("virtual void trace(sc_trace_file* tfp) const { ::sc_core::sc_module::trace(tfp); }\n");
	}
    }

    emitTextSection(AstType::atScInt);

    puts("\n// API METHODS\n");
    if (modp->isTop()) {
	if (optSystemC()) ofp()->putsPrivate(true);	///< eval() is invoked by our sensitive() calls.
	else puts("/// Evaluate the model.  Application must call when inputs change.\n");
	puts("void eval();\n");
	ofp()->putsPrivate(false);  // public:
	if (!optSystemC()) puts("/// Simulation complete, run final blocks.  Application must call on completion.\n");
	puts("void final();\n");
	if (v3Global.opt.inhibitSim()) {
	    puts("void inhibitSim(bool flag) { __Vm_inhibitSim=flag; }  ///< Set true to disable evaluation of module\n");
	}
    }

    puts("\n// INTERNAL METHODS\n");
    if (modp->isTop()) {
	ofp()->putsPrivate(true);  // private:
	puts("static void _eval_initial_loop("+EmitCBaseVisitor::symClassVar()+");\n");
    }

    ofp()->putsPrivate(false);  // public:
    puts("void __Vconfigure("+symClassName()+"* symsp, bool first);\n");

    emitIntFuncDecls(modp);

    if (v3Global.opt.trace()) {
	ofp()->putsPrivate(false);  // public:
        puts("static void traceInit("+v3Global.opt.traceClassBase()+"* vcdp, void* userthis, uint32_t code);\n");
        puts("static void traceFull("+v3Global.opt.traceClassBase()+"* vcdp, void* userthis, uint32_t code);\n");
        puts("static void traceChg("+v3Global.opt.traceClassBase()+"* vcdp, void* userthis, uint32_t code);\n");
    }
    if (v3Global.opt.savable()) {
	ofp()->putsPrivate(false);  // public:
	puts("void __Vserialize(VerilatedSerialize& os);\n");
	puts("void __Vdeserialize(VerilatedDeserialize& os);\n");
	puts("\n");
    }

    puts("} VL_ATTR_ALIGNED(128);\n");
    puts("\n");

    // Save/restore
    if (v3Global.opt.savable() && modp->isTop()) {
	puts("inline VerilatedSerialize&   operator<<(VerilatedSerialize& os,   "+modClassName(modp)+"& rhs) {\n"
	     "Verilated::quiesce(); rhs.__Vserialize(os); return os; }\n");
	puts("inline VerilatedDeserialize& operator>>(VerilatedDeserialize& os, "+modClassName(modp)+"& rhs) {\n"
	     "Verilated::quiesce(); rhs.__Vdeserialize(os); return os; }\n");
	puts("\n");
    }

    // finish up h-file
    puts("#endif // guard\n");
}

//----------------------------------------------------------------------

void EmitCImp::emitImp(AstNodeModule* modp) {
    puts("#include \""+modClassName(modp)+".h\"\n");
    puts("#include \""+symClassName()+".h\"\n");

    if (v3Global.dpi()) {
	puts("\n");
	puts("#include \"verilated_dpi.h\"\n");
    }
    puts("\n");

    emitTextSection(AstType::atScImpHdr);

    if (m_slow && splitFilenum()==0) {
	puts("\n//--------------------\n");
	puts("// STATIC VARIABLES\n\n");
        emitVarList(modp->stmtsp(), EVL_CLASS_ALL, modClassName(modp));
    }

    if (m_fast && splitFilenum()==0) {
	emitTextSection(AstType::atScImp);
	emitStaticDecl(modp);
    }

    if (m_slow && splitFilenum()==0) {
	puts("\n//--------------------\n");
	emitCtorImp(modp);
	emitConfigureImp(modp);
	emitDestructorImp(modp);
	emitSavableImp(modp);
	emitCoverageImp(modp);
    }

    if (m_fast && splitFilenum()==0) {
	if (modp->isTop()) {
	    emitStaticDecl(modp);
	    puts("\n//--------------------\n");
	    puts("\n");
	    emitWrapEval(modp);
	}
    }

    // Blocks
    puts("\n//--------------------\n");
    puts("// Internal Methods\n");
}

//######################################################################

void EmitCImp::maybeSplit(AstNodeModule* modp) {
    if (splitNeeded()) {
        // Close old file
        delete m_ofp; m_ofp=NULL;
        // Open a new file
        m_ofp = newOutCFile(modp, !m_fast, true/*source*/, splitFilenumInc());
        emitImp(modp);
    }
    splitSizeInc(10);  // Even blank functions get a file with a low csplit
}

void EmitCImp::main(AstNodeModule* modp, bool slow, bool fast) {
    // Output a module
    m_modp = modp;
    m_slow = slow;
    m_fast = fast;

    if (debug()>=5) {
	UINFO(0,"  Emitting "<<modClassName(modp)<<endl);
    }

    if (m_fast) {
        m_ofp = newOutCFile(modp, !m_fast, false/*source*/);
        emitInt(modp);
        delete m_ofp; m_ofp=NULL;
    }

    m_ofp = newOutCFile(modp, !m_fast, true/*source*/);
    emitImp(modp);

    for (AstNode* nodep=modp->stmtsp(); nodep; nodep = nodep->nextp()) {
        if (AstCFunc* funcp = VN_CAST(nodep, CFunc)) {
            maybeSplit(modp);
	    mainDoFunc(funcp);
	}
    }

    if (fast && modp->isTop() && v3Global.opt.mtasks()) {
        // Make a final pass and emit function definitions for the mtasks
        // in the ExecGraph
        AstExecGraph* execGraphp = v3Global.rootp()->execGraphp();
        const V3Graph* depGraphp = execGraphp->depGraphp();
        for (const V3GraphVertex* vxp = depGraphp->verticesBeginp();
             vxp; vxp = vxp->verticesNextp()) {
            const ExecMTask* mtaskp = dynamic_cast<const ExecMTask*>(vxp);
            if (mtaskp->threadRoot()) {
                maybeSplit(modp);
                // Only define one function for all the mtasks packed on
                // a given thread. We'll name this function after the
                // root mtask though it contains multiple mtasks' worth
                // of logic.
                iterate(mtaskp->bodyp());
            }
        }
    }
    delete m_ofp; m_ofp=NULL;
}

//######################################################################
// Tracing routines

class EmitCTrace : EmitCStmts {
    // NODE STATE/TYPES
    // Cleared on netlist
    //  AstNode::user1()        -> int.  Enum number
    AstUser1InUse m_inuser1;

    // MEMBERS
    AstCFunc*	m_funcp;	// Function we're in now
    bool	m_slow;		// Making slow file
    int         m_enumNum;      // Enumeration number (whole netlist)

    // METHODS
    void newOutCFile(int filenum) {
        string filename = (v3Global.opt.makeDir()+"/"+ topClassName()
                           +"__Trace");
        if (filenum) filename += "__"+cvtToStr(filenum);
        filename += (m_slow ? "__Slow":"");
        filename += ".cpp";

	AstCFile* cfilep = newCFile(filename, m_slow, true/*source*/);
	cfilep->support(true);

	if (m_ofp) v3fatalSrc("Previous file not closed");
        m_ofp = new V3OutCFile(filename);
	m_ofp->putsHeader();
	m_ofp->puts("// DESCR" "IPTION: Verilator output: Tracing implementation internals\n");

	emitTraceHeader();
    }

    void emitTraceHeader() {
	// Includes
        puts("#include \""+v3Global.opt.traceSourceName()+"_c.h\"\n");
	puts("#include \""+ symClassName() +".h\"\n");
	puts("\n");
    }

    void emitTraceSlow() {
	puts("\n//======================\n\n");

        puts("void "+topClassName()+"::trace(");
        puts(v3Global.opt.traceClassBase()+"C* tfp, int, int) {\n");
        puts(  "tfp->spTrace()->addCallback("
	       "&"+topClassName()+"::traceInit"
	       +", &"+topClassName()+"::traceFull"
	       +", &"+topClassName()+"::traceChg, this);\n");
	puts("}\n");
	splitSizeInc(10);

	puts("void "+topClassName()+"::traceInit("
	     +v3Global.opt.traceClassBase()+"* vcdp, void* userthis, uint32_t code) {\n");
	putsDecoration("// Callback from vcd->open()\n");
	puts(topClassName()+"* t=("+topClassName()+"*)userthis;\n");
	puts(EmitCBaseVisitor::symClassVar()+" = t->__VlSymsp;  // Setup global symbol table\n");
        puts("if (!Verilated::calcUnusedSigs()) {\n");
        puts(    "VL_FATAL_MT(__FILE__,__LINE__,__FILE__,\"Turning on wave traces requires Verilated::traceEverOn(true) call before time 0.\");\n");
        puts("}\n");
	puts("vcdp->scopeEscape(' ');\n");
        puts("t->traceInitThis(vlSymsp, vcdp, code);\n");
	puts("vcdp->scopeEscape('.');\n");  // Restore so later traced files won't break
	puts("}\n");
	splitSizeInc(10);

	puts("void "+topClassName()+"::traceFull("
	     +v3Global.opt.traceClassBase()+"* vcdp, void* userthis, uint32_t code) {\n");
	putsDecoration("// Callback from vcd->dump()\n");
	puts(topClassName()+"* t=("+topClassName()+"*)userthis;\n");
	puts(EmitCBaseVisitor::symClassVar()+" = t->__VlSymsp;  // Setup global symbol table\n");
        puts("t->traceFullThis(vlSymsp, vcdp, code);\n");
	puts("}\n");
	splitSizeInc(10);

	puts("\n//======================\n\n");
    }

    void emitTraceFast() {
	puts("\n//======================\n\n");

	puts("void "+topClassName()+"::traceChg("
	     +v3Global.opt.traceClassBase()+"* vcdp, void* userthis, uint32_t code) {\n");
	putsDecoration("// Callback from vcd->dump()\n");
	puts(topClassName()+"* t=("+topClassName()+"*)userthis;\n");
	puts(EmitCBaseVisitor::symClassVar()+" = t->__VlSymsp;  // Setup global symbol table\n");
	puts("if (vlSymsp->getClearActivity()) {\n");
        puts("t->traceChgThis(vlSymsp, vcdp, code);\n");
	puts("}\n");
	puts("}\n");
	splitSizeInc(10);

	puts("\n//======================\n\n");
    }

    bool emitTraceIsScBv(AstTraceInc* nodep) {
        const AstVarRef* varrefp = VN_CAST(nodep->valuep(), VarRef);
	if (!varrefp) return false;
	AstVar* varp = varrefp->varp();
	return varp->isSc() && varp->isScBv();
    }

    bool emitTraceIsScBigUint(AstTraceInc* nodep) {
        const AstVarRef* varrefp = VN_CAST(nodep->valuep(), VarRef);
	if (!varrefp) return false;
	AstVar* varp = varrefp->varp();
	return varp->isSc() && varp->isScBigUint();
    }

    bool emitTraceIsScUint(AstTraceInc* nodep) {
        const AstVarRef* varrefp = VN_CAST(nodep->valuep(), VarRef);
	if (!varrefp) return false;
	AstVar* varp = varrefp->varp();
	return varp->isSc() && varp->isScUint();
    }

    void emitTraceInitOne(AstTraceDecl* nodep, int enumNum) {
	if (nodep->dtypep()->basicp()->isDouble()) {
	    puts("vcdp->declDouble");
	} else if (nodep->isWide()) {
	    puts("vcdp->declArray");
	} else if (nodep->isQuad()) {
            puts("vcdp->declQuad");
	} else if (nodep->bitRange().ranged()) {
            puts("vcdp->declBus");
	} else {
            puts("vcdp->declBit");
	}

	puts("(c+"+cvtToStr(nodep->code()));
	if (nodep->arrayRange().ranged()) puts("+i*"+cvtToStr(nodep->widthWords()));
	puts(",");
	putsQuoted(nodep->showname());
        // Direction
        if (v3Global.opt.traceFormat().fstFlavor()) {
            puts(","+cvtToStr(enumNum));
            // fstVarDir
            if (nodep->declDirection().isInoutish()) puts(",FST_VD_INOUT");
            else if (nodep->declDirection().isWritable()) puts(",FST_VD_OUTPUT");
            else if (nodep->declDirection().isNonOutput()) puts(",FST_VD_INPUT");
            else puts(",FST_VD_IMPLICIT");
            //
            // fstVarType
            AstVarType vartype = nodep->varType();
            AstBasicDTypeKwd kwd = nodep->declKwd();
            string fstvt;
            // Doubles have special decoding properties, so must indicate if a double
            if (nodep->dtypep()->basicp()->isDouble()) {
                if (vartype == AstVarType::GPARAM || vartype == AstVarType::LPARAM) {
                    fstvt = "FST_VT_VCD_REAL_PARAMETER";
                } else fstvt = "FST_VT_VCD_REAL";
            }
            else if (vartype == AstVarType::GPARAM)  fstvt = "FST_VT_VCD_PARAMETER";
            else if (vartype == AstVarType::LPARAM)  fstvt = "FST_VT_VCD_PARAMETER";
            else if (vartype == AstVarType::SUPPLY0) fstvt = "FST_VT_VCD_SUPPLY0";
            else if (vartype == AstVarType::SUPPLY1) fstvt = "FST_VT_VCD_SUPPLY1";
            else if (vartype == AstVarType::TRI0)    fstvt = "FST_VT_VCD_TRI0";
            else if (vartype == AstVarType::TRI1)    fstvt = "FST_VT_VCD_TRI1";
            else if (vartype == AstVarType::TRIWIRE) fstvt = "FST_VT_VCD_TRI";
            else if (vartype == AstVarType::WIRE)    fstvt = "FST_VT_VCD_WIRE";
            else if (vartype == AstVarType::PORT)    fstvt = "FST_VT_VCD_WIRE";
            //
            else if (kwd == AstBasicDTypeKwd::INTEGER)  fstvt = "FST_VT_VCD_INTEGER";
            else if (kwd == AstBasicDTypeKwd::BIT)      fstvt = "FST_VT_SV_BIT";
            else if (kwd == AstBasicDTypeKwd::LOGIC)    fstvt = "FST_VT_SV_LOGIC";
            else if (kwd == AstBasicDTypeKwd::INT)      fstvt = "FST_VT_SV_INT";
            else if (kwd == AstBasicDTypeKwd::SHORTINT) fstvt = "FST_VT_SV_SHORTINT";
            else if (kwd == AstBasicDTypeKwd::LONGINT)  fstvt = "FST_VT_SV_LONGINT";
            else if (kwd == AstBasicDTypeKwd::BYTE)     fstvt = "FST_VT_SV_BYTE";
            else fstvt = "FST_VT_SV_BIT";
            //
            // Not currently supported
            // FST_VT_VCD_EVENT
            // FST_VT_VCD_PORT
            // FST_VT_VCD_SHORTREAL
            // FST_VT_VCD_REALTIME
            // FST_VT_VCD_SPARRAY
            // FST_VT_VCD_TRIAND
            // FST_VT_VCD_TRIOR
            // FST_VT_VCD_TRIREG
            // FST_VT_VCD_WAND
            // FST_VT_VCD_WOR
            // FST_VT_SV_ENUM
            // FST_VT_GEN_STRING
            puts(","+fstvt);
        }
        // Range
	if (nodep->arrayRange().ranged()) {
	    puts(",(i+"+cvtToStr(nodep->arrayRange().lo())+")");
	} else {
	    puts(",-1");
	}
	if (!nodep->dtypep()->basicp()->isDouble()  // When float/double no longer have widths this can go
	    && nodep->bitRange().ranged()) {
	    puts(","+cvtToStr(nodep->bitRange().left())+","+cvtToStr(nodep->bitRange().right()));
	}
	puts(");");
    }

    int emitTraceDeclDType(AstNodeDType* nodep) {
        // Return enum number or -1 for none
        if (v3Global.opt.traceFormat().fstFlavor()) {
            // Skip over refs-to-refs, but stop before final ref so can get data type name
            // Alternatively back in V3Width we could push enum names from upper typedefs
            if (AstEnumDType* enump = VN_CAST(nodep->skipRefToEnump(), EnumDType)) {
                int enumNum = enump->user1();
                if (!enumNum) {
                    enumNum = ++m_enumNum;
                    enump->user1(enumNum);
                    int nvals = 0;
                    puts("{\n");
                    puts("const char* __VenumItemNames[]\n");
                    puts("= {");
                    for (AstEnumItem* itemp = enump->itemsp(); itemp;
                         itemp=VN_CAST(itemp->nextp(), EnumItem)) {
                        if (++nvals > 1) puts(", ");
                        putbs("\""+itemp->prettyName()+"\"");
                    }
                    puts("};\n");
                    nvals = 0;
                    puts("const char* __VenumItemValues[]\n");
                    puts("= {");
                    for (AstEnumItem* itemp = enump->itemsp(); itemp;
                         itemp=VN_CAST(itemp->nextp(), EnumItem)) {
                        AstConst* constp = VN_CAST(itemp->valuep(), Const);
                        if (++nvals > 1) puts(", ");
                        putbs("\""+constp->num().displayed(nodep->fileline(), "%0b")+"\"");
                    }
                    puts("};\n");
                    puts("vcdp->declDTypeEnum("+cvtToStr(enumNum)
                         +", \""+enump->prettyName()+"\", "
                         +cvtToStr(nvals)
                         +", "+cvtToStr(enump->widthMin())
                         +", __VenumItemNames, __VenumItemValues);\n");
                    puts("}\n");
                }
                return enumNum;
            }
        }
        return -1;
    }

    void emitTraceChangeOne(AstTraceInc* nodep, int arrayindex) {
        iterateAndNextNull(nodep->precondsp());
	string full = ((m_funcp->funcType() == AstCFuncType::TRACE_FULL
			|| m_funcp->funcType() == AstCFuncType::TRACE_FULL_SUB)
		       ? "full":"chg");
        bool emitWidth = false;
	if (nodep->dtypep()->basicp()->isDouble()) {
	    puts("vcdp->"+full+"Double");
	} else if (nodep->isWide() || emitTraceIsScBv(nodep) || emitTraceIsScBigUint(nodep)) {
	    puts("vcdp->"+full+"Array");
            emitWidth = true;
	} else if (nodep->isQuad()) {
            puts("vcdp->"+full+"Quad");
            emitWidth = true;
        } else if (nodep->declp()->bitRange().ranged()
                   // 1 element smaller to use Bit dump
                   && nodep->declp()->bitRange().elements() != 1) {
            puts("vcdp->"+full+"Bus");
            emitWidth = true;
	} else {
            puts("vcdp->"+full+"Bit");
	}
	puts("(c+"+cvtToStr(nodep->declp()->code()
			    + ((arrayindex<0) ? 0 : (arrayindex*nodep->declp()->widthWords()))));
	puts(",");
	emitTraceValue(nodep, arrayindex);
        if (emitWidth) {
	    puts(","+cvtToStr(nodep->declp()->widthMin()));
	}
	puts(");\n");
    }
    void emitTraceValue(AstTraceInc* nodep, int arrayindex) {
        if (VN_IS(nodep->valuep(), VarRef)) {
            AstVarRef* varrefp = VN_CAST(nodep->valuep(), VarRef);
	    AstVar* varp = varrefp->varp();
	    puts("(");
	    if (emitTraceIsScBigUint(nodep)) puts("(vluint32_t*)");
	    else if (emitTraceIsScBv(nodep)) puts("VL_SC_BV_DATAP(");
            iterate(varrefp);  // Put var name out
	    // Tracing only supports 1D arrays
	    if (nodep->declp()->arrayRange().ranged()) {
		if (arrayindex==-2) puts("[i]");
		else if (arrayindex==-1) puts("[0]");
		else puts("["+cvtToStr(arrayindex)+"]");
	    }
	    if (varp->isSc()) puts(".read()");
	    if (emitTraceIsScUint(nodep)) puts(nodep->isQuad() ? ".to_uint64()" : ".to_uint()");
	    else if (emitTraceIsScBigUint(nodep)) puts(".get_raw()");
	    else if (emitTraceIsScBv(nodep)) puts(")");
	    puts(")");
	} else {
	    puts("(");
            iterate(nodep->valuep());
	    puts(")");
	}
    }

    // VISITORS
    using EmitCStmts::visit;  // Suppress hidden overloaded virtual function warnng
    virtual void visit(AstNetlist* nodep) {
	// Top module only
        iterate(nodep->topModulep());
    }
    virtual void visit(AstNodeModule* nodep) {
        iterateChildren(nodep);
    }
    virtual void visit(AstCFunc* nodep) {
	if (nodep->slow() != m_slow) return;
	if (nodep->funcType().isTrace()) {   // TRACE_*
	    m_funcp = nodep;

	    if (splitNeeded()) {
		// Close old file
		delete m_ofp; m_ofp=NULL;
		// Open a new file
                newOutCFile(splitFilenumInc());
	    }

	    splitSizeInc(nodep);

	    puts("\n");
	    puts(nodep->rtnTypeVoid()); puts(" ");
	    puts(topClassName()+"::"+nodep->name()
		 +"("+cFuncArgs(nodep)+") {\n");

	    if (nodep->symProlog()) puts(EmitCBaseVisitor::symTopAssign()+"\n");

	    puts("int c=code;\n");
	    puts("if (0 && vcdp && c) {}  // Prevent unused\n");
	    if (nodep->funcType() == AstCFuncType::TRACE_INIT) {
		puts("vcdp->module(vlSymsp->name());  // Setup signal names\n");
	    } else if (nodep->funcType() == AstCFuncType::TRACE_INIT_SUB) {
	    } else if (nodep->funcType() == AstCFuncType::TRACE_FULL) {
	    } else if (nodep->funcType() == AstCFuncType::TRACE_FULL_SUB) {
	    } else if (nodep->funcType() == AstCFuncType::TRACE_CHANGE) {
	    } else if (nodep->funcType() == AstCFuncType::TRACE_CHANGE_SUB) {
	    } else nodep->v3fatalSrc("Bad Case");

	    if (nodep->initsp()) putsDecoration("// Variables\n");
            emitVarList(nodep->initsp(), EVL_FUNC_ALL, "");
            iterateAndNextNull(nodep->initsp());

	    putsDecoration("// Body\n");
	    puts("{\n");
            iterateAndNextNull(nodep->stmtsp());
	    puts("}\n");
	    if (nodep->finalsp()) putsDecoration("// Final\n");
            iterateAndNextNull(nodep->finalsp());
	    puts("}\n");
	}
	m_funcp = NULL;
    }
    virtual void visit(AstTraceDecl* nodep) {
        int enumNum = emitTraceDeclDType(nodep->dtypep());
	if (nodep->arrayRange().ranged()) {
	    puts("{int i; for (i=0; i<"+cvtToStr(nodep->arrayRange().elements())+"; i++) {\n");
            emitTraceInitOne(nodep, enumNum);
	    puts("}}\n");
	} else {
            emitTraceInitOne(nodep, enumNum);
	    puts("\n");
	}
    }
    virtual void visit(AstTraceInc* nodep) {
	if (nodep->declp()->arrayRange().ranged()) {
	    // It traces faster if we unroll the loop
	    for (int i=0; i<nodep->declp()->arrayRange().elements(); i++) {
		emitTraceChangeOne(nodep, i);
	    }
	} else {
	    emitTraceChangeOne(nodep, -1);
	}
    }
    virtual void visit(AstCoverDecl* nodep) {
    }
    virtual void visit(AstCoverInc* nodep) {
    }

public:
    explicit EmitCTrace(bool slow) {
	m_funcp = NULL;
	m_slow = slow;
        m_enumNum = 0;
    }
    virtual ~EmitCTrace() {}
    void main() {
	// Put out the file
	newOutCFile(0);

	if (m_slow) emitTraceSlow();
	else emitTraceFast();

        iterate(v3Global.rootp());

	delete m_ofp; m_ofp=NULL;
    }
};

//######################################################################
// EmitC class functions

void V3EmitC::emitc() {
    UINFO(2,__FUNCTION__<<": "<<endl);
    // Process each module in turn
    for (AstNodeModule* nodep = v3Global.rootp()->modulesp(); nodep; nodep=VN_CAST(nodep->nextp(), NodeModule)) {
        if (v3Global.opt.outputSplit()) {
            { EmitCImp fast; fast.main(nodep, false, true); }
            { EmitCImp slow; slow.main(nodep, true, false); }
        } else {
            { EmitCImp both; both.main(nodep, true, true); }
        }
    }
}

void V3EmitC::emitcTrace() {
    UINFO(2,__FUNCTION__<<": "<<endl);
    if (v3Global.opt.trace()) {
        { EmitCTrace slow(true);  slow.main(); }
        { EmitCTrace fast(false); fast.main(); }
    }
}
