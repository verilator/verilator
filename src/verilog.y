// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Bison grammer file
//
// Code available from: http://www.veripool.org/verilator
//
//*************************************************************************
//
// Copyright 2003-2015 by Wilson Snyder.  This program is free software; you can
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
// Original code here by Paul Wasson and Duane Galbi
//*************************************************************************

%{
#include <cstdio>
#include <cstdlib>
#include <cstdarg>
#include <cstring>

#include "V3Ast.h"
#include "V3Global.h"
#include "V3Config.h"
#include "V3ParseImp.h"  // Defines YYTYPE; before including bison header

#define YYERROR_VERBOSE 1
#define YYINITDEPTH 10000	// Older bisons ignore YYMAXDEPTH
#define YYMAXDEPTH 10000

// Pick up new lexer
#define yylex PARSEP->lexToBison
#define GATEUNSUP(fl,tok) { if (!v3Global.opt.bboxUnsup()) { (fl)->v3error("Unsupported: Verilog 1995 gate primitive: "<<(tok)); } }

extern void yyerror(const char* errmsg);
extern void yyerrorf(const char* format, ...);

//======================================================================
// Statics (for here only)

#define PARSEP V3ParseImp::parsep()
#define SYMP PARSEP->symp()
#define GRAMMARP V3ParseGrammar::singletonp()

class V3ParseGrammar {
public:
    bool	m_impliedDecl;	// Allow implied wire declarations
    AstVarType	m_varDecl;	// Type for next signal declaration (reg/wire/etc)
    AstVarType	m_varIO;	// Type for next signal declaration (input/output/etc)
    AstVar*	m_varAttrp;	// Current variable for attribute adding
    AstRange*	m_gateRangep;	// Current range for gate declarations
    AstCase*	m_caseAttrp;	// Current case statement for attribute adding
    AstNodeDType* m_varDTypep;	// Pointer to data type for next signal declaration
    AstNodeDType* m_memDTypep;	// Pointer to data type for next member declaration
    int		m_pinNum;	// Pin number currently parsing
    string	m_instModule;	// Name of module referenced for instantiations
    AstPin*	m_instParamp;	// Parameters for instantiations
    bool	m_tracingParse;	// Tracing disable for parser

    static int	s_modTypeImpNum; // Implicit type number, incremented each module

    // CONSTRUCTORS
    V3ParseGrammar() {
	m_impliedDecl = false;
	m_varDecl = AstVarType::UNKNOWN;
	m_varIO = AstVarType::UNKNOWN;
	m_varDTypep = NULL;
	m_gateRangep = NULL;
	m_memDTypep = NULL;
	m_pinNum = -1;
	m_instModule = "";
	m_instParamp = NULL;
	m_varAttrp = NULL;
	m_caseAttrp = NULL;
	m_tracingParse = true;
    }
    static V3ParseGrammar* singletonp() {
	static V3ParseGrammar singleton;
	return &singleton;
    }

    // METHODS
    void argWrapList(AstNodeFTaskRef* nodep);
    bool allTracingOn(FileLine* fl) {
	return v3Global.opt.trace() && m_tracingParse && fl->tracingOn();
    }
    AstNodeDType* createArray(AstNodeDType* basep, AstRange* rangep, bool isPacked);
    AstVar*  createVariable(FileLine* fileline, string name, AstRange* arrayp, AstNode* attrsp);
    AstNode* createSupplyExpr(FileLine* fileline, string name, int value);
    AstText* createTextQuoted(FileLine* fileline, string text) {
	string newtext = deQuote(fileline, text);
	return new AstText(fileline, newtext);
    }
    AstDisplay* createDisplayError(FileLine* fileline) {
	AstDisplay* nodep = new AstDisplay(fileline,AstDisplayType::DT_ERROR,  "", NULL,NULL);
	nodep->addNext(new AstStop(fileline));
	return nodep;
    }
    AstNode* createGatePin(AstNode* exprp) {
	AstRange* rangep = m_gateRangep;
	if (!rangep) return exprp;
	else return new AstGatePin(rangep->fileline(), exprp, rangep->cloneTree(true));
    }
    void endLabel(FileLine* fl, AstNode* nodep, string* endnamep) { endLabel(fl, nodep->prettyName(), endnamep); }
    void endLabel(FileLine* fl, string name, string* endnamep) {
	if (fl && endnamep && *endnamep != "" && name != *endnamep
	    && name != AstNode::prettyName(*endnamep)) {
	    fl->v3warn(ENDLABEL,"End label '"<<*endnamep<<"' does not match begin label '"<<name<<"'");
	}
    }
    void setDType(AstNodeDType* dtypep) {
	if (m_varDTypep) { m_varDTypep->deleteTree(); m_varDTypep=NULL; } // It was cloned, so this is safe.
	m_varDTypep = dtypep;
    }
    AstPackage* unitPackage(FileLine* fl) {
	// Find one made earlier?
	AstPackage* pkgp = SYMP->symRootp()->findIdFlat(AstPackage::dollarUnitName())->nodep()->castPackage();
	if (!pkgp) {
	    pkgp = PARSEP->rootp()->dollarUnitPkgAddp();
	    SYMP->reinsert(pkgp, SYMP->symRootp());  // Don't push/pop scope as they're global
	}
	return pkgp;
    }
    AstNodeDType* addRange(AstBasicDType* dtypep, AstRange* rangesp, bool isPacked) {
	// If dtypep isn't basic, don't use this, call createArray() instead
	if (!rangesp) {
	    return dtypep;
	} else {
	    // If rangesp is "wire [3:3][2:2][1:1] foo [5:5][4:4]"
	    // then [1:1] becomes the basicdtype range; everything else is arraying
	    // the final [5:5][4:4] will be passed in another call to createArray
	    AstRange* rangearraysp = NULL;
	    if (dtypep->isRanged()) {
		rangearraysp = rangesp;  // Already a range; everything is an array
	    } else {
		AstRange* finalp = rangesp;
		while (finalp->nextp()) finalp=finalp->nextp()->castRange();
		if (finalp != rangesp) {
		    finalp->unlinkFrBack();
		    rangearraysp = rangesp;
		}
		if (dtypep->implicit()) {
		    // It's no longer implicit but a real logic type
		    AstBasicDType* newp = new AstBasicDType(dtypep->fileline(), AstBasicDTypeKwd::LOGIC,
							    dtypep->numeric(), dtypep->width(), dtypep->widthMin());
		    dtypep->deleteTree();  dtypep=NULL;
		    dtypep = newp;
		}
		dtypep->rangep(finalp);
	    }
	    return createArray(dtypep, rangearraysp, isPacked);
	}
    }
    string   deQuote(FileLine* fileline, string text);
    void checkDpiVer(FileLine* fileline, const string& str) {
	if (str != "DPI-C" && !v3Global.opt.bboxSys()) {
	    fileline->v3error("Unsupported DPI type '"<<str<<"': Use 'DPI-C'");
	}
    }
};

const AstBasicDTypeKwd LOGIC = AstBasicDTypeKwd::LOGIC;	// Shorthand "LOGIC"
const AstBasicDTypeKwd LOGIC_IMPLICIT = AstBasicDTypeKwd::LOGIC_IMPLICIT;

int V3ParseGrammar::s_modTypeImpNum = 0;

//======================================================================
// Macro functions

#define CRELINE() (PARSEP->copyOrSameFileLine())  // Only use in empty rules, so lines point at beginnings

#define VARRESET_LIST(decl)    { GRAMMARP->m_pinNum=1; VARRESET(); VARDECL(decl); }	// Start of pinlist
#define VARRESET_NONLIST(decl) { GRAMMARP->m_pinNum=0; VARRESET(); VARDECL(decl); }	// Not in a pinlist
#define VARRESET() { VARDECL(UNKNOWN); VARIO(UNKNOWN); VARDTYPE(NULL); }
#define VARDECL(type) { GRAMMARP->m_varDecl = AstVarType::type; }
#define VARIO(type) { GRAMMARP->m_varIO = AstVarType::type; }
#define VARDTYPE(dtypep) { GRAMMARP->setDType(dtypep); }

#define VARDONEA(fl,name,array,attrs) GRAMMARP->createVariable((fl),(name),(array),(attrs))
#define VARDONEP(portp,array,attrs) GRAMMARP->createVariable((portp)->fileline(),(portp)->name(),(array),(attrs))
#define PINNUMINC() (GRAMMARP->m_pinNum++)

#define GATERANGE(rangep) { GRAMMARP->m_gateRangep = rangep; }

#define INSTPREP(modname,paramsp) { GRAMMARP->m_impliedDecl = true; GRAMMARP->m_instModule = modname; GRAMMARP->m_instParamp = paramsp; }

#define DEL(nodep) { if (nodep) nodep->deleteTree(); }

static void ERRSVKWD(FileLine* fileline, const string& tokname) {
    static int toldonce = 0;
    fileline->v3error((string)"Unexpected \""+tokname+"\": \""+tokname+"\" is a SystemVerilog keyword misused as an identifier.");
    if (!toldonce++) fileline->v3error("Modify the Verilog-2001 code to avoid SV keywords, or use `begin_keywords or --language.");
}

//======================================================================

class AstSenTree;
%}

// When writing Bison patterns we use yTOKEN instead of "token",
// so Bison will error out on unknown "token"s.

// Generic lexer tokens, for example a number
// IEEE: real_number
%token<cdouble>		yaFLOATNUM	"FLOATING-POINT NUMBER"

// IEEE: identifier, class_identifier, class_variable_identifier,
// covergroup_variable_identifier, dynamic_array_variable_identifier,
// enum_identifier, interface_identifier, interface_instance_identifier,
// package_identifier, type_identifier, variable_identifier,
%token<strp>		yaID__ETC	"IDENTIFIER"
%token<strp>		yaID__LEX	"IDENTIFIER-in-lex"
%token<strp>		yaID__aPACKAGE	"PACKAGE-IDENTIFIER"
%token<strp>		yaID__aTYPE	"TYPE-IDENTIFIER"
//			Can't predecode aFUNCTION, can declare after use
//			Can't predecode aINTERFACE, can declare after use
//			Can't predecode aTASK, can declare after use

// IEEE: integral_number
%token<nump>		yaINTNUM	"INTEGER NUMBER"
// IEEE: time_literal + time_unit
%token<cdouble>		yaTIMENUM	"TIME NUMBER"
// IEEE: string_literal
%token<strp>		yaSTRING	"STRING"
%token<strp>		yaSTRING__IGNORE "STRING-ignored"	// Used when expr:string not allowed

%token<fl>		yaTIMINGSPEC	"TIMING SPEC ELEMENT"

%token<strp>		yaTABLELINE	"TABLE LINE"

%token<strp>		yaSCHDR		"`systemc_header BLOCK"
%token<strp>		yaSCINT		"`systemc_ctor BLOCK"
%token<strp>		yaSCIMP		"`systemc_dtor BLOCK"
%token<strp>		yaSCIMPH	"`systemc_interface BLOCK"
%token<strp>		yaSCCTOR	"`systemc_implementation BLOCK"
%token<strp>		yaSCDTOR	"`systemc_imp_header BLOCK"

%token<fl>		yVLT_COVERAGE_OFF "coverage_off"
%token<fl>		yVLT_COVERAGE_ON  "coverage_on"
%token<fl>		yVLT_LINT_OFF	  "lint_off"
%token<fl>		yVLT_LINT_ON	  "lint_on"
%token<fl>		yVLT_TRACING_OFF  "tracing_off"
%token<fl>		yVLT_TRACING_ON   "tracing_on"

%token<fl>		yVLT_D_FILE	"--file"
%token<fl>		yVLT_D_LINES	"--lines"
%token<fl>		yVLT_D_MSG	"--msg"

%token<strp>		yaD_IGNORE	"${ignored-bbox-sys}"
%token<strp>		yaD_DPI		"${dpi-sys}"

// <fl> is the fileline, abbreviated to shorten "$<fl>1" references
%token<fl>		'!'
%token<fl>		'#'
%token<fl>		'%'
%token<fl>		'&'
%token<fl>		'('
%token<fl>		')'
%token<fl>		'*'
%token<fl>		'+'
%token<fl>		','
%token<fl>		'-'
%token<fl>		'.'
%token<fl>		'/'
%token<fl>		':'
%token<fl>		';'
%token<fl>		'<'
%token<fl>		'='
%token<fl>		'>'
%token<fl>		'?'
%token<fl>		'@'
%token<fl>		'['
%token<fl>		']'
%token<fl>		'^'
%token<fl>		'{'
%token<fl>		'|'
%token<fl>		'}'
%token<fl>		'~'

// Specific keywords
// yKEYWORD means match "keyword"
// Other cases are yXX_KEYWORD where XX makes it unique,
// for example yP_ for punctuation based operators.
// Double underscores "yX__Y" means token X followed by Y,
// and "yX__ETC" means X folled by everything but Y(s).
%token<fl>		yALWAYS		"always"
%token<fl>		yALWAYS_FF	"always_ff"
%token<fl>		yALWAYS_COMB	"always_comb"
%token<fl>		yALWAYS_LATCH	"always_latch"
%token<fl>		yAND		"and"
%token<fl>		yASSERT		"assert"
%token<fl>		yASSIGN		"assign"
%token<fl>		yAUTOMATIC	"automatic"
%token<fl>		yBEGIN		"begin"
%token<fl>		yBIND		"bind"
%token<fl>		yBIT		"bit"
%token<fl>		yBREAK		"break"
%token<fl>		yBUF		"buf"
%token<fl>		yBUFIF0		"bufif0"
%token<fl>		yBUFIF1		"bufif1"
%token<fl>		yBYTE		"byte"
%token<fl>		yCASE		"case"
%token<fl>		yCASEX		"casex"
%token<fl>		yCASEZ		"casez"
%token<fl>		yCHANDLE	"chandle"
%token<fl>		yCLOCKING	"clocking"
%token<fl>		yCONST__ETC	"const"
%token<fl>		yCONST__LEX	"const-in-lex"
%token<fl>		yCMOS		"cmos"
%token<fl>		yCONTEXT	"context"
%token<fl>		yCONTINUE	"continue"
%token<fl>		yCOVER		"cover"
%token<fl>		yDEFAULT	"default"
%token<fl>		yDEFPARAM	"defparam"
%token<fl>		yDISABLE	"disable"
%token<fl>		yDO		"do"
%token<fl>		yEDGE		"edge"
%token<fl>		yELSE		"else"
%token<fl>		yEND		"end"
%token<fl>		yENDCASE	"endcase"
%token<fl>		yENDCLOCKING	"endclocking"
%token<fl>		yENDFUNCTION	"endfunction"
%token<fl>		yENDGENERATE	"endgenerate"
%token<fl>		yENDINTERFACE	"endinterface"
%token<fl>		yENDMODULE	"endmodule"
%token<fl>		yENDPACKAGE	"endpackage"
%token<fl>		yENDPRIMITIVE	"endprimitive"
%token<fl>		yENDPROGRAM	"endprogram"
%token<fl>		yENDPROPERTY	"endproperty"
%token<fl>		yENDSPECIFY	"endspecify"
%token<fl>		yENDTABLE	"endtable"
%token<fl>		yENDTASK	"endtask"
%token<fl>		yENUM		"enum"
%token<fl>		yEXPORT		"export"
%token<fl>		yFINAL		"final"
%token<fl>		yFOR		"for"
%token<fl>		yFOREVER	"forever"
%token<fl>		yFUNCTION	"function"
%token<fl>		yGENERATE	"generate"
%token<fl>		yGENVAR		"genvar"
%token<fl>		yGLOBAL__CLOCKING "global-then-clocking"
%token<fl>		yGLOBAL__LEX	"global-in-lex"
%token<fl>		yIF		"if"
%token<fl>		yIFF		"iff"
%token<fl>		yIMPORT		"import"
%token<fl>		yINITIAL	"initial"
%token<fl>		yINOUT		"inout"
%token<fl>		yINPUT		"input"
%token<fl>		yINSIDE		"inside"
%token<fl>		yINT		"int"
%token<fl>		yINTEGER	"integer"
%token<fl>		yINTERFACE	"interface"
%token<fl>		yLOCALPARAM	"localparam"
%token<fl>		yLOGIC		"logic"
%token<fl>		yLONGINT	"longint"
%token<fl>		yMODPORT	"modport"
%token<fl>		yMODULE		"module"
%token<fl>		yNAND		"nand"
%token<fl>		yNEGEDGE	"negedge"
%token<fl>		yNMOS		"nmos"
%token<fl>		yNOR		"nor"
%token<fl>		yNOT		"not"
%token<fl>		yNOTIF0		"notif0"
%token<fl>		yNOTIF1		"notif1"
%token<fl>		yOR		"or"
%token<fl>		yOUTPUT		"output"
%token<fl>		yPACKAGE	"package"
%token<fl>		yPACKED		"packed"
%token<fl>		yPARAMETER	"parameter"
%token<fl>		yPMOS		"pmos"
%token<fl>		yPOSEDGE	"posedge"
%token<fl>		yPRIMITIVE	"primitive"
%token<fl>		yPRIORITY	"priority"
%token<fl>		yPROGRAM	"program"
%token<fl>		yPROPERTY	"property"
%token<fl>		yPULLDOWN	"pulldown"
%token<fl>		yPULLUP		"pullup"
%token<fl>		yPURE		"pure"
%token<fl>		yRAND		"rand"
%token<fl>		yRANDC		"randc"
%token<fl>		yRCMOS		"rcmos"
%token<fl>		yREAL		"real"
%token<fl>		yREALTIME	"realtime"
%token<fl>		yREG		"reg"
%token<fl>		yREPEAT		"repeat"
%token<fl>		yRETURN		"return"
%token<fl>		yRNMOS		"rnmos"
%token<fl>		yRPMOS		"rpmos"
%token<fl>		yRTRAN		"rtran"
%token<fl>		yRTRANIF0	"rtranif0"
%token<fl>		yRTRANIF1	"rtranif1"
%token<fl>		ySCALARED	"scalared"
%token<fl>		ySHORTINT	"shortint"
%token<fl>		ySIGNED		"signed"
%token<fl>		ySPECIFY	"specify"
%token<fl>		ySPECPARAM	"specparam"
%token<fl>		ySTATIC		"static"
%token<fl>		ySTRING		"string"
%token<fl>		ySTRUCT		"struct"
%token<fl>		ySUPPLY0	"supply0"
%token<fl>		ySUPPLY1	"supply1"
%token<fl>		yTABLE		"table"
%token<fl>		yTASK		"task"
%token<fl>		yTIME		"time"
%token<fl>		yTIMEPRECISION	"timeprecision"
%token<fl>		yTIMEUNIT	"timeunit"
%token<fl>		yTRAN		"tran"
%token<fl>		yTRANIF0	"tranif0"
%token<fl>		yTRANIF1	"tranif1"
%token<fl>		yTRI		"tri"
%token<fl>		yTRI0		"tri0"
%token<fl>		yTRI1		"tri1"
%token<fl>		yTRUE		"true"
%token<fl>		yTYPEDEF	"typedef"
%token<fl>		yUNION		"union"
%token<fl>		yUNIQUE		"unique"
%token<fl>		yUNIQUE0	"unique0"
%token<fl>		yUNSIGNED	"unsigned"
%token<fl>		yVAR		"var"
%token<fl>		yVECTORED	"vectored"
%token<fl>		yVOID		"void"
%token<fl>		yWHILE		"while"
%token<fl>		yWIRE		"wire"
%token<fl>		yWREAL		"wreal"
%token<fl>		yXNOR		"xnor"
%token<fl>		yXOR		"xor"

%token<fl>		yD_BITS		"$bits"
%token<fl>		yD_BITSTOREAL	"$bitstoreal"
%token<fl>		yD_C		"$c"
%token<fl>		yD_CEIL		"$ceil"
%token<fl>		yD_CLOG2	"$clog2"
%token<fl>		yD_COUNTONES	"$countones"
%token<fl>		yD_DIMENSIONS	"$dimensions"
%token<fl>		yD_DISPLAY	"$display"
%token<fl>		yD_ERROR	"$error"
%token<fl>		yD_EXP		"$exp"
%token<fl>		yD_FATAL	"$fatal"
%token<fl>		yD_FCLOSE	"$fclose"
%token<fl>		yD_FDISPLAY	"$fdisplay"
%token<fl>		yD_FEOF		"$feof"
%token<fl>		yD_FFLUSH	"$fflush"
%token<fl>		yD_FGETC	"$fgetc"
%token<fl>		yD_FGETS	"$fgets"
%token<fl>		yD_FINISH	"$finish"
%token<fl>		yD_FLOOR	"$floor"
%token<fl>		yD_FOPEN	"$fopen"
%token<fl>		yD_FSCANF	"$fscanf"
%token<fl>		yD_FWRITE	"$fwrite"
%token<fl>		yD_HIGH		"$high"
%token<fl>		yD_INCREMENT	"$increment"
%token<fl>		yD_INFO		"$info"
%token<fl>		yD_ISUNKNOWN	"$isunknown"
%token<fl>		yD_ITOR		"$itor"
%token<fl>		yD_LEFT		"$left"
%token<fl>		yD_LN		"$ln"
%token<fl>		yD_LOG10	"$log10"
%token<fl>		yD_LOW		"$low"
%token<fl>		yD_ONEHOT	"$onehot"
%token<fl>		yD_ONEHOT0	"$onehot0"
%token<fl>		yD_POW		"$pow"
%token<fl>		yD_RANDOM	"$random"
%token<fl>		yD_READMEMB	"$readmemb"
%token<fl>		yD_READMEMH	"$readmemh"
%token<fl>		yD_REALTIME	"$realtime"
%token<fl>		yD_REALTOBITS	"$realtobits"
%token<fl>		yD_RIGHT	"$right"
%token<fl>		yD_RTOI		"$rtoi"
%token<fl>		yD_SFORMAT	"$sformat"
%token<fl>		yD_SIGNED	"$signed"
%token<fl>		yD_SIZE		"$size"
%token<fl>		yD_SQRT		"$sqrt"
%token<fl>		yD_SSCANF	"$sscanf"
%token<fl>		yD_STIME	"$stime"
%token<fl>		yD_STOP		"$stop"
%token<fl>		yD_SWRITE	"$swrite"
%token<fl>		yD_SYSTEM	"$system"
%token<fl>		yD_TESTPLUSARGS	"$test$plusargs"
%token<fl>		yD_TIME		"$time"
%token<fl>		yD_UNIT		"$unit"
%token<fl>		yD_UNPACKED_DIMENSIONS "$unpacked_dimensions"
%token<fl>		yD_UNSIGNED	"$unsigned"
%token<fl>		yD_VALUEPLUSARGS "$value$plusargs"
%token<fl>		yD_WARNING	"$warning"
%token<fl>		yD_WRITE	"$write"

%token<fl>		yVL_CLOCK		"/*verilator sc_clock*/"
%token<fl>		yVL_CLOCKER		"/*verilator clocker*/"
%token<fl>		yVL_NO_CLOCKER		"/*verilator no_clocker*/"
%token<fl>		yVL_CLOCK_ENABLE	"/*verilator clock_enable*/"
%token<fl>		yVL_COVERAGE_BLOCK_OFF	"/*verilator coverage_block_off*/"
%token<fl>		yVL_FULL_CASE		"/*verilator full_case*/"
%token<fl>		yVL_INLINE_MODULE	"/*verilator inline_module*/"
%token<fl>		yVL_ISOLATE_ASSIGNMENTS	"/*verilator isolate_assignments*/"
%token<fl>		yVL_NO_INLINE_MODULE	"/*verilator no_inline_module*/"
%token<fl>		yVL_NO_INLINE_TASK	"/*verilator no_inline_task*/"
%token<fl>		yVL_SC_BV		"/*verilator sc_bv*/"
%token<fl>		yVL_SFORMAT		"/*verilator sformat*/"
%token<fl>		yVL_PARALLEL_CASE	"/*verilator parallel_case*/"
%token<fl>		yVL_PUBLIC		"/*verilator public*/"
%token<fl>		yVL_PUBLIC_FLAT		"/*verilator public_flat*/"
%token<fl>		yVL_PUBLIC_FLAT_RD	"/*verilator public_flat_rd*/"
%token<fl>		yVL_PUBLIC_FLAT_RW	"/*verilator public_flat_rw*/"
%token<fl>		yVL_PUBLIC_MODULE	"/*verilator public_module*/"

%token<fl>		yP_TICK		"'"
%token<fl>		yP_TICKBRA	"'{"
%token<fl>		yP_OROR		"||"
%token<fl>		yP_ANDAND	"&&"
%token<fl>		yP_NOR		"~|"
%token<fl>		yP_XNOR		"^~"
%token<fl>		yP_NAND		"~&"
%token<fl>		yP_EQUAL	"=="
%token<fl>		yP_NOTEQUAL	"!="
%token<fl>		yP_CASEEQUAL	"==="
%token<fl>		yP_CASENOTEQUAL	"!=="
%token<fl>		yP_WILDEQUAL	"==?"
%token<fl>		yP_WILDNOTEQUAL	"!=?"
%token<fl>		yP_GTE		">="
%token<fl>		yP_LTE		"<="
%token<fl>		yP_LTE__IGNORE	"<=-ignored"	// Used when expr:<= means assignment
%token<fl>		yP_SLEFT	"<<"
%token<fl>		yP_SRIGHT	">>"
%token<fl>		yP_SSRIGHT	">>>"
%token<fl>		yP_POW		"**"

%token<fl>		yP_PLUSCOLON	"+:"
%token<fl>		yP_MINUSCOLON	"-:"
%token<fl>		yP_MINUSGT	"->"
%token<fl>		yP_MINUSGTGT	"->>"
%token<fl>		yP_EQGT		"=>"
%token<fl>		yP_ASTGT	"*>"
%token<fl>		yP_ANDANDAND	"&&&"
%token<fl>		yP_POUNDPOUND	"##"
%token<fl>		yP_DOTSTAR	".*"

%token<fl>		yP_ATAT		"@@"
%token<fl>		yP_COLONCOLON	"::"
%token<fl>		yP_COLONEQ	":="
%token<fl>		yP_COLONDIV	":/"
%token<fl>		yP_ORMINUSGT	"|->"
%token<fl>		yP_OREQGT	"|=>"
%token<fl>		yP_BRASTAR	"[*"
%token<fl>		yP_BRAEQ	"[="
%token<fl>		yP_BRAMINUSGT	"[->"

%token<fl>		yP_PLUSPLUS	"++"
%token<fl>		yP_MINUSMINUS	"--"
%token<fl>		yP_PLUSEQ	"+="
%token<fl>		yP_MINUSEQ	"-="
%token<fl>		yP_TIMESEQ	"*="
%token<fl>		yP_DIVEQ	"/="
%token<fl>		yP_MODEQ	"%="
%token<fl>		yP_ANDEQ	"&="
%token<fl>		yP_OREQ		"|="
%token<fl>		yP_XOREQ	"^="
%token<fl>		yP_SLEFTEQ	"<<="
%token<fl>		yP_SRIGHTEQ	">>="
%token<fl>		yP_SSRIGHTEQ	">>>="

%token<fl>	 	yP_LOGIFF

// [* is not a operator, as "[ * ]" is legal
// [= and [-> could be repitition operators, but to match [* we don't add them.
// '( is not a operator, as "' (" is legal

//********************
// PSL op precedence
%right	 	yP_MINUSGT  yP_LOGIFF
%right		yP_ORMINUSGT  yP_OREQGT

// Verilog op precedence
%right		'?' ':'
%left		yP_OROR
%left		yP_ANDAND
%left		'|' yP_NOR
%left		'^' yP_XNOR
%left		'&' yP_NAND
%left		yP_EQUAL yP_NOTEQUAL yP_CASEEQUAL yP_CASENOTEQUAL yP_WILDEQUAL yP_WILDNOTEQUAL
%left		'>' '<' yP_GTE yP_LTE yP_LTE__IGNORE yINSIDE
%left		yP_SLEFT yP_SRIGHT yP_SSRIGHT
%left		'+' '-'
%left		'*' '/' '%'
%left		yP_POW
%left		prUNARYARITH yP_MINUSMINUS yP_PLUSPLUS prREDUCTION prNEGATION
%left		'.'
// Not in IEEE, but need to avoid conflicts; TICK should bind tightly just lower than COLONCOLON
%left		yP_TICK
//%left		'(' ')' '[' ']' yP_COLONCOLON '.'

%nonassoc prLOWER_THAN_ELSE
%nonassoc yELSE

//BISONPRE_TYPES
//  Blank lines for type insertion
//  Blank lines for type insertion
//  Blank lines for type insertion
//  Blank lines for type insertion
//  Blank lines for type insertion
//  Blank lines for type insertion
//  Blank lines for type insertion
//  Blank lines for type insertion
//  Blank lines for type insertion
//  Blank lines for type insertion
//  Blank lines for type insertion
//  Blank lines for type insertion
//  Blank lines for type insertion
//  Blank lines for type insertion
//  Blank lines for type insertion
//  Blank lines for type insertion
//  Blank lines for type insertion
//  Blank lines for type insertion
//  Blank lines for type insertion
//  Blank lines for type insertion
//  Blank lines for type insertion
//  Blank lines for type insertion
//  Blank lines for type insertion
//  Blank lines for type insertion
//  Blank lines for type insertion
//  Blank lines for type insertion
//  Blank lines for type insertion
//  Blank lines for type insertion
//  Blank lines for type insertion
//  Blank lines for type insertion

%start source_text

%%
//**********************************************************************
// Files

source_text:			// ==IEEE: source_text
		/* empty */				{ }
	//			// timeunits_declaration moved into description:package_item
	|	descriptionList				{ }
	;

descriptionList:		// IEEE: part of source_text
		description				{ }
	|	descriptionList description		{ }
	;

description:			// ==IEEE: description
		module_declaration			{ }
	//			// udp_declaration moved into module_declaration
	|	interface_declaration			{ }
	|	program_declaration			{ }
	|	package_declaration			{ }
	|	package_item				{ if ($1) GRAMMARP->unitPackage($1->fileline())->addStmtp($1); }
       	|	bind_directive				{ if ($1) GRAMMARP->unitPackage($1->fileline())->addStmtp($1); }
	//	unsupported	// IEEE: config_declaration
	//			// Verilator only
	|	vltItem					{ }
	|	error					{ }
	;

timeunits_declaration<nodep>:	// ==IEEE: timeunits_declaration
		yTIMEUNIT       yaTIMENUM ';'		{ $$ = NULL; }
	|	yTIMEUNIT yaTIMENUM '/' yaTIMENUM ';'	{ $$ = NULL; }
	| 	yTIMEPRECISION  yaTIMENUM ';'		{ $$ = NULL; }
	;

//**********************************************************************
// Packages

package_declaration:		// ==IEEE: package_declaration
		packageFront package_itemListE yENDPACKAGE endLabelE
			{ $1->modTrace(GRAMMARP->allTracingOn($1->fileline()));  // Stash for implicit wires, etc
			  if ($2) $1->addStmtp($2);
			  SYMP->popScope($1);
			  GRAMMARP->endLabel($<fl>4,$1,$4); }
	;

packageFront<modulep>:
		yPACKAGE idAny ';'
			{ $$ = new AstPackage($1,*$2);
			  $$->inLibrary(true);  // packages are always libraries; don't want to make them a "top"
			  $$->modTrace(GRAMMARP->allTracingOn($$->fileline()));
			  PARSEP->rootp()->addModulep($$);
			  SYMP->pushNew($$); }
	;

package_itemListE<nodep>:	// IEEE: [{ package_item }]
		/* empty */				{ $$ = NULL; }
	|	package_itemList			{ $$ = $1; }
	;

package_itemList<nodep>:	// IEEE: { package_item }
		package_item				{ $$ = $1; }
	|	package_itemList package_item		{ $$ = $1->addNextNull($2); }
	;

package_item<nodep>:		// ==IEEE: package_item
		package_or_generate_item_declaration	{ $$ = $1; }
	//UNSUP	anonymous_program			{ $$ = $1; }
	//UNSUP	package_export_declaration		{ $$ = $1; }
	|	timeunits_declaration			{ $$ = $1; }
	;

package_or_generate_item_declaration<nodep>:	// ==IEEE: package_or_generate_item_declaration
		net_declaration				{ $$ = $1; }
	|	data_declaration			{ $$ = $1; }
	|	task_declaration			{ $$ = $1; }
	|	function_declaration			{ $$ = $1; }
	//UNSUP	checker_declaration			{ $$ = $1; }
	|	dpi_import_export			{ $$ = $1; }
	//UNSUP	extern_constraint_declaration		{ $$ = $1; }
	//UNSUP	class_declaration			{ $$ = $1; }
	//			// class_constructor_declaration is part of function_declaration
	|	local_parameter_declaration ';'		{ $$ = $1; }
	|	parameter_declaration ';'		{ $$ = $1; }
	//UNSUP	covergroup_declaration			{ $$ = $1; }
	//UNSUP	overload_declaration			{ $$ = $1; }
	//UNSUP	assertion_item_declaration		{ $$ = $1; }
	|	';'					{ $$ = NULL; }
	;

package_import_declarationList<nodep>:
		package_import_declaration		{ $$ = $1; }
	|	package_import_declarationList package_import_declaration { $$ = $1->addNextNull($2); }
	;

package_import_declaration<nodep>:	// ==IEEE: package_import_declaration
		yIMPORT package_import_itemList ';'	{ $$ = $2; }
	;

package_import_itemList<nodep>:
		package_import_item			{ $$ = $1; }
	|	package_import_itemList ',' package_import_item { $$ = $1->addNextNull($3); }
	;

package_import_item<nodep>:	// ==IEEE: package_import_item
		yaID__aPACKAGE yP_COLONCOLON package_import_itemObj
			{ $$ = new AstPackageImport($<fl>1, $<scp>1->castPackage(), *$3);
			  SYMP->import($<scp>1,*$3); }
	;

package_import_itemObj<strp>:	// IEEE: part of package_import_item
		idAny					{ $<fl>$=$<fl>1; $$=$1; }
	|	'*'					{ $<fl>$=$<fl>1; static string star="*"; $$=&star; }
	;

//**********************************************************************
// Module headers

module_declaration:		// ==IEEE: module_declaration
	//			// timeunits_declaration instead in module_item
	//			// IEEE: module_nonansi_header + module_ansi_header
		modFront importsAndParametersE portsStarE ';'
			module_itemListE yENDMODULE endLabelE
			{ $1->modTrace(GRAMMARP->allTracingOn($1->fileline()));  // Stash for implicit wires, etc
			  if ($2) $1->addStmtp($2); if ($3) $1->addStmtp($3);
			  if ($5) $1->addStmtp($5);
			  SYMP->popScope($1);
			  GRAMMARP->endLabel($<fl>7,$1,$7); }
	|	udpFront parameter_port_listE portsStarE ';'
			module_itemListE yENDPRIMITIVE endLabelE
			{ $1->modTrace(false);  // Stash for implicit wires, etc
			  if ($2) $1->addStmtp($2); if ($3) $1->addStmtp($3);
			  if ($5) $1->addStmtp($5);
			  GRAMMARP->m_tracingParse = true;
			  SYMP->popScope($1);
			  GRAMMARP->endLabel($<fl>7,$1,$7); }
	//
	//UNSUP	yEXTERN modFront parameter_port_listE portsStarE ';'
	//UNSUP		{ UNSUP }
	;

modFront<modulep>:
	//			// General note: all *Front functions must call symPushNew before
	//			// any formal arguments, as the arguments must land in the new scope.
		yMODULE lifetimeE idAny
			{ $$ = new AstModule($1,*$3); $$->inLibrary(PARSEP->inLibrary()||PARSEP->inCellDefine());
			  $$->modTrace(GRAMMARP->allTracingOn($$->fileline()));
			  PARSEP->rootp()->addModulep($$);
			  SYMP->pushNew($$); }
	;

importsAndParametersE<nodep>:	// IEEE: common part of module_declaration, interface_declaration, program_declaration
	//			// { package_import_declaration } [ parameter_port_list ]
		parameter_port_listE			{ $$ = $1; }
	|	package_import_declarationList parameter_port_listE	{ $$ = $1->addNextNull($2); }
	;

udpFront<modulep>:
		yPRIMITIVE lifetimeE idAny
			{ $$ = new AstPrimitive($1,*$3); $$->inLibrary(true);
			  $$->modTrace(false);
			  $$->addStmtp(new AstPragma($1,AstPragmaType::INLINE_MODULE));
			  GRAMMARP->m_tracingParse = false;
			  PARSEP->rootp()->addModulep($$);
			  SYMP->pushNew($$); }
	;

parameter_value_assignmentE<pinp>:	// IEEE: [ parameter_value_assignment ]
		/* empty */				{ $$ = NULL; }
	|	'#' '(' cellpinList ')'			{ $$ = $3; }
	//			// Parentheses are optional around a single parameter
	|	'#' yaINTNUM				{ $$ = new AstPin($1,1,"",new AstConst($1,*$2)); }
	|	'#' yaFLOATNUM				{ $$ = new AstPin($1,1,"",new AstConst($1,AstConst::Unsized32(),(int)(($2<0)?($2-0.5):($2+0.5)))); }
	|	'#' idClassSel				{ $$ = new AstPin($1,1,"",$2); }
	//			// Not needed in Verilator:
	//			// Side effect of combining *_instantiations
	//			// '#' delay_value	{ UNSUP }
	;

parameter_port_listE<nodep>:	// IEEE: parameter_port_list + empty == parameter_value_assignment
		/* empty */				{ $$ = NULL; }
	|	'#' '(' ')'				{ $$ = NULL; }
	//			// IEEE: '#' '(' list_of_param_assignments { ',' parameter_port_declaration } ')'
	//			// IEEE: '#' '(' parameter_port_declaration { ',' parameter_port_declaration } ')'
	//			// Can't just do that as "," conflicts with between vars and between stmts, so
	//			// split into pre-comma and post-comma parts
	|	'#' '(' {VARRESET_LIST(GPARAM);} paramPortDeclOrArgList ')'	{ $$ = $4; VARRESET_NONLIST(UNKNOWN); }
	//			// Note legal to start with "a=b" with no parameter statement
	;

paramPortDeclOrArgList<nodep>:	// IEEE: list_of_param_assignments + { parameter_port_declaration }
		paramPortDeclOrArg				{ $$ = $1; }
	|	paramPortDeclOrArgList ',' paramPortDeclOrArg	{ $$ = $1->addNext($3); }
	;

paramPortDeclOrArg<nodep>:	// IEEE: param_assignment + parameter_port_declaration
	//			// We combine the two as we can't tell which follows a comma
		parameter_port_declarationFrontE param_assignment	{ $$ = $2; }
	;

portsStarE<nodep>:		// IEEE: .* + list_of_ports + list_of_port_declarations + empty
		/* empty */					{ $$ = NULL; }
	|	'(' ')'						{ $$ = NULL; }
	//			// .* expanded from module_declaration
	//UNSUP	'(' yP_DOTSTAR ')'				{ UNSUP }
	|	'(' {VARRESET_LIST(PORT);} list_of_ports ')'	{ $$ = $3; VARRESET_NONLIST(UNKNOWN); }
	;

list_of_ports<nodep>:		// IEEE: list_of_ports + list_of_port_declarations
		port					{ $$ = $1; }
	|	list_of_ports ',' port			{ $$ = $1->addNextNull($3); }
	;

port<nodep>:			// ==IEEE: port
	//			// Though not type for interfaces, we factor out the port direction and type
	//			// so we can simply handle it in one place
	//
	//			// IEEE: interface_port_header port_identifier { unpacked_dimension }
	//			// Expanded interface_port_header
	//			// We use instantCb here because the non-port form looks just like a module instantiation
		portDirNetE id/*interface*/                      portSig variable_dimensionListE sigAttrListE
			{ $$ = $3; VARDECL(AstVarType::IFACEREF); VARIO(UNKNOWN);
			  VARDTYPE(new AstIfaceRefDType($<fl>2,"",*$2));
			  $$->addNextNull(VARDONEP($$,$4,$5)); }
	|	portDirNetE id/*interface*/ '.' idAny/*modport*/ portSig rangeListE sigAttrListE
			{ $$ = $5; VARDECL(AstVarType::IFACEREF); VARIO(UNKNOWN);
			  VARDTYPE(new AstIfaceRefDType($<fl>2,"",*$2,*$4));
			  $$->addNextNull(VARDONEP($$,$6,$7)); }
	|	portDirNetE yINTERFACE                           portSig rangeListE sigAttrListE
			{ $<fl>2->v3error("Unsupported: virtual interfaces"); $$=NULL; }
	|	portDirNetE yINTERFACE      '.' idAny/*modport*/ portSig rangeListE sigAttrListE
			{ $<fl>2->v3error("Unsupported: virtual interfaces"); $$=NULL; }
	//
	//			// IEEE: ansi_port_declaration, with [port_direction] removed
	//			//   IEEE: [ net_port_header | interface_port_header ] port_identifier { unpacked_dimension } [ '=' constant_expression ]
	//			//   IEEE: [ net_port_header | variable_port_header ] '.' port_identifier '(' [ expression ] ')'
	//			//   IEEE: [ variable_port_header ] port_identifier { variable_dimension } [ '=' constant_expression ]
	//			//   Substitute net_port_header = [ port_direction ] net_port_type
	//			//   Substitute variable_port_header = [ port_direction ] variable_port_type
	//			//   Substitute net_port_type = [ net_type ] data_type_or_implicit
	//			//   Substitute variable_port_type = var_data_type
	//			//   Substitute var_data_type = data_type | yVAR data_type_or_implicit
	//			//     [ [ port_direction ] net_port_type | interface_port_header            ] port_identifier { unpacked_dimension }
	//			//     [ [ port_direction ] var_data_type                                    ] port_identifier variable_dimensionListE [ '=' constant_expression ]
	//			//     [ [ port_direction ] net_port_type | [ port_direction ] var_data_type ] '.' port_identifier '(' [ expression ] ')'
	//
	//			// Remove optional '[...] id' is in portAssignment
	//			// Remove optional '[port_direction]' is in port
	//			//     net_port_type | interface_port_header            port_identifier { unpacked_dimension }
	//			//     net_port_type | interface_port_header            port_identifier { unpacked_dimension }
	//			//     var_data_type                                    port_identifier variable_dimensionListE [ '=' constExpr ]
	//			//     net_port_type | [ port_direction ] var_data_type '.' port_identifier '(' [ expr ] ')'
	//			// Expand implicit_type
	//
	//			// variable_dimensionListE instead of rangeListE to avoid conflicts
	//
	//			// Note implicit rules looks just line declaring additional followon port
	//			// No VARDECL("port") for implicit, as we don't want to declare variables for them
	//UNSUP	portDirNetE data_type	       '.' portSig '(' portAssignExprE ')' sigAttrListE
	//UNSUP		{ UNSUP }
	//UNSUP	portDirNetE yVAR data_type     '.' portSig '(' portAssignExprE ')' sigAttrListE
	//UNSUP		{ UNSUP }
	//UNSUP	portDirNetE yVAR implicit_type '.' portSig '(' portAssignExprE ')' sigAttrListE
	//UNSUP		{ UNSUP }
	//UNSUP	portDirNetE signingE rangeList '.' portSig '(' portAssignExprE ')' sigAttrListE
	//UNSUP		{ UNSUP }
	//UNSUP	portDirNetE /*implicit*/       '.' portSig '(' portAssignExprE ')' sigAttrListE
	//UNSUP		{ UNSUP }
	//
	|	portDirNetE data_type           portSig variable_dimensionListE sigAttrListE
			{ $$=$3; VARDTYPE($2); $$->addNextNull(VARDONEP($$,$4,$5)); }
	|	portDirNetE yVAR data_type      portSig variable_dimensionListE sigAttrListE
			{ $$=$4; VARDTYPE($3); $$->addNextNull(VARDONEP($$,$5,$6)); }
	|	portDirNetE yVAR implicit_typeE portSig variable_dimensionListE sigAttrListE
			{ $$=$4; VARDTYPE($3); $$->addNextNull(VARDONEP($$,$5,$6)); }
	|	portDirNetE signingE rangeList  portSig variable_dimensionListE sigAttrListE
			{ $$=$4; VARDTYPE(GRAMMARP->addRange(new AstBasicDType($3->fileline(), LOGIC_IMPLICIT, $2), $3,true)); $$->addNextNull(VARDONEP($$,$5,$6)); }
	|	portDirNetE /*implicit*/        portSig variable_dimensionListE sigAttrListE
			{ $$=$2; /*VARDTYPE-same*/ $$->addNextNull(VARDONEP($$,$3,$4)); }
	//
	|	portDirNetE data_type           portSig variable_dimensionListE sigAttrListE '=' constExpr
			{ $$=$3; VARDTYPE($2); AstVar* vp=VARDONEP($$,$4,$5); $$->addNextNull(vp); vp->valuep($7); }
	|	portDirNetE yVAR data_type      portSig variable_dimensionListE sigAttrListE '=' constExpr
			{ $$=$4; VARDTYPE($3); AstVar* vp=VARDONEP($$,$5,$6); $$->addNextNull(vp); vp->valuep($8); }
	|	portDirNetE yVAR implicit_typeE portSig variable_dimensionListE sigAttrListE '=' constExpr
			{ $$=$4; VARDTYPE($3); AstVar* vp=VARDONEP($$,$5,$6); $$->addNextNull(vp); vp->valuep($8); }
	|	portDirNetE /*implicit*/        portSig variable_dimensionListE sigAttrListE '=' constExpr
			{ $$=$2; /*VARDTYPE-same*/ AstVar* vp=VARDONEP($$,$3,$4); $$->addNextNull(vp); vp->valuep($6); }
 	;

portDirNetE:			// IEEE: part of port, optional net type and/or direction
		/* empty */				{ }
	//			// Per spec, if direction given default the nettype.
	//			// The higher level rule may override this VARDTYPE with one later in the parse.
	|	port_direction					{ VARDECL(PORT); VARDTYPE(NULL/*default_nettype*/); }
	|	port_direction { VARDECL(PORT); } net_type	{ VARDTYPE(NULL/*default_nettype*/); } // net_type calls VARNET
	|	net_type					{ } // net_type calls VARNET
 	;

port_declNetE:			// IEEE: part of port_declaration, optional net type
		/* empty */				{ }
	|	net_type				{ } // net_type calls VARNET
 	;

portSig<nodep>:
		id/*port*/				{ $$ = new AstPort($<fl>1,PINNUMINC(),*$1); }
	|	idSVKwd					{ $$ = new AstPort($<fl>1,PINNUMINC(),*$1); }
 	;

//**********************************************************************
// Interface headers

interface_declaration:		// IEEE: interface_declaration + interface_nonansi_header + interface_ansi_header:
	//			// timeunits_delcarationE is instead in interface_item
		intFront parameter_port_listE portsStarE ';'
			interface_itemListE yENDINTERFACE endLabelE
			{ if ($2) $1->addStmtp($2);
			  if ($3) $1->addStmtp($3);
			  if ($5) $1->addStmtp($5);
			  SYMP->popScope($1); }
	//UNSUP yEXTERN intFront parameter_port_listE portsStarE ';'	{ }
	;

intFront<modulep>:
		yINTERFACE lifetimeE idAny/*new_interface*/
			{ $$ = new AstIface($1,*$3);
			  $$->inLibrary(true);
			  PARSEP->rootp()->addModulep($$);
			  SYMP->pushNew($$); }
	;

interface_itemListE<nodep>:
		/* empty */				{ $$ = NULL; }
	|	interface_itemList			{ $$ = $1; }
	;

interface_itemList<nodep>:
		interface_item				{ $$ = $1; }
	|	interface_itemList interface_item	{ $$ = $1->addNextNull($2); }
	;

interface_item<nodep>:		// IEEE: interface_item + non_port_interface_item
		port_declaration ';'			{ $$ = $1; }
	//			// IEEE: non_port_interface_item
	//			// IEEE: generate_region
	|	interface_generate_region		{ $$ = $1; }
	|	interface_or_generate_item		{ $$ = $1; }
	//UNSUP	program_declaration			{ $$ = $1; }
	//UNSUP	interface_declaration			{ $$ = $1; }
	|	timeunits_declaration			{ $$ = $1; }
	//			// See note in interface_or_generate item
	|	module_common_item			{ $$ = $1; }
	;

interface_generate_region<nodep>:		// ==IEEE: generate_region
		yGENERATE interface_itemList yENDGENERATE	{ $$ = new AstGenerate($1, $2); }
	|	yGENERATE yENDGENERATE			{ $$ = NULL; }
	;

interface_or_generate_item<nodep>:  // ==IEEE: interface_or_generate_item
	//			    // module_common_item in interface_item, as otherwise duplicated
	//			    // with module_or_generate_item's module_common_item
		modport_declaration			{ $$ = $1; }
	//UNSUP	extern_tf_declaration			{ $$ = $1; }
	;

//**********************************************************************
// Program headers

program_declaration:		// IEEE: program_declaration + program_nonansi_header + program_ansi_header:
	//			// timeunits_delcarationE is instead in program_item
		pgmFront parameter_port_listE portsStarE ';'
			program_itemListE yENDPROGRAM endLabelE
			{ $1->modTrace(GRAMMARP->allTracingOn($1->fileline()));  // Stash for implicit wires, etc
			  if ($2) $1->addStmtp($2); if ($3) $1->addStmtp($3);
			  if ($5) $1->addStmtp($5);
			  SYMP->popScope($1);
			  GRAMMARP->endLabel($<fl>7,$1,$7); }
	//UNSUP	yEXTERN	pgmFront parameter_port_listE portsStarE ';'
	//UNSUP		{ PARSEP->symPopScope(VAstType::PROGRAM); }
	;

pgmFront<modulep>:
		yPROGRAM lifetimeE idAny/*new_program*/
			{ $$ = new AstModule($1,*$3); $$->inLibrary(PARSEP->inLibrary()||PARSEP->inCellDefine());
			  $$->modTrace(GRAMMARP->allTracingOn($$->fileline()));
			  PARSEP->rootp()->addModulep($$);
			  SYMP->pushNew($$); }
	;

program_itemListE<nodep>:	// ==IEEE: [{ program_item }]
		/* empty */				{ $$ = NULL; }
	|	program_itemList			{ $$ = $1; }
	;

program_itemList<nodep>:	// ==IEEE: { program_item }
		program_item				{ $$ = $1; }
	|	program_itemList program_item		{ $$ = $1->addNextNull($2); }
	;

program_item<nodep>:		// ==IEEE: program_item
		port_declaration ';'			{ $$ = $1; }
	|	non_port_program_item			{ $$ = $1; }
	;

non_port_program_item<nodep>:	// ==IEEE: non_port_program_item
		continuous_assign			{ $$ = $1; }
	|	module_or_generate_item_declaration	{ $$ = $1; }
	|	initial_construct			{ $$ = $1; }
	|	final_construct				{ $$ = $1; }
	|	concurrent_assertion_item		{ $$ = $1; }
	|	timeunits_declaration			{ $$ = $1; }
	|	program_generate_item			{ $$ = $1; }
	;

program_generate_item<nodep>:		// ==IEEE: program_generate_item
		loop_generate_construct			{ $$ = $1; }
	|	conditional_generate_construct		{ $$ = $1; }
	|	generate_region				{ $$ = $1; }
	//UNSUP	elaboration_system_task			{ $$ = $1; }
	;

modport_declaration<nodep>:		// ==IEEE: modport_declaration
		yMODPORT modport_itemList ';'		{ $$ = $2; }
	;

modport_itemList<nodep>:		// IEEE: part of modport_declaration
		modport_item				{ $$ = $1; }
	|	modport_itemList ',' modport_item	{ $$ = $1->addNextNull($3); }
	;

modport_item<nodep>:			// ==IEEE: modport_item
		id/*new-modport*/ '(' modportPortsDeclList ')'		{ $$ = new AstModport($2,*$1,$3); }
	;

modportPortsDeclList<nodep>:
		modportPortsDecl			    { $$ = $1; }
	|	modportPortsDeclList ',' modportPortsDecl   { $$ = $1->addNextNull($3); }
	;

// IEEE: modport_ports_declaration  + modport_simple_ports_declaration
//	+ (modport_tf_ports_declaration+import_export) + modport_clocking_declaration
// We've expanded the lists each take to instead just have standalone ID ports.
// We track the type as with the V2k series of defines, then create as each ID is seen.
modportPortsDecl<nodep>:
	//			// IEEE: modport_simple_ports_declaration
		port_direction modportSimplePort	{ $$ = new AstModportVarRef($<fl>1,*$2,GRAMMARP->m_varIO); }
	//			// IEEE: modport_clocking_declaration
	|	yCLOCKING idAny/*clocking_identifier*/	{ $1->v3error("Unsupported: Modport clocking"); }
	//			// IEEE: yIMPORT modport_tf_port
	//			// IEEE: yEXPORT modport_tf_port
	//			// modport_tf_port expanded here
	|	yIMPORT id/*tf_identifier*/		{ $$ = new AstModportFTaskRef($<fl>1,*$2,false); }
	|	yEXPORT id/*tf_identifier*/		{ $$ = new AstModportFTaskRef($<fl>1,*$2,true); }
	|	yIMPORT method_prototype		{ $1->v3error("Unsupported: Modport import with prototype"); }
	|	yEXPORT method_prototype		{ $1->v3error("Unsupported: Modport export with prototype"); }
	// Continuations of above after a comma.
	//			// IEEE: modport_simple_ports_declaration
	|	modportSimplePort			{ $$ = new AstModportVarRef($<fl>1,*$1,AstVarType::INOUT); }
	;

modportSimplePort<strp>:	// IEEE: modport_simple_port or modport_tf_port, depending what keyword was earlier
		id					{ $$ = $1; }
	//UNSUP	'.' idAny '(' ')'			{ }
	//UNSUP	'.' idAny '(' expr ')'			{ }
	;

//************************************************
// Variable Declarations

genvar_declaration<nodep>:	// ==IEEE: genvar_declaration
		yGENVAR list_of_genvar_identifiers ';'	{ $$ = $2; }
	;

list_of_genvar_identifiers<nodep>:	// IEEE: list_of_genvar_identifiers (for declaration)
		genvar_identifierDecl			{ $$ = $1; }
	|	list_of_genvar_identifiers ',' genvar_identifierDecl	{ $$ = $1->addNext($3); }
	;

genvar_identifierDecl<varp>:		// IEEE: genvar_identifier (for declaration)
		id/*new-genvar_identifier*/ sigAttrListE
			{ VARRESET_NONLIST(GENVAR); VARDTYPE(new AstBasicDType($<fl>1,AstBasicDTypeKwd::INTEGER));
			  $$ = VARDONEA($<fl>1, *$1, NULL, $2); }
	;

local_parameter_declaration<nodep>:	// IEEE: local_parameter_declaration
	//			// See notes in parameter_declaration
		local_parameter_declarationFront list_of_param_assignments	{ $$ = $2; }
	;

parameter_declaration<nodep>:	// IEEE: parameter_declaration
	//			// IEEE: yPARAMETER yTYPE list_of_type_assignments ';'
	//			// Instead of list_of_type_assignments
	//			// we use list_of_param_assignments because for port handling
	//			// it already must accept types, so simpler to have code only one place
		parameter_declarationFront list_of_param_assignments	{ $$ = $2; }
	;

local_parameter_declarationFront: // IEEE: local_parameter_declaration w/o assignment
		varLParamReset implicit_typeE 		{ /*VARRESET-in-varLParam*/ VARDTYPE($2); }
	|	varLParamReset data_type		{ /*VARRESET-in-varLParam*/ VARDTYPE($2); }
	//UNSUP	varLParamReset yTYPE			{ /*VARRESET-in-varLParam*/ VARDTYPE($2); }
	;

parameter_declarationFront:	// IEEE: parameter_declaration w/o assignment
		varGParamReset implicit_typeE 		{ /*VARRESET-in-varGParam*/ VARDTYPE($2); }
	|	varGParamReset data_type		{ /*VARRESET-in-varGParam*/ VARDTYPE($2); }
	//UNSUP	varGParamReset yTYPE			{ /*VARRESET-in-varGParam*/ VARDTYPE($2); }
	;

parameter_port_declarationFrontE: // IEEE: parameter_port_declaration w/o assignment
	//			// IEEE: parameter_declaration (minus assignment)
		varGParamReset implicit_typeE 		{ /*VARRESET-in-varGParam*/ VARDTYPE($2); }
	|	varGParamReset data_type		{ /*VARRESET-in-varGParam*/ VARDTYPE($2); }
	|	implicit_typeE 				{ /*VARRESET-in-varGParam*/ VARDTYPE($1); }
	|	data_type				{ /*VARRESET-in-varGParam*/ VARDTYPE($1); }
	//UNSUP	varGParamReset yTYPE			{ /*VARRESET-in-varGParam*/ VARDTYPE($2); }
	//UNSUP	data_type				{ VARDTYPE($1); }
	//UNSUP	yTYPE 					{ VARDTYPE($1); }
	;

net_declaration<nodep>:		// IEEE: net_declaration - excluding implict
		net_declarationFront netSigList ';'	{ $$ = $2; }
	;

net_declarationFront:		// IEEE: beginning of net_declaration
		net_declRESET net_type   strengthSpecE net_scalaredE net_dataType { VARDTYPE($5); }
	;

net_declRESET:
		/* empty */ 				{ VARRESET_NONLIST(UNKNOWN); }
	;

net_scalaredE:
		/* empty */ 				{ }
	//UNSUP: ySCALARED/yVECTORED ignored
	|	ySCALARED			 	{ }
	|	yVECTORED				{ }
	;

net_dataType<dtypep>:
	//			// If there's a SV data type there shouldn't be a delay on this wire
	//			// Otherwise #(...) can't be determined to be a delay or parameters
	//			// Submit this as a footnote to the committee
		var_data_type	 			{ $$ = $1; }
	|	signingE rangeList delayE 		{ $$ = GRAMMARP->addRange(new AstBasicDType($2->fileline(), LOGIC, $1),$2,true); }  // not implicit
	|	signing					{ $$ = new AstBasicDType($<fl>1, LOGIC, $1); }  // not implicit
	|	/*implicit*/ delayE 			{ $$ = new AstBasicDType(CRELINE(), LOGIC); }  // not implicit
	;

net_type:			// ==IEEE: net_type
		ySUPPLY0				{ VARDECL(SUPPLY0); }
	|	ySUPPLY1				{ VARDECL(SUPPLY1); }
	|	yTRI 					{ VARDECL(TRIWIRE); }
	|	yTRI0 					{ VARDECL(TRI0); }
	|	yTRI1 					{ VARDECL(TRI1); }
	//UNSUP	yTRIAND 				{ VARDECL(TRIAND); }
	//UNSUP	yTRIOR 					{ VARDECL(TRIOR); }
	//UNSUP	yTRIREG 				{ VARDECL(TRIREG); }
	//UNSUP	yWAND 					{ VARDECL(WAND); }
	|	yWIRE 					{ VARDECL(WIRE); }
	//UNSUP	yWOR 					{ VARDECL(WOR); }
	;

varGParamReset:
		yPARAMETER				{ VARRESET_NONLIST(GPARAM); }
	;

varLParamReset:
		yLOCALPARAM				{ VARRESET_NONLIST(LPARAM); }
	;

port_direction:			// ==IEEE: port_direction + tf_port_direction
	//			// IEEE 19.8 just "input" FIRST forces type to wire - we'll ignore that here
		yINPUT					{ VARIO(INPUT); }
	|	yOUTPUT					{ VARIO(OUTPUT); }
	|	yINOUT					{ VARIO(INOUT); }
	//UNSUP	yREF					{ VARIO(REF); }
	//UNSUP	yCONST__REF yREF			{ VARIO(CONSTREF); }
	;

port_directionReset:		// IEEE: port_direction that starts a port_declaraiton
	//			// Used only for declarations outside the port list
		yINPUT					{ VARRESET_NONLIST(UNKNOWN); VARIO(INPUT); }
	|	yOUTPUT					{ VARRESET_NONLIST(UNKNOWN); VARIO(OUTPUT); }
	|	yINOUT					{ VARRESET_NONLIST(UNKNOWN); VARIO(INOUT); }
	//UNSUP	yREF					{ VARRESET_NONLIST(UNKNOWN); VARIO(REF); }
	//UNSUP	yCONST__REF yREF			{ VARRESET_NONLIST(UNKNOWN); VARIO(CONSTREF); }
	;

port_declaration<nodep>:	// ==IEEE: port_declaration
	//			// Used inside block; followed by ';'
	//			// SIMILAR to tf_port_declaration
	//
	//			// IEEE: inout_declaration
	//			// IEEE: input_declaration
	//			// IEEE: output_declaration
	//			// IEEE: ref_declaration
		port_directionReset port_declNetE data_type          { VARDTYPE($3); }
			list_of_variable_decl_assignments			{ $$ = $5; }
	|	port_directionReset port_declNetE yVAR data_type     { VARDTYPE($4); }
			list_of_variable_decl_assignments			{ $$ = $6; }
	|	port_directionReset port_declNetE yVAR implicit_typeE { VARDTYPE($4); }
			list_of_variable_decl_assignments			{ $$ = $6; }
	|	port_directionReset port_declNetE signingE rangeList { VARDTYPE(GRAMMARP->addRange(new AstBasicDType($4->fileline(), LOGIC_IMPLICIT, $3),$4,true)); }
			list_of_variable_decl_assignments			{ $$ = $6; }
	|	port_directionReset port_declNetE signing	     { VARDTYPE(new AstBasicDType($<fl>3, LOGIC_IMPLICIT, $3)); }
			list_of_variable_decl_assignments			{ $$ = $5; }
	|	port_directionReset port_declNetE /*implicit*/       { VARDTYPE(NULL);/*default_nettype*/}
			list_of_variable_decl_assignments			{ $$ = $4; }
	//			// IEEE: interface_declaration
	//			// Looks just like variable declaration unless has a period
	//			// See etcInst
	;

tf_port_declaration<nodep>:	// ==IEEE: tf_port_declaration
	//			// Used inside function; followed by ';'
	//			// SIMILAR to port_declaration
	//
		port_directionReset      data_type      { VARDTYPE($2); }  list_of_tf_variable_identifiers ';'	{ $$ = $4; }
	|	port_directionReset      implicit_typeE { VARDTYPE($2); }  list_of_tf_variable_identifiers ';'	{ $$ = $4; }
	|	port_directionReset yVAR data_type      { VARDTYPE($3); }  list_of_tf_variable_identifiers ';'	{ $$ = $5; }
	|	port_directionReset yVAR implicit_typeE { VARDTYPE($3); }  list_of_tf_variable_identifiers ';'	{ $$ = $5; }
	;

integer_atom_type<bdtypep>:	// ==IEEE: integer_atom_type
		yBYTE					{ $$ = new AstBasicDType($1,AstBasicDTypeKwd::BYTE); }
	|	ySHORTINT				{ $$ = new AstBasicDType($1,AstBasicDTypeKwd::SHORTINT); }
	|	yINT					{ $$ = new AstBasicDType($1,AstBasicDTypeKwd::INT); }
	|	yLONGINT				{ $$ = new AstBasicDType($1,AstBasicDTypeKwd::LONGINT); }
	|	yINTEGER				{ $$ = new AstBasicDType($1,AstBasicDTypeKwd::INTEGER); }
	|	yTIME					{ $$ = new AstBasicDType($1,AstBasicDTypeKwd::TIME); }
	;

integer_vector_type<bdtypep>:	// ==IEEE: integer_atom_type
		yBIT					{ $$ = new AstBasicDType($1,AstBasicDTypeKwd::BIT); }
	|	yLOGIC					{ $$ = new AstBasicDType($1,AstBasicDTypeKwd::LOGIC); }
	|	yREG					{ $$ = new AstBasicDType($1,AstBasicDTypeKwd::LOGIC); } // logic==reg
	;

non_integer_type<bdtypep>:	// ==IEEE: non_integer_type
		yREAL					{ $$ = new AstBasicDType($1,AstBasicDTypeKwd::DOUBLE); }
	|	yREALTIME				{ $$ = new AstBasicDType($1,AstBasicDTypeKwd::DOUBLE); }
	//UNSUP	ySHORTREAL				{ $$ = new AstBasicDType($1,AstBasicDTypeKwd::FLOAT); }
	//			// VAMS - somewhat hackish
	|	yWREAL 					{ $$ = new AstBasicDType($1,AstBasicDTypeKwd::DOUBLE); VARDECL(WIRE); }
	;

signingE<signstate>:		// IEEE: signing - plus empty
		/*empty*/ 				{ $$ = signedst_NOSIGN; }
	|	signing					{ $$ = $1; }
	;

signing<signstate>:		// ==IEEE: signing
		ySIGNED					{ $<fl>$ = $<fl>1; $$ = signedst_SIGNED; }
	|	yUNSIGNED				{ $<fl>$ = $<fl>1; $$ = signedst_UNSIGNED; }
	;

//************************************************
// Data Types

casting_type<dtypep>:		// IEEE: casting_type
		simple_type				{ $$ = $1; }
	//			// IEEE: constant_primary
	//			// In expr:cast this is expanded to just "expr"
	//
	//			// IEEE: signing
	//See where casting_type used
	//^^	ySIGNED					{ $$ = new AstSigned($1,$3); }
	//^^	yUNSIGNED				{ $$ = new AstUnsigned($1,$3); }
	//UNSUP	ySTRING					{ $$ = $1; }
	//UNSUP	yCONST__ETC/*then `*/			{ $$ = $1; }
	;

simple_type<dtypep>:		// ==IEEE: simple_type
	//			// IEEE: integer_type
		integer_atom_type			{ $$ = $1; }
	|	integer_vector_type			{ $$ = $1; }
	|	non_integer_type			{ $$ = $1; }
	//			// IEEE: ps_type_identifier
	//			// IEEE: ps_parameter_identifier (presumably a PARAMETER TYPE)
	|	ps_type					{ $$ = $1; }
	//			// { generate_block_identifer ... } '.'
	//			// Need to determine if generate_block_identifier can be lex-detected
	;

data_type<dtypep>:		// ==IEEE: data_type
	//			// This expansion also replicated elsewhere, IE data_type__AndID
		data_typeNoRef				{ $$ = $1; }
	//			// IEEE: [ class_scope | package_scope ] type_identifier { packed_dimension }
	|	ps_type  packed_dimensionListE		{ $$ = GRAMMARP->createArray($1,$2,true); }
	//UNSUP	class_scope_type packed_dimensionListE	{ UNSUP }
	//			// IEEE: class_type
	//UNSUP	class_typeWithoutId			{ $$ = $1; }
	//			// IEEE: ps_covergroup_identifier
	//			// we put covergroups under ps_type, so can ignore this
	;

data_typeBasic<dtypep>:		// IEEE: part of data_type
		integer_vector_type signingE rangeListE	{ $1->setSignedState($2); $$ = GRAMMARP->addRange($1,$3,true); }
	|	integer_atom_type signingE		{ $1->setSignedState($2); $$ = $1; }
	|	non_integer_type			{ $$ = $1; }
	;

data_typeNoRef<dtypep>:		// ==IEEE: data_type, excluding class_type etc references
		data_typeBasic				{ $$ = $1; }
	|	struct_unionDecl packed_dimensionListE	{ $$ = GRAMMARP->createArray(new AstDefImplicitDType($1->fileline(),"__typeimpsu"+cvtToStr(GRAMMARP->s_modTypeImpNum++),
													     SYMP,VFlagChildDType(),$1),$2,true); }
	|	enumDecl				{ $$ = new AstDefImplicitDType($1->fileline(),"__typeimpenum"+cvtToStr(GRAMMARP->s_modTypeImpNum++),
										       SYMP,VFlagChildDType(),$1); }
	|	ySTRING					{ $$ = new AstBasicDType($1,AstBasicDTypeKwd::STRING); }
	|	yCHANDLE				{ $$ = new AstBasicDType($1,AstBasicDTypeKwd::CHANDLE); }
	//UNSUP	yEVENT					{ UNSUP }
	//UNSUP	yVIRTUAL__INTERFACE yINTERFACE id/*interface*/	{ UNSUP }
	//UNSUP	yVIRTUAL__anyID                id/*interface*/	{ UNSUP }
	//UNSUP	type_reference				{ UNSUP }
	//			// IEEE: class_scope: see data_type above
	//			// IEEE: class_type: see data_type above
	//			// IEEE: ps_covergroup: see data_type above
	;

data_type_or_void<dtypep>:	// ==IEEE: data_type_or_void
		data_type				{ $$ = $1; }
	//UNSUP	yVOID					{ UNSUP }	// No yTAGGED structures
	;

var_data_type<dtypep>:		// ==IEEE: var_data_type
		data_type				{ $$ = $1; }
	|	yVAR data_type				{ $$ = $2; }
	|	yVAR implicit_typeE			{ $$ = $2; }
	;

struct_unionDecl<classp>:	// IEEE: part of data_type
	//			// packedSigningE is NOP for unpacked
		ySTRUCT        packedSigningE '{' 	{ $<classp>$ = new AstStructDType($1, $2); SYMP->pushNew($<classp>$); }
	/*cont*/	struct_union_memberList '}'
			{ $$=$<classp>4; $$->addMembersp($5); SYMP->popScope($$); }
	|	yUNION taggedE packedSigningE '{' 	{ $<classp>$ = new AstUnionDType($1, $3); SYMP->pushNew($<classp>$); }
	/*cont*/	struct_union_memberList '}'
			{ $$=$<classp>5; $$->addMembersp($6); SYMP->popScope($$); }
	;

struct_union_memberList<nodep>:	// IEEE: { struct_union_member }
		struct_union_member				{ $$ = $1; }
	|	struct_union_memberList struct_union_member	{ $$ = $1->addNextNull($2); }
	;

struct_union_member<nodep>:	// ==IEEE: struct_union_member
		random_qualifierE data_type_or_void
			{ GRAMMARP->m_memDTypep = $2; }  // As a list follows, need to attach this dtype to each member.
	/*cont*/	list_of_member_decl_assignments ';'	{ $$ = $4; GRAMMARP->m_memDTypep = NULL; }
	;

list_of_member_decl_assignments<nodep>:	// Derived from IEEE: list_of_variable_decl_assignments
		member_decl_assignment		{ $$ = $1; }
	|	list_of_member_decl_assignments ',' member_decl_assignment	{ $$ = $1->addNextNull($3); }
	;

member_decl_assignment<memberp>:	// Derived from IEEE: variable_decl_assignment
	//			// At present we allow only packed structures/unions.  So this is different from variable_decl_assignment
		id variable_dimensionListE
			{ if ($2) $2->v3error("Unsupported: Unpacked array in packed struct/union");
			  $$ = new AstMemberDType($<fl>1, *$1, VFlagChildDType(), GRAMMARP->m_memDTypep->cloneTree(true)); }
	|	id variable_dimensionListE '=' variable_declExpr
			{ $4->v3error("Unsupported: Initial values in struct/union members."); }
	|	idSVKwd					{ $$ = NULL; }
	//
	//			// IEEE: "dynamic_array_variable_identifier '[' ']' [ '=' dynamic_array_new ]"
	//			// Matches above with variable_dimensionE = "[]"
	//			// IEEE: "class_variable_identifier [ '=' class_new ]"
	//			// variable_dimensionE must be empty
	//			// Pushed into variable_declExpr:dynamic_array_new
	//
	//			// IEEE: "[ covergroup_variable_identifier ] '=' class_new
	//			// Pushed into variable_declExpr:class_new
	//UNSUP	'=' class_new				{ UNSUP }
	;

list_of_variable_decl_assignments<nodep>:	// ==IEEE: list_of_variable_decl_assignments
		variable_decl_assignment		{ $$ = $1; }
	|	list_of_variable_decl_assignments ',' variable_decl_assignment	{ $$ = $1->addNextNull($3); }
	;

variable_decl_assignment<varp>:	// ==IEEE: variable_decl_assignment
		id variable_dimensionListE sigAttrListE
			{ $$ = VARDONEA($<fl>1,*$1,$2,$3); }
	|	id variable_dimensionListE sigAttrListE '=' variable_declExpr
			{ $$ = VARDONEA($<fl>1,*$1,$2,$3); $$->valuep($5); }
	|	idSVKwd					{ $$ = NULL; }
	//
	//			// IEEE: "dynamic_array_variable_identifier '[' ']' [ '=' dynamic_array_new ]"
	//			// Matches above with variable_dimensionE = "[]"
	//			// IEEE: "class_variable_identifier [ '=' class_new ]"
	//			// variable_dimensionE must be empty
	//			// Pushed into variable_declExpr:dynamic_array_new
	//
	//			// IEEE: "[ covergroup_variable_identifier ] '=' class_new
	//			// Pushed into variable_declExpr:class_new
	//UNSUP	'=' class_new				{ UNSUP }
	;

list_of_tf_variable_identifiers<nodep>: // ==IEEE: list_of_tf_variable_identifiers
		tf_variable_identifier			{ $$ = $1; }
	|	list_of_tf_variable_identifiers ',' tf_variable_identifier	{ $$ = $1->addNext($3); }
	;

tf_variable_identifier<varp>:		// IEEE: part of list_of_tf_variable_identifiers
		id variable_dimensionListE sigAttrListE
			{ $$ = VARDONEA($<fl>1,*$1, $2, $3); }
	|	id variable_dimensionListE sigAttrListE '=' expr
			{ $$ = VARDONEA($<fl>1,*$1, $2, $3);
			  $$->addNext(new AstAssign($4, new AstVarRef($4, *$1, true), $5)); }
	;

variable_declExpr<nodep>:		// IEEE: part of variable_decl_assignment - rhs of expr
		expr					{ $$ = $1; }
	//UNSUP	dynamic_array_new			{ $$ = $1; }
	//UNSUP	class_new				{ $$ = $1; }
	;

variable_dimensionListE<rangep>:	// IEEE: variable_dimension + empty
		/*empty*/				{ $$ = NULL; }
	|	variable_dimensionList			{ $$ = $1; }
	;

variable_dimensionList<rangep>:	// IEEE: variable_dimension + empty
		variable_dimension			{ $$ = $1; }
	|	variable_dimensionList variable_dimension	{ $$ = $1->addNext($2)->castRange(); }
	;

variable_dimension<rangep>:	// ==IEEE: variable_dimension
	//			// IEEE: unsized_dimension
	//UNSUP	'[' ']'					{ UNSUP }
	//			// IEEE: unpacked_dimension
		anyrange				{ $$ = $1; }
	|	'[' constExpr ']'			{ $$ = new AstRange($1, new AstConst($1, 0), new AstSub($1, $2, new AstConst($1, 1))); }
	//			// IEEE: associative_dimension
	//UNSUP	'[' data_type ']'			{ UNSUP }
	//UNSUP	yP_BRASTAR ']'				{ UNSUP }
	//UNSUP	'[' '*' ']'				{ UNSUP }
	//			// IEEE: queue_dimension
	//			// '[' '$' ']' -- $ is part of expr
	//			// '[' '$' ':' expr ']' -- anyrange:expr:$
	;

random_qualifierE:		// IEEE: random_qualifier + empty
		/*empty*/				{ }
	|	random_qualifier			{ }
	;

random_qualifier:		// ==IEEE: random_qualifier
		yRAND					{ }  // Ignored until we support randomize()
	|	yRANDC					{ }  // Ignored until we support randomize()
	;

taggedE:
		/*empty*/				{ }
	//UNSUP	yTAGGED					{ UNSUP }
	;

packedSigningE<signstate>:
	//			// AstNumeric::NOSIGN overloaded to indicate not packed
		/*empty*/				{ $$ = signedst_NOSIGN; }
	|	yPACKED signingE			{ $$ = $2; if ($$ == signedst_NOSIGN) $$ = signedst_UNSIGNED; }
	;

//************************************************
// enum

// IEEE: part of data_type
enumDecl<dtypep>:
		yENUM enum_base_typeE '{' enum_nameList '}' { $$ = new AstEnumDType($1,VFlagChildDType(),$2,$4); }
	;

enum_base_typeE<dtypep>:	// IEEE: enum_base_type
		/* empty */				{ $$ = new AstBasicDType(CRELINE(),AstBasicDTypeKwd::INT); }
	//			// Not in spec, but obviously "enum [1:0]" should work
	//			// implicit_type expanded, without empty
	//			// Note enum base types are always packed data types
	|	signingE rangeList			{ $$ = GRAMMARP->addRange(new AstBasicDType($2->fileline(), LOGIC_IMPLICIT, $1),$2,true); }
	|	signing					{ $$ = new AstBasicDType($<fl>1, LOGIC_IMPLICIT, $1); }
	//
	|	integer_atom_type signingE		{ $1->setSignedState($2); $$ = $1; }
	|	integer_vector_type signingE rangeListE	{ $1->setSignedState($2); $$ = GRAMMARP->addRange($1,$3,true); }
	//			// below can be idAny or yaID__aTYPE
	//			// IEEE requires a type, though no shift conflict if idAny
	|	idAny rangeListE			{ $$ = GRAMMARP->createArray(new AstRefDType($<fl>1, *$1), $2, true); }
	;

enum_nameList<nodep>:
		enum_name_declaration			{ $$ = $1; }
	|	enum_nameList ',' enum_name_declaration	{ $$ = $1->addNextNull($3); }
	;

enum_name_declaration<nodep>:	// ==IEEE: enum_name_declaration
		idAny/*enum_identifier*/ enumNameRangeE enumNameStartE	{ $$ = new AstEnumItem($<fl>1, *$1, $2, $3); }
	;

enumNameRangeE<nodep>:		// IEEE: second part of enum_name_declaration
		/* empty */				{ $$ = NULL; }
	|	'[' intnumAsConst ']'			{ $$ = new AstRange($1,new AstConst($1,0), $2); }
	|	'[' intnumAsConst ':' intnumAsConst ']'	{ $$ = new AstRange($1,$2,$4); }
	;

enumNameStartE<nodep>:		// IEEE: third part of enum_name_declaration
		/* empty */				{ $$ = NULL; }
	|	'=' constExpr				{ $$ = $2; }
	;

intnumAsConst<nodep>:
		yaINTNUM				{ $$ = new AstConst($<fl>1,*$1); }
	;

//************************************************
// Typedef

data_declaration<nodep>:	// ==IEEE: data_declaration
	//			// VARRESET can't be called here - conflicts
		data_declarationVar			{ $$ = $1; }
	|	type_declaration			{ $$ = $1; }
	|	package_import_declaration		{ $$ = $1; }
	//			// IEEE: virtual_interface_declaration
	//			// "yVIRTUAL yID yID" looks just like a data_declaration
	//			// Therefore the virtual_interface_declaration term isn't used
	;

data_declarationVar<nodep>:	// IEEE: part of data_declaration
	//			// The first declaration has complications between assuming what's the type vs ID declaring
		data_declarationVarFront list_of_variable_decl_assignments ';'	{ $$ = $2; }
	;

data_declarationVarFront:	// IEEE: part of data_declaration
	//			// Expanded: "constE yVAR lifetimeE data_type"
	//			// implicit_type expanded into /*empty*/ or "signingE rangeList"
		/**/ 	    yVAR lifetimeE data_type	{ VARRESET_NONLIST(VAR); VARDTYPE($3); }
	|	/**/ 	    yVAR lifetimeE		{ VARRESET_NONLIST(VAR); VARDTYPE(new AstBasicDType($<fl>1, LOGIC_IMPLICIT)); }
	|	/**/ 	    yVAR lifetimeE signingE rangeList { /*VARRESET-in-ddVar*/ VARDTYPE(GRAMMARP->addRange(new AstBasicDType($<fl>1, LOGIC_IMPLICIT, $3), $4,true)); }
	//
	//			// implicit_type expanded into /*empty*/ or "signingE rangeList"
	|	yCONST__ETC yVAR lifetimeE data_type	{ VARRESET_NONLIST(VAR); VARDTYPE(new AstConstDType($<fl>1, VFlagChildDType(), $4)); }
	|	yCONST__ETC yVAR lifetimeE		{ VARRESET_NONLIST(VAR); VARDTYPE(new AstConstDType($<fl>1, VFlagChildDType(), new AstBasicDType($<fl>2, LOGIC_IMPLICIT))); }
	|	yCONST__ETC yVAR lifetimeE signingE rangeList { VARRESET_NONLIST(VAR); VARDTYPE(new AstConstDType($<fl>1, VFlagChildDType(), GRAMMARP->addRange(new AstBasicDType($<fl>2, LOGIC_IMPLICIT, $4), $5,true))); }
	//
	//			// Expanded: "constE lifetimeE data_type"
	|	/**/		      data_type		{ VARRESET_NONLIST(VAR); VARDTYPE($1); }
	|	/**/	    lifetime  data_type		{ VARRESET_NONLIST(VAR); VARDTYPE($2); }
	|	yCONST__ETC lifetimeE data_type		{ VARRESET_NONLIST(VAR); VARDTYPE(new AstConstDType($<fl>1, VFlagChildDType(), $3)); }
	//			// = class_new is in variable_decl_assignment
	;

implicit_typeE<dtypep>:		// IEEE: part of *data_type_or_implicit
	//			// Also expanded in data_declaration
		/* empty */				{ $$ = NULL; }
	|	signingE rangeList			{ $$ = GRAMMARP->addRange(new AstBasicDType($2->fileline(), LOGIC_IMPLICIT, $1),$2,true); }
	|	signing					{ $$ = new AstBasicDType($<fl>1, LOGIC_IMPLICIT, $1); }
	;

type_declaration<nodep>:	// ==IEEE: type_declaration
	//			// Use idAny, as we can redeclare a typedef on an existing typedef
		yTYPEDEF data_type idAny variable_dimensionListE dtypeAttrListE ';'
	/**/	{ $$ = new AstTypedef($<fl>1, *$3, $5, VFlagChildDType(), GRAMMARP->createArray($2,$4,false));
		  SYMP->reinsert($$); }
	//UNSUP	yTYPEDEF id/*interface*/ '.' idAny/*type*/ idAny/*type*/ ';'	{ $$ = NULL; $1->v3error("Unsupported: SystemVerilog 2005 typedef in this context"); } //UNSUP
	//			// Combines into above "data_type id" rule
	//			// Verilator: Not important what it is in the AST, just need to make sure the yaID__aTYPE gets returned
	|	yTYPEDEF id ';'				{ $$ = NULL; $$ = new AstTypedefFwd($<fl>1, *$2); SYMP->reinsert($$); }
	|	yTYPEDEF yENUM idAny ';'		{ $$ = NULL; $$ = new AstTypedefFwd($<fl>1, *$3); SYMP->reinsert($$); }
	|	yTYPEDEF ySTRUCT idAny ';'		{ $$ = NULL; $$ = new AstTypedefFwd($<fl>1, *$3); SYMP->reinsert($$); }
	|	yTYPEDEF yUNION idAny ';'		{ $$ = NULL; $$ = new AstTypedefFwd($<fl>1, *$3); SYMP->reinsert($$); }
	//UNSUP	yTYPEDEF yCLASS idAny ';'		{ $$ = NULL; $$ = new AstTypedefFwd($<fl>1, *$3); SYMP->reinsert($$); }
	;

dtypeAttrListE<nodep>:
		/* empty */				{ $$ = NULL; }
	|	dtypeAttrList				{ $$ = $1; }
	;

dtypeAttrList<nodep>:
		dtypeAttr				{ $$ = $1; }
	|	dtypeAttrList dtypeAttr			{ $$ = $1->addNextNull($2); }
	;

dtypeAttr<nodep>:
		yVL_PUBLIC				{ $$ = new AstAttrOf($1,AstAttrType::DT_PUBLIC); }
	;

//************************************************
// Module Items

module_itemListE<nodep>:	// IEEE: Part of module_declaration
		/* empty */				{ $$ = NULL; }
	|	module_itemList				{ $$ = $1; }
	;

module_itemList<nodep>:		// IEEE: Part of module_declaration
		module_item				{ $$ = $1; }
	|	module_itemList module_item		{ $$ = $1->addNextNull($2); }
	;

module_item<nodep>:		// ==IEEE: module_item
		port_declaration ';'			{ $$ = $1; }
	|	non_port_module_item			{ $$ = $1; }
	;

non_port_module_item<nodep>:	// ==IEEE: non_port_module_item
		generate_region				{ $$ = $1; }
	|	module_or_generate_item 		{ $$ = $1; }
	|	specify_block 				{ $$ = $1; }
	|	specparam_declaration			{ $$ = $1; }
	//UNSUP	program_declaration			{ $$ = $1; }
	//UNSUP	module_declaration			{ $$ = $1; }
	//UNSUP	interface_declaration			{ $$ = $1; }
	|	timeunits_declaration			{ $$ = $1; }
	//			// Verilator specific
	|	yaSCHDR					{ $$ = new AstScHdr($<fl>1,*$1); }
	|	yaSCINT					{ $$ = new AstScInt($<fl>1,*$1); }
	|	yaSCIMP					{ $$ = new AstScImp($<fl>1,*$1); }
	|	yaSCIMPH				{ $$ = new AstScImpHdr($<fl>1,*$1); }
	|	yaSCCTOR				{ $$ = new AstScCtor($<fl>1,*$1); }
	|	yaSCDTOR				{ $$ = new AstScDtor($<fl>1,*$1); }
	|	yVL_INLINE_MODULE			{ $$ = new AstPragma($1,AstPragmaType::INLINE_MODULE); }
	|	yVL_NO_INLINE_MODULE			{ $$ = new AstPragma($1,AstPragmaType::NO_INLINE_MODULE); }
	|	yVL_PUBLIC_MODULE			{ $$ = new AstPragma($1,AstPragmaType::PUBLIC_MODULE); v3Global.dpi(true); }
	;

module_or_generate_item<nodep>:	// ==IEEE: module_or_generate_item
	//			// IEEE: parameter_override
		yDEFPARAM list_of_defparam_assignments ';'	{ $$ = $2; }
	//			// IEEE: gate_instantiation + udp_instantiation + module_instantiation
	//			// not here, see etcInst in module_common_item
	//			// We joined udp & module definitions, so this goes here
	|	combinational_body			{ $$ = $1; }
	//			// This module_common_item shared with interface_or_generate_item:module_common_item
	|	module_common_item			{ $$ = $1; }
	;

module_common_item<nodep>:	// ==IEEE: module_common_item
		module_or_generate_item_declaration	{ $$ = $1; }
	//			// IEEE: interface_instantiation
	//			// + IEEE: program_instantiation
	//			// + module_instantiation from module_or_generate_item
	|	etcInst 				{ $$ = $1; }
	|	concurrent_assertion_item		{ $$ = $1; }
	|	bind_directive				{ $$ = $1; }
	|	continuous_assign			{ $$ = $1; }
	//			// IEEE: net_alias
	//UNSUP	yALIAS variable_lvalue aliasEqList ';'	{ UNSUP }
	|	initial_construct			{ $$ = $1; }
	|	final_construct				{ $$ = $1; }
	//			// IEEE: always_construct
	//			// Verilator only - event_control attached to always
	|	yALWAYS       event_controlE stmtBlock	{ $$ = new AstAlways($1,VAlwaysKwd::ALWAYS, $2,$3); }
	|	yALWAYS_FF    event_controlE stmtBlock	{ $$ = new AstAlways($1,VAlwaysKwd::ALWAYS_FF, $2,$3); }
	|	yALWAYS_COMB  event_controlE stmtBlock	{ $$ = new AstAlways($1,VAlwaysKwd::ALWAYS_COMB, $2,$3); }
	|	yALWAYS_LATCH event_controlE stmtBlock	{ $$ = new AstAlways($1,VAlwaysKwd::ALWAYS_LATCH, $2,$3); }
	|	loop_generate_construct			{ $$ = $1; }
	|	conditional_generate_construct		{ $$ = $1; }
	//
	|	error ';'				{ $$ = NULL; }
	;

continuous_assign<nodep>:	// IEEE: continuous_assign
		yASSIGN delayE assignList ';'		{ $$ = $3; }
	//UNSUP: strengthSpecE not in above assign
	;

initial_construct<nodep>:	// IEEE: initial_construct
		yINITIAL stmtBlock			{ $$ = new AstInitial($1,$2); }
	;

final_construct<nodep>:		// IEEE: final_construct
		yFINAL stmtBlock			{ $$ = new AstFinal($1,$2); }
	;

module_or_generate_item_declaration<nodep>:	// ==IEEE: module_or_generate_item_declaration
		package_or_generate_item_declaration	{ $$ = $1; }
	| 	genvar_declaration			{ $$ = $1; }
	|	clocking_declaration			{ $$ = $1; }
	//UNSUP	yDEFAULT yCLOCKING idAny/*new-clocking_identifier*/ ';'	{ $$ = $1; }
	;

bind_directive<nodep>:		// ==IEEE: bind_directive + bind_target_scope
	//			// ';' - Note IEEE grammar is wrong, includes extra ';' - it's already in module_instantiation
	//			// We merged the rules - id may be a bind_target_instance or module_identifier or interface_identifier
		yBIND bind_target_instance bind_instantiation	{ $$ = new AstBind($<fl>1,*$2,$3); }
	|	yBIND bind_target_instance ':' bind_target_instance_list bind_instantiation	{ $$=NULL; $1->v3error("Unsupported: Bind with instance list"); }
	;

bind_target_instance_list:	// ==IEEE: bind_target_instance_list
		bind_target_instance			{ }
	|	bind_target_instance_list ',' bind_target_instance	{ }
	;

bind_target_instance<strp>:	// ==IEEE: bind_target_instance
	//UNSUP	hierarchical_identifierBit		{ }
		idAny					{ $$ = $1; }
	;

bind_instantiation<nodep>:	// ==IEEE: bind_instantiation
	//			// IEEE: program_instantiation
	//			// IEEE: + module_instantiation
	//			// IEEE: + interface_instantiation
	//			// Need to get an AstBind instead of AstCell, so have special rules
		instDecl				{ $$ = $1; }
	;

//************************************************
// Generates
//
// Way down in generate_item is speced a difference between module,
// interface and checker generates.  modules and interfaces are almost
// identical (minus DEFPARAMs) so we overlap them.  Checkers are too
// different, so we copy all rules for checkers.

generate_region<nodep>:		// ==IEEE: generate_region
		yGENERATE genItemList yENDGENERATE	{ $$ = new AstGenerate($1, $2); }
	|	yGENERATE yENDGENERATE			{ $$ = NULL; }
	;

generate_block_or_null<nodep>:	// IEEE: generate_block_or_null
	//	';'		// is included in
	//			// IEEE: generate_block
	//			// Must always return a BEGIN node, or NULL - see GenFor construction
		generate_item				{ $$ = $1 ? (new AstBegin($1->fileline(),"genblk",$1,true)) : NULL; }
	|	genItemBegin				{ $$ = $1; }
	;

genItemBegin<nodep>:		// IEEE: part of generate_block
		yBEGIN genItemList yEND			{ $$ = new AstBegin($1,"genblk",$2,true); }
	|	yBEGIN yEND				{ $$ = NULL; }
	|	id ':' yBEGIN genItemList yEND endLabelE	{ $$ = new AstBegin($2,*$1,$4,true); GRAMMARP->endLabel($<fl>6,*$1,$6); }
	|	id ':' yBEGIN             yEND endLabelE	{ $$ = NULL; GRAMMARP->endLabel($<fl>5,*$1,$5); }
	|	yBEGIN ':' idAny genItemList yEND endLabelE	{ $$ = new AstBegin($2,*$3,$4,true); GRAMMARP->endLabel($<fl>6,*$3,$6); }
	|	yBEGIN ':' idAny 	  yEND endLabelE	{ $$ = NULL; GRAMMARP->endLabel($<fl>5,*$3,$5); }
	;

genItemOrBegin<nodep>:		// Not in IEEE, but our begin isn't under generate_item
		~c~generate_item			{ $$ = $1; }
	|	~c~genItemBegin				{ $$ = $1; }
	;

genItemList<nodep>:
		~c~genItemOrBegin			{ $$ = $1; }
	|	~c~genItemList ~c~genItemOrBegin	{ $$ = $1->addNextNull($2); }
	;

generate_item<nodep>:		// IEEE: module_or_interface_or_generate_item
	//			// Only legal when in a generate under a module (or interface under a module)
		module_or_generate_item			{ $$ = $1; }
	//			// Only legal when in a generate under an interface
	//UNSUP	interface_or_generate_item		{ $$ = $1; }
	//			// IEEE: checker_or_generate_item
	//			// Only legal when in a generate under a checker
	//			// so below in c_generate_item
	;

conditional_generate_construct<nodep>:	// ==IEEE: conditional_generate_construct
		yCASE  '(' expr ')' ~c~case_generate_itemListE yENDCASE	{ $$ = new AstGenCase($1,$3,$5); }
	|	yIF '(' expr ')' generate_block_or_null	%prec prLOWER_THAN_ELSE	{ $$ = new AstGenIf($1,$3,$5,NULL); }
	|	yIF '(' expr ')' generate_block_or_null yELSE generate_block_or_null	{ $$ = new AstGenIf($1,$3,$5,$7); }
	;

loop_generate_construct<nodep>:	// ==IEEE: loop_generate_construct
		yFOR '(' genvar_initialization ';' expr ';' genvar_iteration ')' ~c~generate_block_or_null
			{ // Convert BEGIN(...) to BEGIN(GENFOR(...)), as we need the BEGIN to hide the local genvar
			  AstBegin* lowerBegp = $9->castBegin();
			  if ($9 && !lowerBegp) $9->v3fatalSrc("Child of GENFOR should have been begin");
			  if (!lowerBegp) lowerBegp = new AstBegin($1,"genblk",NULL,true);  // Empty body
			  AstNode* lowerNoBegp = lowerBegp->stmtsp();
			  if (lowerNoBegp) lowerNoBegp->unlinkFrBackWithNext();
			  //
			  AstBegin* blkp = new AstBegin($1,lowerBegp->name(),NULL,true);
			  // V3LinkDot detects BEGIN(GENFOR(...)) as a special case
			  AstNode* initp = $3;  AstNode* varp = $3;
			  if (varp->castVar()) {  // Genvar
				initp = varp->nextp();
				initp->unlinkFrBackWithNext();  // Detach 2nd from varp, make 1st init
				blkp->addStmtsp(varp);
			  }
			  // Statements are under 'genforp' as cells under this
			  // for loop won't get an extra layer of hierarchy tacked on
			  blkp->addGenforp(new AstGenFor($1,initp,$5,$7,lowerNoBegp));
			  $$ = blkp;
			  lowerBegp->deleteTree(); lowerBegp=NULL;
			}
	;

genvar_initialization<nodep>:	// ==IEEE: genvar_initalization
		varRefBase '=' expr			{ $$ = new AstAssign($2,$1,$3); }
	|	yGENVAR genvar_identifierDecl '=' constExpr	{ $$ = $2; $2->addNext(new AstAssign($3,new AstVarRef($3,$2,true), $4)); }
	;

genvar_iteration<nodep>:	// ==IEEE: genvar_iteration
		varRefBase '=' 		expr		{ $$ = new AstAssign($2,$1,$3); }
	|	varRefBase yP_PLUSEQ	expr		{ $$ = new AstAssign($2,$1,new AstAdd    ($2,$1->cloneTree(true),$3)); }
	|	varRefBase yP_MINUSEQ	expr		{ $$ = new AstAssign($2,$1,new AstSub    ($2,$1->cloneTree(true),$3)); }
	|	varRefBase yP_TIMESEQ	expr		{ $$ = new AstAssign($2,$1,new AstMul    ($2,$1->cloneTree(true),$3)); }
	|	varRefBase yP_DIVEQ	expr		{ $$ = new AstAssign($2,$1,new AstDiv    ($2,$1->cloneTree(true),$3)); }
	|	varRefBase yP_MODEQ	expr		{ $$ = new AstAssign($2,$1,new AstModDiv ($2,$1->cloneTree(true),$3)); }
	|	varRefBase yP_ANDEQ	expr		{ $$ = new AstAssign($2,$1,new AstAnd    ($2,$1->cloneTree(true),$3)); }
	|	varRefBase yP_OREQ	expr		{ $$ = new AstAssign($2,$1,new AstOr     ($2,$1->cloneTree(true),$3)); }
	|	varRefBase yP_XOREQ	expr		{ $$ = new AstAssign($2,$1,new AstXor    ($2,$1->cloneTree(true),$3)); }
	|	varRefBase yP_SLEFTEQ	expr		{ $$ = new AstAssign($2,$1,new AstShiftL ($2,$1->cloneTree(true),$3)); }
	|	varRefBase yP_SRIGHTEQ	expr		{ $$ = new AstAssign($2,$1,new AstShiftR ($2,$1->cloneTree(true),$3)); }
	|	varRefBase yP_SSRIGHTEQ	expr		{ $$ = new AstAssign($2,$1,new AstShiftRS($2,$1->cloneTree(true),$3)); }
	//			// inc_or_dec_operator
	// When support ++ as a real AST type, maybe AstWhile::precondsp() becomes generic AstMathStmt?
	|	yP_PLUSPLUS   varRefBase		{ $$ = new AstAssign($1,$2,new AstAdd    ($1,$2->cloneTree(true),new AstConst($1,V3Number($1,"'b1")))); }
	|	yP_MINUSMINUS varRefBase		{ $$ = new AstAssign($1,$2,new AstSub    ($1,$2->cloneTree(true),new AstConst($1,V3Number($1,"'b1")))); }
	|	varRefBase yP_PLUSPLUS			{ $$ = new AstAssign($2,$1,new AstAdd    ($2,$1->cloneTree(true),new AstConst($2,V3Number($2,"'b1")))); }
	|	varRefBase yP_MINUSMINUS		{ $$ = new AstAssign($2,$1,new AstSub    ($2,$1->cloneTree(true),new AstConst($2,V3Number($2,"'b1")))); }
	;

case_generate_itemListE<nodep>:	// IEEE: [{ case_generate_itemList }]
		/* empty */				{ $$ = NULL; }
	|	case_generate_itemList			{ $$ = $1; }
	;

case_generate_itemList<nodep>:	// IEEE: { case_generate_itemList }
		~c~case_generate_item			{ $$=$1; }
	|	~c~case_generate_itemList ~c~case_generate_item	{ $$=$1; $1->addNext($2); }
	;

case_generate_item<nodep>:	// ==IEEE: case_generate_item
		caseCondList ':' generate_block_or_null		{ $$ = new AstCaseItem($2,$1,$3); }
	|	yDEFAULT ':' generate_block_or_null		{ $$ = new AstCaseItem($2,NULL,$3); }
	|	yDEFAULT generate_block_or_null			{ $$ = new AstCaseItem($1,NULL,$2); }
	;

//************************************************
// Assignments and register declarations

assignList<nodep>:
		assignOne				{ $$ = $1; }
	|	assignList ',' assignOne		{ $$ = $1->addNext($3); }
	;

assignOne<nodep>:
		variable_lvalue '=' expr		{ $$ = new AstAssignW($2,$1,$3); }
	;

delayE:
		/* empty */				{ }
	|	delay_control				{ $1->v3warn(ASSIGNDLY,"Unsupported: Ignoring delay on this assignment/primitive."); } /* ignored */
	;

delay_control<fl>:	//== IEEE: delay_control
		'#' delay_value				{ $$ = $1; } /* ignored */
	|	'#' '(' minTypMax ')'			{ $$ = $1; } /* ignored */
	|	'#' '(' minTypMax ',' minTypMax ')'			{ $$ = $1; } /* ignored */
	|	'#' '(' minTypMax ',' minTypMax ',' minTypMax ')'	{ $$ = $1; } /* ignored */
	;

delay_value:			// ==IEEE:delay_value
	//			// IEEE: ps_identifier
		ps_id_etc				{ }
	|	yaINTNUM 				{ }
	|	yaFLOATNUM 				{ }
	|	yaTIMENUM 				{ }
	;

delayExpr:
		expr					{ DEL($1); }
	//			// Verilator doesn't support yaTIMENUM, so not in expr
	|	yaTIMENUM 				{ }
	;

minTypMax:			// IEEE: mintypmax_expression and constant_mintypmax_expression
		delayExpr				{ }
	|	delayExpr ':' delayExpr ':' delayExpr	{ }
	;

netSigList<varp>:		// IEEE: list_of_port_identifiers
		netSig  				{ $$ = $1; }
	|	netSigList ',' netSig		       	{ $$ = $1; $1->addNext($3); }
	;

netSig<varp>:			// IEEE: net_decl_assignment -  one element from list_of_port_identifiers
		netId sigAttrListE			{ $$ = VARDONEA($<fl>1,*$1, NULL, $2); }
	|	netId sigAttrListE '=' expr		{ $$ = VARDONEA($<fl>1,*$1, NULL, $2); $$->addNext(new AstAssignW($3,new AstVarRef($3,$$->name(),true),$4)); }
	|	netId variable_dimensionList sigAttrListE	{ $$ = VARDONEA($<fl>1,*$1, $2, $3); }
	;

netId<strp>:
		id/*new-net*/				{ $$ = $1; $<fl>$=$<fl>1; }
	|	idSVKwd					{ $$ = $1; $<fl>$=$<fl>1; }
	;

sigAttrListE<nodep>:
		/* empty */				{ $$ = NULL; }
	|	sigAttrList				{ $$ = $1; }
	;

sigAttrList<nodep>:
		sigAttr					{ $$ = $1; }
	|	sigAttrList sigAttr			{ $$ = $1->addNextNull($2); }
	;

sigAttr<nodep>:
		yVL_CLOCK				{ $$ = new AstAttrOf($1,AstAttrType::VAR_CLOCK); }
	|	yVL_CLOCKER				{ $$ = new AstAttrOf($1,AstAttrType::VAR_CLOCKER); }
	|	yVL_NO_CLOCKER				{ $$ = new AstAttrOf($1,AstAttrType::VAR_NO_CLOCKER); }
	|	yVL_CLOCK_ENABLE			{ $$ = new AstAttrOf($1,AstAttrType::VAR_CLOCK_ENABLE); }
	|	yVL_PUBLIC				{ $$ = new AstAttrOf($1,AstAttrType::VAR_PUBLIC); v3Global.dpi(true); }
	|	yVL_PUBLIC_FLAT				{ $$ = new AstAttrOf($1,AstAttrType::VAR_PUBLIC_FLAT); v3Global.dpi(true); }
	|	yVL_PUBLIC_FLAT_RD			{ $$ = new AstAttrOf($1,AstAttrType::VAR_PUBLIC_FLAT_RD); v3Global.dpi(true); }
	|	yVL_PUBLIC_FLAT_RW			{ $$ = new AstAttrOf($1,AstAttrType::VAR_PUBLIC_FLAT_RW); v3Global.dpi(true); }
	|	yVL_PUBLIC_FLAT_RW attr_event_control	{ $$ = new AstAttrOf($1,AstAttrType::VAR_PUBLIC_FLAT_RW); v3Global.dpi(true);
							  $$ = $$->addNext(new AstAlwaysPublic($1,$2,NULL)); }
	|	yVL_ISOLATE_ASSIGNMENTS			{ $$ = new AstAttrOf($1,AstAttrType::VAR_ISOLATE_ASSIGNMENTS); }
	|	yVL_SC_BV				{ $$ = new AstAttrOf($1,AstAttrType::VAR_SC_BV); }
	|	yVL_SFORMAT				{ $$ = new AstAttrOf($1,AstAttrType::VAR_SFORMAT); }
	;

rangeListE<rangep>:		// IEEE: [{packed_dimension}]
		/* empty */    		               	{ $$ = NULL; }
	|	rangeList 				{ $$ = $1; }
	;

rangeList<rangep>:		// IEEE: {packed_dimension}
		anyrange				{ $$ = $1; }
        |	rangeList anyrange			{ $$ = $1; $1->addNext($2); }
	;

// IEEE: select
// Merged into more general idArray

anyrange<rangep>:
		'[' constExpr ':' constExpr ']'		{ $$ = new AstRange($1,$2,$4); }
	;

packed_dimensionListE<rangep>:	// IEEE: [{ packed_dimension }]
		/* empty */				{ $$ = NULL; }
	|	packed_dimensionList			{ $$ = $1; }
	;

packed_dimensionList<rangep>:	// IEEE: { packed_dimension }
		packed_dimension			{ $$ = $1; }
	|	packed_dimensionList packed_dimension	{ $$ = $1->addNext($2)->castRange(); }
	;

packed_dimension<rangep>:	// ==IEEE: packed_dimension
		anyrange				{ $$ = $1; }
	//UNSUP	'[' ']'					{ UNSUP }
	;

//************************************************
// Parameters

param_assignment<varp>:		// ==IEEE: param_assignment
	//			// IEEE: constant_param_expression
	//			// constant_param_expression: '$' is in expr
		id/*new-parameter*/ variable_dimensionListE sigAttrListE '=' expr
	/**/		{ $$ = VARDONEA($<fl>1,*$1, $2, $3); $$->valuep($5); }
	//UNSUP:  exprOrDataType instead of expr
	;

list_of_param_assignments<varp>:	// ==IEEE: list_of_param_assignments
		param_assignment			{ $$ = $1; }
	|	list_of_param_assignments ',' param_assignment	{ $$ = $1; $1->addNext($3); }
	;

list_of_defparam_assignments<nodep>:	//== IEEE: list_of_defparam_assignments
		defparam_assignment			{ $$ = $1; }
	|	list_of_defparam_assignments ',' defparam_assignment	{ $$ = $1->addNext($3); }
	;

defparam_assignment<nodep>:	// ==IEEE: defparam_assignment
		id '.' id '=' expr 			{ $$ = new AstDefParam($4,*$1,*$3,$5); }
	//UNSUP	More general dotted identifiers
	;

//************************************************
// Instances
// We don't know identifier types, so this matches all module,udp,etc instantiation
//   module_id      [#(params)]   name  (pins) [, name ...] ;	// module_instantiation
//   gate (strong0) [#(delay)]   [name] (pins) [, (pins)...] ;	// gate_instantiation
//   program_id     [#(params}]   name ;			// program_instantiation
//   interface_id   [#(params}]   name ;			// interface_instantiation
//   checker_id			  name  (pins) ;		// checker_instantiation

etcInst<nodep>:			// IEEE: module_instantiation + gate_instantiation + udp_instantiation
		instDecl				{ $$ = $1; }
	|	gateDecl 				{ $$ = $1; }
	;

instDecl<nodep>:
		id parameter_value_assignmentE {INSTPREP(*$1,$2);} instnameList ';'
			{ $$ = $4; GRAMMARP->m_impliedDecl=false;
			  if (GRAMMARP->m_instParamp) { GRAMMARP->m_instParamp->deleteTree(); GRAMMARP->m_instParamp = NULL; } }
	//			// IEEE: interface_identifier' .' modport_identifier list_of_interface_identifiers
	|	id/*interface*/ '.' id/*modport*/
			{ VARRESET_NONLIST(AstVarType::IFACEREF);
			  VARDTYPE(new AstIfaceRefDType($<fl>1,"",*$1,*$3)); }
		mpInstnameList ';'
			{ $$ = VARDONEP($5,NULL,NULL); }
	//UNSUP: strengthSpecE for udp_instantiations
	;

mpInstnameList<nodep>:		// Similar to instnameList, but for modport instantiations which have no parenthesis
		mpInstnameParen				{ $$ = $1; }
	|	mpInstnameList ',' mpInstnameParen	{ $$ = $1->addNext($3); }
	;

mpInstnameParen<nodep>:		// Similar to instnameParen, but for modport instantiations which have no parenthesis
		id instRangeE sigAttrListE		{ $$ = VARDONEA($<fl>1,*$1,$2,$3); }
	;

instnameList<nodep>:
		instnameParen				{ $$ = $1; }
	|	instnameList ',' instnameParen		{ $$ = $1->addNext($3); }
	;

instnameParen<cellp>:
	//			// Must clone m_instParamp as may be comma'ed list of instances
		id instRangeE '(' cellpinList ')'	{ $$ = new AstCell($<fl>1,*$1,GRAMMARP->m_instModule,$4,  GRAMMARP->m_instParamp->cloneTree(true),$2);
						          $$->trace(GRAMMARP->allTracingOn($<fl>1)); }
	|	id instRangeE 				{ $$ = new AstCell($<fl>1,*$1,GRAMMARP->m_instModule,NULL,GRAMMARP->m_instParamp->cloneTree(true),$2);
						          $$->trace(GRAMMARP->allTracingOn($<fl>1)); }
	//UNSUP	instRangeE '(' cellpinList ')'		{ UNSUP } // UDP
	//			// Adding above and switching to the Verilog-Perl syntax
	//			// causes a shift conflict due to use of idClassSel inside exprScope.
	//			// It also breaks allowing "id foo;" instantiation syntax.
	;

instRangeE<rangep>:
		/* empty */				{ $$ = NULL; }
	|	'[' constExpr ']'			{ $$ = new AstRange($1,$2,$2->cloneTree(true)); }
	|	'[' constExpr ':' constExpr ']'		{ $$ = new AstRange($1,$2,$4); }
	;

cellpinList<pinp>:
		{VARRESET_LIST(UNKNOWN);} cellpinItList	{ $$ = $2; VARRESET_NONLIST(UNKNOWN); }
	;

cellpinItList<pinp>:		// IEEE: list_of_port_connections + list_of_parameter_assignmente
		cellpinItemE				{ $$ = $1; }
	|	cellpinItList ',' cellpinItemE		{ $$ = $1->addNextNull($3)->castPin(); }
	;

cellpinItemE<pinp>:		// IEEE: named_port_connection + named_parameter_assignment + empty
				// Note empty can match either () or (,); V3LinkCells cleans up ()
		/* empty: ',,' is legal */		{ $$ = new AstPin(CRELINE(),PINNUMINC(),"",NULL); }
	|	yP_DOTSTAR				{ $$ = new AstPin($1,PINNUMINC(),".*",NULL); }
	|	'.' idSVKwd				{ $$ = new AstPin($1,PINNUMINC(),*$2,new AstVarRef($1,*$2,false)); $$->svImplicit(true);}
	|	'.' idAny				{ $$ = new AstPin($1,PINNUMINC(),*$2,new AstVarRef($1,*$2,false)); $$->svImplicit(true);}
	|	'.' idAny '(' ')'			{ $$ = new AstPin($1,PINNUMINC(),*$2,NULL); }
	//			// mintypmax is expanded here, as it might be a UDP or gate primitive
	|	'.' idAny '(' expr ')'			{ $$ = new AstPin($1,PINNUMINC(),*$2,$4); }
	//UNSUP	'.' idAny '(' expr ':' expr ')'		{ }
	//UNSUP	'.' idAny '(' expr ':' expr ':' expr ')' { }
	//			// For parameters
	//UNSUP	'.' idAny '(' data_type ')'		{ PINDONE($1,$2,$4);  GRAMMARP->pinNumInc(); }
	//			// For parameters
	//UNSUP	data_type				{ PINDONE($1->fileline(),"",$1);  GRAMMARP->pinNumInc(); }
	//
	|	expr					{ $$ = new AstPin($1->fileline(),PINNUMINC(),"",$1); }
	//UNSUP	expr ':' expr				{ }
	//UNSUP	expr ':' expr ':' expr			{ }
	;

//************************************************
// EventControl lists

attr_event_control<sentreep>:	// ==IEEE: event_control
		'@' '(' event_expression ')'		{ $$ = new AstSenTree($1,$3); }
	|	'@' '(' '*' ')'				{ $$ = NULL; }
	|	'@' '*'					{ $$ = NULL; }
	;

event_controlE<sentreep>:
		/* empty */				{ $$ = NULL; }
	|	event_control				{ $$ = $1; }
	;

event_control<sentreep>:	// ==IEEE: event_control
		'@' '(' event_expression ')'		{ $$ = new AstSenTree($1,$3); }
	|	'@' '(' '*' ')'				{ $$ = NULL; }
	|	'@' '*'					{ $$ = NULL; }
	//			// IEEE: hierarchical_event_identifier
	|	'@' senitemVar				{ $$ = new AstSenTree($1,$2); }	/* For events only */
	//			// IEEE: sequence_instance
	//			// sequence_instance without parens matches idClassSel above.
	//			// Ambiguity: "'@' sequence (-for-sequence" versus expr:delay_or_event_controlE "'@' id (-for-expr
	//			// For now we avoid this, as it's very unlikely someone would mix
	//			// 1995 delay with a sequence with parameters.
	//			// Alternatively split this out of event_control, and delay_or_event_controlE
	//			// and anywhere delay_or_event_controlE is called allow two expressions
	//|	'@' idClassSel '(' list_of_argumentsE ')'	{ }
	;

event_expression<senitemp>:	// IEEE: event_expression - split over several
		senitem					{ $$ = $1; }
	|	event_expression yOR senitem		{ $$ = $1->addNextNull($3)->castNodeSenItem(); }
	|	event_expression ',' senitem		{ $$ = $1->addNextNull($3)->castNodeSenItem(); }	/* Verilog 2001 */
	;

senitem<senitemp>:		// IEEE: part of event_expression, non-'OR' ',' terms
		senitemEdge				{ $$ = $1; }
	|	senitemVar				{ $$ = $1; }
	|	'(' senitemVar ')'			{ $$ = $2; }
	//UNSUP	expr					{ UNSUP }
	|	'{' event_expression '}'		{ $$ = $2; }
	//UNSUP	expr yIFF expr				{ UNSUP }
	// Since expr is unsupported we allow and ignore constants (removed in V3Const)
	|	yaINTNUM				{ $$ = NULL; }
	|	yaFLOATNUM				{ $$ = NULL; }
	|	'(' yaINTNUM ')'			{ $$ = NULL; }
	|	'(' yaFLOATNUM ')'			{ $$ = NULL; }
	;

senitemVar<senitemp>:
		idClassSel				{ $$ = new AstSenItem($1->fileline(),AstEdgeType::ET_ANYEDGE,$1); }
	;

senitemEdge<senitemp>:		// IEEE: part of event_expression
		yPOSEDGE idClassSel			{ $$ = new AstSenItem($1,AstEdgeType::ET_POSEDGE,$2); }
	|	yNEGEDGE idClassSel			{ $$ = new AstSenItem($1,AstEdgeType::ET_NEGEDGE,$2); }
	|	yEDGE idClassSel			{ $$ = new AstSenItem($1,AstEdgeType::ET_BOTHEDGE,$2); }
	|	yPOSEDGE '(' idClassSel ')'		{ $$ = new AstSenItem($1,AstEdgeType::ET_POSEDGE,$3); }
	|	yNEGEDGE '(' idClassSel ')'		{ $$ = new AstSenItem($1,AstEdgeType::ET_NEGEDGE,$3); }
	|	yEDGE '(' idClassSel ')'		{ $$ = new AstSenItem($1,AstEdgeType::ET_BOTHEDGE,$3); }
	//UNSUP	yIFF...
	;

//************************************************
// Statements

stmtBlock<nodep>:		// IEEE: statement + seq_block + par_block
		stmt					{ $$ = $1; }
	;

seq_block<nodep>:		// ==IEEE: seq_block
	//			// IEEE doesn't allow declarations in unnamed blocks, but several simulators do.
	//			// So need AstBegin's even if unnamed to scope variables down
		seq_blockFront blockDeclStmtList yEND endLabelE	{ $$=$1; $1->addStmtsp($2); SYMP->popScope($1); GRAMMARP->endLabel($<fl>4,$1,$4); }
	|	seq_blockFront /**/		 yEND endLabelE	{ $$=$1; SYMP->popScope($1); GRAMMARP->endLabel($<fl>3,$1,$3); }
	;

seq_blockFront<beginp>:		// IEEE: part of par_block
		yBEGIN					 { $$ = new AstBegin($1,"",NULL);  SYMP->pushNew($$); }
	|	yBEGIN ':' idAny/*new-block_identifier*/ { $$ = new AstBegin($1,*$3,NULL); SYMP->pushNew($$); }
	;

blockDeclStmtList<nodep>:	// IEEE: { block_item_declaration } { statement or null }
	//			// The spec seems to suggest a empty declaration isn't ok, but most simulators take it
		block_item_declarationList		{ $$ = $1; }
	|	block_item_declarationList stmtList	{ $$ = $1->addNextNull($2); }
	|	stmtList				{ $$ = $1; }
	;

block_item_declarationList<nodep>:	// IEEE: [ block_item_declaration ]
		block_item_declaration			{ $$ = $1; }
	|	block_item_declarationList block_item_declaration	{ $$ = $1->addNextNull($2); }
	;

block_item_declaration<nodep>:	// ==IEEE: block_item_declaration
		data_declaration 			{ $$ = $1; }
	|	local_parameter_declaration ';'		{ $$ = $1; }
	|	parameter_declaration ';' 		{ $$ = $1; }
	//UNSUP	overload_declaration 			{ $$ = $1; }
	//UNSUP	let_declaration 			{ $$ = $1; }
	;

stmtList<nodep>:
		stmtBlock				{ $$ = $1; }
	|	stmtList stmtBlock			{ $$ = ($2==NULL)?($1):($1->addNext($2)); }
	;

stmt<nodep>:			// IEEE: statement_or_null == function_statement_or_null
		statement_item				{ }
	//UNSUP: Labeling any statement
	|	labeledStmt				{ $$ = $1; }
	|	id ':' labeledStmt			{ $$ = new AstBegin($2, *$1, $3); }  /*S05 block creation rule*/
	//			// from _or_null
	|	';'					{ $$ = NULL; }
	;

statement_item<nodep>:		// IEEE: statement_item
	//			// IEEE: operator_assignment
		foperator_assignment ';'		{ $$ = $1; }
	//
	//		 	// IEEE: blocking_assignment
	//			// 1800-2009 restricts LHS of assignment to new to not have a range
	//			// This is ignored to avoid conflicts
	//UNSUP	fexprLvalue '=' class_new ';'		{ UNSUP }
	//UNSUP	fexprLvalue '=' dynamic_array_new ';'	{ UNSUP }
	//
	//			// IEEE: nonblocking_assignment
	|	fexprLvalue yP_LTE delayE expr ';'	{ $$ = new AstAssignDly($2,$1,$4); }
	//UNSUP	fexprLvalue yP_LTE delay_or_event_controlE expr ';'	{ UNSUP }
	//
	//			// IEEE: procedural_continuous_assignment
	|	yASSIGN idClassSel '=' delayE expr ';'	{ $$ = new AstAssign($1,$2,$5); }
	//UNSUP:			delay_or_event_controlE above
	//UNSUP	yDEASSIGN variable_lvalue ';'		{ UNSUP }
	//UNSUP	yFORCE expr '=' expr ';'		{ UNSUP }
	//UNSUP	yRELEASE variable_lvalue ';'		{ UNSUP }
	//
	//			// IEEE: case_statement
	|	unique_priorityE caseStart caseAttrE case_itemListE yENDCASE	{ $$ = $2; if ($4) $2->addItemsp($4);
							  if ($1 == uniq_UNIQUE) $2->uniquePragma(true);
							  if ($1 == uniq_UNIQUE0) $2->unique0Pragma(true);
							  if ($1 == uniq_PRIORITY) $2->priorityPragma(true); }
	//UNSUP	caseStart caseAttrE yMATCHES case_patternListE yENDCASE	{ }
	|	unique_priorityE caseStart caseAttrE yINSIDE case_insideListE yENDCASE	{ $$ = $2; if ($5) $2->addItemsp($5);
							  if (!$2->caseSimple()) $2->v3error("Illegal to have inside on a casex/casez");
							  $2->caseInsideSet();
							  if ($1 == uniq_UNIQUE) $2->uniquePragma(true);
							  if ($1 == uniq_UNIQUE0) $2->unique0Pragma(true);
							  if ($1 == uniq_PRIORITY) $2->priorityPragma(true); }
	//
	//			// IEEE: conditional_statement
	|	unique_priorityE yIF '(' expr ')' stmtBlock	%prec prLOWER_THAN_ELSE
							{ $$ = new AstIf($2,$4,$6,NULL);
							  if ($1 == uniq_UNIQUE) $$->castIf()->uniquePragma(true);
							  if ($1 == uniq_UNIQUE0) $$->castIf()->unique0Pragma(true);
							  if ($1 == uniq_PRIORITY) $$->castIf()->priorityPragma(true); }
	|	unique_priorityE yIF '(' expr ')' stmtBlock yELSE stmtBlock
							{ $$ = new AstIf($2,$4,$6,$8);
							  if ($1 == uniq_UNIQUE) $$->castIf()->uniquePragma(true);
							  if ($1 == uniq_UNIQUE0) $$->castIf()->unique0Pragma(true);
							  if ($1 == uniq_PRIORITY) $$->castIf()->priorityPragma(true); }
	//
	|	finc_or_dec_expression ';'		{ $$ = $1; }
	//			// IEEE: inc_or_dec_expression
	//			// Below under expr
	//
	//			// IEEE: subroutine_call_statement
	//UNSUP	yVOID yP_TICK '(' function_subroutine_callNoMethod ')' ';' { }
	//UNSUP	yVOID yP_TICK '(' expr '.' function_subroutine_callNoMethod ')' ';' { }
	//			// Expr included here to resolve our not knowing what is a method call
	//			// Expr here must result in a subroutine_call
	|	task_subroutine_callNoMethod ';'	{ $$ = $1; }
	//UNSUP	fexpr '.' array_methodNoRoot ';'	{ UNSUP }
	|	fexpr '.' task_subroutine_callNoMethod ';'	{ $$ = new AstDot($<fl>2,$1,$3); }
	//UNSUP	fexprScope ';'				{ UNSUP }
	//			// Not here in IEEE; from class_constructor_declaration
	//			// Because we've joined class_constructor_declaration into generic functions
	//			// Way over-permissive;
	//			// IEEE: [ ySUPER '.' yNEW [ '(' list_of_arguments ')' ] ';' ]
	//UNSUP	fexpr '.' class_new ';'		{ }
	//
	|	statementVerilatorPragmas			{ $$ = $1; }
	//
	//			// IEEE: disable_statement
	|	yDISABLE idAny/*hierarchical_identifier-task_or_block*/ ';'	{ $$ = new AstDisable($1,*$2); }
	//UNSUP	yDISABLE yFORK ';'			{ UNSUP }
	//			// IEEE: event_trigger
	//UNSUP	yP_MINUSGT hierarchical_identifier/*event*/ ';'	{ UNSUP }
	//UNSUP	yP_MINUSGTGT delay_or_event_controlE hierarchical_identifier/*event*/ ';'	{ UNSUP }
	//			// IEEE: loop_statement
	|	yFOREVER stmtBlock			{ $$ = new AstWhile($1,new AstConst($1,AstConst::LogicTrue()),$2); }
	|	yREPEAT '(' expr ')' stmtBlock		{ $$ = new AstRepeat($1,$3,$5);}
	|	yWHILE '(' expr ')' stmtBlock		{ $$ = new AstWhile($1,$3,$5);}
	//			// for's first ';' is in for_initalization
	|	yFOR '(' for_initialization expr ';' for_stepE ')' stmtBlock
							{ $$ = new AstBegin($1,"",$3); $3->addNext(new AstWhile($1, $4,$8,$6)); }
	|	yDO stmtBlock yWHILE '(' expr ')' ';'	{ $$ = $2->cloneTree(true); $$->addNext(new AstWhile($1,$5,$2));}
	//			// IEEE says array_identifier here, but dotted accepted in VMM and 1800-2009
	//UNSUP	yFOREACH '(' idClassForeach/*array_id[loop_variables]*/ ')' stmt	{ UNSUP }
	//
	//			// IEEE: jump_statement
	|	yRETURN ';'				{ $$ = new AstReturn($1); }
	|	yRETURN expr ';'			{ $$ = new AstReturn($1,$2); }
	|	yBREAK ';'				{ $$ = new AstBreak($1); }
	|	yCONTINUE ';'				{ $$ = new AstContinue($1); }
	//
	//UNSUP	par_block				{ $$ = $1; }
	//			// IEEE: procedural_timing_control_statement + procedural_timing_control
	|	delay_control stmtBlock			{ $$ = $2; $1->v3warn(STMTDLY,"Unsupported: Ignoring delay on this delayed statement."); }
	//UNSUP	event_control stmtBlock			{ UNSUP }
	//UNSUP	cycle_delay stmtBlock			{ UNSUP }
	//
	|	seq_block				{ $$ = $1; }
	//
	//			// IEEE: wait_statement
	//UNSUP	yWAIT '(' expr ')' stmtBlock		{ UNSUP }
	//UNSUP	yWAIT yFORK ';'				{ UNSUP }
	//UNSUP	yWAIT_ORDER '(' hierarchical_identifierList ')' action_block	{ UNSUP }
	//
	//			// IEEE: procedural_assertion_statement
	//			// Verilator: Label included instead
	|	concurrent_assertion_item		{ $$ = $1; }
	//			// concurrent_assertion_statement { $$ = $1; }
	//			// Verilator: Part of labeledStmt instead
	//			// immediate_assert_statement	{ UNSUP }
	//
	//			// IEEE: clocking_drive ';'
	//			// Pattern w/o cycle_delay handled by nonblocking_assign above
	//			// clockvar_expression made to fexprLvalue to prevent reduce conflict
	//			// Note LTE in this context is highest precedence, so first on left wins
	//UNSUP	cycle_delay fexprLvalue yP_LTE ';'	{ UNSUP }
	//UNSUP	fexprLvalue yP_LTE cycle_delay expr ';'	{ UNSUP }
	//
	//UNSUP	randsequence_statement			{ $$ = $1; }
	//
	//			// IEEE: randcase_statement
	//UNSUP	yRANDCASE case_itemList yENDCASE	{ UNSUP }
	//
	//UNSUP	expect_property_statement		{ $$ = $1; }
	//
	|	error ';'				{ $$ = NULL; }
	;

statementVerilatorPragmas<nodep>:
		yVL_COVERAGE_BLOCK_OFF			{ $$ = new AstPragma($1,AstPragmaType::COVERAGE_BLOCK_OFF); }
	;

foperator_assignment<nodep>:	// IEEE: operator_assignment (for first part of expression)
		fexprLvalue '=' delayE expr	{ $$ = new AstAssign($2,$1,$4); }
	|	fexprLvalue '=' yD_FOPEN '(' expr ')'		{ $$ = NULL; $3->v3error("Unsupported: $fopen with multichannel descriptor.  Add ,\"w\" as second argument to open a file descriptor."); }
	|	fexprLvalue '=' yD_FOPEN '(' expr ',' expr ')'	{ $$ = new AstFOpen($3,$1,$5,$7); }
	//
	//UNSUP	~f~exprLvalue '=' delay_or_event_controlE expr { UNSUP }
	//UNSUP	~f~exprLvalue yP_PLUS(etc) expr		{ UNSUP }
	|	fexprLvalue yP_PLUSEQ    expr		{ $$ = new AstAssign($2,$1,new AstAdd    ($2,$1->cloneTree(true),$3)); }
	|	fexprLvalue yP_MINUSEQ   expr		{ $$ = new AstAssign($2,$1,new AstSub    ($2,$1->cloneTree(true),$3)); }
	|	fexprLvalue yP_TIMESEQ   expr		{ $$ = new AstAssign($2,$1,new AstMul    ($2,$1->cloneTree(true),$3)); }
	|	fexprLvalue yP_DIVEQ     expr		{ $$ = new AstAssign($2,$1,new AstDiv    ($2,$1->cloneTree(true),$3)); }
	|	fexprLvalue yP_MODEQ     expr		{ $$ = new AstAssign($2,$1,new AstModDiv ($2,$1->cloneTree(true),$3)); }
	|	fexprLvalue yP_ANDEQ     expr		{ $$ = new AstAssign($2,$1,new AstAnd    ($2,$1->cloneTree(true),$3)); }
	|	fexprLvalue yP_OREQ      expr		{ $$ = new AstAssign($2,$1,new AstOr     ($2,$1->cloneTree(true),$3)); }
	|	fexprLvalue yP_XOREQ     expr		{ $$ = new AstAssign($2,$1,new AstXor    ($2,$1->cloneTree(true),$3)); }
	|	fexprLvalue yP_SLEFTEQ   expr		{ $$ = new AstAssign($2,$1,new AstShiftL ($2,$1->cloneTree(true),$3)); }
	|	fexprLvalue yP_SRIGHTEQ  expr		{ $$ = new AstAssign($2,$1,new AstShiftR ($2,$1->cloneTree(true),$3)); }
	|	fexprLvalue yP_SSRIGHTEQ expr		{ $$ = new AstAssign($2,$1,new AstShiftRS($2,$1->cloneTree(true),$3)); }
	;

finc_or_dec_expression<nodep>:	// ==IEEE: inc_or_dec_expression
	//UNSUP: Generic scopes in incrementes
		fexprLvalue yP_PLUSPLUS			{ $$ = new AstAssign($2,$1,new AstAdd    ($2,$1->cloneTree(true),new AstConst($2,V3Number($2,"'b1")))); }
	|	fexprLvalue yP_MINUSMINUS		{ $$ = new AstAssign($2,$1,new AstSub    ($2,$1->cloneTree(true),new AstConst($2,V3Number($2,"'b1")))); }
	|	yP_PLUSPLUS   fexprLvalue		{ $$ = new AstAssign($1,$2,new AstAdd    ($1,$2->cloneTree(true),new AstConst($1,V3Number($1,"'b1")))); }
	|	yP_MINUSMINUS fexprLvalue		{ $$ = new AstAssign($1,$2,new AstSub    ($1,$2->cloneTree(true),new AstConst($1,V3Number($1,"'b1")))); }
	;

//************************************************
// Case/If

unique_priorityE<uniqstate>:	// IEEE: unique_priority + empty
		/*empty*/				{ $$ = uniq_NONE; }
	|	yPRIORITY				{ $$ = uniq_PRIORITY; }
	|	yUNIQUE					{ $$ = uniq_UNIQUE; }
	|	yUNIQUE0				{ $$ = uniq_UNIQUE0; }
	;

caseStart<casep>:		// IEEE: part of case_statement
	 	yCASE  '(' expr ')' 			{ $$ = GRAMMARP->m_caseAttrp = new AstCase($1,VCaseType::CT_CASE,$3,NULL); }
	|	yCASEX '(' expr ')' 			{ $$ = GRAMMARP->m_caseAttrp = new AstCase($1,VCaseType::CT_CASEX,$3,NULL); }
	|	yCASEZ '(' expr ')'			{ $$ = GRAMMARP->m_caseAttrp = new AstCase($1,VCaseType::CT_CASEZ,$3,NULL); }
	;

caseAttrE:
	 	/*empty*/				{ }
	|	caseAttrE yVL_FULL_CASE			{ GRAMMARP->m_caseAttrp->fullPragma(true); }
	|	caseAttrE yVL_PARALLEL_CASE		{ GRAMMARP->m_caseAttrp->parallelPragma(true); }
	;

case_itemListE<caseitemp>:	// IEEE: [ { case_item } ]
		/* empty */				{ $$ = NULL; }
	|	case_itemList				{ $$ = $1; }
	;

case_insideListE<caseitemp>:	// IEEE: [ { case_inside_item } ]
		/* empty */				{ $$ = NULL; }
	|	case_inside_itemList			{ $$ = $1; }
	;

case_itemList<caseitemp>:	// IEEE: { case_item + ... }
		caseCondList ':' stmtBlock		{ $$ = new AstCaseItem($2,$1,$3); }
	|	yDEFAULT ':' stmtBlock			{ $$ = new AstCaseItem($2,NULL,$3); }
	|	yDEFAULT stmtBlock			{ $$ = new AstCaseItem($1,NULL,$2); }
	|	case_itemList caseCondList ':' stmtBlock	{ $$ = $1;$1->addNext(new AstCaseItem($3,$2,$4)); }
	|       case_itemList yDEFAULT stmtBlock		{ $$ = $1;$1->addNext(new AstCaseItem($2,NULL,$3)); }
	|	case_itemList yDEFAULT ':' stmtBlock		{ $$ = $1;$1->addNext(new AstCaseItem($3,NULL,$4)); }
	;

case_inside_itemList<caseitemp>:	// IEEE: { case_inside_item + open_range_list ... }
		open_range_list ':' stmtBlock		{ $$ = new AstCaseItem($2,$1,$3); }
	|	yDEFAULT ':' stmtBlock			{ $$ = new AstCaseItem($2,NULL,$3); }
	|	yDEFAULT stmtBlock			{ $$ = new AstCaseItem($1,NULL,$2); }
	|	case_inside_itemList open_range_list ':' stmtBlock { $$ = $1;$1->addNext(new AstCaseItem($3,$2,$4)); }
	|       case_inside_itemList yDEFAULT stmtBlock		{ $$ = $1;$1->addNext(new AstCaseItem($2,NULL,$3)); }
	|	case_inside_itemList yDEFAULT ':' stmtBlock	{ $$ = $1;$1->addNext(new AstCaseItem($3,NULL,$4)); }
	;

open_range_list<nodep>:		// ==IEEE: open_range_list + open_value_range
		open_value_range			{ $$ = $1; }
	|	open_range_list ',' open_value_range	{ $$ = $1;$1->addNext($3); }
	;

open_value_range<nodep>:	// ==IEEE: open_value_range
		value_range				{ $$ = $1; }
	;

value_range<nodep>:		// ==IEEE: value_range
		expr					{ $$ = $1; }
	|	'[' expr ':' expr ']'			{ $$ = new AstInsideRange($3,$2,$4); }
	;

caseCondList<nodep>:		// IEEE: part of case_item
		expr 					{ $$ = $1; }
	|	caseCondList ',' expr			{ $$ = $1;$1->addNext($3); }
	;

patternNoExpr<nodep>:		// IEEE: pattern **Excluding Expr*
		'.' id/*variable*/			{ $1->v3error("Unsupported: '{} tagged patterns"); $$=NULL; }
	|	yP_DOTSTAR				{ $1->v3error("Unsupported: '{} tagged patterns"); $$=NULL; }
	//			// IEEE: "expr" excluded; expand in callers
	//			// "yTAGGED id [expr]" Already part of expr
	//UNSUP	yTAGGED id/*member_identifier*/ patternNoExpr		{ $1->v3error("Unsupported: '{} tagged patterns"); $$=NULL; }
	//			// "yP_TICKBRA patternList '}'" part of expr under assignment_pattern
	;

patternList<nodep>:		// IEEE: part of pattern
		patternOne				{ $$ = $1; }
	|	patternList ',' patternOne		{ $$ = $1->addNextNull($3); }
	;

patternOne<nodep>:		// IEEE: part of pattern
		expr					{ $$ = new AstPatMember($1->fileline(),$1,NULL,NULL); }
	|	expr '{' argsExprList '}'		{ $$ = new AstPatMember($2,$3,NULL,$1); }
	|	patternNoExpr				{ $$ = $1; }
	;

patternMemberList<nodep>:	// IEEE: part of pattern and assignment_pattern
		patternMemberOne			{ $$ = $1; }
	|	patternMemberList ',' patternMemberOne	{ $$ = $1->addNextNull($3); }
	;

patternMemberOne<patmemberp>:	// IEEE: part of pattern and assignment_pattern
		patternKey ':' expr			{ $$ = new AstPatMember($2,$3,$1,NULL); }
	|	patternKey ':' patternNoExpr		{ $2->v3error("Unsupported: '{} .* patterns"); $$=NULL; }
	//			// From assignment_pattern_key
	|	yDEFAULT ':' expr			{ $$ = new AstPatMember($2,$3,NULL,NULL); $$->isDefault(true); }
	|	yDEFAULT ':' patternNoExpr		{ $2->v3error("Unsupported: '{} .* patterns"); $$=NULL; }
	;

patternKey<nodep>:		// IEEE: merge structure_pattern_key, array_pattern_key, assignment_pattern_key
	//			// IEEE: structure_pattern_key
	//			// id/*member*/ is part of constExpr below
	//UNSUP	constExpr				{ $$ = $1; }
	//			// IEEE: assignment_pattern_key
	//UNSUP	simple_type				{ $1->v3error("Unsupported: '{} with data type as key"); $$=$1; }
	//			// simple_type reference looks like constExpr
	//			// Verilator:
	//			//   The above expressions cause problems because "foo" may be a constant identifier
	//			//   (if array) or a reference to the "foo"member (if structure)
	//			//   So for now we only allow a true constant number, or a identifier which we treat as a structure member name
		yaINTNUM				{ $$ = new AstConst($<fl>1,*$1); }
	|	yaFLOATNUM				{ $$ = new AstConst($<fl>1,AstConst::RealDouble(),$1); }
	|	yaID__ETC				{ $$ = new AstText($<fl>1,*$1); }
	;

assignment_pattern<patternp>:	// ==IEEE: assignment_pattern
	// This doesn't match the text of the spec.  I think a : is missing, or example code needed
	// yP_TICKBRA constExpr exprList '}'	{ $$="'{"+$2+" "+$3"}"; }
	//			// "'{ const_expression }" is same as patternList with one entry
	//			// From patternNoExpr
	//			// also IEEE: "''{' expression { ',' expression } '}'"
	//			//      matches since patternList includes expr
		yP_TICKBRA patternList '}'		{ $$ = new AstPattern($1,$2); }
	//			// From patternNoExpr
	//			// also IEEE "''{' structure_pattern_key ':' ...
	//			// also IEEE "''{' array_pattern_key ':' ...
	|	yP_TICKBRA patternMemberList '}'	{ $$ = new AstPattern($1,$2); }
	//			// IEEE: Not in grammar, but in VMM
	|	yP_TICKBRA '}'				{ $1->v3error("Unsupported: Empty '{}"); $$=NULL; }
	;

// "datatype id = x {, id = x }"  |  "yaId = x {, id=x}" is legal
for_initialization<nodep>:	// ==IEEE: for_initialization + for_variable_declaration + extra terminating ";"
	//			// IEEE: for_variable_declaration
		data_type idAny/*new*/ '=' expr ';'
			{ VARRESET_NONLIST(VAR); VARDTYPE($1);
			  $$ = VARDONEA($<fl>2,*$2,NULL,NULL);
			  $$->addNext(new AstAssign($3,new AstVarRef($3,*$2,true),$4));}
	|	varRefBase '=' expr ';'			{ $$ = new AstAssign($2,$1,$3); }
	//UNSUP: List of initializations
	;

for_stepE<nodep>:		// IEEE: for_step + empty
		/* empty */				{ $$ = NULL; }
	|	for_step				{ $$ = $1; }
	;

for_step<nodep>:		// IEEE: for_step
	//UNSUP: List of steps, instead we keep it simple
		genvar_iteration			{ $$ = $1; }
	;

//************************************************
// Functions/tasks

taskRef<nodep>:			// IEEE: part of tf_call
		id		 		{ $$ = new AstTaskRef($<fl>1,*$1,NULL); }
	|	id '(' list_of_argumentsE ')'	{ $$ = new AstTaskRef($<fl>1,*$1,$3); }
	|	package_scopeIdFollows id '(' list_of_argumentsE ')'	{ $$ = AstDot::newIfPkg($<fl>2, $1, new AstTaskRef($<fl>2,*$2,$4)); }
	;

funcRef<nodep>:			// IEEE: part of tf_call
	//			// package_scope/hierarchical_... is part of expr, so just need ID
	//			//	making-a		id-is-a
	//			//	-----------------	------------------
	//			//      tf_call			tf_identifier		expr (list_of_arguments)
	//			//      method_call(post .)	function_identifier	expr (list_of_arguments)
	//			//	property_instance	property_identifier	property_actual_arg
	//			//	sequence_instance	sequence_identifier	sequence_actual_arg
	//			//      let_expression		let_identifier		let_actual_arg
	//
		id '(' list_of_argumentsE ')'		{ $$ = new AstFuncRef($2, *$1, $3); }
	|	package_scopeIdFollows id '(' list_of_argumentsE ')'	{ $$ = AstDot::newIfPkg($<fl>2, $1, new AstFuncRef($<fl>2,*$2,$4)); }
	//UNSUP: idDotted is really just id to allow dotted method calls
	;

task_subroutine_callNoMethod<nodep>:	// function_subroutine_callNoMethod (as task)
	//			// IEEE: tf_call
		taskRef					{ $$ = $1; }
	|	system_t_call				{ $$ = $1; }
	//			// IEEE: method_call requires a "." so is in expr
	//UNSUP	randomize_call 				{ $$ = $1; }
	;

function_subroutine_callNoMethod<nodep>:	// IEEE: function_subroutine_call (as function)
	//			// IEEE: tf_call
		funcRef					{ $$ = $1; }
	|	system_f_call				{ $$ = $1; }
	//			// IEEE: method_call requires a "." so is in expr
	//UNSUP	randomize_call 				{ $$ = $1; }
	;

system_t_call<nodep>:		// IEEE: system_tf_call (as task)
	//
		yaD_IGNORE  parenE			{ $$ = new AstSysIgnore($<fl>1,NULL); }
	|	yaD_IGNORE  '(' exprList ')'		{ $$ = new AstSysIgnore($<fl>1,$3); }
	//
	|	yaD_DPI parenE				{ $$ = new AstTaskRef($<fl>1,*$1,NULL); }
	|	yaD_DPI '(' exprList ')'		{ $$ = new AstTaskRef($2,*$1,$3); GRAMMARP->argWrapList($$->castTaskRef()); }
	//
	|	yD_C '(' cStrList ')'			{ $$ = (v3Global.opt.ignc() ? NULL : new AstUCStmt($1,$3)); }
	|	yD_FCLOSE '(' idClassSel ')'		{ $$ = new AstFClose($1, $3); }
	|	yD_FFLUSH parenE			{ $1->v3error("Unsupported: $fflush of all handles does not map to C++."); }
	|	yD_FFLUSH '(' idClassSel ')'		{ $$ = new AstFFlush($1, $3); }
	|	yD_FINISH parenE			{ $$ = new AstFinish($1); }
	|	yD_FINISH '(' expr ')'			{ $$ = new AstFinish($1); DEL($3); }
	|	yD_STOP parenE				{ $$ = new AstStop($1); }
	|	yD_STOP '(' expr ')'			{ $$ = new AstStop($1); DEL($3); }
	//
	|	yD_SFORMAT '(' expr ',' str commaEListE ')'	{ $$ = new AstSFormat($1,$3,*$5,$6); }
	|	yD_SWRITE  '(' expr ',' str commaEListE ')'	{ $$ = new AstSFormat($1,$3,*$5,$6); }
	|	yD_SYSTEM  '(' expr ')'				{ $$ = new AstSystemT($1,$3); }
	//
	|	yD_DISPLAY  parenE					{ $$ = new AstDisplay($1,AstDisplayType::DT_DISPLAY,"", NULL,NULL); }
	|	yD_DISPLAY  '(' str commaEListE ')'			{ $$ = new AstDisplay($1,AstDisplayType::DT_DISPLAY,*$3,NULL,$4); }
	|	yD_WRITE    parenE					{ $$ = NULL; } // NOP
	|	yD_WRITE    '(' str commaEListE ')'			{ $$ = new AstDisplay($1,AstDisplayType::DT_WRITE,  *$3,NULL,$4); }
	|	yD_FDISPLAY '(' idClassSel ')'			 	{ $$ = new AstDisplay($1,AstDisplayType::DT_DISPLAY,"",$3,NULL); }
	|	yD_FDISPLAY '(' idClassSel ',' str commaEListE ')' 	{ $$ = new AstDisplay($1,AstDisplayType::DT_DISPLAY,*$5,$3,$6); }
	|	yD_FWRITE   '(' idClassSel ',' str commaEListE ')'	{ $$ = new AstDisplay($1,AstDisplayType::DT_WRITE,  *$5,$3,$6); }
	|	yD_INFO	    parenE					{ $$ = new AstDisplay($1,AstDisplayType::DT_INFO,   "", NULL,NULL); }
	|	yD_INFO	    '(' str commaEListE ')'			{ $$ = new AstDisplay($1,AstDisplayType::DT_INFO,   *$3,NULL,$4); }
	|	yD_WARNING  parenE					{ $$ = new AstDisplay($1,AstDisplayType::DT_WARNING,"", NULL,NULL); }
	|	yD_WARNING  '(' str commaEListE ')'			{ $$ = new AstDisplay($1,AstDisplayType::DT_WARNING,*$3,NULL,$4); }
	|	yD_ERROR    parenE					{ $$ = GRAMMARP->createDisplayError($1); }
	|	yD_ERROR    '(' str commaEListE ')'			{ $$ = new AstDisplay($1,AstDisplayType::DT_ERROR,  *$3,NULL,$4);   $$->addNext(new AstStop($1)); }
	|	yD_FATAL    parenE					{ $$ = new AstDisplay($1,AstDisplayType::DT_FATAL,  "", NULL,NULL); $$->addNext(new AstStop($1)); }
	|	yD_FATAL    '(' expr ')'				{ $$ = new AstDisplay($1,AstDisplayType::DT_FATAL,  "", NULL,NULL); $$->addNext(new AstStop($1)); DEL($3); }
	|	yD_FATAL    '(' expr ',' str commaEListE ')'		{ $$ = new AstDisplay($1,AstDisplayType::DT_FATAL,  *$5,NULL,$6);   $$->addNext(new AstStop($1)); DEL($3); }
	//
	|	yD_READMEMB '(' expr ',' idClassSel ')'				{ $$ = new AstReadMem($1,false,$3,$5,NULL,NULL); }
	|	yD_READMEMB '(' expr ',' idClassSel ',' expr ')'		{ $$ = new AstReadMem($1,false,$3,$5,$7,NULL); }
	|	yD_READMEMB '(' expr ',' idClassSel ',' expr ',' expr ')'	{ $$ = new AstReadMem($1,false,$3,$5,$7,$9); }
	|	yD_READMEMH '(' expr ',' idClassSel ')'				{ $$ = new AstReadMem($1,true, $3,$5,NULL,NULL); }
	|	yD_READMEMH '(' expr ',' idClassSel ',' expr ')'		{ $$ = new AstReadMem($1,true, $3,$5,$7,NULL); }
	|	yD_READMEMH '(' expr ',' idClassSel ',' expr ',' expr ')'	{ $$ = new AstReadMem($1,true, $3,$5,$7,$9); }
	;

system_f_call<nodep>:		// IEEE: system_tf_call (as func)
		yaD_IGNORE parenE			{ $$ = new AstConst($<fl>1,V3Number($<fl>1,"'b0")); } // Unsized 0
	|	yaD_IGNORE '(' exprList ')'		{ $$ = new AstConst($2,V3Number($2,"'b0")); } // Unsized 0
	//
	|	yaD_DPI parenE				{ $$ = new AstFuncRef($<fl>1,*$1,NULL); }
	|	yaD_DPI '(' exprList ')'		{ $$ = new AstFuncRef($2,*$1,$3); GRAMMARP->argWrapList($$->castFuncRef()); }
	//
	|	yD_BITS '(' data_type ')'		{ $$ = new AstAttrOf($1,AstAttrType::DIM_BITS,$3); }
	|	yD_BITS '(' data_type ',' expr ')'	{ $$ = new AstAttrOf($1,AstAttrType::DIM_BITS,$3,$5); }
	|	yD_BITS '(' expr ')'			{ $$ = new AstAttrOf($1,AstAttrType::DIM_BITS,$3); }
	|	yD_BITS '(' expr ',' expr ')'		{ $$ = new AstAttrOf($1,AstAttrType::DIM_BITS,$3,$5); }
	|	yD_BITSTOREAL '(' expr ')'		{ $$ = new AstBitsToRealD($1,$3); }
	|	yD_C '(' cStrList ')'			{ $$ = (v3Global.opt.ignc() ? NULL : new AstUCFunc($1,$3)); }
	|	yD_CEIL '(' expr ')'			{ $$ = new AstCeilD($1,$3); }
	|	yD_CLOG2 '(' expr ')'			{ $$ = new AstCLog2($1,$3); }
	|	yD_COUNTONES '(' expr ')'		{ $$ = new AstCountOnes($1,$3); }
	|	yD_DIMENSIONS '(' expr ')'		{ $$ = new AstAttrOf($1,AstAttrType::DIM_DIMENSIONS,$3); }
	|	yD_EXP '(' expr ')'			{ $$ = new AstExpD($1,$3); }
	|	yD_FEOF '(' expr ')'			{ $$ = new AstFEof($1,$3); }
	|	yD_FGETC '(' expr ')'			{ $$ = new AstFGetC($1,$3); }
	|	yD_FGETS '(' idClassSel ',' expr ')'	{ $$ = new AstFGetS($1,$3,$5); }
	|	yD_FLOOR '(' expr ')'			{ $$ = new AstFloorD($1,$3); }
	|	yD_FSCANF '(' expr ',' str commaVRDListE ')'	{ $$ = new AstFScanF($1,*$5,$3,$6); }
	|	yD_HIGH '(' expr ')'			{ $$ = new AstAttrOf($1,AstAttrType::DIM_HIGH,$3,NULL); }
	|	yD_HIGH '(' expr ',' expr ')'		{ $$ = new AstAttrOf($1,AstAttrType::DIM_HIGH,$3,$5); }
	|	yD_INCREMENT '(' expr ')'		{ $$ = new AstAttrOf($1,AstAttrType::DIM_INCREMENT,$3,NULL); }
	|	yD_INCREMENT '(' expr ',' expr ')'	{ $$ = new AstAttrOf($1,AstAttrType::DIM_INCREMENT,$3,$5); }
	|	yD_ISUNKNOWN '(' expr ')'		{ $$ = new AstIsUnknown($1,$3); }
	|	yD_ITOR '(' expr ')'			{ $$ = new AstIToRD($1,$3); }
	|	yD_LEFT '(' expr ')'			{ $$ = new AstAttrOf($1,AstAttrType::DIM_LEFT,$3,NULL); }
	|	yD_LEFT '(' expr ',' expr ')'		{ $$ = new AstAttrOf($1,AstAttrType::DIM_LEFT,$3,$5); }
	|	yD_LN '(' expr ')'			{ $$ = new AstLogD($1,$3); }
	|	yD_LOG10 '(' expr ')'			{ $$ = new AstLog10D($1,$3); }
	|	yD_LOW '(' expr ')'			{ $$ = new AstAttrOf($1,AstAttrType::DIM_LOW,$3,NULL); }
	|	yD_LOW '(' expr ',' expr ')'		{ $$ = new AstAttrOf($1,AstAttrType::DIM_LOW,$3,$5); }
	|	yD_ONEHOT '(' expr ')'			{ $$ = new AstOneHot($1,$3); }
	|	yD_ONEHOT0 '(' expr ')'			{ $$ = new AstOneHot0($1,$3); }
	|	yD_POW '(' expr ',' expr ')'		{ $$ = new AstPowD($1,$3,$5); }
	|	yD_RANDOM '(' expr ')'			{ $1->v3error("Unsupported: Seeding $random doesn't map to C++, use $c(\"srand\")"); }
	|	yD_RANDOM parenE			{ $$ = new AstRand($1); }
	|	yD_REALTIME parenE			{ $$ = new AstTimeD($1); }
	|	yD_REALTOBITS '(' expr ')'		{ $$ = new AstRealToBits($1,$3); }
	|	yD_RIGHT '(' expr ')'			{ $$ = new AstAttrOf($1,AstAttrType::DIM_RIGHT,$3,NULL); }
	|	yD_RIGHT '(' expr ',' expr ')'		{ $$ = new AstAttrOf($1,AstAttrType::DIM_RIGHT,$3,$5); }
	|	yD_RTOI '(' expr ')'			{ $$ = new AstRToIS($1,$3); }
	//|	yD_SFORMATF '(' str commaEListE ')'	{ $$ = new AstSFormatF($1,*$3,false,$4); }  // Have AST, just need testing and debug
	|	yD_SIGNED '(' expr ')'			{ $$ = new AstSigned($1,$3); }
	|	yD_SIZE '(' expr ')'			{ $$ = new AstAttrOf($1,AstAttrType::DIM_SIZE,$3,NULL); }
	|	yD_SIZE '(' expr ',' expr ')'		{ $$ = new AstAttrOf($1,AstAttrType::DIM_SIZE,$3,$5); }
	|	yD_SQRT '(' expr ')'			{ $$ = new AstSqrtD($1,$3); }
	|	yD_SSCANF '(' expr ',' str commaVRDListE ')'	{ $$ = new AstSScanF($1,*$5,$3,$6); }
	|	yD_STIME parenE				{ $$ = new AstSel($1,new AstTime($1),0,32); }
	|	yD_SYSTEM  '(' expr ')'				{ $$ = new AstSystemF($1,$3); }
	|	yD_TESTPLUSARGS '(' str ')'		{ $$ = new AstTestPlusArgs($1,*$3); }
	|	yD_TIME	parenE				{ $$ = new AstTime($1); }
	|	yD_UNPACKED_DIMENSIONS '(' expr ')'	{ $$ = new AstAttrOf($1,AstAttrType::DIM_UNPK_DIMENSIONS,$3); }
	|	yD_UNSIGNED '(' expr ')'		{ $$ = new AstUnsigned($1,$3); }
	|	yD_VALUEPLUSARGS '(' str ',' expr ')'	{ $$ = new AstValuePlusArgs($1,*$3,$5); }
	;

list_of_argumentsE<nodep>:	// IEEE: [list_of_arguments]
		argsDottedList				{ $$ = $1; }
	|	argsExprListE				{ if ($1->castArg() && $1->castArg()->emptyConnectNoNext()) { $1->deleteTree(); $$ = NULL; } // Mis-created when have 'func()'
	/*cont*/					  else $$ = $1; }
	|	argsExprListE ',' argsDottedList	{ $$ = $1->addNextNull($3); }
	;

task_declaration<ftaskp>:	// ==IEEE: task_declaration
		yTASK lifetimeE taskId tfGuts yENDTASK endLabelE
			{ $$ = $3; $$->addStmtsp($4); SYMP->popScope($$);
			  GRAMMARP->endLabel($<fl>6,$$,$6); }
	;

task_prototype<ftaskp>:		// ==IEEE: task_prototype
		yTASK taskId '(' tf_port_listE ')'	{ $$=$2; $$->addStmtsp($4); $$->prototype(true); SYMP->popScope($$); }
	;

function_declaration<ftaskp>:	// IEEE: function_declaration + function_body_declaration
	 	yFUNCTION lifetimeE funcId funcIsolateE tfGuts yENDFUNCTION endLabelE
			{ $$ = $3; $3->attrIsolateAssign($4); $$->addStmtsp($5);
			  SYMP->popScope($$);
			  GRAMMARP->endLabel($<fl>7,$$,$7); }
	;

function_prototype<ftaskp>:	// IEEE: function_prototype
		yFUNCTION funcId '(' tf_port_listE ')'	{ $$=$2; $$->addStmtsp($4); $$->prototype(true); SYMP->popScope($$); }
	;

funcIsolateE<cint>:
		/* empty */		 		{ $$ = 0; }
	|	yVL_ISOLATE_ASSIGNMENTS			{ $$ = 1; }
	;

method_prototype:
		task_prototype				{ }
	|	function_prototype			{ }
	;

lifetimeE:			// IEEE: [lifetime]
		/* empty */		 		{ }
	|	lifetime		 		{ }
	;

lifetime:			// ==IEEE: lifetime
	//			// Note lifetime used by members is instead under memberQual
		ySTATIC			 		{ $1->v3error("Unsupported: Static in this context"); }
	|	yAUTOMATIC		 		{ }
	;

taskId<ftaskp>:
		tfIdScoped
			{ $$ = new AstTask($<fl>1, *$<strp>1, NULL);
			  SYMP->pushNewUnder($$, NULL); }
	;

funcId<ftaskp>:			// IEEE: function_data_type_or_implicit + part of function_body_declaration
	//			// IEEE: function_data_type_or_implicit must be expanded here to prevent conflict
	//			// function_data_type expanded here to prevent conflicts with implicit_type:empty vs data_type:ID
		/**/			tfIdScoped
			{ $$ = new AstFunc ($<fl>1,*$<strp>1,NULL,
					    new AstBasicDType($<fl>1, LOGIC_IMPLICIT));
			  SYMP->pushNewUnder($$, NULL); }
	|	signingE rangeList	tfIdScoped
			{ $$ = new AstFunc ($<fl>3,*$<strp>3,NULL,
					    GRAMMARP->addRange(new AstBasicDType($<fl>3, LOGIC_IMPLICIT, $1), $2,true));
			  SYMP->pushNewUnder($$, NULL); }
	|	signing			tfIdScoped
			{ $$ = new AstFunc ($<fl>2,*$<strp>2,NULL,
					    new AstBasicDType($<fl>2, LOGIC_IMPLICIT, $1));
			  SYMP->pushNewUnder($$, NULL); }
	|	data_type		tfIdScoped
			{ $$ = new AstFunc ($<fl>2,*$<strp>2,NULL,$1);
			  SYMP->pushNewUnder($$, NULL); }
	//			// To verilator tasks are the same as void functions (we separately detect time passing)
	|	yVOID			tfIdScoped
			{ $$ = new AstTask ($<fl>2,*$<strp>2,NULL);
			  SYMP->pushNewUnder($$, NULL); }
	;

tfIdScoped<strp>:		// IEEE: part of function_body_declaration/task_body_declaration
 	//			// IEEE: [ interface_identifier '.' | class_scope ] function_identifier
		id					{ $<fl>$=$<fl>1; $<strp>$ = $1; }
	//UNSUP	id/*interface_identifier*/ '.' id	{ UNSUP }
	//UNSUP	class_scope_id				{ UNSUP }
	;

tfGuts<nodep>:
		'(' tf_port_listE ')' ';' tfBodyE	{ $$ = $2->addNextNull($5); }
	|	';' tfBodyE				{ $$ = $2; }
	;

tfBodyE<nodep>:			// IEEE: part of function_body_declaration/task_body_declaration
		/* empty */				{ $$ = NULL; }
	|	tf_item_declarationList			{ $$ = $1; }
	|	tf_item_declarationList stmtList	{ $$ = $1->addNextNull($2); }
	|	stmtList				{ $$ = $1; }
	;

tf_item_declarationList<nodep>:
		tf_item_declaration			{ $$ = $1; }
	|	tf_item_declarationList tf_item_declaration	{ $$ = $1->addNextNull($2); }
	;

tf_item_declaration<nodep>:	// ==IEEE: tf_item_declaration
		block_item_declaration			{ $$ = $1; }
	|	tf_port_declaration			{ $$ = $1; }
	|	tf_item_declarationVerilator		{ $$ = $1; }
	;

tf_item_declarationVerilator<nodep>:	// Verilator extensions
		yVL_PUBLIC				{ $$ = new AstPragma($1,AstPragmaType::PUBLIC_TASK); v3Global.dpi(true); }
	|	yVL_NO_INLINE_TASK			{ $$ = new AstPragma($1,AstPragmaType::NO_INLINE_TASK); }
	;

tf_port_listE<nodep>:		// IEEE: tf_port_list + empty
	//			// Empty covered by tf_port_item
		{VARRESET_LIST(UNKNOWN); VARIO(INPUT); }
			tf_port_listList		{ $$ = $2; VARRESET_NONLIST(UNKNOWN); }
	;

tf_port_listList<nodep>:	// IEEE: part of tf_port_list
		tf_port_item				{ $$ = $1; }
	|	tf_port_listList ',' tf_port_item	{ $$ = $1->addNextNull($3); }
	;

tf_port_item<nodep>:		// ==IEEE: tf_port_item
	//			// We split tf_port_item into the type and assignment as don't know what follows a comma
		/* empty */				{ $$ = NULL; PINNUMINC(); }	// For example a ",," port
	|	tf_port_itemFront tf_port_itemAssignment { $$ = $2; }
	|	tf_port_itemAssignment 			{ $$ = $1; }
	;

tf_port_itemFront:		// IEEE: part of tf_port_item, which has the data type
		data_type				{ VARDTYPE($1); }
	|	signingE rangeList			{ VARDTYPE(GRAMMARP->addRange(new AstBasicDType($2->fileline(), LOGIC_IMPLICIT, $1), $2, true)); }
	|	signing					{ VARDTYPE(new AstBasicDType($<fl>1, LOGIC_IMPLICIT, $1)); }
	|	yVAR data_type				{ VARDTYPE($2); }
	|	yVAR implicit_typeE			{ VARDTYPE($2); }
	//
	|	tf_port_itemDir /*implicit*/		{ VARDTYPE(NULL); /*default_nettype-see spec*/ }
	|	tf_port_itemDir data_type		{ VARDTYPE($2); }
	|	tf_port_itemDir signingE rangeList	{ VARDTYPE(GRAMMARP->addRange(new AstBasicDType($3->fileline(), LOGIC_IMPLICIT, $2),$3,true)); }
	|	tf_port_itemDir signing			{ VARDTYPE(new AstBasicDType($<fl>2, LOGIC_IMPLICIT, $2)); }
	|	tf_port_itemDir yVAR data_type		{ VARDTYPE($3); }
	|	tf_port_itemDir yVAR implicit_typeE	{ VARDTYPE($3); }
	;

tf_port_itemDir:		// IEEE: part of tf_port_item, direction
		port_direction				{ }  // port_direction sets VARIO
	;

tf_port_itemAssignment<varp>:	// IEEE: part of tf_port_item, which has assignment
		id variable_dimensionListE sigAttrListE
			{ $$ = VARDONEA($<fl>1, *$1, $2, $3); }
	|	id variable_dimensionListE sigAttrListE '=' expr
			{ $$ = VARDONEA($<fl>1, *$1, $2, $3); $$->valuep($5); }
	;

parenE:
		/* empty */				{ }
	|	'(' ')'					{ }
	;

//	method_call:		// ==IEEE: method_call + method_call_body
//				// IEEE: method_call_root '.' method_identifier [ '(' list_of_arguments ')' ]
//				//   "method_call_root '.' method_identifier" looks just like "expr '.' id"
//				//   "method_call_root '.' method_identifier (...)" looks just like "expr '.' tf_call"
//				// IEEE: built_in_method_call
//				//   method_call_root not needed, part of expr resolution
//				// What's left is below array_methodNoRoot

dpi_import_export<nodep>:	// ==IEEE: dpi_import_export
		yIMPORT yaSTRING dpi_tf_import_propertyE dpi_importLabelE function_prototype ';'
			{ $$ = $5; if (*$4!="") $5->cname(*$4); $5->dpiContext($3==iprop_CONTEXT); $5->pure($3==iprop_PURE);
			  $5->dpiImport(true); GRAMMARP->checkDpiVer($1,*$2); v3Global.dpi(true);
			  if ($$->prettyName()[0]=='$') SYMP->reinsert($$,NULL,$$->prettyName());  // For $SysTF overriding
			  SYMP->reinsert($$); }
	|	yIMPORT yaSTRING dpi_tf_import_propertyE dpi_importLabelE task_prototype ';'
			{ $$ = $5; if (*$4!="") $5->cname(*$4); $5->dpiContext($3==iprop_CONTEXT); $5->pure($3==iprop_PURE);
			  $5->dpiImport(true); $5->dpiTask(true); GRAMMARP->checkDpiVer($1,*$2); v3Global.dpi(true);
			  if ($$->prettyName()[0]=='$') SYMP->reinsert($$,NULL,$$->prettyName());  // For $SysTF overriding
			  SYMP->reinsert($$); }
	|	yEXPORT yaSTRING dpi_importLabelE yFUNCTION idAny ';'	{ $$ = new AstDpiExport($1,*$5,*$3);
			  GRAMMARP->checkDpiVer($1,*$2); v3Global.dpi(true); }
	|	yEXPORT yaSTRING dpi_importLabelE yTASK     idAny ';'	{ $$ = new AstDpiExport($1,*$5,*$3);
			  GRAMMARP->checkDpiVer($1,*$2); v3Global.dpi(true); }
	;

dpi_importLabelE<strp>:		// IEEE: part of dpi_import_export
		/* empty */				{ static string s = ""; $$ = &s; }
	|	idAny/*c_identifier*/ '='		{ $$ = $1; $<fl>$=$<fl>1; }
	;

dpi_tf_import_propertyE<iprop>:	// IEEE: [ dpi_function_import_property + dpi_task_import_property ]
		/* empty */				{ $$ = iprop_NONE; }
	|	yCONTEXT				{ $$ = iprop_CONTEXT; }
	|	yPURE					{ $$ = iprop_PURE; }
	;

//************************************************
// Expressions
//
// ~l~ means this is the (l)eft hand side of any operator
//     it will get replaced by "", "f" or "s"equence
// ~r~ means this is a (r)ight hand later expansion in the same statement,
//     not under parenthesis for <= disambiguation
//     it will get replaced by "", or "f"
// ~p~ means this is a (p)arenthetized expression
//     it will get replaced by "", or "s"equence

constExpr<nodep>:
		expr					{ $$ = $1; }
	;

expr<nodep>:			// IEEE: part of expression/constant_expression/primary
	// *SEE BELOW*		// IEEE: primary/constant_primary
	//
	//			// IEEE: unary_operator primary
		'+' ~r~expr	%prec prUNARYARITH	{ $$ = $2; }
	|	'-' ~r~expr	%prec prUNARYARITH	{ $$ = new AstNegate	($1,$2); }
	|	'!' ~r~expr	%prec prNEGATION	{ $$ = new AstLogNot	($1,$2); }
	|	'&' ~r~expr	%prec prREDUCTION	{ $$ = new AstRedAnd	($1,$2); }
	|	'~' ~r~expr	%prec prNEGATION	{ $$ = new AstNot	($1,$2); }
	|	'|' ~r~expr	%prec prREDUCTION	{ $$ = new AstRedOr	($1,$2); }
	|	'^' ~r~expr	%prec prREDUCTION	{ $$ = new AstRedXor	($1,$2); }
	|	yP_NAND ~r~expr	%prec prREDUCTION	{ $$ = new AstLogNot($1,new AstRedAnd($1,$2)); }
	|	yP_NOR  ~r~expr	%prec prREDUCTION	{ $$ = new AstLogNot($1,new AstRedOr ($1,$2)); }
	|	yP_XNOR ~r~expr	%prec prREDUCTION	{ $$ = new AstRedXnor	($1,$2); }
	//
	//			// IEEE: inc_or_dec_expression
	//UNSUP	~l~inc_or_dec_expression		{ UNSUP }
	//
	//			// IEEE: '(' operator_assignment ')'
	//			// Need exprScope of variable_lvalue to prevent conflict
	//UNSUP	'(' ~p~exprScope '=' 	      expr ')'	{ UNSUP }
	//UNSUP	'(' ~p~exprScope yP_PLUSEQ    expr ')'	{ UNSUP }
	//UNSUP	'(' ~p~exprScope yP_MINUSEQ   expr ')'	{ UNSUP }
	//UNSUP	'(' ~p~exprScope yP_TIMESEQ   expr ')'	{ UNSUP }
	//UNSUP	'(' ~p~exprScope yP_DIVEQ     expr ')'	{ UNSUP }
	//UNSUP	'(' ~p~exprScope yP_MODEQ     expr ')'	{ UNSUP }
	//UNSUP	'(' ~p~exprScope yP_ANDEQ     expr ')'	{ UNSUP }
	//UNSUP	'(' ~p~exprScope yP_OREQ      expr ')'	{ UNSUP }
	//UNSUP	'(' ~p~exprScope yP_XOREQ     expr ')'	{ UNSUP }
	//UNSUP	'(' ~p~exprScope yP_SLEFTEQ   expr ')'	{ UNSUP }
	//UNSUP	'(' ~p~exprScope yP_SRIGHTEQ  expr ')'	{ UNSUP }
	//UNSUP	'(' ~p~exprScope yP_SSRIGHTEQ expr ')'	{ UNSUP }
	//
	//			// IEEE: expression binary_operator expression
	|	~l~expr '+' ~r~expr			{ $$ = new AstAdd	($2,$1,$3); }
	|	~l~expr '-' ~r~expr			{ $$ = new AstSub	($2,$1,$3); }
	|	~l~expr '*' ~r~expr			{ $$ = new AstMul	($2,$1,$3); }
	|	~l~expr '/' ~r~expr			{ $$ = new AstDiv	($2,$1,$3); }
	|	~l~expr '%' ~r~expr			{ $$ = new AstModDiv	($2,$1,$3); }
	|	~l~expr yP_EQUAL ~r~expr		{ $$ = new AstEq	($2,$1,$3); }
	|	~l~expr yP_NOTEQUAL ~r~expr		{ $$ = new AstNeq	($2,$1,$3); }
	|	~l~expr yP_CASEEQUAL ~r~expr		{ $$ = new AstEqCase	($2,$1,$3); }
	|	~l~expr yP_CASENOTEQUAL ~r~expr		{ $$ = new AstNeqCase	($2,$1,$3); }
	|	~l~expr yP_WILDEQUAL ~r~expr		{ $$ = new AstEqWild	($2,$1,$3); }
	|	~l~expr yP_WILDNOTEQUAL ~r~expr		{ $$ = new AstNeqWild	($2,$1,$3); }
	|	~l~expr yP_ANDAND ~r~expr		{ $$ = new AstLogAnd	($2,$1,$3); }
	|	~l~expr yP_OROR ~r~expr			{ $$ = new AstLogOr	($2,$1,$3); }
	|	~l~expr yP_POW ~r~expr			{ $$ = new AstPow	($2,$1,$3); }
	|	~l~expr '<' ~r~expr			{ $$ = new AstLt	($2,$1,$3); }
	|	~l~expr '>' ~r~expr			{ $$ = new AstGt	($2,$1,$3); }
	|	~l~expr yP_GTE ~r~expr			{ $$ = new AstGte	($2,$1,$3); }
	|	~l~expr '&' ~r~expr			{ $$ = new AstAnd	($2,$1,$3); }
	|	~l~expr '|' ~r~expr			{ $$ = new AstOr	($2,$1,$3); }
	|	~l~expr '^' ~r~expr			{ $$ = new AstXor	($2,$1,$3); }
	|	~l~expr yP_XNOR ~r~expr			{ $$ = new AstXnor	($2,$1,$3); }
	|	~l~expr yP_NOR ~r~expr			{ $$ = new AstNot($2,new AstOr	($2,$1,$3)); }
	|	~l~expr yP_NAND ~r~expr			{ $$ = new AstNot($2,new AstAnd	($2,$1,$3)); }
	|	~l~expr yP_SLEFT ~r~expr		{ $$ = new AstShiftL	($2,$1,$3); }
	|	~l~expr yP_SRIGHT ~r~expr		{ $$ = new AstShiftR	($2,$1,$3); }
	|	~l~expr yP_SSRIGHT ~r~expr		{ $$ = new AstShiftRS	($2,$1,$3); }
	//			// <= is special, as we need to disambiguate it with <= assignment
	//			// We copy all of expr to fexpr and rename this token to a fake one.
	|	~l~expr yP_LTE~f__IGNORE~ ~r~expr	{ $$ = new AstLte	($2,$1,$3); }
	//
	//			// IEEE: conditional_expression
	|	~l~expr '?' ~r~expr ':' ~r~expr		{ $$ = new AstCond($2,$1,$3,$5); }
	//
	//			// IEEE: inside_expression
	|	~l~expr yINSIDE '{' open_range_list '}'	{ $$ = new AstInside($2,$1,$4); }
	//
	//			// IEEE: tagged_union_expression
	//UNSUP	yTAGGED id/*member*/ %prec prTAGGED		{ UNSUP }
	//UNSUP	yTAGGED id/*member*/ %prec prTAGGED expr	{ UNSUP }
	//
	//======================// PSL expressions
	//
	|	~l~expr yP_MINUSGT ~r~expr		{ $$ = new AstLogIf	($2,$1,$3); }
	|	~l~expr yP_LOGIFF ~r~expr		{ $$ = new AstLogIff	($2,$1,$3); }
	//
	//======================// IEEE: primary/constant_primary
	//
	//			// IEEE: primary_literal (minus string, which is handled specially)
	|	yaINTNUM				{ $$ = new AstConst($<fl>1,*$1); }
	|	yaFLOATNUM				{ $$ = new AstConst($<fl>1,AstConst::RealDouble(),$1); }
	//UNSUP	yaTIMENUM				{ UNSUP }
	|	strAsInt~noStr__IGNORE~			{ $$ = $1; }
	//
	//			// IEEE: "... hierarchical_identifier select"  see below
	//
	//			// IEEE: empty_queue
	//UNSUP	'{' '}'
	//
	//			// IEEE: concatenation/constant_concatenation
	//			// Part of exprOkLvalue below
	//
	//			// IEEE: multiple_concatenation/constant_multiple_concatenation
	|	'{' constExpr '{' cateList '}' '}'	{ $$ = new AstReplicate($1,$4,$2); }
	//
	|	function_subroutine_callNoMethod	{ $$ = $1; }
	//			// method_call
	|	~l~expr '.' function_subroutine_callNoMethod	{ $$ = new AstDot($2,$1,$3); }
	//			// method_call:array_method requires a '.'
	//UNSUP	~l~expr '.' array_methodNoRoot		{ UNSUP }
	//
	//			// IEEE: let_expression
	//			// see funcRef
	//
	//			// IEEE: '(' mintypmax_expression ')'
	|	~noPar__IGNORE~'(' expr ')'		{ $$ = $2; }
	//UNSUP	~noPar__IGNORE~'(' expr ':' expr ':' expr ')'	{ $$ = $4; }
	//			// PSL rule
	|	'_' '(' expr ')'			{ $$ = $3; }	// Arbitrary Verilog inside PSL
	//
	//			// IEEE: cast/constant_cast
	|	casting_type yP_TICK '(' expr ')'	{ $$ = new AstCast($2,$4,$1); }
	//			// expanded from casting_type
	|	ySIGNED	     yP_TICK '(' expr ')'	{ $$ = new AstSigned($1,$4); }
	|	yUNSIGNED    yP_TICK '(' expr ')'	{ $$ = new AstUnsigned($1,$4); }
	//			// Spec only allows primary with addition of a type reference
	//			// We'll be more general, and later assert LHS was a type.
	|	~l~expr      yP_TICK '(' expr ')'	{ $$ = new AstCastParse($2,$4,$1); }
	//
	//			// IEEE: assignment_pattern_expression
	//			// IEEE: streaming_concatenation
	//			// See exprOkLvalue
	//
	//			// IEEE: sequence_method_call
	//			// Indistinguishable from function_subroutine_call:method_call
	//
	//UNSUP	'$'					{ UNSUP }
	//UNSUP	yNULL					{ UNSUP }
	//			// IEEE: yTHIS
	//			// See exprScope
	//
	//----------------------
	//
	//			// Part of expr that may also be used as lvalue
	|	~l~exprOkLvalue				{ $$ = $1; }
	//
	//----------------------
	//
	//			// IEEE: cond_predicate - here to avoid reduce problems
	//			// Note expr includes cond_pattern
	//UNSUP	~l~expr yP_ANDANDAND ~r~expr		{ UNSUP }
	//
	//			// IEEE: cond_pattern - here to avoid reduce problems
	//			// "expr yMATCHES pattern"
	//			// IEEE: pattern - expanded here to avoid conflicts
	//UNSUP	~l~expr yMATCHES patternNoExpr		{ UNSUP }
	//UNSUP	~l~expr yMATCHES ~r~expr		{ UNSUP }
	//
	//			// IEEE: expression_or_dist - here to avoid reduce problems
	//			// "expr yDIST '{' dist_list '}'"
	//UNSUP	~l~expr yDIST '{' dist_list '}'		{ UNSUP }
	;

fexpr<nodep>:			// For use as first part of statement (disambiguates <=)
		BISONPRE_COPY(expr,{s/~l~/f/g; s/~r~/f/g; s/~f__IGNORE~/__IGNORE/g;})	// {copied}
	;

exprNoStr<nodep>:		// expression with string removed
		BISONPRE_COPY(expr,{s/~noStr__IGNORE~/Ignore/g;})	// {copied}
	;

exprOkLvalue<nodep>:		// expression that's also OK to use as a variable_lvalue
		~l~exprScope				{ $$ = $1; }
	//			// IEEE: concatenation/constant_concatenation
	//			// Replicate(1) required as otherwise "{a}" would not be self-determined
	|	'{' cateList '}'			{ $$ = new AstReplicate($1,$2,1); }
	//			// IEEE: assignment_pattern_expression
	//			// IEEE: [ assignment_pattern_expression_type ] == [ ps_type_id /ps_paremeter_id/data_type]
	//			// We allow more here than the spec requires
	//UNSUP	~l~exprScope assignment_pattern		{ UNSUP }
	|	data_type assignment_pattern		{ $$ = $2; $2->childDTypep($1); }
	|	assignment_pattern			{ $$ = $1; }
	//
	|	streaming_concatenation			{ $$ = $1; }
	;

fexprOkLvalue<nodep>:		// exprOkLValue, For use as first part of statement (disambiguates <=)
		BISONPRE_COPY(exprOkLvalue,{s/~l~/f/g})	// {copied}
	;

fexprLvalue<nodep>:		// For use as first part of statement (disambiguates <=)
		fexprOkLvalue				{ $<fl>$=$<fl>1; $$ = $1; }
	;

exprScope<nodep>:		// scope and variable for use to inside an expression
	// 			// Here we've split method_call_root | implicit_class_handle | class_scope | package_scope
	//			// from the object being called and let expr's "." deal with resolving it.
	//			// (note method_call_root was simplified to require a primary in 1800-2009)
	//
	//			// IEEE: [ implicit_class_handle . | class_scope | package_scope ] hierarchical_identifier select
	//			// Or method_call_body without parenthesis
	//			// See also varRefClassBit, which is the non-expr version of most of this
	//UNSUP	yTHIS					{ UNSUP }
		idArrayed				{ $$ = $1; }
	|	package_scopeIdFollows idArrayed	{ $$ = AstDot::newIfPkg($2->fileline(), $1, $2); }
	//UNSUP	class_scopeIdFollows idArrayed		{ UNSUP }
	|	~l~expr '.' idArrayed			{ $$ = new AstDot($<fl>2,$1,$3); }
	//			// expr below must be a "yTHIS"
	//UNSUP	~l~expr '.' ySUPER			{ UNSUP }
	//			// Part of implicit_class_handle
	//UNSUP	ySUPER					{ UNSUP }
	;

fexprScope<nodep>:		// exprScope, For use as first part of statement (disambiguates <=)
		BISONPRE_COPY(exprScope,{s/~l~/f/g})	// {copied}
	;

// PLI calls exclude "" as integers, they're strings
// For $c("foo","bar") we want "bar" as a string, not a Verilog integer.
exprStrText<nodep>:
		exprNoStr				{ $$ = $1; }
	|	strAsText				{ $$ = $1; }
	;

cStrList<nodep>:
		exprStrText				{ $$ = $1; }
	|	exprStrText ',' cStrList		{ $$ = $1;$1->addNext($3); }
	;

cateList<nodep>:
	//			// Not just 'expr' to prevent conflict via stream_concOrExprOrType
		stream_expression			{ $$ = $1; }
	|	cateList ',' stream_expression		{ $$ = new AstConcat($2,$1,$3); }
	;

exprList<nodep>:
		expr					{ $$ = $1; }
	|	exprList ',' expr			{ $$ = $1;$1->addNext($3); }
	;

commaEListE<nodep>:
		/* empty */				{ $$ = NULL; }
	|	',' exprList				{ $$ = $2; }
	;

vrdList<nodep>:
		idClassSel				{ $$ = $1; }
	|	vrdList ',' idClassSel			{ $$ = $1;$1->addNext($3); }
	;

commaVRDListE<nodep>:
		/* empty */				{ $$ = NULL; }
	|	',' vrdList				{ $$ = $2; }
	;

argsExprList<nodep>:		// IEEE: part of list_of_arguments (used where ,, isn't legal)
		expr					{ $$ = $1; }
	|	argsExprList ',' expr			{ $$ = $1->addNext($3); }
	;

argsExprListE<nodep>:		// IEEE: part of list_of_arguments
		argsExprOneE				{ $$ = $1; }
	|	argsExprListE ',' argsExprOneE		{ $$ = $1->addNext($3); }
	;

argsExprOneE<nodep>:		// IEEE: part of list_of_arguments
		/*empty*/				{ $$ = new AstArg(CRELINE(),"",NULL); }
	|	expr					{ $$ = new AstArg(CRELINE(),"",$1); }
	;

argsDottedList<nodep>:		// IEEE: part of list_of_arguments
		argsDotted				{ $$ = $1; }
	|	argsDottedList ',' argsDotted		{ $$ = $1->addNextNull($3); }
	;

argsDotted<nodep>:		// IEEE: part of list_of_arguments
		'.' idAny '(' ')'			{ $$ = new AstArg($1,*$2,NULL); }
	|	'.' idAny '(' expr ')'			{ $$ = new AstArg($1,*$2,$4); }
	;

streaming_concatenation<nodep>:	// ==IEEE: streaming_concatenation
	//	 		// Need to disambiguate {<< expr-{ ... expr-} stream_concat }
	//			// From                 {<< stream-{ ... stream-} }
	//			// Likewise simple_type's idScoped from constExpr's idScope
	//			// Thus we allow always any two operations.  Sorry
	//			// IEEE: "'{' yP_SL/R             stream_concatenation '}'"
	//			// IEEE: "'{' yP_SL/R simple_type stream_concatenation '}'"
	//			// IEEE: "'{' yP_SL/R constExpr	  stream_concatenation '}'"
		'{' yP_SLEFT              stream_concOrExprOrType '}'	{ $$ = new AstStreamL($1, $3, new AstConst($1,1)); }
	|	'{' yP_SRIGHT             stream_concOrExprOrType '}'	{ $$ = new AstStreamR($1, $3, new AstConst($1,1)); }
	|	'{' yP_SLEFT  stream_concOrExprOrType stream_concatenation '}'	{ $$ = new AstStreamL($1, $4, $3); }
	|	'{' yP_SRIGHT stream_concOrExprOrType stream_concatenation '}'	{ $$ = new AstStreamR($1, $4, $3); }
	;

stream_concOrExprOrType<nodep>:	// IEEE: stream_concatenation | slice_size:simple_type | slice_size:constExpr
		cateList				{ $$ = $1; }
	|	simple_type				{ $$ = $1; }
	//			// stream_concatenation found via cateList:stream_expr:'{-normal-concat'
	//			// simple_typeRef found via cateList:stream_expr:expr:id
	//			// constant_expression found via cateList:stream_expr:expr
	;

stream_concatenation<nodep>:	// ==IEEE: stream_concatenation
		'{' cateList '}'			{ $$ = $2; }
	;

stream_expression<nodep>:	// ==IEEE: stream_expression
	//			// IEEE: array_range_expression expanded below
		expr					{ $$ = $1; }
	//UNSUP	expr yWITH__BRA '[' expr ']'		{ UNSUP }
	//UNSUP	expr yWITH__BRA '[' expr ':' expr ']'	{ UNSUP }
	//UNSUP	expr yWITH__BRA '[' expr yP_PLUSCOLON  expr ']'	{ UNSUP }
	//UNSUP	expr yWITH__BRA '[' expr yP_MINUSCOLON expr ']'	{ UNSUP }
	;

//************************************************
// Gate declarations

gateDecl<nodep>:
		yBUF    delayE gateBufList ';'		{ $$ = $3; }
	|	yBUFIF0 delayE gateBufif0List ';'	{ $$ = $3; }
	|	yBUFIF1 delayE gateBufif1List ';'	{ $$ = $3; }
	|	yNOT    delayE gateNotList ';'		{ $$ = $3; }
	|	yNOTIF0 delayE gateNotif0List ';'	{ $$ = $3; }
	|	yNOTIF1 delayE gateNotif1List ';'	{ $$ = $3; }
	|	yAND  delayE gateAndList ';'		{ $$ = $3; }
	|	yNAND delayE gateNandList ';'		{ $$ = $3; }
	|	yOR   delayE gateOrList ';'		{ $$ = $3; }
	|	yNOR  delayE gateNorList ';'		{ $$ = $3; }
	|	yXOR  delayE gateXorList ';'		{ $$ = $3; }
	|	yXNOR delayE gateXnorList ';'		{ $$ = $3; }
	|	yPULLUP delayE gatePullupList ';'	{ $$ = $3; }
	|	yPULLDOWN delayE gatePulldownList ';'	{ $$ = $3; }
	|	yNMOS delayE gateBufif1List ';'		{ $$ = $3; }  // ~=bufif1, as don't have strengths yet
	|	yPMOS delayE gateBufif0List ';'		{ $$ = $3; }  // ~=bufif0, as don't have strengths yet
	//
	|	yTRAN delayE gateUnsupList ';'		{ $$ = $3; GATEUNSUP($3,"tran"); } // Unsupported
	|	yRCMOS delayE gateUnsupList ';'		{ $$ = $3; GATEUNSUP($3,"rcmos"); } // Unsupported
	|	yCMOS delayE gateUnsupList ';'		{ $$ = $3; GATEUNSUP($3,"cmos"); } // Unsupported
	|	yRNMOS delayE gateUnsupList ';'		{ $$ = $3; GATEUNSUP($3,"rmos"); } // Unsupported
	|	yRPMOS delayE gateUnsupList ';'		{ $$ = $3; GATEUNSUP($3,"pmos"); } // Unsupported
	|	yRTRAN delayE gateUnsupList ';'		{ $$ = $3; GATEUNSUP($3,"rtran"); } // Unsupported
	|	yRTRANIF0 delayE gateUnsupList ';'	{ $$ = $3; GATEUNSUP($3,"rtranif0"); } // Unsupported
	|	yRTRANIF1 delayE gateUnsupList ';'	{ $$ = $3; GATEUNSUP($3,"rtranif1"); } // Unsupported
	|	yTRANIF0 delayE gateUnsupList ';'	{ $$ = $3; GATEUNSUP($3,"tranif0"); } // Unsupported
	|	yTRANIF1 delayE gateUnsupList ';'	{ $$ = $3; GATEUNSUP($3,"tranif1"); } // Unsupported
	;

gateBufList<nodep>:
		gateBuf 				{ $$ = $1; }
	|	gateBufList ',' gateBuf			{ $$ = $1->addNext($3); }
	;
gateBufif0List<nodep>:
		gateBufif0 				{ $$ = $1; }
	|	gateBufif0List ',' gateBufif0		{ $$ = $1->addNext($3); }
	;
gateBufif1List<nodep>:
		gateBufif1 				{ $$ = $1; }
	|	gateBufif1List ',' gateBufif1		{ $$ = $1->addNext($3); }
	;
gateNotList<nodep>:
		gateNot 				{ $$ = $1; }
	|	gateNotList ',' gateNot			{ $$ = $1->addNext($3); }
	;
gateNotif0List<nodep>:
		gateNotif0 				{ $$ = $1; }
	|	gateNotif0List ',' gateNotif0		{ $$ = $1->addNext($3); }
	;
gateNotif1List<nodep>:
		gateNotif1 				{ $$ = $1; }
	|	gateNotif1List ',' gateNotif1		{ $$ = $1->addNext($3); }
	;
gateAndList<nodep>:
		gateAnd 				{ $$ = $1; }
	|	gateAndList ',' gateAnd			{ $$ = $1->addNext($3); }
	;
gateNandList<nodep>:
		gateNand 				{ $$ = $1; }
	|	gateNandList ',' gateNand		{ $$ = $1->addNext($3); }
	;
gateOrList<nodep>:
		gateOr 					{ $$ = $1; }
	|	gateOrList ',' gateOr			{ $$ = $1->addNext($3); }
	;
gateNorList<nodep>:
		gateNor 				{ $$ = $1; }
	|	gateNorList ',' gateNor			{ $$ = $1->addNext($3); }
	;
gateXorList<nodep>:
		gateXor 				{ $$ = $1; }
	|	gateXorList ',' gateXor			{ $$ = $1->addNext($3); }
	;
gateXnorList<nodep>:
		gateXnor 				{ $$ = $1; }
	|	gateXnorList ',' gateXnor		{ $$ = $1->addNext($3); }
	;
gatePullupList<nodep>:
		gatePullup 				{ $$ = $1; }
	|	gatePullupList ',' gatePullup		{ $$ = $1->addNext($3); }
	;
gatePulldownList<nodep>:
		gatePulldown 				{ $$ = $1; }
	|	gatePulldownList ',' gatePulldown	{ $$ = $1->addNext($3); }
	;
gateUnsupList<nodep>:
		gateUnsup 				{ $$ = $1; }
	|	gateUnsupList ',' gateUnsup		{ $$ = $1->addNext($3); }
	;

gateRangeE<nodep>:
		instRangeE 				{ $$ = $1; GATERANGE($1); }
	;

gateBuf<nodep>:
		gateIdE gateRangeE '(' variable_lvalue ',' gatePinExpr ')'
			{ $$ = new AstAssignW ($3,$4,$6); DEL($2); }
	;
gateBufif0<nodep>:
		gateIdE gateRangeE '(' variable_lvalue ',' gatePinExpr ',' gatePinExpr ')'
			{ $$ = new AstAssignW ($3,$4,new AstBufIf1($3,new AstNot($3,$8),$6)); DEL($2); }
	;
gateBufif1<nodep>:
		gateIdE gateRangeE '(' variable_lvalue ',' gatePinExpr ',' gatePinExpr ')'
			{ $$ = new AstAssignW ($3,$4,new AstBufIf1($3,$8,$6)); DEL($2); }
	;
gateNot<nodep>:
		gateIdE gateRangeE '(' variable_lvalue ',' gatePinExpr ')'
			{ $$ = new AstAssignW ($3,$4,new AstNot($5,$6)); DEL($2); }
	;
gateNotif0<nodep>:
		gateIdE gateRangeE '(' variable_lvalue ',' gatePinExpr ',' gatePinExpr ')'
			{ $$ = new AstAssignW ($3,$4,new AstBufIf1($3,new AstNot($3,$8), new AstNot($3, $6))); DEL($2); }
	;
gateNotif1<nodep>:
		gateIdE gateRangeE '(' variable_lvalue ',' gatePinExpr ',' gatePinExpr ')'
			{ $$ = new AstAssignW ($3,$4,new AstBufIf1($3,$8, new AstNot($3,$6))); DEL($2); }
	;
gateAnd<nodep>:
		gateIdE gateRangeE '(' variable_lvalue ',' gateAndPinList ')'
			{ $$ = new AstAssignW ($3,$4,$6); DEL($2); }
	;
gateNand<nodep>:
		gateIdE gateRangeE '(' variable_lvalue ',' gateAndPinList ')'
			{ $$ = new AstAssignW ($3,$4,new AstNot($5,$6)); DEL($2); }
	;
gateOr<nodep>:
		gateIdE gateRangeE '(' variable_lvalue ',' gateOrPinList ')'
			{ $$ = new AstAssignW ($3,$4,$6); DEL($2); }
	;
gateNor<nodep>:
		gateIdE gateRangeE '(' variable_lvalue ',' gateOrPinList ')'
			{ $$ = new AstAssignW ($3,$4,new AstNot($5,$6)); DEL($2); }
	;
gateXor<nodep>:
		gateIdE gateRangeE '(' variable_lvalue ',' gateXorPinList ')'
			{ $$ = new AstAssignW ($3,$4,$6); DEL($2); }
	;
gateXnor<nodep>:
		gateIdE gateRangeE '(' variable_lvalue ',' gateXorPinList ')'
			{ $$ = new AstAssignW ($3,$4,new AstNot($5,$6)); DEL($2); }
	;
gatePullup<nodep>:
		gateIdE gateRangeE '(' variable_lvalue ')'	{ $$ = new AstPull ($3, $4, true); DEL($2); }
	;
gatePulldown<nodep>:
		gateIdE gateRangeE '(' variable_lvalue ')'	{ $$ = new AstPull ($3, $4, false); DEL($2); }
	;
gateUnsup<nodep>:
		gateIdE gateRangeE '(' gateUnsupPinList ')'	{ $$ = new AstImplicit ($3,$4); DEL($2); }
	;

gateIdE:
		/*empty*/				{}
	|	id					{}
	;

gateAndPinList<nodep>:
		gatePinExpr 				{ $$ = $1; }
	|	gateAndPinList ',' gatePinExpr		{ $$ = new AstAnd($2,$1,$3); }
	;
gateOrPinList<nodep>:
		gatePinExpr 				{ $$ = $1; }
	|	gateOrPinList ',' gatePinExpr		{ $$ = new AstOr($2,$1,$3); }
	;
gateXorPinList<nodep>:
		gatePinExpr 				{ $$ = $1; }
	|	gateXorPinList ',' gatePinExpr		{ $$ = new AstXor($2,$1,$3); }
	;
gateUnsupPinList<nodep>:
		gatePinExpr 				{ $$ = $1; }
	|	gateUnsupPinList ',' gatePinExpr	{ $$ = $1->addNext($3); }
	;

gatePinExpr<nodep>:
		expr					{ $$ = GRAMMARP ->createGatePin($1); }
	;

strengthSpecE:			// IEEE: drive_strength + pullup_strength + pulldown_strength + charge_strength - plus empty
		/* empty */				{ }
	//UNSUP	strengthSpec				{ }
	;

//************************************************
// Tables

combinational_body<nodep>:	// IEEE: combinational_body + sequential_body
		yTABLE tableEntryList yENDTABLE		{ $$ = new AstUdpTable($1,$2); }
	;

tableEntryList<nodep>:	// IEEE: { combinational_entry | sequential_entry }
		tableEntry 				{ $$ = $1; }
	|	tableEntryList tableEntry		{ $$ = $1->addNext($2); }
	;

tableEntry<nodep>:	// IEEE: combinational_entry + sequential_entry
		yaTABLELINE				{ $$ = new AstUdpTableLine($<fl>1,*$1); }
	|	error					{ $$ = NULL; }
	;

//************************************************
// Specify

specify_block<nodep>:		// ==IEEE: specify_block
		ySPECIFY specifyJunkList yENDSPECIFY	{ $$ = NULL; }
	|	ySPECIFY yENDSPECIFY			{ $$ = NULL; }
	;

specifyJunkList:
		specifyJunk 				{ } /* ignored */
	|	specifyJunkList specifyJunk		{ } /* ignored */
	;

specifyJunk:
		BISONPRE_NOT(ySPECIFY,yENDSPECIFY)	{ }
	|	ySPECIFY specifyJunk yENDSPECIFY	{ }
	|	error {}
	;

specparam_declaration<nodep>:		// ==IEEE: specparam_declaration
		ySPECPARAM junkToSemiList ';'		{ $$ = NULL; }
	;

junkToSemiList:
		junkToSemi 				{ } /* ignored */
	|	junkToSemiList junkToSemi		{ } /* ignored */
 	;

junkToSemi:
		BISONPRE_NOT(';',yENDSPECIFY,yENDMODULE)	{ }
	|	error {}
	;

//************************************************
// IDs

id<strp>:
		yaID__ETC				{ $$ = $1; $<fl>$=$<fl>1; }
	;

idAny<strp>:			// Any kind of identifier
	//UNSUP	yaID__aCLASS				{ $$ = $1; $<fl>$=$<fl>1; }
	//UNSUP	yaID__aCOVERGROUP			{ $$ = $1; $<fl>$=$<fl>1; }
		yaID__aPACKAGE				{ $$ = $1; $<fl>$=$<fl>1; }
	|	yaID__aTYPE				{ $$ = $1; $<fl>$=$<fl>1; }
	|	yaID__ETC				{ $$ = $1; $<fl>$=$<fl>1; }
	;

idSVKwd<strp>:			// Warn about non-forward compatible Verilog 2001 code
	//			// yBIT, yBYTE won't work here as causes conflicts
		yDO					{ static string s = "do"   ; $$ = &s; ERRSVKWD($1,*$$); $<fl>$=$<fl>1; }
	|	yFINAL					{ static string s = "final"; $$ = &s; ERRSVKWD($1,*$$); $<fl>$=$<fl>1; }
	;

variable_lvalue<nodep>:		// IEEE: variable_lvalue or net_lvalue
	//			// Note many variable_lvalue's must use exprOkLvalue when arbitrary expressions may also exist
		idClassSel				{ $$ = $1; }
	|	'{' variable_lvalueConcList '}'		{ $$ = $2; }
	//			// IEEE: [ assignment_pattern_expression_type ] assignment_pattern_variable_lvalue
	//			// We allow more assignment_pattern_expression_types then strictly required
	//UNSUP	data_type  yP_TICKBRA variable_lvalueList '}'	{ UNSUP }
	//UNSUP	idClassSel yP_TICKBRA variable_lvalueList '}'	{ UNSUP }
	//UNSUP	/**/       yP_TICKBRA variable_lvalueList '}'	{ UNSUP }
	//UNSUP	streaming_concatenation			{ UNSUP }
	|	streaming_concatenation			{ $$ = $1; }
	;

variable_lvalueConcList<nodep>:	// IEEE: part of variable_lvalue: '{' variable_lvalue { ',' variable_lvalue } '}'
		variable_lvalue					{ $$ = $1; }
	|	variable_lvalueConcList ',' variable_lvalue	{ $$ = new AstConcat($2,$1,$3); }
	;

// VarRef to dotted, and/or arrayed, and/or bit-ranged variable
idClassSel<nodep>:			// Misc Ref to dotted, and/or arrayed, and/or bit-ranged variable
		idDotted				{ $$ = $1; }
	//			// IEEE: [ implicit_class_handle . | package_scope ] hierarchical_variable_identifier select
	//UNSUP	yTHIS '.' idDotted			{ UNSUP }
	//UNSUP	ySUPER '.' idDotted			{ UNSUP }
	//UNSUP	yTHIS '.' ySUPER '.' idDotted		{ UNSUP }
	//			// Expanded: package_scope idDotted
	//UNSUP	class_scopeIdFollows idDotted		{ UNSUP }
	//UNSUP	package_scopeIdFollows idDotted		{ UNSUP }
	;

idDotted<nodep>:
	//UNSUP	yD_ROOT '.' idDottedMore		{ UNSUP }
		idDottedMore		 		{ $$ = $1; }
	;

idDottedMore<nodep>:
		idArrayed 				{ $$ = $1; }
	|	idDottedMore '.' idArrayed	 	{ $$ = new AstDot($2,$1,$3); }
	;

// Single component of dotted path, maybe [#].
// Due to lookahead constraints, we can't know if [:] or [+:] are valid (last dotted part),
// we'll assume so and cleanup later.
// id below includes:
//	 enum_identifier
idArrayed<nodep>:		// IEEE: id + select
		id						{ $$ = new AstParseRef($<fl>1,AstParseRefExp::PX_TEXT,*$1,NULL,NULL); }
	//			// IEEE: id + part_select_range/constant_part_select_range
	|	idArrayed '[' expr ']'				{ $$ = new AstSelBit($2,$1,$3); }  // Or AstArraySel, don't know yet.
	|	idArrayed '[' constExpr ':' constExpr ']'	{ $$ = new AstSelExtract($2,$1,$3,$5); }
	//			// IEEE: id + indexed_range/constant_indexed_range
	|	idArrayed '[' expr yP_PLUSCOLON  constExpr ']'	{ $$ = new AstSelPlus($2,$1,$3,$5); }
	|	idArrayed '[' expr yP_MINUSCOLON constExpr ']'	{ $$ = new AstSelMinus($2,$1,$3,$5); }
	;

// VarRef without any dots or vectorizaion
varRefBase<varrefp>:
		id					{ $$ = new AstVarRef($<fl>1,*$1,false);}
	;

// yaSTRING shouldn't be used directly, instead via an abstraction below
str<strp>:			// yaSTRING but with \{escapes} need decoded
		yaSTRING				{ $$ = PARSEP->newString(GRAMMARP->deQuote($<fl>1,*$1)); }
	;

strAsInt<nodep>:
		yaSTRING				{ $$ = new AstConst($<fl>1,V3Number(V3Number::VerilogStringLiteral(),$<fl>1,GRAMMARP->deQuote($<fl>1,*$1)));}
	;

strAsIntIgnore<nodep>:		// strAsInt, but never matches for when expr shouldn't parse strings
		yaSTRING__IGNORE			{ $$ = NULL; yyerror("Impossible token"); }
	;

strAsText<nodep>:
		yaSTRING				{ $$ = GRAMMARP->createTextQuoted($<fl>1,*$1);}
	;

endLabelE<strp>:
		/* empty */				{ $$ = NULL; $<fl>$=NULL; }
	|	':' idAny				{ $$ = $2; $<fl>$=$<fl>2; }
	//UNSUP	':' yNEW__ETC				{ $$ = $2; $<fl>$=$<fl>2; }
	;

//************************************************
// Clocking

clocking_declaration<nodep>:		// IEEE: clocking_declaration  (INCOMPLETE)
		yDEFAULT yCLOCKING '@' '(' senitemEdge ')' ';' yENDCLOCKING
			{ $$ = new AstClocking($1, $5, NULL); }
	//UNSUP: Vastly simplified grammar
	;

//************************************************
// Asserts

labeledStmt<nodep>:
		immediate_assert_statement		{ $$ = $1; }
	;

concurrent_assertion_item<nodep>:	// IEEE: concurrent_assertion_item
		concurrent_assertion_statement		{ $$ = $1; }
	|	id/*block_identifier*/ ':' concurrent_assertion_statement	{ $$ = new AstBegin($2,*$1,$3); }
	//			// IEEE: checker_instantiation
	//			// identical to module_instantiation; see etcInst
	;

concurrent_assertion_statement<nodep>:	// ==IEEE: concurrent_assertion_statement
	//UNSUP: assert/assume
	//				// IEEE: cover_property_statement
		yCOVER yPROPERTY '(' property_spec ')' stmtBlock	{ $$ = new AstPslCover($1,$4,$6); }
	;

property_spec<nodep>:			// IEEE: property_spec
	//UNSUP: This rule has been super-specialized to what is supported now
		'@' '(' senitemEdge ')' yDISABLE yIFF '(' expr ')' expr
			{ $$ = new AstPslClocked($1,$3,$8,$10); }
	|	'@' '(' senitemEdge ')' expr		{ $$ = new AstPslClocked($1,$3,NULL,$5); }
	|	yDISABLE yIFF '(' expr ')' expr	 	{ $$ = new AstPslClocked($4->fileline(),NULL,$4,$6); }
	|	expr	 				{ $$ = new AstPslClocked($1->fileline(),NULL,NULL,$1); }
	;

immediate_assert_statement<nodep>:	// ==IEEE: immediate_assert_statement
	//				// action_block expanded here, for compatibility with AstVAssert
		yASSERT '(' expr ')' stmtBlock %prec prLOWER_THAN_ELSE	{ $$ = new AstVAssert($1,$3,$5, GRAMMARP->createDisplayError($1)); }
	|	yASSERT '(' expr ')'           yELSE stmtBlock		{ $$ = new AstVAssert($1,$3,NULL,$6); }
	|	yASSERT '(' expr ')' stmtBlock yELSE stmtBlock		{ $$ = new AstVAssert($1,$3,$5,$7);   }
	;

//************************************************
// Covergroup

//**********************************************************************
// Randsequence

//**********************************************************************
// Class

//=========
// Package scoping - to traverse the symbol table properly, the final identifer
// must be included in the rules below.
// Each of these must end with {symsPackageDone | symsClassDone}

ps_id_etc:		// package_scope + general id
		package_scopeIdFollowsE id		{ }
	;

ps_type<dtypep>:		// IEEE: ps_parameter_identifier | ps_type_identifier
				// Even though we looked up the type and have a AstNode* to it,
				// we can't fully resolve it because it may have been just a forward definition.
		package_scopeIdFollowsE yaID__aTYPE	{ $$ = new AstRefDType($<fl>2, *$2); $$->castRefDType()->packagep($1); }
	//			// Simplify typing - from ps_covergroup_identifier
	//UNSUP	package_scopeIdFollowsE yaID__aCOVERGROUP	{ $<fl>$=$<fl>1; $$=$1+$2; }
	;

//=== Below rules assume special scoping per above

package_scopeIdFollowsE<packagep>:	// IEEE: [package_scope]
	//			// IMPORTANT: The lexer will parse the following ID to be in the found package
	//			// class_qualifier := [ yLOCAL '::'  ] [ implicit_class_handle '.'  class_scope ]
		/* empty */				{ $$ = NULL; }
	|	package_scopeIdFollows			{ $$ = $1; }
	;

package_scopeIdFollows<packagep>:	// IEEE: package_scope
	//			// IMPORTANT: The lexer will parse the following ID to be in the found package
	//			//vv mid rule action needed otherwise we might not have NextId in time to parse the id token
		yD_UNIT        { SYMP->nextId(PARSEP->rootp()); }
	/*cont*/	yP_COLONCOLON	{ $$ = GRAMMARP->unitPackage($<fl>1); }
	|	yaID__aPACKAGE { SYMP->nextId($<scp>1); }
	/*cont*/	yP_COLONCOLON	{ $$ = $<scp>1->castPackage(); }
	//UNSUP	yLOCAL__COLONCOLON { PARSEP->symTableNextId($<scp>1); }
	//UNSUP	/*cont*/	yP_COLONCOLON	{ UNSUP }
	;

//**********************************************************************
// VLT Files

vltItem:
		vltOffFront				{ V3Config::addIgnore($1,false,"*",0,0); }
	|	vltOffFront yVLT_D_FILE yaSTRING	{ V3Config::addIgnore($1,false,*$3,0,0); }
	|	vltOffFront yVLT_D_FILE yaSTRING yVLT_D_LINES yaINTNUM			{ V3Config::addIgnore($1,false,*$3,$5->toUInt(),$5->toUInt()+1); }
	|	vltOffFront yVLT_D_FILE yaSTRING yVLT_D_LINES yaINTNUM '-' yaINTNUM	{ V3Config::addIgnore($1,false,*$3,$5->toUInt(),$7->toUInt()+1); }
	|	vltOnFront				{ V3Config::addIgnore($1,true,"*",0,0); }
	|	vltOnFront yVLT_D_FILE yaSTRING		{ V3Config::addIgnore($1,true,*$3,0,0); }
	|	vltOnFront yVLT_D_FILE yaSTRING yVLT_D_LINES yaINTNUM			{ V3Config::addIgnore($1,true,*$3,$5->toUInt(),$5->toUInt()+1); }
	|	vltOnFront yVLT_D_FILE yaSTRING yVLT_D_LINES yaINTNUM '-' yaINTNUM	{ V3Config::addIgnore($1,true,*$3,$5->toUInt(),$7->toUInt()+1); }
	;

vltOffFront<errcodeen>:
		yVLT_COVERAGE_OFF			{ $$ = V3ErrorCode::I_COVERAGE; }
	|	yVLT_TRACING_OFF			{ $$ = V3ErrorCode::I_TRACING; }
	|	yVLT_LINT_OFF				{ $$ = V3ErrorCode::I_LINT; }
	|	yVLT_LINT_OFF yVLT_D_MSG yaID__ETC
			{ $$ = V3ErrorCode((*$3).c_str());
			  if ($$ == V3ErrorCode::EC_ERROR) { $1->v3error("Unknown Error Code: "<<*$3<<endl);  } }
	;

vltOnFront<errcodeen>:
		yVLT_COVERAGE_ON			{ $$ = V3ErrorCode::I_COVERAGE; }
	|	yVLT_TRACING_ON				{ $$ = V3ErrorCode::I_TRACING; }
	|	yVLT_LINT_ON				{ $$ = V3ErrorCode::I_LINT; }
	|	yVLT_LINT_ON yVLT_D_MSG yaID__ETC
			{ $$ = V3ErrorCode((*$3).c_str());
			  if ($$ == V3ErrorCode::EC_ERROR) { $1->v3error("Unknown Error Code: "<<*$3<<endl);  } }
	;

//**********************************************************************
%%

int V3ParseImp::bisonParse() {
    if (PARSEP->debugBison()>=9) yydebug = 1;
    return yyparse();
}

const char* V3ParseImp::tokenName(int token) {
#if YYDEBUG || YYERROR_VERBOSE
    if (token >= 255)
	return yytname[token-255];
    else {
	static char ch[2];  ch[0]=token; ch[1]='\0';
	return ch;
    }
#else
    return "";
#endif
}

void V3ParseImp::parserClear() {
    // Clear up any dynamic memory V3Parser required
    VARDTYPE(NULL);
}

void V3ParseGrammar::argWrapList(AstNodeFTaskRef* nodep) {
    // Convert list of expressions to list of arguments
    AstNode* outp = NULL;
    while (nodep->pinsp()) {
	AstNode* exprp = nodep->pinsp()->unlinkFrBack();
	// addNext can handle nulls:
	// cppcheck-suppress nullPointer
	outp = outp->addNext(new AstArg(exprp->fileline(), "", exprp));
    }
    if (outp) nodep->addPinsp(outp);
}

AstNode* V3ParseGrammar::createSupplyExpr(FileLine* fileline, string name, int value) {
    FileLine* newfl = new FileLine (fileline);
    newfl->warnOff(V3ErrorCode::WIDTH, true);
    AstNode* nodep = new AstConst(newfl, V3Number(newfl));
    // Adding a NOT is less work than figuring out how wide to make it
    if (value) nodep = new AstNot(newfl, nodep);
    nodep = new AstAssignW(newfl, new AstVarRef(fileline, name, true),
			   nodep);
    return nodep;
}

AstNodeDType* V3ParseGrammar::createArray(AstNodeDType* basep, AstRange* rangep, bool isPacked) {
    // Split RANGE0-RANGE1-RANGE2 into ARRAYDTYPE0(ARRAYDTYPE1(ARRAYDTYPE2(BASICTYPE3),RANGE),RANGE)
    AstNodeDType* arrayp = basep;
    if (rangep) { // Maybe no range - return unmodified base type
	while (rangep->nextp()) rangep = rangep->nextp()->castRange();
	while (rangep) {
	    AstRange* prevp = rangep->backp()->castRange();
	    if (prevp) rangep->unlinkFrBack();
	    if (isPacked) {
	        arrayp = new AstPackArrayDType(rangep->fileline(), VFlagChildDType(), arrayp, rangep);
	    } else {
	        arrayp = new AstUnpackArrayDType(rangep->fileline(), VFlagChildDType(), arrayp, rangep);
	    }
	    rangep = prevp;
	}
    }
    return arrayp;
}

AstVar* V3ParseGrammar::createVariable(FileLine* fileline, string name, AstRange* arrayp, AstNode* attrsp) {
    AstNodeDType* dtypep = GRAMMARP->m_varDTypep;
    UINFO(5,"  creVar "<<name<<"  decl="<<GRAMMARP->m_varDecl<<"  io="<<GRAMMARP->m_varIO<<"  dt="<<(dtypep?"set":"")<<endl);
    if (GRAMMARP->m_varIO == AstVarType::UNKNOWN
	&& GRAMMARP->m_varDecl == AstVarType::PORT) {
	// Just a port list with variable name (not v2k format); AstPort already created
	if (dtypep) fileline->v3error("Unsupported: Ranges ignored in port-lists");
	return NULL;
    }
    AstVarType type = GRAMMARP->m_varIO;
    if (dtypep->castIfaceRefDType()) {
	if (arrayp) { fileline->v3error("Unsupported: Arrayed interfaces"); arrayp=NULL; }
    }
    if (!dtypep) {  // Created implicitly
	dtypep = new AstBasicDType(fileline, LOGIC_IMPLICIT);
    } else {  // May make new variables with same type, so clone
	dtypep = dtypep->cloneTree(false);
    }
    //UINFO(0,"CREVAR "<<fileline->ascii()<<" decl="<<GRAMMARP->m_varDecl.ascii()<<" io="<<GRAMMARP->m_varIO.ascii()<<endl);
    if (type == AstVarType::UNKNOWN
	|| (type == AstVarType::PORT && GRAMMARP->m_varDecl != AstVarType::UNKNOWN))
	type = GRAMMARP->m_varDecl;
    if (type == AstVarType::UNKNOWN) fileline->v3fatalSrc("Unknown signal type declared");
    if (type == AstVarType::GENVAR) {
	if (arrayp) fileline->v3error("Genvars may not be arrayed: "<<name);
    }

    // Split RANGE0-RANGE1-RANGE2 into ARRAYDTYPE0(ARRAYDTYPE1(ARRAYDTYPE2(BASICTYPE3),RANGE),RANGE)
    AstNodeDType* arrayDTypep = createArray(dtypep,arrayp,false);

    AstVar* nodep = new AstVar(fileline, type, name, VFlagChildDType(), arrayDTypep);
    nodep->addAttrsp(attrsp);
    if (GRAMMARP->m_varDecl != AstVarType::UNKNOWN) nodep->combineType(GRAMMARP->m_varDecl);
    if (GRAMMARP->m_varIO != AstVarType::UNKNOWN) nodep->combineType(GRAMMARP->m_varIO);

    if (GRAMMARP->m_varDecl == AstVarType::SUPPLY0) {
	nodep->addNext(V3ParseGrammar::createSupplyExpr(fileline, nodep->name(), 0));
    }
    if (GRAMMARP->m_varDecl == AstVarType::SUPPLY1) {
	nodep->addNext(V3ParseGrammar::createSupplyExpr(fileline, nodep->name(), 1));
    }
    // Don't set dtypep in the ranging;
    // We need to autosize parameters and integers separately
    //
    // Propagate from current module tracing state
    if (nodep->isGenVar()) nodep->trace(false);
    else if (nodep->isParam() && !v3Global.opt.traceParams()) nodep->trace(false);
    else nodep->trace(allTracingOn(nodep->fileline()));

    // Remember the last variable created, so we can attach attributes to it in later parsing
    GRAMMARP->m_varAttrp = nodep;
    return nodep;
}

string V3ParseGrammar::deQuote(FileLine* fileline, string text) {
    // Fix up the quoted strings the user put in, for example "\"" becomes "
    // Reverse is V3Number::quoteNameControls(...)
    bool quoted = false;
    string newtext;
    unsigned char octal_val = 0;
    int octal_digits = 0;
    for (const char* cp=text.c_str(); *cp; ++cp) {
	if (quoted) {
	    if (isdigit(*cp)) {
		octal_val = octal_val*8 + (*cp-'0');
		if (++octal_digits == 3) {
		    octal_digits = 0;
		    quoted = false;
		    newtext += octal_val;
		}
	    } else {
		if (octal_digits) {
		    // Spec allows 1-3 digits
		    octal_digits = 0;
		    quoted = false;
		    newtext += octal_val;
		    --cp;  // Backup to reprocess terminating character as non-escaped
		    continue;
		}
		quoted = false;
		if (*cp == 'n') newtext += '\n';
		else if (*cp == 'a') newtext += '\a'; // SystemVerilog 3.1
		else if (*cp == 'f') newtext += '\f'; // SystemVerilog 3.1
		else if (*cp == 'r') newtext += '\r';
		else if (*cp == 't') newtext += '\t';
		else if (*cp == 'v') newtext += '\v'; // SystemVerilog 3.1
		else if (*cp == 'x' && isxdigit(cp[1]) && isxdigit(cp[2])) { // SystemVerilog 3.1
#define vl_decodexdigit(c) ((isdigit(c)?((c)-'0'):(tolower((c))-'a'+10)))
		    newtext += (char)(16*vl_decodexdigit(cp[1]) + vl_decodexdigit(cp[2]));
		    cp += 2;
		}
		else if (isalnum(*cp)) {
		    fileline->v3error("Unknown escape sequence: \\"<<*cp);
		    break;
		}
		else newtext += *cp;
	    }
	}
	else if (*cp == '\\') {
	    quoted = true;
	    octal_digits = 0;
	}
	else if (*cp != '"') {
	    newtext += *cp;
	}
    }
    return newtext;
}

//YACC = /kits/sources/bison-2.4.1/src/bison --report=lookahead
// --report=lookahead
// --report=itemset
// --graph
