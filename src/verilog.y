// -*- C++ -*-
//*************************************************************************
// DESCRIPTION: Verilator: Bison grammer file
//
// Code available from: http://www.veripool.org/verilator
//
//*************************************************************************
//
// Copyright 2003-2008 by Wilson Snyder.  This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// General Public License or the Perl Artistic License.
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

#include "V3Read.h"
#include "V3Ast.h"
#include "V3Global.h"

#define YYERROR_VERBOSE 1
#define YYMAXDEPTH 10000

// Pick up new lexer
#define yylex V3Read::yylex
#define PSLUNSUP(what) NULL; yyerrorf("Unsupported: PSL language feature not implemented");

extern void yyerror(char* errmsg);
extern void yyerrorf(const char* format, ...);

//======================================================================
// Statics (for here only)

class V3Parse {
public:
    static bool		s_impliedDecl;	// Allow implied wire declarations
    static AstVarType	s_varDecl;	// Type for next signal declaration (reg/wire/etc)
    static AstVarType	s_varIO;	// Type for next signal declaration (input/output/etc)
    static bool		s_varSigned;	// Signed state for next signal declaration
    static AstVar*	s_varAttrp;	// Current variable for attribute adding
    static AstCase*	s_caseAttrp;	// Current case statement for attribute adding
    static AstRange*	s_varRangep;	// Pointer to range for next signal declaration
    static int		s_pinNum;	// Pin number currently parsing
    static bool		s_pinStar;	// Encountered SystemVerilog .*
    static string	s_instModule;	// Name of module referenced for instantiations
    static AstPin*	s_instParamp;	// Parameters for instantiations
    static bool		s_trace;	// Tracing is turned on

    static AstVar*  createVariable(FileLine* fileline, string name, AstRange* arrayp);
    static AstNode* createSupplyExpr(FileLine* fileline, string name, int value);
    static AstText* createTextQuoted(FileLine* fileline, string text);
    static AstDisplay* createDisplayError(FileLine* fileline) {
	AstDisplay* nodep = new AstDisplay(fileline,AstDisplayType::ERROR,  "", NULL,NULL);
	nodep->addNext(new AstStop(fileline));
	return nodep;
    }
    static void setRange(AstRange* rangep) {
	if (s_varRangep) { s_varRangep->deleteTree(); s_varRangep=NULL; } // It was cloned, so this is safe.
	s_varRangep = rangep;
    }
    static string   deQuote(FileLine* fileline, string text);
};

bool		V3Parse::s_impliedDecl = false;
bool		V3Parse::s_trace = false;   // Set on first module creation
AstVarType	V3Parse::s_varDecl = AstVarType::UNKNOWN;
AstVarType	V3Parse::s_varIO = AstVarType::UNKNOWN;
bool		V3Parse::s_varSigned = false;
AstRange*	V3Parse::s_varRangep = NULL;
int 		V3Parse::s_pinNum = -1;
bool		V3Parse::s_pinStar = false;
string		V3Parse::s_instModule;
AstPin*		V3Parse::s_instParamp = NULL;
AstVar*		V3Parse::s_varAttrp = NULL;
AstCase*	V3Parse::s_caseAttrp = NULL;

#define CRELINE() (V3Read::copyOrSameFileLine())

#define VARRESET() { VARDECL(UNKNOWN); VARIO(UNKNOWN); VARSIGNED(false); VARRANGE(NULL); }
#define VARDECL(type) { V3Parse::s_varDecl = AstVarType::type; }
#define VARIO(type) { V3Parse::s_varIO = AstVarType::type; }
#define VARSIGNED(value) { V3Parse::s_varSigned = value; }
#define VARRANGE(rangep) { V3Parse::setRange(rangep); }

#define INSTPREP(modname,paramsp) { V3Parse::s_impliedDecl = true; V3Parse::s_instModule = modname; V3Parse::s_instParamp = paramsp; }

//======================================================================

class AstSenTree;
%}

%union {
    FileLine*	fileline;
    V3Number*	nump;
    string*	strp;
    int 	cint;
    double	cdouble;

    AstNode*	nodep;

    AstAssignW* assignwp;
    AstBegin*	beginp;
    AstCase*	casep;
    AstCaseItem* caseitemp;
    AstCell*	cellp;
    AstConst*	constp;
    AstFunc*	funcp;
    AstModule*	modulep;
    AstNodeVarRef*	varnodep;
    AstParseRef*	parserefp;
    AstPin*	pinp;
    AstRange*	rangep;
    AstSenItem*	senitemp;
    AstSenTree*	sentreep;
    AstVar*	varp;
    AstVarRef*	varrefp;
}

// Generic lexer tokens, for example a number
// IEEE: real_number
%token<cdouble>		yaFLOATNUM	"FLOATING-POINT NUMBER"
// IEEE: identifier, class_identifier, class_variable_identifier,
// covergroup_variable_identifier, dynamic_array_variable_identifier,
// enum_identifier, interface_identifier, interface_instance_identifier,
// package_identifier, type_identifier, variable_identifier,
%token<strp>		yaID		"IDENTIFIER"

// IEEE: integral_number
%token<nump>		yaINTNUM	"INTEGER NUMBER"
// IEEE: string_literal
%token<strp>		yaSTRING	"STRING"
%token<fileline>	yaTIMINGSPEC	"TIMING SPEC ELEMENT"

%token<strp>		yaSCHDR		"`systemc_header BLOCK"
%token<strp>		yaSCINT		"`systemc_ctor BLOCK"
%token<strp>		yaSCIMP		"`systemc_dtor BLOCK"
%token<strp>		yaSCIMPH	"`systemc_interface BLOCK"
%token<strp>		yaSCCTOR	"`systemc_implementation BLOCK"
%token<strp>		yaSCDTOR	"`systemc_imp_header BLOCK"

// Specific keywords
// yKEYWORD means match "keyword"
// Other cases are yXX_KEYWORD where XX makes it unique,
// for example yP_ for punctuation based operators.
%token<fileline>	yALWAYS		"always"
%token<fileline>	yAND		"and"
%token<fileline>	yASSERT		"assert"
%token<fileline>	yASSIGN		"assign"
%token<fileline>	yAUTOMATIC	"automatic"
%token<fileline>	yBEGIN		"begin"
%token<fileline>	yBUF		"buf"
%token<fileline>	yCASE		"case"
%token<fileline>	yCASEX		"casex"
%token<fileline>	yCASEZ		"casez"
%token<fileline>	yCLOCKING	"clocking"
%token<fileline>	yCOVER		"cover"
%token<fileline>	yDEFAULT	"default"
%token<fileline>	yDEFPARAM	"defparam"
%token<fileline>	yDISABLE	"disable"
%token<fileline>	yDO		"do"
%token<fileline>	yELSE		"else"
%token<fileline>	yEND		"end"
%token<fileline>	yENDCASE	"endcase"
%token<fileline>	yENDCLOCKING	"endclocking"
%token<fileline>	yENDFUNCTION	"endfunction"
%token<fileline>	yENDGENERATE	"endgenerate"
%token<fileline>	yENDMODULE	"endmodule"
%token<fileline>	yENDPROPERTY	"endproperty"
%token<fileline>	yENDSPECIFY	"endspecify"
%token<fileline>	yENDTASK	"endtask"
%token<fileline>	yFINAL		"final"
%token<fileline>	yFOR		"for"
%token<fileline>	yFUNCTION	"function"
%token<fileline>	yGENERATE	"generate"
%token<fileline>	yGENVAR		"genvar"
%token<fileline>	yIF		"if"
%token<fileline>	yIFF		"iff"
%token<fileline>	yINITIAL	"initial"
%token<fileline>	yINOUT		"inout"
%token<fileline>	yINPUT		"input"
%token<fileline>	yINTEGER	"integer"
%token<fileline>	yLOCALPARAM	"localparam"
%token<fileline>	yMODULE		"module"
%token<fileline>	yNAND		"nand"
%token<fileline>	yNEGEDGE	"negedge"
%token<fileline>	yNOR		"nor"
%token<fileline>	yNOT		"not"
%token<fileline>	yOR		"or"
%token<fileline>	yOUTPUT		"output"
%token<fileline>	yPARAMETER	"parameter"
%token<fileline>	yPOSEDGE	"posedge"
%token<fileline>	yPROPERTY	"property"
%token<fileline>	yREG		"reg"
%token<fileline>	ySCALARED	"scalared"
%token<fileline>	ySIGNED		"signed"
%token<fileline>	ySPECIFY	"specify"
%token<fileline>	ySTATIC		"static"
%token<fileline>	ySUPPLY0	"supply0"
%token<fileline>	ySUPPLY1	"supply1"
%token<fileline>	yTASK		"task"
%token<fileline>	yTRI		"tri"
%token<fileline>	yTRUE		"true"
%token<fileline>	yUNSIGNED	"unsigned"
%token<fileline>	yVECTORED	"vectored"
%token<fileline>	yWHILE		"while"
%token<fileline>	yWIRE		"wire"
%token<fileline>	yXNOR		"xnor"
%token<fileline>	yXOR		"xor"

%token<fileline>	yD_BITS		"$bits"
%token<fileline>	yD_C		"$c"
%token<fileline>	yD_CLOG2	"$clog2"
%token<fileline>	yD_COUNTONES	"$countones"
%token<fileline>	yD_DISPLAY	"$display"
%token<fileline>	yD_ERROR	"$error"
%token<fileline>	yD_FATAL	"$fatal"
%token<fileline>	yD_FCLOSE	"$fclose"
%token<fileline>	yD_FDISPLAY	"$fdisplay"
%token<fileline>	yD_FEOF		"$feof"
%token<fileline>	yD_FFLUSH	"$fflush"
%token<fileline>	yD_FGETC	"$fgetc"
%token<fileline>	yD_FGETS	"$fgets"
%token<fileline>	yD_FINISH	"$finish"
%token<fileline>	yD_FOPEN	"$fopen"
%token<fileline>	yD_FSCANF	"$fscanf"
%token<fileline>	yD_FWRITE	"$fwrite"
%token<fileline>	yD_INFO		"$info"
%token<fileline>	yD_ISUNKNOWN	"$isunknown"
%token<fileline>	yD_ONEHOT	"$onehot"
%token<fileline>	yD_ONEHOT0	"$onehot0"
%token<fileline>	yD_RANDOM	"$random"
%token<fileline>	yD_READMEMB	"$readmemb"
%token<fileline>	yD_READMEMH	"$readmemh"
%token<fileline>	yD_SIGNED	"$signed"
%token<fileline>	yD_SSCANF	"$sscanf"
%token<fileline>	yD_STIME	"$stime"
%token<fileline>	yD_STOP		"$stop"
%token<fileline>	yD_TIME		"$time"
%token<fileline>	yD_UNSIGNED	"$unsigned"
%token<fileline>	yD_WARNING	"$warning"
%token<fileline>	yD_WRITE	"$write"

%token<fileline>	yPSL		"psl"
%token<fileline>	yPSL_ASSERT	"PSL assert"
%token<fileline>	yPSL_CLOCK	"PSL clock"
%token<fileline>	yPSL_COVER	"PSL cover"
%token<fileline>	yPSL_REPORT	"PSL report"

%token<fileline>	yVL_CLOCK		"/*verilator sc_clock*/"
%token<fileline>	yVL_CLOCK_ENABLE	"/*verilator clock_enable*/"
%token<fileline>	yVL_COVER_OFF		"/*verilator coverage_block_off*/"
%token<fileline>	yVL_FULL_CASE		"/*verilator full_case*/"
%token<fileline>	yVL_INLINE_MODULE	"/*verilator inline_module*/"
%token<fileline>	yVL_ISOLATE_ASSIGNMENTS	"/*verilator isolate_assignments*/"
%token<fileline>	yVL_NO_INLINE_MODULE	"/*verilator no_inline_module*/"
%token<fileline>	yVL_NO_INLINE_TASK	"/*verilator no_inline_task*/"
%token<fileline>	yVL_PARALLEL_CASE	"/*verilator parallel_case*/"
%token<fileline>	yVL_PUBLIC		"/*verilator public*/"
%token<fileline>	yVL_PUBLIC_FLAT		"/*verilator public_flat*/"
%token<fileline>	yVL_PUBLIC_MODULE	"/*verilator public_module*/"
%token<fileline>	yVL_TRACING_OFF		"/*verilator tracing_off*/"
%token<fileline>	yVL_TRACING_ON		"/*verilator tracing_on*/"

%token<fileline>	yP_OROR		"||"
%token<fileline>	yP_ANDAND	"&&"
%token<fileline>	yP_NOR		"~|"
%token<fileline>	yP_XNOR		"^~"
%token<fileline>	yP_NAND		"~&"
%token<fileline>	yP_EQUAL	"=="
%token<fileline>	yP_NOTEQUAL	"!="
%token<fileline>	yP_CASEEQUAL	"==="
%token<fileline>	yP_CASENOTEQUAL	"!=="
%token<fileline>	yP_WILDEQUAL	"==?"
%token<fileline>	yP_WILDNOTEQUAL	"!=?"
%token<fileline>	yP_GTE		">="
%token<fileline>	yP_LTE		"<="
%token<fileline>	yP_SLEFT	"<<"
%token<fileline>	yP_SRIGHT	">>"
%token<fileline>	yP_SSRIGHT	">>>"
%token<fileline>	yP_POW		"**"

%token<fileline>	yP_PLUSCOLON	"+:"
%token<fileline>	yP_MINUSCOLON	"-:"
%token<fileline>	yP_MINUSGT	"->"
%token<fileline>	yP_MINUSGTGT	"->>"
%token<fileline>	yP_EQGT		"=>"
%token<fileline>	yP_ASTGT	"*>"
%token<fileline>	yP_ANDANDAND	"&&&"
%token<fileline>	yP_POUNDPOUND	"##"
%token<fileline>	yP_DOTSTAR	".*"

%token<fileline>	yP_ATAT		"@@"
%token<fileline>	yP_COLONCOLON	"::"
%token<fileline>	yP_COLONEQ	":="
%token<fileline>	yP_COLONDIV	":/"
%token<fileline>	yP_ORMINUSGT	"|->"
%token<fileline>	yP_OREQGT	"|=>"

%token<fileline>	yP_PLUSEQ	"+="
%token<fileline>	yP_MINUSEQ	"-="
%token<fileline>	yP_TIMESEQ	"*="
%token<fileline>	yP_DIVEQ	"/="
%token<fileline>	yP_MODEQ	"%="
%token<fileline>	yP_ANDEQ	"&="
%token<fileline>	yP_OREQ		"|="
%token<fileline>	yP_XOREQ	"^="
%token<fileline>	yP_SLEFTEQ	"<<="
%token<fileline>	yP_SRIGHTEQ	">>="
%token<fileline>	yP_SSRIGHTEQ	">>>="

%token<fileline>	yPSL_BRA	"{"
%token<fileline>	yPSL_KET	"}"
%token<fileline> 	yP_LOGIFF

%token<fileline>	'!'
%token<fileline>	'#'
%token<fileline>	'%'
%token<fileline>	'&'
%token<fileline>	'('
%token<fileline>	')'
%token<fileline>	'*'
%token<fileline>	'+'
%token<fileline>	','
%token<fileline>	'-'
%token<fileline>	'.'
%token<fileline>	'/'
%token<fileline>	':'
%token<fileline>	';'
%token<fileline>	'<'
%token<fileline>	'='
%token<fileline>	'>'
%token<fileline>	'?'
%token<fileline>	'@'
%token<fileline>	'['
%token<fileline>	']'
%token<fileline>	'^'
%token<fileline>	'{'
%token<fileline>	'|'
%token<fileline>	'}'
%token<fileline>	'~'

// [* is not a operator, as "[ * ]" is legal
// [= and [-> could be repitition operators, but to match [* we don't add them.
// '( is not a operator, as "' (" is legal
// '{ could be an operator.  More research needed.

//********************
// PSL op precedence
%right	 	yP_MINUSGT  yP_LOGIFF
%right		yP_ORMINUSGT  yP_OREQGT
%left<fileline>	prPSLCLK

// Verilog op precedence
%left		':'
%left		'?'
%left		yP_OROR
%left		yP_ANDAND
%left		'|' yP_NOR
%left		'^'
%left		yP_XNOR
%left		'&' yP_NAND
%left		yP_EQUAL yP_NOTEQUAL yP_CASEEQUAL yP_CASENOTEQUAL yP_WILDEQUAL yP_WILDNOTEQUAL
%left		'>' '<' yP_GTE yP_LTE
%left		yP_SLEFT yP_SRIGHT yP_SSRIGHT
%left		'+' '-'
%left		'*' '/' '%'
%left		yP_POW
%left		'{' '}'
%left<fileline>	prUNARYARITH
%left<fileline>	prREDUCTION
%left<fileline>	prNEGATION

%nonassoc prLOWER_THAN_ELSE
%nonassoc yELSE

// Types are in same order as declarations.
// Naming:
//	Trailing E indicates this type may have empty match

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

%start fileE

%%
//**********************************************************************
// Feedback to the Lexer

stateExitPsl:	/* empty */			 	{ V3Read::stateExitPsl(); }
	;
statePushVlg:	/* empty */			 	{ V3Read::statePushVlg(); }
	;
statePop:	/* empty */			 	{ V3Read::statePop(); }
	;

//**********************************************************************
// Files

fileE:		/* empty */				{ }
	|	file					{ }
	;

file:		description				{ }
	|	file description			{ }
	;

// IEEE: description
description:	moduleDecl				{ }
	;

//**********************************************************************
// Module headers

// IEEE: module_declaration:
moduleDecl:	modHdr modParE modPortsE ';' modItemListE yENDMODULE endLabelE
			{ $1->modTrace(V3Parse::s_trace);  // Stash for implicit wires, etc
			  if ($2) $1->addStmtp($2); if ($3) $1->addStmtp($3); if ($5) $1->addStmtp($5); }
	;

modHdr<modulep>:
		yMODULE { V3Parse::s_trace=v3Global.opt.trace();}
			yaID				{ $$ = new AstModule($1,*$3); $$->inLibrary(V3Read::inLibrary()||V3Read::inCellDefine());
							  $$->modTrace(v3Global.opt.trace());
							  V3Read::rootp()->addModulep($$); }
	;

modParE<nodep>:
		/* empty */				{ $$ = NULL; }
	|	'#' '(' ')'				{ $$ = NULL; }
	|	'#' '(' modParArgs ')'			{ $$ = $3; }
	;

modParArgs<nodep>:
		modParDecl				{ $$ = $1; }
	|	modParDecl ',' modParList		{ $$ = $1->addNext($3); }
	;

modParList<nodep>:
		modParSecond				{ $$ = $1; }
	|	modParList ',' modParSecond 		{ $$ = $1->addNext($3); }
	;

// Called only after a comma in a v2k list, to allow parsing "parameter a,b, parameter x"
modParSecond<nodep>:
		modParDecl				{ $$ = $1; }
	|	param					{ $$ = $1; }
	;

modPortsE<nodep>:
		/* empty */					{ $$ = NULL; }
	|	'(' ')'						{ $$ = NULL; }
	|	'(' {V3Parse::s_pinNum=1;} portList ')'		{ $$ = $3; }
	|	'(' {V3Parse::s_pinNum=1;} portV2kArgs ')'	{ $$ = $3; }
	;

portList<nodep>:
		port				       	{ $$ = $1; }
	|	portList ',' port	  	   	{ $$ = $1->addNext($3); }
	;

port<nodep>:
		yaID portRangeE			       	{ $$ = new AstPort(CRELINE(),V3Parse::s_pinNum++,*$1); }
	;

portV2kArgs<nodep>:
		portV2kDecl				{ $$ = $1; }
	|	portV2kDecl ',' portV2kList		{ $$ = $1->addNext($3); }
	;

portV2kList<nodep>:
		portV2kSecond				{ $$ = $1; }
	|	portV2kList ',' portV2kSecond		{ $$ = $1->addNext($3); }
	;

// Called only after a comma in a v2k list, to allow parsing "input a,b"
portV2kSecond<nodep>:
		portV2kDecl				{ $$ = $1; }
	|	portV2kInit				{ $$ = $1; }
	;

portV2kInit<nodep>:
		portV2kSig				{ $$=$1; }
	|	portV2kSig '=' expr
			{ $$=$1; $$->addNext(new AstInitial($2,new AstAssign($2, new AstVarRef($2,V3Parse::s_varAttrp->name(),true), $3))); }
	;

portV2kSig<nodep>:
		sigAndAttr				{ $$=$1; $$->addNext(new AstPort(CRELINE(),V3Parse::s_pinNum++, V3Parse::s_varAttrp->name())); }
	;

//************************************************
// Variable Declarations

varDeclList<nodep>:
		varDecl					{ $$ = $1; }
	|	varDecl varDeclList			{ $$ = $1->addNext($2); }
	;

regsigList<varp>:
		regsig  				{ $$ = $1; }
	|	regsigList ',' regsig		       	{ $$ = $1;$1->addNext($3); }
	;

portV2kDecl<nodep>:
		varRESET portDirection v2kVarDeclE signingE regrangeE portV2kInit	{ $$ = $6; }
	;

// IEEE: port_declaration - plus ';'
portDecl<nodep>:
		varRESET portDirection v2kVarDeclE signingE regrangeE  regsigList ';'	{ $$ = $6; }
	;

varDecl<nodep>:
		varRESET varReg     signingE regrangeE  regsigList ';'	{ $$ = $5; }
	|	varRESET varGParam  signingE regrangeE  paramList ';'		{ $$ = $5; }
	|	varRESET varLParam  signingE regrangeE  paramList ';'		{ $$ = $5; }
	|	varRESET varNet     signingE delayrange netSigList ';'	{ $$ = $5; }
	|	varRESET varGenVar  signingE            regsigList ';'	{ $$ = $4; }
	;

modParDecl<nodep>:
		varRESET varGParam  signingE regrangeE   param 	{ $$ = $5; }
	;

varRESET:	/* empty */ 				{ VARRESET(); }
	;

varNet:		ySUPPLY0				{ VARDECL(SUPPLY0); }
	|	ySUPPLY1				{ VARDECL(SUPPLY1); }
	|	yWIRE 					{ VARDECL(WIRE); }
	|	yTRI 					{ VARDECL(TRIWIRE); }
	;
varGParam:	yPARAMETER				{ VARDECL(GPARAM); }
	;
varLParam:	yLOCALPARAM				{ VARDECL(LPARAM); }
	;
varGenVar:	yGENVAR					{ VARDECL(GENVAR); }
	;
varReg:		yREG					{ VARDECL(REG); }
	|	yINTEGER				{ VARDECL(INTEGER); }
	;

//IEEE: port_direction
portDirection:	yINPUT					{ VARIO(INPUT); }
	|	yOUTPUT					{ VARIO(OUTPUT); }
	|	yINOUT					{ VARIO(INOUT); }
//	|	yREF					{ VARIO(REF); }
	;

// IEEE: signing - plus empty
signingE:	/*empty*/ 				{ }
	|	ySIGNED					{ VARSIGNED(true); }
	|	yUNSIGNED				{ VARSIGNED(false); }
	;

v2kVarDeclE:	/*empty*/ 				{ }
	|	varNet 					{ }
	|	varReg 					{ }
	;

//************************************************
// Module Items

modItemListE<nodep>:
		/* empty */				{ $$ = NULL; }
	|	modItemList				{ $$ = $1; }
	;

modItemList<nodep>:
		modItem					{ $$ = $1; }
	|	modItemList modItem			{ $$ = $1->addNextNull($2); }
	;

modItem<nodep>:
		modOrGenItem 				{ $$ = $1; }
	|	generateRegion				{ $$ = $1; }
	|	yaSCHDR					{ $$ = new AstScHdr(CRELINE(),*$1); }
	|	yaSCINT					{ $$ = new AstScInt(CRELINE(),*$1); }
	|	yaSCIMP					{ $$ = new AstScImp(CRELINE(),*$1); }
	|	yaSCIMPH				{ $$ = new AstScImpHdr(CRELINE(),*$1); }
	|	yaSCCTOR				{ $$ = new AstScCtor(CRELINE(),*$1); }
	|	yaSCDTOR				{ $$ = new AstScDtor(CRELINE(),*$1); }
	|	yVL_INLINE_MODULE			{ $$ = new AstPragma($1,AstPragmaType::INLINE_MODULE); }
	|	yVL_NO_INLINE_MODULE			{ $$ = new AstPragma($1,AstPragmaType::NO_INLINE_MODULE); }
	|	yVL_PUBLIC_MODULE			{ $$ = new AstPragma($1,AstPragmaType::PUBLIC_MODULE); }
	|	yVL_TRACING_OFF				{ $$ = NULL; V3Parse::s_trace=false; }
	|	yVL_TRACING_ON				{ $$ = NULL; V3Parse::s_trace=v3Global.opt.trace(); }
	|	ySPECIFY specifyJunkList yENDSPECIFY	{ $$ = NULL; }
	|	ySPECIFY yENDSPECIFY			{ $$ = NULL; }
	;

// IEEE: generate_region
generateRegion<nodep>:
		yGENERATE genTopBlock yENDGENERATE	{ $$ = new AstGenerate($1, $2); }
	;

modOrGenItem<nodep>:
		yALWAYS eventControlE stmtBlock		{ $$ = new AstAlways($1,$2,$3); }
	|	yFINAL stmtBlock			{ $$ = new AstFinal($1,$2); }
	|	yINITIAL stmtBlock			{ $$ = new AstInitial($1,$2); }
	|	yASSIGN delayE assignList ';'		{ $$ = $3; }
	|	yDEFPARAM defpList ';'			{ $$ = $2; }
	|	instDecl 				{ $$ = $1; }
	|	taskDecl 				{ $$ = $1; }
	|	funcDecl 				{ $$ = $1; }
	|	gateDecl 				{ $$ = $1; }
	|	portDecl 				{ $$ = $1; }
	|	varDecl 				{ $$ = $1; }
	//No: |	tableDecl				// Unsupported
	|	pslStmt 				{ $$ = $1; }
	|	concurrent_assertion_item		{ $$ = $1; }  // IEEE puts in modItem; seems silly
	|	clocking_declaration			{ $$ = $1; }
	;

//************************************************
// Generates

// Because genItemList includes variable declarations, we don't need beginNamed
genItemBlock<nodep>:
		genItem					{ $$ = new AstBegin(CRELINE(),"genblk",$1); }
	|	genItemBegin				{ $$ = $1; }
	;

genTopBlock<nodep>:
		genItemList				{ $$ = $1; }
	|	genItemBegin				{ $$ = $1; }
	;

genItemBegin<nodep>:
		yBEGIN genItemList yEND			{ $$ = new AstBegin($1,"genblk",$2); }
	|	yBEGIN yEND				{ $$ = NULL; }
	|	yBEGIN ':' yaID genItemList yEND endLabelE	{ $$ = new AstBegin($2,*$3,$4); }
	|	yBEGIN ':' yaID 	    yEND endLabelE	{ $$ = NULL; }
	;

genItemList<nodep>:
		genItem					{ $$ = $1; }
	|	genItemList genItem			{ $$ = $1->addNextNull($2); }
	;

genItem<nodep>:
		modOrGenItem 				{ $$ = $1; }
	|	yCASE  '(' expr ')' genCaseListE yENDCASE	{ $$ = new AstGenCase($1,$3,$5); }
	|	yIF '(' expr ')' genItemBlock	%prec prLOWER_THAN_ELSE	{ $$ = new AstGenIf($1,$3,$5,NULL); }
	|	yIF '(' expr ')' genItemBlock yELSE genItemBlock	{ $$ = new AstGenIf($1,$3,$5,$7); }
	|	yFOR '(' varRefBase '=' expr ';' expr ';' varRefBase '=' expr ')' genItemBlock
							{ $$ = new AstGenFor($1, new AstAssign($4,$3,$5)
									     ,$7, new AstAssign($10,$9,$11)
									     ,$13);}
	;

genCaseListE<nodep>:
		/* empty */				{ $$ = NULL; }
	|	genCaseList				{ $$ = $1; }
	;

genCaseList<nodep>:
		caseCondList ':' genItemBlock		{ $$ = new AstCaseItem($2,$1,$3); }
	|	yDEFAULT ':' genItemBlock		{ $$ = new AstCaseItem($2,NULL,$3); }
	|	yDEFAULT genItemBlock			{ $$ = new AstCaseItem($1,NULL,$2); }
	|	genCaseList caseCondList ':' genItemBlock	{ $$ = $1;$1->addNext(new AstCaseItem($3,$2,$4)); }
	|       genCaseList yDEFAULT genItemBlock		{ $$ = $1;$1->addNext(new AstCaseItem($2,NULL,$3)); }
	|	genCaseList yDEFAULT ':' genItemBlock		{ $$ = $1;$1->addNext(new AstCaseItem($3,NULL,$4)); }
	;

//************************************************
// Assignments and register declarations

assignList<nodep>:
		assignOne				{ $$ = $1; }
	|	assignList ',' assignOne		{ $$ = $1->addNext($3); }
	;

assignOne<nodep>:
		varRefDotBit '=' expr			{ $$ = new AstAssignW($2,$1,$3); }
	|	'{' concIdList '}' '=' expr		{ $$ = new AstAssignW($1,$2,$5); }
	;

delayE:		/* empty */				{ }
	|	delay					{ } /* ignored */
	;

delay<fileline>:
		'#' dlyTerm				{ $$ = $1; } /* ignored */
	|	'#' '(' minTypMax ')'			{ $$ = $1; } /* ignored */
	|	'#' '(' minTypMax ',' minTypMax ')'			{ $$ = $1; } /* ignored */
	|	'#' '(' minTypMax ',' minTypMax ',' minTypMax ')'	{ $$ = $1; } /* ignored */
	;

dlyTerm<nodep>:
		yaID 					{ $$ = NULL; }
	|	yaINTNUM 				{ $$ = NULL; }
	|	yaFLOATNUM 				{ $$ = NULL; }
	;

// IEEE: mintypmax_expression and constant_mintypmax_expression
minTypMax<nodep>:
		dlyTerm					{ $$ = $1; } /* ignored */
	|	dlyTerm ':' dlyTerm ':' dlyTerm		{ $$ = $1; } /* ignored */
	;

sigAndAttr<varp>:
		sigId sigAttrListE			{ $$ = $1; }
	;

netSigList<varp>:
		netSig  				{ $$ = $1; }
	|	netSigList ',' netSig		       	{ $$ = $1; $1->addNext($3); }
	;

netSig<varp>:
		sigId sigAttrListE			{ $$ = $1; }
	|	sigId sigAttrListE '=' expr		{ $$ = $1; $1->addNext(new AstAssignW($3,new AstVarRef($3,$1->name(),true),$4)); }
	|	sigIdRange sigAttrListE			{ $$ = $1; }
	;

sigIdRange<varp>:
		yaID rangeList				{ $$ = V3Parse::createVariable(CRELINE(), *$1, $2); }
	;

regSigId<varp>:
		yaID rangeListE				{ $$ = V3Parse::createVariable(CRELINE(), *$1, $2); }
	|	yaID rangeListE '=' constExpr		{ $$ = V3Parse::createVariable(CRELINE(), *$1, $2);
							  $$->addNext(new AstInitial($3,new AstAssign($3, new AstVarRef($3, $$, true), $4))); }
	;

sigId<varp>:	yaID					{ $$ = V3Parse::createVariable(CRELINE(), *$1, NULL); }
	;

regsig<varp>:	regSigId sigAttrListE			{}
	;

sigAttrListE:	/* empty */				{}
	|	sigAttrList				{}
	;

sigAttrList:	sigAttr					{}
	|	sigAttrList sigAttr			{}
	;

sigAttr:	yVL_CLOCK				{ V3Parse::s_varAttrp->attrScClocked(true); }
	|	yVL_CLOCK_ENABLE			{ V3Parse::s_varAttrp->attrClockEn(true); }
	|	yVL_PUBLIC				{ V3Parse::s_varAttrp->sigPublic(true); V3Parse::s_varAttrp->sigModPublic(true); }
	|	yVL_PUBLIC_FLAT				{ V3Parse::s_varAttrp->sigPublic(true); }
	|	yVL_ISOLATE_ASSIGNMENTS			{ V3Parse::s_varAttrp->attrIsolateAssign(true); }
	;

rangeListE<rangep>:
		/* empty */    		               	{ $$ = NULL; }
	|	rangeList 				{ $$ = $1; }
	;

rangeList<rangep>:
		anyrange				{ $$ = $1; }
        |	rangeList anyrange			{ $$ = $1; $1->addNext($2); }
	;

regrangeE<rangep>:
		/* empty */    		               	{ $$ = NULL; VARRANGE($$); }
	|	anyrange 				{ $$ = $1; VARRANGE($$); }
	;

anyrange<rangep>:
		'[' constExpr ':' constExpr ']'		{ $$ = new AstRange($1,$2,$4); }
	;

delayrange<rangep>:
		regrangeE delayE 			{ $$ = $1; }
	|	ySCALARED regrangeE delayE 		{ $$ = $2; }
	|	yVECTORED regrangeE delayE 		{ $$ = $2; }
	;

portRangeE<rangep>:
		/* empty */	                   	{ $$ = NULL; }
	|	'[' constExpr ']'              		{ $$ = NULL; $1->v3error("Ranges ignored on port-list.\n"); }
	|	'[' constExpr ':' constExpr  ']'    	{ $$ = NULL; $1->v3error("Ranges ignored on port-list.\n"); }
	;

//************************************************
// Parameters

param<varp>:
		sigId sigAttrListE '=' expr		{ $$ = $1; $$->initp($4); }
	;

paramList<varp>:
		param					{ $$ = $1; }
	|	paramList ',' param			{ $$ = $1; $1->addNext($3); }
	;

// IEEE: list_of_defparam_assignments
defpList<nodep>:
		defpOne					{ $$ = $1; }
	|	defpList ',' defpOne			{ $$ = $1->addNext($3); }
	;

defpOne<nodep>:
		yaID '.' yaID '=' expr 			{ $$ = new AstDefParam($4,*$1,*$3,$5); }
	;

//************************************************
// Instances

instDecl<nodep>:
		yaID instparamListE {INSTPREP(*$1,$2);} instnameList ';'  { $$ = $4; V3Parse::s_impliedDecl=false;}

instparamListE<pinp>:
		/* empty */				{ $$ = NULL; }
	|	'#' '(' cellpinList ')'			{ $$ = $3; }
	;

instnameList<nodep>:
		instnameParen				{ $$ = $1; }
	|	instnameList ',' instnameParen		{ $$ = $1->addNext($3); }
	;

instnameParen<cellp>:
		yaID instRangeE '(' cellpinList ')'	{ $$ = new AstCell($3,       *$1,V3Parse::s_instModule,$4,  V3Parse::s_instParamp,$2); $$->pinStar(V3Parse::s_pinStar); }
	|	yaID instRangeE 			{ $$ = new AstCell(CRELINE(),*$1,V3Parse::s_instModule,NULL,V3Parse::s_instParamp,$2); $$->pinStar(V3Parse::s_pinStar); }
	;

instRangeE<rangep>:
		/* empty */				{ $$ = NULL; }
	|	'[' constExpr ':' constExpr ']'		{ $$ = new AstRange($1,$2,$4); }
	;

cellpinList<pinp>:
		{V3Parse::s_pinNum=1; V3Parse::s_pinStar=false; } cellpinItList	{ $$ = $2; }
	;

cellpinItList<pinp>:
		cellpinItemE				{ $$ = $1; }
	|	cellpinItList ',' cellpinItemE		{ $$ = $1->addNextNull($3)->castPin(); }
	;

cellpinItemE<pinp>:
		/* empty: ',,' is legal */		{ $$ = NULL; V3Parse::s_pinNum++; }
	|	yP_DOTSTAR				{ $$ = NULL; if (V3Parse::s_pinStar) $1->v3error("Duplicate .* in a cell"); V3Parse::s_pinStar=true; }
	|	'.' yaID				{ $$ = new AstPin($1,V3Parse::s_pinNum++,*$2,new AstVarRef($1,*$2,false)); $$->svImplicit(true);}
	|	'.' yaID '(' ')'			{ $$ = NULL; V3Parse::s_pinNum++; }
	|	'.' yaID '(' expr ')'			{ $$ = new AstPin($1,V3Parse::s_pinNum++,*$2,$4); }
	|	expr					{ $$ = new AstPin(CRELINE(),V3Parse::s_pinNum++,"",$1); }
	;

//************************************************
// EventControl lists

eventControlE<sentreep>:
		/* empty */				{ $$ = NULL; }
	|	eventControl				{ $$ = $1; }

// IEEE: event_control
eventControl<sentreep>:
		'@' '(' senList ')'			{ $$ = new AstSenTree($1,$3); }
	|	'@' senitemVar				{ $$ = new AstSenTree($1,$2); }	/* For events only */
	|	'@' '(' '*' ')'				{ $$ = NULL; }  /* Verilog 2001 */
	|	'@' '*'					{ $$ = NULL; }  /* Verilog 2001 */
	;

// IEEE: event_expression - split over several
senList<senitemp>:
		senitem					{ $$ = $1; }
	|	senList yOR senitem			{ $$ = $1;$1->addNext($3); }
	|	senList ',' senitem			{ $$ = $1;$1->addNext($3); }	/* Verilog 2001 */
	;

senitem<senitemp>:
		senitemEdge				{ $$ = $1; }
	|	senitemVar				{ $$ = $1; }
	|	'(' senitemVar ')'			{ $$ = $2; }
	;

senitemVar<senitemp>:
		varRefDotBit				{ $$ = new AstSenItem(CRELINE(),AstEdgeType::ANYEDGE,$1); }
	;

senitemEdge<senitemp>:
		yPOSEDGE varRefDotBit			{ $$ = new AstSenItem($1,AstEdgeType::POSEDGE,$2); }
	|	yNEGEDGE varRefDotBit			{ $$ = new AstSenItem($1,AstEdgeType::NEGEDGE,$2); }
	|	yPOSEDGE '(' varRefDotBit ')'		{ $$ = new AstSenItem($1,AstEdgeType::POSEDGE,$3); }
	|	yNEGEDGE '(' varRefDotBit ')'		{ $$ = new AstSenItem($1,AstEdgeType::NEGEDGE,$3); }
	;

//************************************************
// Statements

stmtBlock<nodep>:
		stmt					{ $$ = $1; }
	|	yBEGIN stmtList yEND			{ $$ = $2; }
	|	yBEGIN yEND				{ $$ = NULL; }
	|	beginNamed stmtList yEND endLabelE	{ $$ = $1; $1->addStmtp($2); }
	|	beginNamed 	    yEND endLabelE	{ $$ = $1; }
	;

beginNamed<beginp>:
		yBEGIN ':' yaID varDeclList		{ $$ = new AstBegin($2,*$3,$4); }
	|	yBEGIN ':' yaID 			{ $$ = new AstBegin($2,*$3,NULL); }
	;

stmtList<nodep>:
		stmtBlock				{ $$ = $1; }
	|	stmtList stmtBlock			{ $$ = ($2==NULL)?($1):($1->addNext($2)); }
	;

stmt<nodep>:
		';'					{ $$ = NULL; }
	|	labeledStmt				{ $$ = $1; }
	|	yaID ':' labeledStmt			{ $$ = new AstBegin($2, *$1, $3); }  /*S05 block creation rule*/

	|	delay stmtBlock				{ $$ = $2; $1->v3warn(STMTDLY,"Ignoring delay on this delayed statement.\n"); }

	|	varRefDotBit yP_LTE delayE expr ';'	{ $$ = new AstAssignDly($2,$1,$4); }
	|	varRefDotBit '=' delayE expr ';'	{ $$ = new AstAssign($2,$1,$4); }
	|	varRefDotBit '=' yD_FOPEN '(' expr ',' expr ')' ';'	{ $$ = new AstFOpen($3,$1,$5,$7); }
	|	yASSIGN varRefDotBit '=' delayE expr ';'	{ $$ = new AstAssign($1,$2,$5); }
	|	'{' concIdList '}' yP_LTE delayE expr ';' { $$ = new AstAssignDly($4,$2,$6); }
	|	'{' concIdList '}' '=' delayE expr ';'  { $$ = new AstAssign($4,$2,$6); }
	|	yD_C '(' cStrList ')' ';'		{ $$ = (v3Global.opt.ignc() ? NULL : new AstUCStmt($1,$3)); }
	|	yD_FCLOSE '(' varRefDotBit ')' ';'	{ $$ = new AstFClose($1, $3); }
	|	yD_FFLUSH ';'				{ $1->v3error("Unsupported: $fflush of all handles does not map to C++.\n"); }
	|	yD_FFLUSH '(' ')' ';'			{ $1->v3error("Unsupported: $fflush of all handles does not map to C++.\n"); }
	|	yD_FFLUSH '(' varRefDotBit ')' ';'	{ $$ = new AstFClose($1, $3); }
	|	yD_FINISH parenE ';'			{ $$ = new AstFinish($1); }
	|	yD_FINISH '(' expr ')' ';'		{ $$ = new AstFinish($1); }
	|	yD_STOP parenE ';'			{ $$ = new AstStop($1); }
	|	yD_STOP '(' expr ')' ';'		{ $$ = new AstStop($1); }
	|	yVL_COVER_OFF				{ $$ = new AstPragma($1,AstPragmaType::COVERAGE_BLOCK_OFF); }
	|	stateCaseForIf				{ $$ = $1; }
	|	taskRef ';' 				{ $$ = $1; }

	|	yD_DISPLAY  parenE ';'						{ $$ = new AstDisplay($1,AstDisplayType::DISPLAY,"", NULL,NULL); }
	|	yD_DISPLAY  '(' yaSTRING commaEListE ')' ';'			{ $$ = new AstDisplay($1,AstDisplayType::DISPLAY,*$3,NULL,$4); }
	|	yD_WRITE    '(' yaSTRING commaEListE ')' ';'			{ $$ = new AstDisplay($1,AstDisplayType::WRITE,  *$3,NULL,$4); }
	|	yD_FDISPLAY '(' varRefDotBit ',' yaSTRING commaEListE ')' ';' 	{ $$ = new AstDisplay($1,AstDisplayType::DISPLAY,*$5,$3,$6); }
	|	yD_FWRITE   '(' varRefDotBit ',' yaSTRING commaEListE ')' ';'	{ $$ = new AstDisplay($1,AstDisplayType::WRITE,  *$5,$3,$6); }
	|	yD_INFO	    parenE ';'						{ $$ = new AstDisplay($1,AstDisplayType::INFO,   "", NULL,NULL); }
	|	yD_INFO	    '(' yaSTRING commaEListE ')' ';'			{ $$ = new AstDisplay($1,AstDisplayType::INFO,   *$3,NULL,$4); }
	|	yD_WARNING  parenE ';'						{ $$ = new AstDisplay($1,AstDisplayType::WARNING,"", NULL,NULL); }
	|	yD_WARNING  '(' yaSTRING commaEListE ')' ';'			{ $$ = new AstDisplay($1,AstDisplayType::WARNING,*$3,NULL,$4); }
	|	yD_ERROR    parenE ';'						{ $$ = V3Parse::createDisplayError($1); }
	|	yD_ERROR    '(' yaSTRING commaEListE ')' ';'			{ $$ = new AstDisplay($1,AstDisplayType::ERROR,  *$3,NULL,$4);   $$->addNext(new AstStop($1)); }
	|	yD_FATAL    parenE ';'						{ $$ = new AstDisplay($1,AstDisplayType::FATAL,  "", NULL,NULL); $$->addNext(new AstStop($1)); }
	|	yD_FATAL    '(' expr ')' ';'					{ $$ = new AstDisplay($1,AstDisplayType::FATAL,  "", NULL,NULL); $$->addNext(new AstStop($1)); if ($3) $3->deleteTree(); }
	|	yD_FATAL    '(' expr ',' yaSTRING commaEListE ')' ';'		{ $$ = new AstDisplay($1,AstDisplayType::FATAL,  *$5,NULL,$6);   $$->addNext(new AstStop($1)); if ($3) $3->deleteTree(); }

	|	yD_READMEMB '(' expr ',' varRefMem ')' ';'			{ $$ = new AstReadMem($1,false,$3,$5,NULL,NULL); }
	|	yD_READMEMB '(' expr ',' varRefMem ',' expr ')' ';'		{ $$ = new AstReadMem($1,false,$3,$5,$7,NULL); }
	|	yD_READMEMB '(' expr ',' varRefMem ',' expr ',' expr ')' ';'	{ $$ = new AstReadMem($1,false,$3,$5,$7,$9); }
	|	yD_READMEMH '(' expr ',' varRefMem ')' ';'			{ $$ = new AstReadMem($1,true, $3,$5,NULL,NULL); }
	|	yD_READMEMH '(' expr ',' varRefMem ',' expr ')' ';'		{ $$ = new AstReadMem($1,true, $3,$5,$7,NULL); }
	|	yD_READMEMH '(' expr ',' varRefMem ',' expr ',' expr ')' ';'	{ $$ = new AstReadMem($1,true, $3,$5,$7,$9); }
	;

//************************************************
// Case/If

stateCaseForIf<nodep>:
		caseStmt caseAttrE caseListE yENDCASE	{ $$ = $1; if ($3) $1->addItemsp($3); }
	|	yIF '(' expr ')' stmtBlock	%prec prLOWER_THAN_ELSE	{ $$ = new AstIf($1,$3,$5,NULL); }
	|	yIF '(' expr ')' stmtBlock yELSE stmtBlock		{ $$ = new AstIf($1,$3,$5,$7); }
	|	yFOR '(' varRefBase '=' expr ';' expr ';' varRefBase '=' expr ')' stmtBlock
							{ $$ = new AstFor($1, new AstAssign($4,$3,$5)
									  ,$7, new AstAssign($10,$9,$11)
									  ,$13);}
	|	yWHILE '(' expr ')' stmtBlock		{ $$ = new AstWhile($1,$3,$5);}
	|	yDO stmtBlock yWHILE '(' expr ')'	{ $$ = $2->cloneTree(true); $$->addNext(new AstWhile($1,$5,$2));}
	;

caseStmt<casep>:
	 	yCASE  '(' expr ')' 			{ $$ = V3Parse::s_caseAttrp = new AstCase($1,AstCaseType::CASE,$3,NULL); }
	|	yCASEX '(' expr ')' 			{ $$ = V3Parse::s_caseAttrp = new AstCase($1,AstCaseType::CASEX,$3,NULL); $1->v3warn(CASEX,"Suggest casez (with ?'s) in place of casex (with X's)\n"); }
	|	yCASEZ '(' expr ')'	 		{ $$ = V3Parse::s_caseAttrp = new AstCase($1,AstCaseType::CASEZ,$3,NULL); }
	;

caseAttrE: 	/*empty*/				{ }
	|	caseAttrE yVL_FULL_CASE			{ V3Parse::s_caseAttrp->fullPragma(true); }
	|	caseAttrE yVL_PARALLEL_CASE		{ V3Parse::s_caseAttrp->parallelPragma(true); }
	;

caseListE<caseitemp>:
		/* empty */				{ $$ = NULL; }
	|	caseList				{ $$ = $1; }
	;

caseList<caseitemp>:
		caseCondList ':' stmtBlock		{ $$ = new AstCaseItem($2,$1,$3); }
	|	yDEFAULT ':' stmtBlock			{ $$ = new AstCaseItem($2,NULL,$3); }
	|	yDEFAULT stmtBlock			{ $$ = new AstCaseItem($1,NULL,$2); }
	|	caseList caseCondList ':' stmtBlock	{ $$ = $1;$1->addNext(new AstCaseItem($3,$2,$4)); }
	|       caseList yDEFAULT stmtBlock		{ $$ = $1;$1->addNext(new AstCaseItem($2,NULL,$3)); }
	|	caseList yDEFAULT ':' stmtBlock		{ $$ = $1;$1->addNext(new AstCaseItem($3,NULL,$4)); }
	;

caseCondList<nodep>:
		expr 					{ $$ = $1; }
	|	caseCondList ',' expr			{ $$ = $1;$1->addNext($3); }
	;

//************************************************
// Functions/tasks

taskRef<nodep>:
		idDotted		 		{ $$ = new AstTaskRef(CRELINE(),new AstParseRef($1->fileline(), AstParseRefExp::TASK, $1),NULL);}
	|	idDotted '(' exprList ')'		{ $$ = new AstTaskRef(CRELINE(),new AstParseRef($1->fileline(), AstParseRefExp::TASK, $1),$3);}
	;

funcRef<nodep>:
		idDotted '(' exprList ')'		{ $$ = new AstFuncRef($2,new AstParseRef($1->fileline(), AstParseRefExp::FUNC, $1), $3); }
	;

taskDecl<nodep>:
		yTASK lifetimeE yaID funcGuts yENDTASK endLabelE
			{ $$ = new AstTask ($1,*$3,$4);}
	;

funcDecl<funcp>:
	 	yFUNCTION lifetimeE         funcTypeE yaID			   funcGuts yENDFUNCTION endLabelE { $$ = new AstFunc ($1,*$4,$5,$3); }
	|	yFUNCTION lifetimeE ySIGNED funcTypeE yaID			   funcGuts yENDFUNCTION endLabelE { $$ = new AstFunc ($1,*$5,$6,$4); $$->isSigned(true); }
	| 	yFUNCTION lifetimeE         funcTypeE yaID yVL_ISOLATE_ASSIGNMENTS funcGuts yENDFUNCTION endLabelE { $$ = new AstFunc ($1,*$4,$6,$3); $$->attrIsolateAssign(true);}
	|	yFUNCTION lifetimeE ySIGNED funcTypeE yaID yVL_ISOLATE_ASSIGNMENTS funcGuts yENDFUNCTION endLabelE { $$ = new AstFunc ($1,*$5,$7,$4); $$->attrIsolateAssign(true); $$->isSigned(true); }
	;

// IEEE: lifetime - plus empty
lifetimeE:	/* empty */		 		{ }
	|	ySTATIC			 		{ $1->v3error("Unsupported: Static in this context\n"); }
	|	yAUTOMATIC		 		{ }
	;

funcGuts<nodep>:
		'(' {V3Parse::s_pinNum=1;} portV2kArgs ')' ';' funcBody	{ $$ = $3->addNextNull($6); }
	|	';' funcBody				{ $$ = $2; }
	;

funcBody<nodep>:
		funcVarList stmtBlock			{ $$ = $1;$1->addNextNull($2); }
	|	stmtBlock				{ $$ = $1; }
	;

funcTypeE<rangep>:
		/* empty */				{ $$ = NULL; }
	|	yINTEGER				{ $$ = new AstRange($1,31,0); }
	|	'[' constExpr ':' constExpr ']'		{ $$ = new AstRange($1,$2,$4); }
	;

funcVarList<nodep>:
		funcVar					{ $$ = $1; }
	|	funcVarList funcVar			{ $$ = $1;$1->addNext($2); }
	;

funcVar<nodep>:
		portDecl				{ $$ = $1; }
	|	varDecl 				{ $$ = $1; }
	|	yVL_PUBLIC				{ $$ = new AstPragma($1,AstPragmaType::PUBLIC_TASK); }
	|	yVL_NO_INLINE_TASK			{ $$ = new AstPragma($1,AstPragmaType::NO_INLINE_TASK); }
	;

parenE:		/* empty */				{ }
	|	'(' ')'					{ }
	;

//************************************************
// Expressions

constExpr<nodep>:
		expr					{ $$ = $1; }
	;

exprNoStr<nodep>:
		expr yP_OROR expr			{ $$ = new AstLogOr	($2,$1,$3); }
	|	expr yP_ANDAND expr			{ $$ = new AstLogAnd	($2,$1,$3); }
	|	expr '&' expr				{ $$ = new AstAnd	($2,$1,$3); }
	|	expr '|' expr				{ $$ = new AstOr	($2,$1,$3); }
	|	expr yP_NAND expr			{ $$ = new AstNot($2,new AstAnd	($2,$1,$3)); }
	|	expr yP_NOR expr			{ $$ = new AstNot($2,new AstOr	($2,$1,$3)); }
	|	expr '^' expr				{ $$ = new AstXor	($2,$1,$3); }
	|	expr yP_XNOR expr			{ $$ = new AstXnor	($2,$1,$3); }
	|	expr yP_EQUAL expr			{ $$ = new AstEq	($2,$1,$3); }
	|	expr yP_NOTEQUAL expr			{ $$ = new AstNeq	($2,$1,$3); }
	|	expr yP_CASEEQUAL expr			{ $$ = new AstEqCase	($2,$1,$3); }
	|	expr yP_CASENOTEQUAL expr		{ $$ = new AstNeqCase	($2,$1,$3); }
	|	expr yP_WILDEQUAL expr			{ $$ = new AstEqWild	($2,$1,$3); }
	|	expr yP_WILDNOTEQUAL expr		{ $$ = new AstNeqWild	($2,$1,$3); }
	|	expr '>' expr				{ $$ = new AstGt	($2,$1,$3); }
	|	expr '<' expr				{ $$ = new AstLt	($2,$1,$3); }
	|	expr yP_GTE expr			{ $$ = new AstGte	($2,$1,$3); }
	|	expr yP_LTE expr			{ $$ = new AstLte	($2,$1,$3); }
	|	expr yP_SLEFT expr			{ $$ = new AstShiftL	($2,$1,$3); }
	|	expr yP_SRIGHT expr			{ $$ = new AstShiftR	($2,$1,$3); }
	|	expr yP_SSRIGHT expr			{ $$ = new AstShiftRS	($2,$1,$3); }
	|	expr '+' expr				{ $$ = new AstAdd	($2,$1,$3); }
	|	expr '-' expr				{ $$ = new AstSub	($2,$1,$3); }
	|	expr '*' expr				{ $$ = new AstMul	($2,$1,$3); }
	|	expr '/' expr				{ $$ = new AstDiv	($2,$1,$3); }
	|	expr '%' expr				{ $$ = new AstModDiv	($2,$1,$3); }
	|	expr yP_POW expr			{ $$ = new AstPow	($2,$1,$3); }
	|	expr yP_MINUSGT expr			{ $$ = new AstLogIf	($2,$1,$3); }
	|	expr yP_LOGIFF expr			{ $$ = new AstLogIff	($2,$1,$3); }

	|	'-' expr	%prec prUNARYARITH	{ $$ = new AstUnaryMin	($1,$2); }
	|	'+' expr	%prec prUNARYARITH	{ $$ = $2; }
	|	'&' expr	%prec prREDUCTION	{ $$ = new AstRedAnd	($1,$2); }
	|	'|' expr	%prec prREDUCTION	{ $$ = new AstRedOr	($1,$2); }
	|	'^' expr	%prec prREDUCTION	{ $$ = new AstRedXor	($1,$2); }
	|	yP_XNOR expr	%prec prREDUCTION	{ $$ = new AstRedXnor	($1,$2); }
	|	yP_NAND expr	%prec prREDUCTION	{ $$ = new AstNot($1,new AstRedAnd($1,$2)); }
	|	yP_NOR expr	%prec prREDUCTION	{ $$ = new AstNot($1,new AstRedOr ($1,$2)); }
	|	'!' expr	%prec prNEGATION	{ $$ = new AstLogNot	($1,$2); }
	|	'~' expr	%prec prNEGATION	{ $$ = new AstNot	($1,$2); }

	|	expr '?' expr ':' expr			{ $$ = new AstCond($2,$1,$3,$5); }
	|	'(' expr ')'				{ $$ = $2; }
	|	'_' '(' statePushVlg expr statePop ')'	{ $$ = $4; }	// Arbitrary Verilog inside PSL
	|	'{' cateList '}'			{ $$ = $2; }
	|	'{' constExpr '{' cateList '}' '}'	{ $$ = new AstReplicate($1,$4,$2); }

	|	yD_BITS '(' expr ')'			{ $$ = new AstAttrOf($1,AstAttrType::BITS,$3); }
	|	yD_C '(' cStrList ')'			{ $$ = (v3Global.opt.ignc() ? NULL : new AstUCFunc($1,$3)); }
	|	yD_CLOG2 '(' expr ')'			{ $$ = new AstCLog2($1,$3); }
	|	yD_COUNTONES '(' expr ')'		{ $$ = new AstCountOnes($1,$3); }
	|	yD_FEOF '(' expr ')'			{ $$ = new AstFEof($1,$3); }
	|	yD_FGETC '(' expr ')'			{ $$ = new AstFGetC($1,$3); }
	|	yD_FGETS '(' varRefDotBit ',' expr ')'	{ $$ = new AstFGetS($1,$3,$5); }
	|	yD_FSCANF '(' expr ',' yaSTRING commaVRDListE ')'	{ $$ = new AstFScanF($1,*$5,$3,$6); }
	|	yD_SSCANF '(' expr ',' yaSTRING commaVRDListE ')'	{ $$ = new AstSScanF($1,*$5,$3,$6); }
	|	yD_ISUNKNOWN '(' expr ')'		{ $$ = new AstIsUnknown($1,$3); }
	|	yD_ONEHOT '(' expr ')'			{ $$ = new AstOneHot($1,$3); }
	|	yD_ONEHOT0 '(' expr ')'			{ $$ = new AstOneHot0($1,$3); }
	|	yD_RANDOM '(' expr ')'			{ $1->v3error("Unsupported: Seeding $random doesn't map to C++, use $c(\"srand\")\n"); }
	|	yD_RANDOM '(' ')'			{ $$ = new AstRand($1); }
	|	yD_RANDOM				{ $$ = new AstRand($1); }
	|	yD_SIGNED '(' expr ')'			{ $$ = new AstSigned($1,$3); }
	|	yD_STIME				{ $$ = new AstSel($1,new AstTime($1),0,32); }
	|	yD_TIME					{ $$ = new AstTime($1); }
	|	yD_UNSIGNED '(' expr ')'		{ $$ = new AstUnsigned($1,$3); }

	|	funcRef					{ $$ = $1; }

	|	yaINTNUM				{ $$ = new AstConst(CRELINE(),*$1); }

	|	varRefDotBit	  			{ $$ = $1; }
	;

// Generic expressions
expr<nodep>:
		exprNoStr				{ $$ = $1; }
	|	strAsInt				{ $$ = $1; }
	;

// Psl excludes {}'s by lexer converting to different token
exprPsl<nodep>:
		exprNoStr				{ $$ = $1; }
	|	strAsInt				{ $$ = $1; }
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
		expr					{ $$ = $1; }
	|	cateList ',' expr			{ $$ = new AstConcat($2,$1,$3); }
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
		varRefDotBit				{ $$ = $1; }
	|	vrdList ',' varRefDotBit		{ $$ = $1;$1->addNext($3); }
	;

commaVRDListE<nodep>:
		/* empty */				{ $$ = NULL; }
	|	',' vrdList				{ $$ = $2; }
	;

//************************************************
// Gate declarations

gateDecl<nodep>:
		yBUF  delayE gateBufList ';'		{ $$ = $3; }
	|	yNOT  delayE gateNotList ';'		{ $$ = $3; }
	|	yAND  delayE gateAndList ';'		{ $$ = $3; }
	|	yNAND delayE gateNandList ';'		{ $$ = $3; }
	|	yOR   delayE gateOrList ';'		{ $$ = $3; }
	|	yNOR  delayE gateNorList ';'		{ $$ = $3; }
	|	yXOR  delayE gateXorList ';'		{ $$ = $3; }
	|	yXNOR delayE gateXnorList ';'		{ $$ = $3; }
	;

gateBufList<nodep>:
		gateBuf 				{ $$ = $1; }
	|	gateBufList ',' gateBuf			{ $$ = $1->addNext($3); }
	;
gateNotList<nodep>:
		gateNot 				{ $$ = $1; }
	|	gateNotList ',' gateNot			{ $$ = $1->addNext($3); }
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

gateBuf<assignwp>:	gateIdE instRangeE '(' varRefDotBit ',' expr ')'		{ $$ = new AstAssignW ($3,$4,$6); $$->allowImplicit(true); }
	;
gateNot<assignwp>:	gateIdE instRangeE '(' varRefDotBit ',' expr ')'		{ $$ = new AstAssignW ($3,$4,new AstNot($5,$6)); $$->allowImplicit(true); }
	;
gateAnd<assignwp>:	gateIdE instRangeE '(' varRefDotBit ',' gateAndPinList ')'	{ $$ = new AstAssignW ($3,$4,$6); $$->allowImplicit(true); }
	;
gateNand<assignwp>: 	gateIdE instRangeE '(' varRefDotBit ',' gateAndPinList ')'	{ $$ = new AstAssignW ($3,$4,new AstNot($5,$6)); $$->allowImplicit(true); }
	;
gateOr<assignwp>:	gateIdE instRangeE '(' varRefDotBit ',' gateOrPinList ')'	{ $$ = new AstAssignW ($3,$4,$6); $$->allowImplicit(true); }
	;
gateNor<assignwp>:	gateIdE instRangeE '(' varRefDotBit ',' gateOrPinList ')'	{ $$ = new AstAssignW ($3,$4,new AstNot($5,$6)); $$->allowImplicit(true); }
	;
gateXor<assignwp>:	gateIdE instRangeE '(' varRefDotBit ',' gateXorPinList ')'	{ $$ = new AstAssignW ($3,$4,$6); $$->allowImplicit(true); }
	;
gateXnor<assignwp>:	gateIdE instRangeE '(' varRefDotBit ',' gateXorPinList ')'	{ $$ = new AstAssignW ($3,$4,new AstNot($5,$6)); $$->allowImplicit(true); }
	;

gateIdE:	/*empty*/				{}
	|	yaID					{}
	;

gateAndPinList<nodep>:
		expr 					{ $$ = $1; }
	|	gateAndPinList ',' expr			{ $$ = new AstAnd($2,$1,$3); }
	;
gateOrPinList<nodep>:
		expr 					{ $$ = $1; }
	|	gateOrPinList ',' expr			{ $$ = new AstOr($2,$1,$3); }
	;
gateXorPinList<nodep>:
		expr 					{ $$ = $1; }
	|	gateXorPinList ',' expr			{ $$ = new AstXor($2,$1,$3); }
	;

//************************************************
// Tables
// Not supported

//************************************************
// Specify

specifyJunkList:	specifyJunk 			{} /* ignored */
	|	specifyJunkList specifyJunk		{} /* ignored */
	;

specifyJunk:	dlyTerm 	{} /* ignored */
	|	';' {}
	|	'!' {}
	|	'&' {}
	|	'(' {}
	|	')' {}
	|	'*' {} | '/' {} | '%' {}
	|	'+' {} | '-' {}
	|	',' {}
	|	':' {}
	|	'$' {}
	|	'=' {}
	|	'>' {} | '<' {}
	|	'?' {}
	|	'^' {}
	|	'{' {} | '}' {}
	|	'[' {} | ']' {}
	|	'|' {}
	|	'~' {}
	|	'@' {}

	|	yIF {}
	|	yNEGEDGE {}
	|	yPOSEDGE {}

	|	yaSTRING {}
	|	yaTIMINGSPEC {}

	|	yP_ANDAND {} | yP_GTE {} | yP_LTE {}
	|	yP_EQUAL {} | yP_NOTEQUAL {}
	|	yP_CASEEQUAL {} | yP_CASENOTEQUAL {}
	|	yP_WILDEQUAL {} | yP_WILDNOTEQUAL {}
	|	yP_XNOR {} | yP_NOR {} | yP_NAND {}
	|	yP_OROR {}
	|	yP_SLEFT {} | yP_SRIGHT {} | yP_SSRIGHT {}
	|	yP_PLUSCOLON {} | yP_MINUSCOLON {}
	|	yP_POW {}

	|	yP_MINUSGT {}
	|	yP_LOGIFF {}
	|	yPSL_BRA {}
	|	yPSL_KET {}
	|	yP_ORMINUSGT {}
	|	yP_OREQGT {}
	|	yP_EQGT {}	| yP_ASTGT {}
	|	yP_ANDANDAND {}
	|	yP_MINUSGTGT {}
	|	yP_POUNDPOUND {}
	|	yP_DOTSTAR {}
	|	yP_ATAT {}
	|	yP_COLONCOLON {}
	|	yP_COLONEQ {}
	|	yP_COLONDIV {}

	|	yP_PLUSEQ {}	| yP_MINUSEQ {}
	|	yP_TIMESEQ {}
	|	yP_DIVEQ {}	| yP_MODEQ {}
	|	yP_ANDEQ {}	| yP_OREQ {}
	|	yP_XOREQ {}
	|	yP_SLEFTEQ {}	| yP_SRIGHTEQ {} | yP_SSRIGHTEQ {}

	|	error {}
	;

//************************************************
// IDs

// VarRef to a Memory
varRefMem<parserefp>:
		idDotted				{ $$ = new AstParseRef($1->fileline(), AstParseRefExp::VAR_MEM, $1); }
	;

// VarRef to dotted, and/or arrayed, and/or bit-ranged variable
varRefDotBit<parserefp>:
		idDotted				{ $$ = new AstParseRef($1->fileline(), AstParseRefExp::VAR_ANY, $1); }
	;

idDotted<nodep>:
		idArrayed 				{ $$ = $1; }
	|	idDotted '.' idArrayed	 		{ $$ = new AstDot($2,$1,$3); }
	;

// Single component of dotted path, maybe [#].
// Due to lookahead constraints, we can't know if [:] or [+:] are valid (last dotted part),
// we'll assume so and cleanup later.
idArrayed<nodep>:
		yaID						{ $$ = new AstText(CRELINE(),*$1); }
	|	idArrayed '[' expr ']'				{ $$ = new AstSelBit($2,$1,$3); }  // Or AstArraySel, don't know yet.
	|	idArrayed '[' constExpr ':' constExpr ']'	{ $$ = new AstSelExtract($2,$1,$3,$5); }
	|	idArrayed '[' expr yP_PLUSCOLON  constExpr ']'	{ $$ = new AstSelPlus($2,$1,$3,$5); }
	|	idArrayed '[' expr yP_MINUSCOLON constExpr ']'	{ $$ = new AstSelMinus($2,$1,$3,$5); }
	;

// VarRef without any dots or vectorizaion
varRefBase<varrefp>:
		yaID					{ $$ = new AstVarRef(CRELINE(),*$1,false);}
	;

strAsInt<nodep>:
		yaSTRING				{ $$ = new AstConst(CRELINE(),V3Number(V3Number::VerilogString(),CRELINE(),V3Parse::deQuote(CRELINE(),*$1)));}
	;

strAsText<nodep>:
		yaSTRING				{ $$ = V3Parse::createTextQuoted(CRELINE(),*$1);}
	;

concIdList<nodep>:
		varRefDotBit				{ $$ = $1; }
	|	concIdList ',' varRefDotBit		{ $$ = new AstConcat($2,$1,$3); }
	;

endLabelE:	/* empty */				{ }
	|	':' yaID				{ }
	;

//************************************************
// Asserts

labeledStmt<nodep>:
		assertStmt				{ $$ = $1; }
	;

clocking_declaration<nodep>:		// IEEE: clocking_declaration  (INCOMPLETE)
		yDEFAULT yCLOCKING '@' '(' senitemEdge ')' ';' yENDCLOCKING
			{ $$ = new AstClocking($1, $5, NULL); }
	;

concurrent_assertion_item<nodep>:	// IEEE: concurrent_assertion_item  (complete)
		concurrent_assertion_statement		{ $$ = $1; }
	|	yaID ':' concurrent_assertion_statement	{ $$ = new AstBegin($2,*$1,$3); }
	;

concurrent_assertion_statement<nodep>:	// IEEE: concurrent_assertion_statement  (INCOMPLETE)
		cover_property_statement		{ $$ = $1; }
	;

cover_property_statement<nodep>:	// IEEE: cover_property_statement (complete)
		yCOVER yPROPERTY '(' property_spec ')' stmtBlock	{ $$ = new AstPslCover($1,$4,$6); }
	;

property_spec<nodep>:			// IEEE: property_spec
		'@' '(' senitemEdge ')' property_spec_disable expr	{ $$ = new AstPslClocked($1,$3,$5,$6); }
	|	property_spec_disable expr	 			{ $$ = new AstPslClocked(CRELINE(),NULL,$1,$2); }
	;

property_spec_disable<nodep>:
		/* empty */				{ $$ = NULL; }
	|	yDISABLE yIFF '(' expr ')'		{ $$ = $4; }
	;

assertStmt<nodep>:
		yASSERT '(' expr ')' stmtBlock %prec prLOWER_THAN_ELSE	{ $$ = new AstVAssert($1,$3,$5, V3Parse::createDisplayError($1)); }
	|	yASSERT '(' expr ')'           yELSE stmtBlock		{ $$ = new AstVAssert($1,$3,NULL,$6); }
	|	yASSERT '(' expr ')' stmtBlock yELSE stmtBlock		{ $$ = new AstVAssert($1,$3,$5,$7);   }
	;

//************************************************
// PSL Statements

pslStmt<nodep>:
		yPSL pslDir  stateExitPsl		{ $$ = $2; }
	|	yPSL pslDecl stateExitPsl 		{ $$ = $2; }
	;

pslDir<nodep>:
		yaID ':' pslDirOne			{ $$ = $3; }
	|	pslDirOne		       		{ $$ = $1; }
	;

pslDirOne<nodep>:
		yPSL_ASSERT pslProp ';'				{ $$ = new AstPslAssert($1,$2); }
	|	yPSL_ASSERT pslProp yPSL_REPORT yaSTRING ';'	{ $$ = new AstPslAssert($1,$2,*$4); }
	|	yPSL_COVER  pslProp ';'				{ $$ = new AstPslCover($1,$2,NULL); }
	|	yPSL_COVER  pslProp yPSL_REPORT yaSTRING ';'	{ $$ = new AstPslCover($1,$2,NULL,*$4); }
	;

pslDecl<nodep>:
		yDEFAULT yPSL_CLOCK '=' senitemEdge ';'		{ $$ = new AstPslDefClock($3, $4); UINFO(0,"CRE "<<$$<<endl)}
	|	yDEFAULT yPSL_CLOCK '=' '(' senitemEdge ')' ';'	{ $$ = new AstPslDefClock($3, $5); }
	;

//************************************************
// PSL Properties, Sequences and SEREs
// Don't use '{' or '}'; in PSL they're yPSL_BRA and yPSL_KET to avoid expr concatenates

pslProp<nodep>:
		pslSequence				{ $$ = $1; }
	|	pslSequence '@' %prec prPSLCLK '(' senitemEdge ')' { $$ = new AstPslClocked($2,$4,NULL,$1); }  // or pslSequence @ ...?
	;

pslSequence<nodep>:
		yPSL_BRA pslSere yPSL_KET		{ $$ = $2; }
	;

pslSere<nodep>:
		pslExpr					{ $$ = $1; }
	|	pslSequence				{ $$ = $1; }  // Sequence containing sequence
	;

// Undocumented PSL rule is that {} is always a SERE; concatenation is not allowed.
// This can be bypassed with the _(...) embedding of any arbitrary expression.
pslExpr<nodep>:
		exprPsl					{ $$ = new AstPslBool($1->fileline(), $1); }
	|	yTRUE					{ $$ = new AstPslBool($1, new AstConst($1, V3Number($1,1,1))); }
	;

//**********************************************************************
%%

void V3Read::parserClear() {
    // Clear up any dynamic memory V3Parser required
    V3Parse::setRange(NULL);
}

AstNode* V3Parse::createSupplyExpr(FileLine* fileline, string name, int value) {
    FileLine* newfl = new FileLine (fileline);
    newfl->warnOff(V3ErrorCode::WIDTH, true);
    AstNode* nodep = new AstConst(newfl, V3Number(fileline));
    // Adding a NOT is less work than figuring out how wide to make it
    if (value) nodep = new AstNot(newfl, nodep);
    nodep = new AstAssignW(newfl, new AstVarRef(fileline, name, true),
			   nodep);
    return nodep;
}

AstVar* V3Parse::createVariable(FileLine* fileline, string name, AstRange* arrayp) {
    AstVarType type = V3Parse::s_varIO;
    AstRange* rangep = V3Parse::s_varRangep;
    AstRange* cleanup_rangep = NULL;
    //UINFO(0,"CREVAR "<<fileline->ascii()<<" decl="<<V3Parse::s_varDecl.ascii()<<" io="<<V3Parse::s_varIO.ascii()<<endl);
    if (type == AstVarType::UNKNOWN) type = V3Parse::s_varDecl;
    if (type == AstVarType::UNKNOWN) fileline->v3fatalSrc("Unknown signal type declared");
    // Linting, because we allow parsing of a superset of the language
    if (type == AstVarType::INTEGER || V3Parse::s_varDecl == AstVarType::INTEGER
	|| type == AstVarType::GENVAR) {
	if (rangep) fileline->v3error("Integers may not be ranged: "<<name);
	cleanup_rangep = new AstRange(fileline, 31, 0);  // Integer == REG[31:0]
	rangep = cleanup_rangep;
    }
    if (type == AstVarType::GENVAR) {
	if (arrayp) fileline->v3error("Genvars may not be arrayed: "<<name);
    }
    AstVar* nodep = new AstVar(fileline, type, name,
			       rangep->cloneTree(false),
			       arrayp);
    nodep->isSigned(V3Parse::s_varSigned);
    if (type == AstVarType::INTEGER || V3Parse::s_varDecl == AstVarType::INTEGER
	|| type == AstVarType::GENVAR) {
	nodep->isSigned(true);
    }
    if (V3Parse::s_varDecl != AstVarType::UNKNOWN) nodep->combineType(V3Parse::s_varDecl);
    if (V3Parse::s_varIO != AstVarType::UNKNOWN) nodep->combineType(V3Parse::s_varIO);

    if (V3Parse::s_varDecl == AstVarType::SUPPLY0) {
	nodep->addNext(V3Parse::createSupplyExpr(fileline, nodep->name(), 0));
    }
    if (V3Parse::s_varDecl == AstVarType::SUPPLY1) {
	nodep->addNext(V3Parse::createSupplyExpr(fileline, nodep->name(), 1));
    }
    // Clear any widths that got presumed by the ranging;
    // We need to autosize parameters and integers separately
    nodep->width(0,0);
    // Propagate from current module tracing state
    if (nodep->isGenVar() || nodep->isParam()) nodep->trace(false);
    else nodep->trace(V3Parse::s_trace);

    // Remember the last variable created, so we can attach attributes to it in later parsing
    V3Parse::s_varAttrp = nodep;
    if (cleanup_rangep) { cleanup_rangep->deleteTree(); cleanup_rangep=NULL; }
    return nodep;
}

string V3Parse::deQuote(FileLine* fileline, string text) {
    // Fix up the quoted strings the user put in, for example "\"" becomes "
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

AstText* V3Parse::createTextQuoted(FileLine* fileline, string text) {
    string newtext = deQuote(fileline, text);
    return new AstText(fileline, newtext);
}

// Local Variables:
// compile-command: "cd obj_dbg ; /usr/bin/bison -y -d -v ../verilog.y ; cat y.output"
// End:
