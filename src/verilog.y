// -*- C++ -*-
//*************************************************************************
// DESCRIPTION: Verilator: Bison grammer file
//
// Code available from: http://www.veripool.org/verilator
//
//*************************************************************************
//
// Copyright 2003-2009 by Wilson Snyder.  This program is free software; you can
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
#define YYINITDEPTH 10000	// Older bisons ignore YYMAXDEPTH
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
    static int		s_uniqueAttr;	// Bitmask of unique/priority keywords

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
    V3UniqState	uniqstate;

    AstNode*	nodep;

    AstAssignW* assignwp;
    AstPull*    pullp;
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
    AstNodeSenItem*	senitemp;
    AstSenTree*	sentreep;
    AstVar*	varp;
    AstVarRef*	varrefp;
}

// When writing Bison patterns we use yTOKEN instead of "token",
// so Bison will error out on unknown "token"s.

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
// IEEE: time_literal + time_unit
%token<cdouble>		yaTIMENUM	"TIME NUMBER"
// IEEE: string_literal
%token<strp>		yaSTRING	"STRING"
%token<fileline>	yaTIMINGSPEC	"TIMING SPEC ELEMENT"

%token<strp>		yaSCHDR		"`systemc_header BLOCK"
%token<strp>		yaSCINT		"`systemc_ctor BLOCK"
%token<strp>		yaSCIMP		"`systemc_dtor BLOCK"
%token<strp>		yaSCIMPH	"`systemc_interface BLOCK"
%token<strp>		yaSCCTOR	"`systemc_implementation BLOCK"
%token<strp>		yaSCDTOR	"`systemc_imp_header BLOCK"

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
%token<fileline>	yBUFIF0		"bufif0"
%token<fileline>	yBUFIF1		"bufif1"
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
%token<fileline>	yNOTIF0		"notif0"
%token<fileline>	yNOTIF1		"notif1"
%token<fileline>	yOR		"or"
%token<fileline>	yOUTPUT		"output"
%token<fileline>	yPARAMETER	"parameter"
%token<fileline>	yPOSEDGE	"posedge"
%token<fileline>	yPRIORITY	"priority"
%token<fileline>	yPROPERTY	"property"
%token<fileline>	yPULLDOWN 	"pulldown"
%token<fileline>	yPULLUP 	"pullup"
%token<fileline>	yREG		"reg"
%token<fileline>	ySCALARED	"scalared"
%token<fileline>	ySIGNED		"signed"
%token<fileline>	ySPECIFY	"specify"
%token<fileline>	ySTATIC		"static"
%token<fileline>	ySUPPLY0	"supply0"
%token<fileline>	ySUPPLY1	"supply1"
%token<fileline>	yTASK		"task"
%token<fileline>	yTIMEPRECISION	"timeprecision"
%token<fileline>	yTIMEUNIT	"timeunit"
%token<fileline>	yTRI		"tri"
%token<fileline>	yTRUE		"true"
%token<fileline>	yUNIQUE		"unique"
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
%token<fileline>	yVL_COVERAGE_BLOCK_OFF	"/*verilator coverage_block_off*/"
%token<fileline>	yVL_FULL_CASE		"/*verilator full_case*/"
%token<fileline>	yVL_INLINE_MODULE	"/*verilator inline_module*/"
%token<fileline>	yVL_ISOLATE_ASSIGNMENTS	"/*verilator isolate_assignments*/"
%token<fileline>	yVL_NO_INLINE_MODULE	"/*verilator no_inline_module*/"
%token<fileline>	yVL_NO_INLINE_TASK	"/*verilator no_inline_task*/"
%token<fileline>	yVL_PARALLEL_CASE	"/*verilator parallel_case*/"
%token<fileline>	yVL_PUBLIC		"/*verilator public*/"
%token<fileline>	yVL_PUBLIC_FLAT		"/*verilator public_flat*/"
%token<fileline>	yVL_PUBLIC_MODULE	"/*verilator public_module*/"

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

// [* is not a operator, as "[ * ]" is legal
// [= and [-> could be repitition operators, but to match [* we don't add them.
// '( is not a operator, as "' (" is legal

//********************
// PSL op precedence
%right	 	yP_MINUSGT  yP_LOGIFF
%right		yP_ORMINUSGT  yP_OREQGT
%left<fileline>	prPSLCLK

// Verilog op precedence
%right		'?' ':'
%left		yP_OROR
%left		yP_ANDAND
%left		'|' yP_NOR
%left		'^' yP_XNOR
%left		'&' yP_NAND
%left		yP_EQUAL yP_NOTEQUAL yP_CASEEQUAL yP_CASENOTEQUAL yP_WILDEQUAL yP_WILDNOTEQUAL
%left		'>' '<' yP_GTE yP_LTE
%left		yP_SLEFT yP_SRIGHT yP_SSRIGHT
%left		'+' '-'
%left		'*' '/' '%'
%left		yP_POW
%left		prUNARYARITH prREDUCTION prNEGATION

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

%start source_text

%%
//**********************************************************************
// Feedback to the Lexer
// Note we read a parenthesis ahead, so this may not change the lexer at the right point.

stateExitPsl:			// For PSL lexing, return from PSL state
		/* empty */			 	{ V3Read::stateExitPsl(); }
	;
statePushVlg:			// For PSL lexing, escape current state into Verilog state
		/* empty */			 	{ V3Read::statePushVlg(); }
	;
statePop:			// Return to previous lexing state
		/* empty */			 	{ V3Read::statePop(); }
	;

//**********************************************************************
// Files

source_text:			// ==IEEE: source_text
		/* empty */				{ }
	|       timeunits_declarationE 	descriptionList	{ }
	;

descriptionList:		// IEEE: part of source_text
		description				{ }
	|	descriptionList description		{ }
	;

description:			// ==IEEE: description
		module_declaration			{ }
//	|	interface_declaration			{ }
//      |       program_declaration			{ }
//	|       package_declaration			{ }
//	|	package_item				{ }
//	|	bind_directive				{ }
	//	unsupported	// IEEE: config_declaration
	|	error					{ }
	;

timeunits_declarationE:		// IEEE: timeunits_declaration + empty
		/*empty*/							{ }
	|	yTIMEUNIT       yaTIMENUM ';'					{ }
	| 	yTIMEPRECISION  yaTIMENUM ';'					{ }
	| 	yTIMEUNIT       yaTIMENUM ';' yTIMEPRECISION  yaTIMENUM ';' 	{ }
	| 	yTIMEPRECISION  yaTIMENUM ';' yTIMEUNIT       yaTIMENUM ';'	{ }
	;

//**********************************************************************
// Module headers

module_declaration:		// ==IEEE: module_declaration (incomplete)
		modHeader timeunits_declarationE module_itemListE yENDMODULE endLabelE
			{ if ($3) $1->addStmtp($3); }
	;

modHeader<modulep>:		// IEEE: module_nonansi_header + module_ansi_header
		modHdr parameter_port_listE modPortsStarE ';'
			{ $1->modTrace(v3Global.opt.trace() && $1->fileline()->tracingOn());  // Stash for implicit wires, etc
			  if ($2) $1->addStmtp($2); if ($3) $1->addStmtp($3); }
	;

modHdr<modulep>:
		yMODULE lifetimeE yaID
			{ $$ = new AstModule($1,*$3); $$->inLibrary(V3Read::inLibrary()||V3Read::inCellDefine());
			  $$->modTrace(v3Global.opt.trace());
			  V3Read::rootp()->addModulep($$); }
	;

parameter_port_listE<nodep>:	// IEEE: parameter_port_list + empty == parameter_value_assignment
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

modPortsStarE<nodep>:
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
		varRESET port_direction v2kVarDeclE signingE regrangeE portV2kInit	{ $$ = $6; }
	;

portDecl<nodep>:		// IEEE: port_declaration - plus ';'
		varRESET port_direction v2kVarDeclE signingE regrangeE  regsigList ';'	{ $$ = $6; }
	;

varDecl<nodep>:
		varRESET varReg     signingE regrangeE  regsigList ';'	{ $$ = $5; }
	|	varRESET varGParam  signingE regrangeE  paramList ';'		{ $$ = $5; }
	|	varRESET varLParam  signingE regrangeE  paramList ';'		{ $$ = $5; }
	|	varRESET net_type    signingE delayrange netSigList ';'	{ $$ = $5; }
	|	varRESET varGenVar  signingE            regsigList ';'	{ $$ = $4; }
	;

modParDecl<nodep>:
		varRESET varGParam  signingE regrangeE   param 	{ $$ = $5; }
	;

varRESET:
		/* empty */ 				{ VARRESET(); }
	;

net_type:			// ==IEEE: net_type
		ySUPPLY0				{ VARDECL(SUPPLY0); }
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

port_direction:			// ==IEEE: port_direction
		yINPUT					{ VARIO(INPUT); }
	|	yOUTPUT					{ VARIO(OUTPUT); }
	|	yINOUT					{ VARIO(INOUT); }
//	|	yREF					{ VARIO(REF); }
	;

signingE:			// IEEE: signing - plus empty
		/*empty*/ 				{ }
	|	ySIGNED					{ VARSIGNED(true); }
	|	yUNSIGNED				{ VARSIGNED(false); }
	;

v2kVarDeclE:
		/*empty*/ 				{ }
	|	net_type				{ }
	|	varReg 					{ }
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
	//			// IEEE: non_port_module_item
		generate_region				{ $$ = $1; }
	|	module_or_generate_item 		{ $$ = $1; }
	|	specify_block 				{ $$ = $1; }
	//			// Verilator specific
	|	yaSCHDR					{ $$ = new AstScHdr(CRELINE(),*$1); }
	|	yaSCINT					{ $$ = new AstScInt(CRELINE(),*$1); }
	|	yaSCIMP					{ $$ = new AstScImp(CRELINE(),*$1); }
	|	yaSCIMPH				{ $$ = new AstScImpHdr(CRELINE(),*$1); }
	|	yaSCCTOR				{ $$ = new AstScCtor(CRELINE(),*$1); }
	|	yaSCDTOR				{ $$ = new AstScDtor(CRELINE(),*$1); }
	|	yVL_INLINE_MODULE			{ $$ = new AstPragma($1,AstPragmaType::INLINE_MODULE); }
	|	yVL_NO_INLINE_MODULE			{ $$ = new AstPragma($1,AstPragmaType::NO_INLINE_MODULE); }
	|	yVL_PUBLIC_MODULE			{ $$ = new AstPragma($1,AstPragmaType::PUBLIC_MODULE); }
	;

generate_region<nodep>:		// ==IEEE: generate_region
		yGENERATE genTopBlock yENDGENERATE	{ $$ = new AstGenerate($1, $2); }
	;

// IEEE: module_or_generate_item + module_common_item + parameter_override
module_or_generate_item<nodep>:
	//			// IEEE: always_construct
		yALWAYS event_controlE stmtBlock	{ $$ = new AstAlways($1,$2,$3); }
	|	continuous_assign			{ $$ = $1; }
	|	initial_construct			{ $$ = $1; }
	|	final_construct				{ $$ = $1; }
	|	yDEFPARAM list_of_defparam_assignments ';'	{ $$ = $2; }
	|	instDecl 				{ $$ = $1; }
	|	task_declaration 			{ $$ = $1; }
	|	function_declaration 			{ $$ = $1; }
	|	gateDecl 				{ $$ = $1; }
	|	portDecl 				{ $$ = $1; }
	|	varDecl 				{ $$ = $1; }
	//No: |	tableDecl				// Unsupported
	|	pslStmt 				{ $$ = $1; }
	|	concurrent_assertion_item		{ $$ = $1; }  // IEEE puts in module_item; seems silly
	|	clocking_declaration			{ $$ = $1; }
	;

continuous_assign<nodep>:	// IEEE: continuous_assign
		yASSIGN delayE assignList ';'		{ $$ = $3; }
	;

initial_construct<nodep>:	// IEEE: initial_construct
		yINITIAL stmtBlock			{ $$ = new AstInitial($1,$2); }
	;

final_construct<nodep>:		// IEEE: final_construct
		yFINAL stmtBlock			{ $$ = new AstFinal($1,$2); }
	;

//************************************************
// Generates

// Because genItemList includes variable declarations, we don't need beginNamed
generate_block_or_null<nodep>:	// IEEE: generate_block_or_null
		genItem					{ $$ = new AstBegin(CRELINE(),"genblk",$1); }
	|	genItemBegin				{ $$ = $1; }
	;

genTopBlock<nodep>:
		genItemList				{ $$ = $1; }
	|	genItemBegin				{ $$ = $1; }
	;

genItemBegin<nodep>:		// IEEE: part of generate_block
		yBEGIN genItemList yEND			{ $$ = new AstBegin($1,"genblk",$2); }
	|	yBEGIN yEND				{ $$ = NULL; }
	|	yaID ':' yBEGIN genItemList yEND endLabelE	{ $$ = new AstBegin($2,*$1,$4); }
	|	yaID ':' yBEGIN             yEND endLabelE	{ $$ = NULL; }
	|	yBEGIN ':' yaID genItemList yEND endLabelE	{ $$ = new AstBegin($2,*$3,$4); }
	|	yBEGIN ':' yaID 	    yEND endLabelE	{ $$ = NULL; }
	;

genItemList<nodep>:
		genItem					{ $$ = $1; }
	|	genItemList genItem			{ $$ = $1->addNextNull($2); }
	;

genItem<nodep>:		// IEEE: module_or_interface_or_generate_item (INCOMPLETE)
		module_or_generate_item			{ $$ = $1; }
	|	conditional_generate_construct		{}
	|	loop_generate_construct			{}
	;

conditional_generate_construct<nodep>:	// ==IEEE: conditional_generate_construct
		yCASE  '(' expr ')' case_generate_itemListE yENDCASE	{ $$ = new AstGenCase($1,$3,$5); }
	|	yIF '(' expr ')' generate_block_or_null	%prec prLOWER_THAN_ELSE	{ $$ = new AstGenIf($1,$3,$5,NULL); }
	|	yIF '(' expr ')' generate_block_or_null yELSE generate_block_or_null	{ $$ = new AstGenIf($1,$3,$5,$7); }
	;

loop_generate_construct<nodep>:	// ==IEEE: loop_generate_construct
		yFOR '(' varRefBase '=' expr ';' expr ';' varRefBase '=' expr ')' generate_block_or_null
			{ $$ = new AstGenFor($1, new AstAssign($4,$3,$5)
					     ,$7, new AstAssign($10,$9,$11)
					     ,$13);}
	;

case_generate_itemListE<nodep>:	// IEEE: [{ case_generate_itemList }]
		/* empty */				{ $$ = NULL; }
	|	case_generate_itemList			{ $$ = $1; }
	;

case_generate_itemList<nodep>:	// IEEE: { case_generate_itemList }
		case_generate_item			{ $$=$1; }
	|	case_generate_itemList case_generate_item	{ $$=$1; $1->addNext($2); }
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
		varRefDotBit '=' expr			{ $$ = new AstAssignW($2,$1,$3); }
	|	'{' identifier_listLvalue '}' '=' expr	{ $$ = new AstAssignW($1,$2,$5); }
	;

delayE:
		/* empty */				{ }
	|	delay_control				{ } /* ignored */
	;

delay_control<fileline>:	//== IEEE: delay_control
		'#' dlyTerm				{ $$ = $1; } /* ignored */
	|	'#' '(' minTypMax ')'			{ $$ = $1; } /* ignored */
	|	'#' '(' minTypMax ',' minTypMax ')'			{ $$ = $1; } /* ignored */
	|	'#' '(' minTypMax ',' minTypMax ',' minTypMax ')'	{ $$ = $1; } /* ignored */
	;

dlyTerm<nodep>:
		yaID 					{ $$ = NULL; }
	|	yaINTNUM 				{ $$ = NULL; }
	|	yaFLOATNUM 				{ $$ = NULL; }
	|	yaTIMENUM 				{ $$ = NULL; }
	;

minTypMax<nodep>:		// IEEE: mintypmax_expression and constant_mintypmax_expression
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
							  $$->addNext(new AstInitial($3,new AstAssign($3, new AstVarRef($3, *$1, true), $4))); }
	;

sigId<varp>:
		yaID					{ $$ = V3Parse::createVariable(CRELINE(), *$1, NULL); }
	;

regsig<varp>:
		regSigId sigAttrListE			{}
	;

sigAttrListE:
		/* empty */				{}
	|	sigAttrList				{}
	;

sigAttrList:
		sigAttr					{}
	|	sigAttrList sigAttr			{}
	;

sigAttr:
		yVL_CLOCK				{ V3Parse::s_varAttrp->attrScClocked(true); }
	|	yVL_CLOCK_ENABLE			{ V3Parse::s_varAttrp->attrClockEn(true); }
	|	yVL_PUBLIC				{ V3Parse::s_varAttrp->sigPublic(true); V3Parse::s_varAttrp->sigModPublic(true); }
	|	yVL_PUBLIC_FLAT				{ V3Parse::s_varAttrp->sigPublic(true); }
	|	yVL_ISOLATE_ASSIGNMENTS			{ V3Parse::s_varAttrp->attrIsolateAssign(true); }
	;

rangeListE<rangep>:
		/* empty */    		               	{ $$ = NULL; }
	|	rangeList 				{ $$ = $1; }
	;

rangeList<rangep>:		// IEEE: packed_dimension + ...
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

list_of_defparam_assignments<nodep>:	//== IEEE: list_of_defparam_assignments
		defparam_assignment			{ $$ = $1; }
	|	list_of_defparam_assignments ',' defparam_assignment	{ $$ = $1->addNext($3); }
	;

defparam_assignment<nodep>:	// ==IEEE: defparam_assignment
		yaID '.' yaID '=' expr 			{ $$ = new AstDefParam($4,*$1,*$3,$5); }
	;

//************************************************
// Instances

instDecl<nodep>:
		yaID instparamListE {INSTPREP(*$1,$2);} instnameList ';'  { $$ = $4; V3Parse::s_impliedDecl=false;}
	;

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

event_controlE<sentreep>:
		/* empty */				{ $$ = NULL; }
	|	event_control				{ $$ = $1; }
	;

event_control<sentreep>:	// ==IEEE: event_control
		'@' '(' senList ')'			{ $$ = new AstSenTree($1,$3); }
	|	'@' senitemVar				{ $$ = new AstSenTree($1,$2); }	/* For events only */
	|	'@' '(' '*' ')'				{ $$ = NULL; }
	|	'@' '*'					{ $$ = NULL; }  /* Verilog 2001 */
	;

senList<senitemp>:		// IEEE: event_expression - split over several
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

senitemEdge<senitemp>:		// IEEE: part of event_expression
		yPOSEDGE varRefDotBit			{ $$ = new AstSenItem($1,AstEdgeType::POSEDGE,$2); }
	|	yNEGEDGE varRefDotBit			{ $$ = new AstSenItem($1,AstEdgeType::NEGEDGE,$2); }
	|	yPOSEDGE '(' varRefDotBit ')'		{ $$ = new AstSenItem($1,AstEdgeType::POSEDGE,$3); }
	|	yNEGEDGE '(' varRefDotBit ')'		{ $$ = new AstSenItem($1,AstEdgeType::NEGEDGE,$3); }
	;

//************************************************
// Statements

stmtBlock<nodep>:		// IEEE: statement + seq_block + par_block
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

// IEEE: statement_or_null (may include more stuff, not analyzed)
//	== function_statement_or_null
stmt<nodep>:
	//			// from _or_null
		';'					{ $$ = NULL; }
	|	labeledStmt				{ $$ = $1; }
	|	yaID ':' labeledStmt			{ $$ = new AstBegin($2, *$1, $3); }  /*S05 block creation rule*/
	//
	|	delay_control stmtBlock			{ $$ = $2; $1->v3warn(STMTDLY,"Ignoring delay on this delayed statement.\n"); }
	//
	//			// IEEE: operator_assignment
	|	varRefDotBit '=' delayE expr ';'	{ $$ = new AstAssign($2,$1,$4); }
	|	varRefDotBit '=' yD_FOPEN '(' expr ',' expr ')' ';'	{ $$ = new AstFOpen($3,$1,$5,$7); }
	|	'{' identifier_listLvalue '}' '=' delayE expr ';'  { $$ = new AstAssign($4,$2,$6); }
	//
	//			// IEEE: nonblocking_assignment
	|	varRefDotBit yP_LTE delayE expr ';'	{ $$ = new AstAssignDly($2,$1,$4); }
	|	'{' identifier_listLvalue '}' yP_LTE delayE expr ';' { $$ = new AstAssignDly($4,$2,$6); }
	//
	//			// IEEE: procedural_continuous_assignment
	|	yASSIGN varRefDotBit '=' delayE expr ';'	{ $$ = new AstAssign($1,$2,$5); }
	//
	//			// IEEE: case_statement
	|	unique_priorityE caseStart caseAttrE case_itemListE yENDCASE	{ $$ = $2; if ($4) $2->addItemsp($4);
							  if ($1 == uniq_UNIQUE) $2->parallelPragma(true);
							  if ($1 == uniq_PRIORITY) $2->fullPragma(true); }
	//
	//			// IEEE: conditional_statement
	|	unique_priorityE yIF '(' expr ')' stmtBlock	%prec prLOWER_THAN_ELSE
							{ $$ = new AstIf($2,$4,$6,NULL); }
	|	unique_priorityE yIF '(' expr ')' stmtBlock yELSE stmtBlock
							{ $$ = new AstIf($2,$4,$6,$8); }
	//
	//			// IEEE: subroutine_call_statement (INCOMPLETE)
	|	taskRef ';' 				{ $$ = $1; }
	//
	|	yD_C '(' cStrList ')' ';'		{ $$ = (v3Global.opt.ignc() ? NULL : new AstUCStmt($1,$3)); }
	|	yD_FCLOSE '(' varRefDotBit ')' ';'	{ $$ = new AstFClose($1, $3); }
	|	yD_FFLUSH ';'				{ $1->v3error("Unsupported: $fflush of all handles does not map to C++.\n"); }
	|	yD_FFLUSH '(' ')' ';'			{ $1->v3error("Unsupported: $fflush of all handles does not map to C++.\n"); }
	|	yD_FFLUSH '(' varRefDotBit ')' ';'	{ $$ = new AstFClose($1, $3); }
	|	yD_FINISH parenE ';'			{ $$ = new AstFinish($1); }
	|	yD_FINISH '(' expr ')' ';'		{ $$ = new AstFinish($1); }
	|	yD_STOP parenE ';'			{ $$ = new AstStop($1); }
	|	yD_STOP '(' expr ')' ';'		{ $$ = new AstStop($1); }
	|	yVL_COVERAGE_BLOCK_OFF			{ $$ = new AstPragma($1,AstPragmaType::COVERAGE_BLOCK_OFF); }
	//
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
	//
	|	yD_READMEMB '(' expr ',' varRefMem ')' ';'			{ $$ = new AstReadMem($1,false,$3,$5,NULL,NULL); }
	|	yD_READMEMB '(' expr ',' varRefMem ',' expr ')' ';'		{ $$ = new AstReadMem($1,false,$3,$5,$7,NULL); }
	|	yD_READMEMB '(' expr ',' varRefMem ',' expr ',' expr ')' ';'	{ $$ = new AstReadMem($1,false,$3,$5,$7,$9); }
	|	yD_READMEMH '(' expr ',' varRefMem ')' ';'			{ $$ = new AstReadMem($1,true, $3,$5,NULL,NULL); }
	|	yD_READMEMH '(' expr ',' varRefMem ',' expr ')' ';'		{ $$ = new AstReadMem($1,true, $3,$5,$7,NULL); }
	|	yD_READMEMH '(' expr ',' varRefMem ',' expr ',' expr ')' ';'	{ $$ = new AstReadMem($1,true, $3,$5,$7,$9); }
	//
	//			// IEEE: loop_statement (INCOMPLETE)
	|	yWHILE '(' expr ')' stmtBlock		{ $$ = new AstWhile($1,$3,$5);}
	|	yFOR '(' varRefBase '=' expr ';' expr ';' varRefBase '=' expr ')' stmtBlock
							{ $$ = new AstFor($1, new AstAssign($4,$3,$5)
									  ,$7, new AstAssign($10,$9,$11)
									  ,$13);}
	|	yDO stmtBlock yWHILE '(' expr ')'	{ $$ = $2->cloneTree(true); $$->addNext(new AstWhile($1,$5,$2));}
	;

//************************************************
// Case/If

unique_priorityE<uniqstate>:	// IEEE: unique_priority + empty
		/*empty*/				{ $$ = uniq_NONE; }
	|	yPRIORITY				{ $$ = uniq_PRIORITY; }
	|	yUNIQUE					{ $$ = uniq_UNIQUE; }
	;

caseStart<casep>:		// IEEE: part of case_statement
	 	yCASE  '(' expr ')' 			{ $$ = V3Parse::s_caseAttrp = new AstCase($1,AstCaseType::CASE,$3,NULL); }
	|	yCASEX '(' expr ')' 			{ $$ = V3Parse::s_caseAttrp = new AstCase($1,AstCaseType::CASEX,$3,NULL); $1->v3warn(CASEX,"Suggest casez (with ?'s) in place of casex (with X's)\n"); }
	|	yCASEZ '(' expr ')'			{ $$ = V3Parse::s_caseAttrp = new AstCase($1,AstCaseType::CASEZ,$3,NULL); }
	;

caseAttrE:
	 	/*empty*/				{ }
	|	caseAttrE yVL_FULL_CASE			{ V3Parse::s_caseAttrp->fullPragma(true); }
	|	caseAttrE yVL_PARALLEL_CASE		{ V3Parse::s_caseAttrp->parallelPragma(true); }
	;

case_itemListE<caseitemp>:	// IEEE: [ { case_item } ]
		/* empty */				{ $$ = NULL; }
	|	case_itemList				{ $$ = $1; }
	;

case_itemList<caseitemp>:	// IEEE: { case_item + ... }
		caseCondList ':' stmtBlock		{ $$ = new AstCaseItem($2,$1,$3); }
	|	yDEFAULT ':' stmtBlock			{ $$ = new AstCaseItem($2,NULL,$3); }
	|	yDEFAULT stmtBlock			{ $$ = new AstCaseItem($1,NULL,$2); }
	|	case_itemList caseCondList ':' stmtBlock	{ $$ = $1;$1->addNext(new AstCaseItem($3,$2,$4)); }
	|       case_itemList yDEFAULT stmtBlock		{ $$ = $1;$1->addNext(new AstCaseItem($2,NULL,$3)); }
	|	case_itemList yDEFAULT ':' stmtBlock		{ $$ = $1;$1->addNext(new AstCaseItem($3,NULL,$4)); }
	;

caseCondList<nodep>:		// IEEE: part of case_item
		expr 					{ $$ = $1; }
	|	caseCondList ',' expr			{ $$ = $1;$1->addNext($3); }
	;

//************************************************
// Functions/tasks

taskRef<nodep>:			// IEEE: part of tf_call
		idDotted		 		{ $$ = new AstTaskRef(CRELINE(),new AstParseRef($1->fileline(), AstParseRefExp::TASK, $1),NULL);}
	|	idDotted '(' exprList ')'		{ $$ = new AstTaskRef(CRELINE(),new AstParseRef($1->fileline(), AstParseRefExp::TASK, $1),$3);}
	;

funcRef<nodep>:			// IEEE: part of tf_call
		idDotted '(' exprList ')'		{ $$ = new AstFuncRef($2,new AstParseRef($1->fileline(), AstParseRefExp::FUNC, $1), $3); }
	;

task_declaration<nodep>:	// ==IEEE: task_declaration
		yTASK lifetimeE yaID tfGuts yENDTASK endLabelE
			{ $$ = new AstTask ($1,*$3,$4);}
	;

function_declaration<funcp>:	// IEEE: function_declaration + function_body_declaration
	 	yFUNCTION lifetimeE         funcTypeE yaID			   tfGuts yENDFUNCTION endLabelE { $$ = new AstFunc ($1,*$4,$5,$3); }
	|	yFUNCTION lifetimeE ySIGNED funcTypeE yaID			   tfGuts yENDFUNCTION endLabelE { $$ = new AstFunc ($1,*$5,$6,$4); $$->isSigned(true); }
	| 	yFUNCTION lifetimeE         funcTypeE yaID yVL_ISOLATE_ASSIGNMENTS tfGuts yENDFUNCTION endLabelE { $$ = new AstFunc ($1,*$4,$6,$3); $$->attrIsolateAssign(true);}
	|	yFUNCTION lifetimeE ySIGNED funcTypeE yaID yVL_ISOLATE_ASSIGNMENTS tfGuts yENDFUNCTION endLabelE { $$ = new AstFunc ($1,*$5,$7,$4); $$->attrIsolateAssign(true); $$->isSigned(true); }
	;

lifetimeE:			// IEEE: lifetime - plus empty
		/* empty */		 		{ }
	|	ySTATIC			 		{ $1->v3error("Unsupported: Static in this context\n"); }
	|	yAUTOMATIC		 		{ }
	;

tfGuts<nodep>:
		'(' {V3Parse::s_pinNum=1;} portV2kArgs ')' ';' tfBody	{ $$ = $3->addNextNull($6); }
	|	';' tfBody				{ $$ = $2; }
	;

tfBody<nodep>:			// IEEE: part of function_body_declaration/task_body_declaration
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

parenE:
		/* empty */				{ }
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
	//
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
	//
	|	expr '?' expr ':' expr			{ $$ = new AstCond($2,$1,$3,$5); }
	|	'(' expr ')'				{ $$ = $2; }
	|	'_' '(' statePushVlg expr statePop ')'	{ $$ = $4; }	// Arbitrary Verilog inside PSL
	//
	//			// IEEE: concatenation/constant_concatenation
	|	'{' cateList '}'			{ $$ = $2; }
	|	'{' constExpr '{' cateList '}' '}'	{ $$ = new AstReplicate($1,$4,$2); }
	//
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
	//
	|	funcRef					{ $$ = $1; }
	//
	|	yaINTNUM				{ $$ = new AstConst(CRELINE(),*$1); }
	//
	|	varRefDotBit	  			{ $$ = $1; }
	//
	|	error ';'				{ $$ = NULL; }
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

gateBuf<assignwp>:	gateIdE instRangeE '(' varRefDotBit ',' expr ')'		{ $$ = new AstAssignW ($3,$4,$6); $$->allowImplicit(true); }
	;
gateBufif0<assignwp>:	gateIdE instRangeE '(' varRefDotBit ',' expr ',' expr ')'	{ $$ = new AstAssignW ($3,$4,new AstCond($3,$8, new AstConst($3,V3Number($3,"1'bz")), $6)); }
	;
gateBufif1<assignwp>:	gateIdE instRangeE '(' varRefDotBit ',' expr ',' expr ')'	{ $$ = new AstAssignW ($3,$4,new AstCond($3,$8, $6, new AstConst($3,V3Number($3,"1'bz")))); }
	;
gateNot<assignwp>:	gateIdE instRangeE '(' varRefDotBit ',' expr ')'		{ $$ = new AstAssignW ($3,$4,new AstNot($5,$6)); $$->allowImplicit(true); }
	;
gateNotif0<assignwp>:	gateIdE instRangeE '(' varRefDotBit ',' expr ',' expr ')'	{ $$ = new AstAssignW ($3,$4,new AstCond($3,$8, new AstConst($3,V3Number($3,"1'bz")), new AstNot($3, $6))); }
	;
gateNotif1<assignwp>:	gateIdE instRangeE '(' varRefDotBit ',' expr ',' expr ')'	{ $$ = new AstAssignW ($3,$4,new AstCond($3,$8, new AstNot($3,$6), new AstConst($3,V3Number($3,"1'bz")))); }
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
gatePullup<pullp>: gateIdE instRangeE '(' varRefDotBit ')'	{ $$ = new AstPull ($3, $4, true); }
	;
gatePulldown<pullp>: gateIdE instRangeE '(' varRefDotBit ')'	{ $$ = new AstPull ($3, $4, false); }
	;
gateIdE:
		/*empty*/				{}
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
	//			// IEEE: id + part_select_range/constant_part_select_range
	|	idArrayed '[' expr ']'				{ $$ = new AstSelBit($2,$1,$3); }  // Or AstArraySel, don't know yet.
	|	idArrayed '[' constExpr ':' constExpr ']'	{ $$ = new AstSelExtract($2,$1,$3,$5); }
	//			// IEEE: id + indexed_range/constant_indexed_range
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

identifier_listLvalue<nodep>:	// IEEE: identifier_list for lvalue only
		varRefDotBit				{ $$ = $1; }
	|	identifier_listLvalue ',' varRefDotBit	{ $$ = new AstConcat($2,$1,$3); }
	;

endLabelE:
		/* empty */				{ }
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

concurrent_assertion_item<nodep>:	// IEEE: concurrent_assertion_item
		concurrent_assertion_statement		{ $$ = $1; }
	|	yaID ':' concurrent_assertion_statement	{ $$ = new AstBegin($2,*$1,$3); }
	;

concurrent_assertion_statement<nodep>:	// IEEE: concurrent_assertion_statement  (INCOMPLETE)
		cover_property_statement		{ $$ = $1; }
	;

cover_property_statement<nodep>:	// IEEE: cover_property_statement
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
		yDEFAULT yPSL_CLOCK '=' senitemEdge ';'		{ $$ = new AstPslDefClock($3, $4); }
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
    else nodep->trace(v3Global.opt.trace() && nodep->fileline()->tracingOn());

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
