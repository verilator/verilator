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

#include "V3Read.h"
#include "V3Ast.h"
#include "V3Global.h"

#define YYERROR_VERBOSE 1
#define YYINITDEPTH 10000	// Older bisons ignore YYMAXDEPTH
#define YYMAXDEPTH 10000

// Pick up new lexer
#define yylex V3Read::yylex
#define PSLUNSUP(what) NULL; yyerrorf("Unsupported: PSL language feature not implemented");

extern void yyerror(const char* errmsg);
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
    static string	s_instModule;	// Name of module referenced for instantiations
    static AstPin*	s_instParamp;	// Parameters for instantiations
    static int		s_uniqueAttr;	// Bitmask of unique/priority keywords

    static AstVar*  createVariable(FileLine* fileline, string name, AstRange* arrayp, AstNode* attrsp);
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
string		V3Parse::s_instModule;
AstPin*		V3Parse::s_instParamp = NULL;
AstVar*		V3Parse::s_varAttrp = NULL;
AstCase*	V3Parse::s_caseAttrp = NULL;

//======================================================================
// Utility functions

static AstNode* newVarInit(FileLine* fileline, AstNode* varp, AstNode* initp) {
	return new AstInitial(fileline, new AstAssign(fileline,
						      new AstVarRef(fileline, varp->name(),true),
						      initp));
}	

//======================================================================
// Macro functions

#define CRELINE() (V3Read::copyOrSameFileLine())

#define VARRESET_LIST(decl)    { V3Parse::s_pinNum=1; VARRESET(); VARDECL(decl); }	// Start of pinlist
#define VARRESET_NONLIST(decl) { V3Parse::s_pinNum=0; VARRESET(); VARDECL(decl); }	// Not in a pinlist
#define VARRESET() { VARDECL(UNKNOWN); VARIO(UNKNOWN); VARSIGNED(false); VARRANGE(NULL); }
#define VARDECL(type) { V3Parse::s_varDecl = AstVarType::type; }
#define VARIO(type) { V3Parse::s_varIO = AstVarType::type; }
#define VARSIGNED(value) { V3Parse::s_varSigned = value; }
#define VARRANGE(rangep) { V3Parse::setRange(rangep); }
#define VARTYPE(typep) { VARRANGE(typep); }  // Temp until other data types supported

#define VARDONEA(name,array,attrs) V3Parse::createVariable(CRELINE(),(name),(array),(attrs))
#define VARDONEP(portp,array,attrs) V3Parse::createVariable((portp)->fileline(),(portp)->name(),(array),(attrs))
#define PINNUMINC() (V3Parse::s_pinNum++)

#define INSTPREP(modname,paramsp) { V3Parse::s_impliedDecl = true; V3Parse::s_instModule = modname; V3Parse::s_instParamp = paramsp; }

static void ERRSVKWD(FileLine* fileline, const string& tokname) {
    static int toldonce = 0;
    fileline->v3error((string)"Unexpected \""+tokname+"\": \""+tokname+"\" is a SystemVerilog keyword misused as an identifier.");
    if (!toldonce++) fileline->v3error("Modify the Verilog-2001 code to avoid SV keywords, or use `begin_keywords or --language.");
}

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
    AstPort*	portp;
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
%token<strp>		yaID__ETC	"IDENTIFIER"

// IEEE: integral_number
%token<nump>		yaINTNUM	"INTEGER NUMBER"
// IEEE: time_literal + time_unit
%token<cdouble>		yaTIMENUM	"TIME NUMBER"
// IEEE: string_literal
%token<strp>		yaSTRING	"STRING"
%token<strp>		yaSTRING__IGNORE "STRING-ignored"	// Used when expr:string not allowed

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
// Double underscores "yX__Y" means token X followed by Y,
// and "yX__ETC" means X folled by everything but Y(s).
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
%token<fileline>	yFOREVER	"forever"
%token<fileline>	yFUNCTION	"function"
%token<fileline>	yGENERATE	"generate"
%token<fileline>	yGENVAR		"genvar"
%token<fileline>	yIF		"if"
%token<fileline>	yIFF		"iff"
%token<fileline>	yLOGIC		"logic"
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
%token<fileline>	yPULLDOWN	"pulldown"
%token<fileline>	yPULLUP		"pullup"
%token<fileline>	yREG		"reg"
%token<fileline>	yREPEAT		"repeat"
%token<fileline>	ySCALARED	"scalared"
%token<fileline>	ySIGNED		"signed"
%token<fileline>	ySPECIFY	"specify"
%token<fileline>	ySPECPARAM	"specparam"
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
%token<fileline>	yD_aIGNORE	"${ignored-bbox-sys}"

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

%token<fileline>	yP_TICK		"'"
%token<fileline>	yP_TICKBRA	"'{"
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
%token<fileline>	yP_BRASTAR	"[*"
%token<fileline>	yP_BRAEQ	"[="
%token<fileline>	yP_BRAMINUSGT	"[->"

%token<fileline>	yP_PLUSPLUS	"++"
%token<fileline>	yP_MINUSMINUS	"--"
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
	//			// timeunits_declaration moved into description:package_item
	|	descriptionList				{ }
	;

descriptionList:		// IEEE: part of source_text
		description				{ }
	|	descriptionList description		{ }
	;

description:			// ==IEEE: description
		module_declaration			{ }
	//UNSUP	interface_declaration			{ }
	//UNSUP	program_declaration			{ }
	//UNSUP	package_declaration			{ }
	//UNSUP	package_item				{ }
	//UNSUP	bind_directive				{ }
	//	unsupported	// IEEE: config_declaration
	|	error					{ }
	;

timeunits_declaration:		// ==IEEE: timeunits_declaration
		yTIMEUNIT       yaTIMENUM ';'		{ }
	| 	yTIMEPRECISION  yaTIMENUM ';'		{ }
	;

//**********************************************************************
// Packages

package_or_generate_item_declaration<nodep>:	// ==IEEE: package_or_generate_item_declaration
		net_declaration				{ $$ = $1; }
	|	data_declaration			{ $$ = $1; }
	|	task_declaration			{ $$ = $1; }
	|	function_declaration			{ $$ = $1; }
	//UNSUP	dpi_import_export			{ $$ = $1; }
	//UNSUP	extern_constraint_declaration		{ $$ = $1; }
	//UNSUP	class_declaration			{ $$ = $1; }
	//			// class_constructor_declaration is part of function_declaration
	|	parameter_declaration ';'		{ $$ = $1; }
	|	local_parameter_declaration		{ $$ = $1; }
	//UNSUP	covergroup_declaration			{ $$ = $1; }
	//UNSUP	overload_declaration			{ $$ = $1; }
	//UNSUP	concurrent_assertion_item_declaration	{ $$ = $1; }
	|	';'					{ $$ = NULL; }
	;

//**********************************************************************
// Module headers

module_declaration:		// ==IEEE: module_declaration
	//			// timeunits_declaration instead in module_item
	//			// IEEE: module_nonansi_header + module_ansi_header
		modFront parameter_port_listE portsStarE ';'
			module_itemListE yENDMODULE endLabelE
			{ $1->modTrace(v3Global.opt.trace() && $1->fileline()->tracingOn());  // Stash for implicit wires, etc
			  if ($2) $1->addStmtp($2); if ($3) $1->addStmtp($3);
			  if ($5) $1->addStmtp($5); }
	//
	//UNSUP	yEXTERN modFront parameter_port_listE portsStarE ';'
	//UNSUP		{ UNSUP }
	;

modFront<modulep>:
		yMODULE lifetimeE idAny
			{ $$ = new AstModule($1,*$3); $$->inLibrary(V3Read::inLibrary()||V3Read::inCellDefine());
			  $$->modTrace(v3Global.opt.trace());
			  V3Read::rootp()->addModulep($$); }
	;

parameter_value_assignmentE<pinp>:	// IEEE: [ parameter_value_assignment ]
		/* empty */				{ $$ = NULL; }
	|	'#' '(' cellpinList ')'			{ $$ = $3; }
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
		param_assignment				{ $$ = $1; }
	|	parameter_port_declarationFront param_assignment	{ $$ = $2; }
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
	//UNSUP	portDirNetE id/*interface*/                      idAny/*port*/ regArRangeE sigAttrListE	{ VARTYPE($2); VARDONEA($3, $4); PARSEP->instantCb(CRELINE(), $2, $3, $4); PINNUMINC(); }
	//UNSUP	portDirNetE yINTERFACE                           idAny/*port*/ regArRangeE sigAttrListE	{ VARTYPE($2); VARDONEA($3, $4); PINNUMINC(); }
	//UNSUP	portDirNetE id/*interface*/ '.' idAny/*modport*/ idAny/*port*/ regArRangeE sigAttrListE	{ VARTYPE($2); VARDONEA($5, $6); PARSEP->instantCb(CRELINE(), $2, $5, $6); PINNUMINC(); }
	//UNSUP	portDirNetE yINTERFACE      '.' idAny/*modport*/ idAny/*port*/ regArRangeE sigAttrListE	{ VARTYPE($2); VARDONEA($5, $6); PINNUMINC(); }
	//
	//			// IEEE: ansi_port_declaration, with [port_direction] removed
	//			//   IEEE: [ net_port_header | interface_port_header ] port_identifier { unpacked_dimension }
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
	//			// variable_dimensionListE instead of regArRangeE to avoid conflicts
	//
	//			// Note implicit rules looks just line declaring additional followon port
	//			// No VARDECL("port") for implicit, as we don't want to declare variables for them
	//UNSUP	portDirNetE data_type	       '.' portSig '(' portAssignExprE ')' sigAttrListE	{ UNSUP }
	//UNSUP	portDirNetE yVAR data_type     '.' portSig '(' portAssignExprE ')' sigAttrListE	{ UNSUP }
	//UNSUP	portDirNetE yVAR implicit_type '.' portSig '(' portAssignExprE ')' sigAttrListE	{ UNSUP }
	//UNSUP	portDirNetE signingE rangeList '.' portSig '(' portAssignExprE ')' sigAttrListE	{ UNSUP }
	//UNSUP	portDirNetE /*implicit*/       '.' portSig '(' portAssignExprE ')' sigAttrListE	{ UNSUP }
	//
		portDirNetE data_type          portSig variable_dimensionListE sigAttrListE	{ $$=$3; VARTYPE($2); $$->addNextNull(VARDONEP($$,$4,$5)); }
	//UNSUP	portDirNetE yVAR data_type     portSig variable_dimensionListE sigAttrListE	{ $$=$4; VARTYPE($3); $$->addNextNull(VARDONEP($$,$5,$6)); }
	//UNSUP	portDirNetE yVAR implicit_type portSig variable_dimensionListE sigAttrListE	{ $$=$4; VARTYPE($3); $$->addNextNull(VARDONEP($$,$5,$6)); }
	|	portDirNetE signingE rangeList portSig variable_dimensionListE sigAttrListE	{ $$=$4; VARTYPE($3); $$->addNextNull(VARDONEP($$,$5,$6)); }
	|	portDirNetE /*implicit*/       portSig variable_dimensionListE sigAttrListE	{ $$=$2; /*VARTYPE-same*/ $$->addNextNull(VARDONEP($$,$3,$4)); }
	//
	|	portDirNetE data_type          portSig variable_dimensionListE sigAttrListE '=' constExpr	{ $$=$3; VARTYPE($2); $$->addNextNull(VARDONEP($$,$4,$5));     $$->addNextNull(newVarInit($6,$$,$7)); }
	//UNSUP	portDirNetE yVAR data_type     portSig variable_dimensionListE sigAttrListE '=' constExpr	{ $$=$3; VARTYPE($3); $$->addNextNull(VARDONEP($$,$5,$6));     $$->addNextNull(newVarInit($7,$$,$8)); }
	//UNSUP	portDirNetE yVAR implicit_type portSig variable_dimensionListE sigAttrListE '=' constExpr	{ $$=$3; VARTYPE($3); $$->addNextNull(VARDONEP($$,$5,$6));     $$->addNextNull(newVarInit($7,$$,$8)); }
	|	portDirNetE /*implicit*/       portSig variable_dimensionListE sigAttrListE '=' constExpr	{ $$=$3; /*VARTYPE-same*/ $$->addNextNull(VARDONEP($$,$3,$4)); $$->addNextNull(newVarInit($5,$$,$6)); }
 	;
 
portDirNetE:			// IEEE: part of port, optional net type and/or direction
		/* empty */				{ }
	//			// Per spec, if direction given default the nettype.
	//			// The higher level rule may override this VARTYPE with one later in the parse.
	|	port_direction				{ VARDECL(PORT); VARTYPE(NULL/*default_nettype*/); }
	|	port_direction net_type			{ VARDECL(PORT); VARTYPE(NULL/*default_nettype*/); } // net_type calls VARNET
	|	net_type				{ } // net_type calls VARNET
 	;
 
port_declNetE:			// IEEE: part of port_declaration, optional net type
		/* empty */				{ }
	|	net_type				{ } // net_type calls VARNET
 	;
 
portSig<portp>:
		id/*port*/				{ $$ = new AstPort(CRELINE(),PINNUMINC(),*$1); }
	|	idSVKwd					{ $$ = new AstPort(CRELINE(),PINNUMINC(),*$1); }
 	;

//**********************************************************************
// Interface headers

//**********************************************************************
// Program headers

//************************************************
// Variable Declarations

genvar_declaration<nodep>:	// ==IEEE: genvar_declaration
		yGENVAR list_of_genvar_identifiers ';'	{ $$ = $2; }
	;

list_of_genvar_identifiers<nodep>:	// IEEE: list_of_genvar_identifiers (for declaration)
		genvar_identifierDecl			{ $$ = $1; }
	|	list_of_genvar_identifiers ',' genvar_identifierDecl	{ $$ = $1->addNext($3); }
	;

genvar_identifierDecl<nodep>:		// IEEE: genvar_identifier (for declaration)
		id/*new-genvar_identifier*/ sigAttrListE	{ VARRESET_NONLIST(GENVAR); $$ = VARDONEA(*$1, NULL, $2); }
	;

local_parameter_declaration<nodep>:	// IEEE: local_parameter_declaration
	//			// See notes in parameter_declaration
		local_parameter_declarationFront list_of_param_assignments ';'	{ $$ = $2; }
	;

parameter_declaration<nodep>:	// IEEE: parameter_declaration
	//			// IEEE: yPARAMETER yTYPE list_of_type_assignments ';'
	//			// Instead of list_of_type_assignments
	//			// we use list_of_param_assignments because for port handling
	//			// it already must accept types, so simpler to have code only one place
		parameter_declarationFront list_of_param_assignments	{ $$ = $2; }
	;

local_parameter_declarationFront: // IEEE: local_parameter_declaration w/o assignment
		varLParamReset implicit_type 		{ /*VARRESET-in-varLParam*/ VARTYPE($2); }
	//UNSUP	varLParamReset data_type		{ /*VARRESET-in-varLParam*/ VARTYPE($2); }
	//UNSUP	varLParamReset yTYPE			{ /*VARRESET-in-varLParam*/ VARTYPE($2); }
	;

parameter_declarationFront:	// IEEE: parameter_declaration w/o assignment
		varGParamReset implicit_type 		{ /*VARRESET-in-varGParam*/ VARTYPE($2); }
	//UNSUP	varGParamReset data_type		{ /*VARRESET-in-varGParam*/ VARTYPE($2); }
	//UNSUP	varGParamReset yTYPE			{ /*VARRESET-in-varGParam*/ VARTYPE($2); }
	;

parameter_port_declarationFront: // IEEE: parameter_port_declaration w/o assignment
	//			// IEEE: parameter_declaration (minus assignment)
		parameter_declarationFront		{ }
	//
	//UNSUP	data_type				{ VARTYPE($1); }
	//UNSUP	yTYPE 					{ VARTYPE($1); }
	;

net_declaration<nodep>:		// IEEE: net_declaration - excluding implict
		net_declarationFront netSigList ';'	{ $$ = $2; }
	;

net_declarationFront:		// IEEE: beginning of net_declaration
		net_declRESET net_type   strengthSpecE signingE delayrange { }
	;

net_declRESET:
		/* empty */ 				{ VARRESET_NONLIST(UNKNOWN); }
	;

net_type:			// ==IEEE: net_type
		ySUPPLY0				{ VARDECL(SUPPLY0); }
	|	ySUPPLY1				{ VARDECL(SUPPLY1); }
	|	yTRI 					{ VARDECL(TRIWIRE); }
	//UNSUP	yTRI0 					{ VARDECL(TRI0); }
	//UNSUP	yTRI1 					{ VARDECL(TRI1); }
	//UNSUP	yTRIAND 				{ VARDECL(TRIAND); }
	//UNSUP	yTRIOR 					{ VARDECL(TRIOR); }
	//UNSUP	yTRIREG 				{ VARDECL(TRIREG); }
	//UNSUP	yWAND 					{ VARDECL(WAND); }
	|	yWIRE 					{ VARDECL(WIRE); }
	//UNSUP	yWOR 					{ VARDECL(WOR); }
	;

varRESET:
		/* empty */ 				{ VARRESET(); }
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
		port_directionReset port_declNetE data_type          { VARTYPE($3); } list_of_variable_decl_assignments	{ $$ = $5; }
	//UNSUP	port_directionReset port_declNetE yVAR data_type     { VARTYPE($4); } list_of_variable_decl_assignments	{ $$ = $6; }
	//UNSUP	port_directionReset port_declNetE yVAR implicit_type { VARTYPE($4); } list_of_variable_decl_assignments	{ $$ = $6; }
	|	port_directionReset port_declNetE signingE rangeList { VARTYPE($4); } list_of_variable_decl_assignments	{ $$ = $6; }
	|	port_directionReset port_declNetE signing	     { VARTYPE(NULL); } list_of_variable_decl_assignments	{ $$ = $5; }
	|	port_directionReset port_declNetE /*implicit*/       { VARTYPE(NULL);/*default_nettype*/} list_of_variable_decl_assignments	{ $$ = $4; }
	;

tf_port_declaration<nodep>:	// ==IEEE: tf_port_declaration
	//			// Used inside function; followed by ';'
	//			// SIMILAR to port_declaration
	//
		port_directionReset      data_type     { VARTYPE($2); }  list_of_tf_variable_identifiers ';'	{ $$ = $4; }
	|	port_directionReset      implicit_type { VARTYPE($2); }  list_of_tf_variable_identifiers ';'	{ $$ = $4; }
	//UNSUP	port_directionReset yVAR data_type     { VARTYPE($3); }  list_of_tf_variable_identifiers ';'	{ $$ = $5; }
	//UNSUP	port_directionReset yVAR implicit_type { VARTYPE($3); }  list_of_tf_variable_identifiers ';'	{ $$ = $5; }
	;

signingE:			// IEEE: signing - plus empty
		/*empty*/ 				{ }
	|	signing					{ }
	;

signing:			// ==IEEE: signing
		ySIGNED					{ VARSIGNED(true); }
	|	yUNSIGNED				{ VARSIGNED(false); }
	;

//************************************************
// Data Types

data_type<rangep>:		// ==IEEE: data_type
	//			// This expansion also replicated elsewhere, IE data_type__AndID
		data_typeNoRef				{ $$ = $1; }
	//			// IEEE: [ class_scope | package_scope ] type_identifier { packed_dimension }
	//UNSUP	ps_type  packed_dimensionE		{ UNSUP }
	//UNSUP	class_scope_type packed_dimensionE	{ UNSUP }
	//			// IEEE: class_type
	//UNSUP	class_typeWithoutId			{ $$ = $1; }
	//			// IEEE: ps_covergroup_identifier
	//UNSUP	ps_covergroup_identifier		{ $$ = $1; }
	;

data_typeNoRef<rangep>:		// ==IEEE: data_type, excluding class_type etc references
		yINTEGER				{ VARDECL(INTEGER); $$ = new AstRange($1,31,0); $$->isSigned(true); }
	|	yREG signingE rangeListE		{ VARDECL(REG); $$ = $3; }
	|	yLOGIC signingE rangeListE		{ VARDECL(REG); $$ = $3; }
	//UNSUP: above instead of integer_type
	//
	//UNSUP	integer_type signingE regArRangeE	{ UNSUP }
	//UNSUP	non_integer_type			{ UNSUP }
	//UNSUP	ySTRUCT        packedSigningE '{' struct_union_memberList '}' packed_dimensionE	{ UNSUP }
	//UNSUP	yUNION taggedE packedSigningE '{' struct_union_memberList '}' packed_dimensionE	{ UNSUP }
	//UNSUP	enumDecl				{ UNSUP }
	//UNSUP	ySTRING					{ UNSUP }
	//UNSUP	yCHANDLE				{ UNSUP }
	//UNSUP	yEVENT					{ UNSUP }
	//UNSUP	yVIRTUAL__INTERFACE yINTERFACE id/*interface*/	{ UNSUP }
	//UNSUP	yVIRTUAL__anyID                id/*interface*/	{ UNSUP }
	//UNSUP	type_reference				{ UNSUP }
	//			// IEEE: class_scope: see data_type above
	//			// IEEE: class_type: see data_type above
	//			// IEEE: ps_covergroup: see data_type above
	;

list_of_variable_decl_assignments<nodep>:	// ==IEEE: list_of_variable_decl_assignments
		variable_decl_assignment		{ $$ = $1; }
	|	list_of_variable_decl_assignments ',' variable_decl_assignment	{ $$ = $1->addNextNull($3); }
	;

variable_decl_assignment<varp>:	// ==IEEE: variable_decl_assignment
		id variable_dimensionListE sigAttrListE
			{ $$ = VARDONEA(*$1,$2,$3); }
	|	id variable_dimensionListE sigAttrListE '=' variable_declExpr
			{ $$ = VARDONEA(*$1,$2,$3);
			  $$->addNext(new AstInitial($4,new AstAssign($4, new AstVarRef($4, *$1, true), $5))); }
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
			{ $$ = VARDONEA(*$1, $2, $3); }
	|	id variable_dimensionListE sigAttrListE '=' expr
			{ $$ = VARDONEA(*$1, $2, $3);
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
	|	'[' constExpr ']'			{ $$ = new AstRange($1,$2,$2->cloneTree(true)); }
	//			// IEEE: associative_dimension
	//UNSUP	'[' data_type ']'			{ UNSUP }
	//UNSUP	yP_BRASTAR ']'				{ UNSUP }
	//UNSUP	'[' '*' ']'				{ UNSUP }
	//			// IEEE: queue_dimension
	//			// '[' '$' ']' -- $ is part of expr
	//			// '[' '$' ':' expr ']' -- anyrange:expr:$
	;

//************************************************
// Typedef

data_declaration<nodep>:	// ==IEEE: data_declaration
	//			// VARRESET can't be called here - conflicts
		data_declarationVar			{ $$ = $1; }
	//UNSUP	type_declaration			{ $$ = $1; }
	//UNSUP	package_import_declaration		{ $$ = $1; }
	//			// IEEE: virtual_interface_declaration
	//			// "yVIRTUAL yID yID" looks just like a data_declaration
	//			// Therefore the virtual_interface_declaration term isn't used
	;

data_declarationVar<nodep>:	// IEEE: part of data_declaration
	//			// The first declaration has complications between assuming what's the type vs ID declaring
		varRESET data_declarationVarFront list_of_variable_decl_assignments ';'	{ $$ = $3; }
	;

data_declarationVarFront:	// IEEE: part of data_declaration
	//			// implicit_type expanded into /*empty*/ or "signingE rangeList"
	//UNSUP	constE yVAR lifetimeE data_type	 	{ /*VARRESET-in-ddVar*/ VARDECL("var"); VARTYPE(SPACED($1,$4)); }
	//UNSUP	constE yVAR lifetimeE		 	{ /*VARRESET-in-ddVar*/ VARDECL("var"); VARTYPE($1); }
	//UNSUP	constE yVAR lifetimeE signingE rangeList { /*VARRESET-in-ddVar*/ VARDECL("var"); VARTYPE(SPACED($1,SPACED($4,$5))); }
	//
	//			// Expanded: "constE lifetimeE data_type"
		/**/		      data_type		{ /*VARRESET-in-ddVar*/ VARTYPE($1); }
	|	/**/	    lifetime  data_type		{ /*VARRESET-in-ddVar*/ VARTYPE($2); }
	//UNSUP	yCONST__ETC lifetimeE data_type		{ /*VARRESET-in-ddVar*/ VARTYPE($3); }
	//			// = class_new is in variable_decl_assignment
	;

implicit_type<rangep>:		// IEEE: part of *data_type_or_implicit
	//			// Also expanded in data_declaration
		/* empty */				{ $$ = NULL; }
	|	signingE rangeList			{ $$ = $2; }  // signing sets VARSIGNED, so not passed up
	|	signing					{ $$ = NULL; }  // signing sets VARSIGNED, so not passed up
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
	|	timeunits_declaration			{ $$ = NULL; }
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

module_or_generate_item<nodep>:	// ==IEEE: module_or_generate_item
	//			// IEEE: parameter_override
		yDEFPARAM list_of_defparam_assignments ';'	{ $$ = $2; }
	//			// IEEE: gate_instantiation + udp_instantiation + module_instantiation
	//			// not here, see etcInst in module_common_item
	//			// We joined udp & module definitions, so this goes here
	//UNSUP	combinational_body			{ $$ = $1; }
	|	module_common_item			{ $$ = $1; }
	;

module_common_item<nodep>:	// ==IEEE: module_common_item
		module_or_generate_item_declaration	{ $$ = $1; }
	//			// IEEE: interface_instantiation
	//			// + IEEE: program_instantiation
	//			// + module_instantiation from module_or_generate_item
	|	etcInst 				{ $$ = $1; }
	|	concurrent_assertion_item		{ $$ = $1; }
	//UNSUP	bind_directive				{ $$ = $1; }
	|	continuous_assign			{ $$ = $1; }
	//			// IEEE: net_alias
	//UNSUP	yALIAS variable_lvalue aliasEqList ';'	{ UNSUP }
	|	initial_construct			{ $$ = $1; }
	|	final_construct				{ $$ = $1; }
	//			// IEEE: always_construct
	//			// Verilator only - event_control attached to always
	|	yALWAYS event_controlE stmtBlock	{ $$ = new AstAlways($1,$2,$3); }
	|	loop_generate_construct			{ $$ = $1; }
	|	conditional_generate_construct		{ $$ = $1; }
	//			// Verilator only
	|	pslStmt 				{ $$ = $1; }
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

//************************************************
// Generates

generate_block_or_null<nodep>:	// IEEE: generate_block_or_null
	//	';'		// is included in
	//			// IEEE: generate_block
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
	|	id ':' yBEGIN genItemList yEND endLabelE	{ $$ = new AstBegin($2,*$1,$4); }
	|	id ':' yBEGIN             yEND endLabelE	{ $$ = NULL; }
	|	yBEGIN ':' idAny genItemList yEND endLabelE	{ $$ = new AstBegin($2,*$3,$4); }
	|	yBEGIN ':' idAny 	  yEND endLabelE	{ $$ = NULL; }
	;

genItemList<nodep>:
		genItem					{ $$ = $1; }
	|	genItemList genItem			{ $$ = $1->addNextNull($2); }
	;

genItem<nodep>:			// IEEE: module_or_interface_or_generate_item
		module_or_generate_item			{ $$ = $1; }
	//UNSUP	interface_or_generate_item		{ $$ = $1; }
	;

conditional_generate_construct<nodep>:	// ==IEEE: conditional_generate_construct
		yCASE  '(' expr ')' case_generate_itemListE yENDCASE	{ $$ = new AstGenCase($1,$3,$5); }
	|	yIF '(' expr ')' generate_block_or_null	%prec prLOWER_THAN_ELSE	{ $$ = new AstGenIf($1,$3,$5,NULL); }
	|	yIF '(' expr ')' generate_block_or_null yELSE generate_block_or_null	{ $$ = new AstGenIf($1,$3,$5,$7); }
	;

loop_generate_construct<nodep>:	// ==IEEE: loop_generate_construct
		yFOR '(' genvar_initialization ';' expr ';' genvar_iteration ')' generate_block_or_null
			{ $$ = new AstGenFor($1,$3,$5,$7,$9); }
	;

genvar_initialization<nodep>:	// ==IEEE: genvar_initalization
		varRefBase '=' expr			{ $$ = new AstAssign($2,$1,$3); }
	//UNSUP	yGENVAR genvar_identifierDecl '=' constExpr	{ UNSUP }
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
		variable_lvalue '=' expr		{ $$ = new AstAssignW($2,$1,$3); }
	;

delayE:
		/* empty */				{ }
	|	delay_control				{ } /* ignored */
	;

delay_control<fileline>:	//== IEEE: delay_control
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
		expr					{ }
	//			// Verilator doesn't support yaFLOATNUM/yaTIMENUM, so not in expr
	|	yaFLOATNUM 				{ }
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
		netId sigAttrListE			{ $$ = VARDONEA(*$1, NULL, $2); }
	|	netId sigAttrListE '=' expr		{ $$ = VARDONEA(*$1, NULL, $2); $$->addNext(new AstAssignW($3,new AstVarRef($3,$$->name(),true),$4)); }
	|	netId rangeList sigAttrListE		{ $$ = VARDONEA(*$1, $2, $3); }
	;

netId<strp>:
		id/*new-net*/				{ $$ = $1; }
	|	idSVKwd					{ $$ = $1; }
	;

sigId<varp>:
		id					{ $$ = VARDONEA(*$1, NULL, NULL); }
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
	|	yVL_CLOCK_ENABLE			{ $$ = new AstAttrOf($1,AstAttrType::VAR_CLOCK_ENABLE); }
	|	yVL_PUBLIC				{ $$ = new AstAttrOf($1,AstAttrType::VAR_PUBLIC); }
	|	yVL_PUBLIC_FLAT				{ $$ = new AstAttrOf($1,AstAttrType::VAR_PUBLIC_FLAT); }
	|	yVL_ISOLATE_ASSIGNMENTS			{ $$ = new AstAttrOf($1,AstAttrType::VAR_ISOLATE_ASSIGNMENTS); }
	;

rangeListE<rangep>:		// IEEE: [{packed_dimension}]
		/* empty */    		               	{ $$ = NULL; }
	|	rangeList 				{ $$ = $1; }
	;

rangeList<rangep>:		// IEEE: {packed_dimension}
		anyrange				{ $$ = $1; }
        |	rangeList anyrange			{ $$ = $1; $1->addNext($2); }
	;

regrangeE<rangep>:
		/* empty */    		               	{ $$ = NULL; VARRANGE($$); }
	|	anyrange 				{ $$ = $1; VARRANGE($$); }
	;

// IEEE: select
// Merged into more general idArray

anyrange<rangep>:
		'[' constExpr ':' constExpr ']'		{ $$ = new AstRange($1,$2,$4); }
	;

delayrange<rangep>:
		regrangeE delayE 			{ $$ = $1; }
	|	ySCALARED regrangeE delayE 		{ $$ = $2; }
	|	yVECTORED regrangeE delayE 		{ $$ = $2; }
	//UNSUP: ySCALARED/yVECTORED ignored
	;

//************************************************
// Parameters

param_assignment<varp>:		// ==IEEE: param_assignment
	//			// IEEE: constant_param_expression
	//			// constant_param_expression: '$' is in expr
		sigId sigAttrListE '=' expr		{ $$ = $1; $1->addAttrsp($2); $$->initp($4); }
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

etcInst<nodep>:			// IEEE: module_instantiation + gate_instantiation + udp_instantiation
		instDecl				{ $$ = $1; }
	|	gateDecl 				{ $$ = $1; }
	;

instDecl<nodep>:
		id parameter_value_assignmentE {INSTPREP(*$1,$2);} instnameList ';'
			{ $$ = $4; V3Parse::s_impliedDecl=false;}
	//UNSUP: strengthSpecE for udp_instantiations
	;

instnameList<nodep>:
		instnameParen				{ $$ = $1; }
	|	instnameList ',' instnameParen		{ $$ = $1->addNext($3); }
	;

instnameParen<cellp>:
		id instRangeE '(' cellpinList ')'	{ $$ = new AstCell($3,       *$1,V3Parse::s_instModule,$4,  V3Parse::s_instParamp,$2); }
	|	id instRangeE 				{ $$ = new AstCell(CRELINE(),*$1,V3Parse::s_instModule,NULL,V3Parse::s_instParamp,$2); }
	//UNSUP	instRangeE '(' cellpinList ')'		{ UNSUP } // UDP
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
		/* empty: ',,' is legal */		{ $$ = NULL; PINNUMINC(); }
	|	yP_DOTSTAR				{ $$ = new AstPin($1,PINNUMINC(),".*",NULL); }
	|	'.' idSVKwd				{ $$ = NULL; PINNUMINC(); }
	|	'.' idAny				{ $$ = new AstPin($1,PINNUMINC(),*$2,new AstVarRef($1,*$2,false)); $$->svImplicit(true);}
	|	'.' idAny '(' ')'			{ $$ = NULL; PINNUMINC(); }
	|	'.' idAny '(' expr ')'			{ $$ = new AstPin($1,PINNUMINC(),*$2,$4); }
	//			// For parameters
	//UNSUP	'.' idAny '(' data_type ')'		{ PINDONE($1,$2,$4);  GRAMMARP->pinNumInc(); }
	//			// For parameters
	//UNSUP	data_type				{ PINDONE($1->fileline(),"",$1);  GRAMMARP->pinNumInc(); }
	//
	|	expr					{ $$ = new AstPin($1->fileline(),PINNUMINC(),"",$1); }
	;

//************************************************
// EventControl lists

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
	|	event_expression yOR senitem		{ $$ = $1;$1->addNext($3); }
	|	event_expression ',' senitem		{ $$ = $1;$1->addNext($3); }	/* Verilog 2001 */
	;

senitem<senitemp>:		// IEEE: part of event_expression, non-'OR' ',' terms
		senitemEdge				{ $$ = $1; }
	|	senitemVar				{ $$ = $1; }
	|	'(' senitemVar ')'			{ $$ = $2; }
	//UNSUP	expr					{ UNSUP }
	//UNSUP	expr yIFF expr				{ UNSUP }
	;

senitemVar<senitemp>:
		idClassSel				{ $$ = new AstSenItem(CRELINE(),AstEdgeType::ANYEDGE,$1); }
	;

senitemEdge<senitemp>:		// IEEE: part of event_expression
		yPOSEDGE idClassSel			{ $$ = new AstSenItem($1,AstEdgeType::POSEDGE,$2); }
	|	yNEGEDGE idClassSel			{ $$ = new AstSenItem($1,AstEdgeType::NEGEDGE,$2); }
	|	yPOSEDGE '(' idClassSel ')'		{ $$ = new AstSenItem($1,AstEdgeType::POSEDGE,$3); }
	|	yNEGEDGE '(' idClassSel ')'		{ $$ = new AstSenItem($1,AstEdgeType::NEGEDGE,$3); }
	//UNSUP	yIFF...
	;

//************************************************
// Statements

stmtBlock<nodep>:		// IEEE: statement + seq_block + par_block
		stmt					{ $$ = $1; }
	;

seq_block<nodep>:		// ==IEEE: seq_block
	//			// IEEE doesn't allow declarations in unnamed blocks, but several simulators do.
		yBEGIN blockDeclStmtList yEND		{ $$ = $2; }
	|	yBEGIN /**/		 yEND		{ $$ = NULL; }
	|	yBEGIN ':' seq_blockId blockDeclStmtList yEND endLabelE	{ $$ = new AstBegin($2,*$3,$4); }
	|	yBEGIN ':' seq_blockId /**/	         yEND endLabelE	{ $$ = new AstBegin($2,*$3,NULL); }
	;

seq_blockId<strp>:		// IEEE: part of seq_block
		idAny/*new-block_identifier*/		{ $$ = $1; }
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
	|	local_parameter_declaration 		{ $$ = $1; }
	|	parameter_declaration ';' 		{ $$ = $1; }
	//UNSUP	overload_declaration 			{ $$ = $1; }
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
	//UNSUP	fexprLvalue '=' class_new ';'		{ UNSUP }
	//UNSUP	fexprLvalue '=' dynamic_array_new ';'	{ UNSUP }
	//
	//			// IEEE: nonblocking_assignment
	|	idClassSel yP_LTE delayE expr ';'	{ $$ = new AstAssignDly($2,$1,$4); }
	|	'{' variable_lvalueConcList '}' yP_LTE delayE expr ';' { $$ = new AstAssignDly($4,$2,$6); }
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
							  if ($1 == uniq_UNIQUE) $2->parallelPragma(true);
							  if ($1 == uniq_PRIORITY) $2->fullPragma(true); }
	//UNSUP	caseStart caseAttrE yMATCHES case_patternListE yENDCASE	{ }
	//UNSUP	caseStart caseAttrE yINSIDE  case_insideListE yENDCASE	{ }
	//
	//			// IEEE: conditional_statement
	|	unique_priorityE yIF '(' expr ')' stmtBlock	%prec prLOWER_THAN_ELSE
							{ $$ = new AstIf($2,$4,$6,NULL); }
	|	unique_priorityE yIF '(' expr ')' stmtBlock yELSE stmtBlock
							{ $$ = new AstIf($2,$4,$6,$8); }
	//
	//UNSUP	finc_or_dec_expression ';'		{ }
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
	//UNSUP	fexpr '.' task_subroutine_callNoMethod ';'	{ UNSUP }
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
	//UNSUP	yDISABLE hierarchical_identifier/*task_or_block*/ ';'	{ UNSUP }
	//UNSUP	yDISABLE yFORK ';'			{ UNSUP }
	//			// IEEE: event_trigger
	//UNSUP	yP_MINUSGT hierarchical_identifier/*event*/ ';'	{ UNSUP }
	//UNSUP	yP_MINUSGTGT delay_or_event_controlE hierarchical_identifier/*event*/ ';'	{ UNSUP }
	//			// IEEE: loop_statement
	|	yFOREVER stmtBlock			{ $$ = new AstWhile($1,new AstConst($1,V3Number($1,1,1)),$2); }
	|	yREPEAT '(' expr ')' stmtBlock		{ $$ = new AstRepeat($1,$3,$5);}
	|	yWHILE '(' expr ')' stmtBlock		{ $$ = new AstWhile($1,$3,$5);}
	//			// for's first ';' is in for_initalization
	|	yFOR '(' for_initialization expr ';' for_stepE ')' stmtBlock
							{ $$ = new AstFor($1, $3,$4,$6, $8);}
	|	yDO stmtBlock yWHILE '(' expr ')'	{ $$ = $2->cloneTree(true); $$->addNext(new AstWhile($1,$5,$2));}
	//UNSUP	yFOREACH '(' idClassForeach/*array_id[loop_variables]*/ ')' stmt	{ UNSUP }
	//
	//			// IEEE: jump_statement
	//UNSUP	yRETURN ';'				{ UNSUP }
	//UNSUP	yRETURN expr ';'			{ UNSUP }
	//UNSUP	yBREAK ';'				{ UNSUP }
	//UNSUP	yCONTINUE ';'				{ UNSUP }
	//
	//UNSUP	par_block				{ $$ = $1; }
	//			// IEEE: procedural_timing_control_statement + procedural_timing_control
	|	delay_control stmtBlock			{ $$ = $2; $1->v3warn(STMTDLY,"Ignoring delay on this delayed statement.\n"); }
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
		idClassSel '=' delayE expr	{ $$ = new AstAssign($2,$1,$4); }
	|	idClassSel '=' yD_FOPEN '(' expr ',' expr ')'	{ $$ = new AstFOpen($3,$1,$5,$7); }
	|	'{' variable_lvalueConcList '}' '=' delayE expr	{ $$ = new AstAssign($4,$2,$6); }
	//
	//UNSUP	~f~exprLvalue '=' delay_or_event_controlE expr { UNSUP }
	//UNSUP	~f~exprLvalue yP_PLUSEQ    expr		{ UNSUP }
	//UNSUP	~f~exprLvalue yP_MINUSEQ   expr		{ UNSUP }
	//UNSUP	~f~exprLvalue yP_TIMESEQ   expr		{ UNSUP }
	//UNSUP	~f~exprLvalue yP_DIVEQ     expr		{ UNSUP }
	//UNSUP	~f~exprLvalue yP_MODEQ     expr		{ UNSUP }
	//UNSUP	~f~exprLvalue yP_ANDEQ     expr		{ UNSUP }
	//UNSUP	~f~exprLvalue yP_OREQ      expr		{ UNSUP }
	//UNSUP	~f~exprLvalue yP_XOREQ     expr		{ UNSUP }
	//UNSUP	~f~exprLvalue yP_SLEFTEQ   expr		{ UNSUP }
	//UNSUP	~f~exprLvalue yP_SRIGHTEQ  expr		{ UNSUP }
	//UNSUP	~f~exprLvalue yP_SSRIGHTEQ expr		{ UNSUP }
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

// "datatype id = x {, id = x }"  |  "yaId = x {, id=x}" is legal
for_initialization<nodep>:	// ==IEEE: for_initialization + for_variable_declaration + extra terminating ";"
	//			// IEEE: for_variable_declaration
		varRefBase '=' expr ';'			{ $$ = new AstAssign($2,$1,$3); }
	//UNSUP: List of initializations
	;

for_stepE<nodep>:		// IEEE: for_step + empty
		/* empty */				{ $$ = NULL; }
	|	for_step				{ $$ = $1; }
	;

for_step<nodep>:		// IEEE: for_step
		varRefBase '=' expr			{ $$ = new AstAssign($2,$1,$3); }
	//UNSUP: List of steps
	;

//************************************************
// Functions/tasks

taskRef<nodep>:			// IEEE: part of tf_call
		idDotted		 		{ $$ = new AstTaskRef(CRELINE(),new AstParseRef($1->fileline(), AstParseRefExp::TASK, $1),NULL);}
	|	idDotted '(' list_of_argumentsE ')'	{ $$ = new AstTaskRef(CRELINE(),new AstParseRef($1->fileline(), AstParseRefExp::TASK, $1),$3);}
	//UNSUP: idDotted is really just id to allow dotted method calls
	;

funcRef<nodep>:			// IEEE: part of tf_call
		idDotted '(' list_of_argumentsE ')'	{ $$ = new AstFuncRef($2,new AstParseRef($1->fileline(), AstParseRefExp::FUNC, $1), $3); }
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
		yD_aIGNORE  '(' ')'			{ $$ = NULL; }
	|	yD_aIGNORE  '(' exprList ')'		{ $$ = NULL; }
	//
	|	yD_C '(' cStrList ')'			{ $$ = (v3Global.opt.ignc() ? NULL : new AstUCStmt($1,$3)); }
	|	yD_FCLOSE '(' idClassSel ')'		{ $$ = new AstFClose($1, $3); }
	|	yD_FFLUSH				{ $1->v3error("Unsupported: $fflush of all handles does not map to C++.\n"); }
	|	yD_FFLUSH '(' ')'			{ $1->v3error("Unsupported: $fflush of all handles does not map to C++.\n"); }
	|	yD_FFLUSH '(' idClassSel ')'		{ $$ = new AstFClose($1, $3); }
	|	yD_FINISH parenE			{ $$ = new AstFinish($1); }
	|	yD_FINISH '(' expr ')'			{ $$ = new AstFinish($1); }
	|	yD_STOP parenE				{ $$ = new AstStop($1); }
	|	yD_STOP '(' expr ')'			{ $$ = new AstStop($1); }
	//
	|	yD_DISPLAY  parenE						{ $$ = new AstDisplay($1,AstDisplayType::DISPLAY,"", NULL,NULL); }
	|	yD_DISPLAY  '(' yaSTRING commaEListE ')'			{ $$ = new AstDisplay($1,AstDisplayType::DISPLAY,*$3,NULL,$4); }
	|	yD_WRITE    '(' yaSTRING commaEListE ')'			{ $$ = new AstDisplay($1,AstDisplayType::WRITE,  *$3,NULL,$4); }
	|	yD_FDISPLAY '(' idClassSel ',' yaSTRING commaEListE ')' 	{ $$ = new AstDisplay($1,AstDisplayType::DISPLAY,*$5,$3,$6); }
	|	yD_FWRITE   '(' idClassSel ',' yaSTRING commaEListE ')'	{ $$ = new AstDisplay($1,AstDisplayType::WRITE,  *$5,$3,$6); }
	|	yD_INFO	    parenE						{ $$ = new AstDisplay($1,AstDisplayType::INFO,   "", NULL,NULL); }
	|	yD_INFO	    '(' yaSTRING commaEListE ')'			{ $$ = new AstDisplay($1,AstDisplayType::INFO,   *$3,NULL,$4); }
	|	yD_WARNING  parenE						{ $$ = new AstDisplay($1,AstDisplayType::WARNING,"", NULL,NULL); }
	|	yD_WARNING  '(' yaSTRING commaEListE ')'			{ $$ = new AstDisplay($1,AstDisplayType::WARNING,*$3,NULL,$4); }
	|	yD_ERROR    parenE						{ $$ = V3Parse::createDisplayError($1); }
	|	yD_ERROR    '(' yaSTRING commaEListE ')'			{ $$ = new AstDisplay($1,AstDisplayType::ERROR,  *$3,NULL,$4);   $$->addNext(new AstStop($1)); }
	|	yD_FATAL    parenE						{ $$ = new AstDisplay($1,AstDisplayType::FATAL,  "", NULL,NULL); $$->addNext(new AstStop($1)); }
	|	yD_FATAL    '(' expr ')'					{ $$ = new AstDisplay($1,AstDisplayType::FATAL,  "", NULL,NULL); $$->addNext(new AstStop($1)); if ($3) $3->deleteTree(); }
	|	yD_FATAL    '(' expr ',' yaSTRING commaEListE ')'		{ $$ = new AstDisplay($1,AstDisplayType::FATAL,  *$5,NULL,$6);   $$->addNext(new AstStop($1)); if ($3) $3->deleteTree(); }
	//
	|	yD_READMEMB '(' expr ',' varRefMem ')'				{ $$ = new AstReadMem($1,false,$3,$5,NULL,NULL); }
	|	yD_READMEMB '(' expr ',' varRefMem ',' expr ')'			{ $$ = new AstReadMem($1,false,$3,$5,$7,NULL); }
	|	yD_READMEMB '(' expr ',' varRefMem ',' expr ',' expr ')'	{ $$ = new AstReadMem($1,false,$3,$5,$7,$9); }
	|	yD_READMEMH '(' expr ',' varRefMem ')'				{ $$ = new AstReadMem($1,true, $3,$5,NULL,NULL); }
	|	yD_READMEMH '(' expr ',' varRefMem ',' expr ')'			{ $$ = new AstReadMem($1,true, $3,$5,$7,NULL); }
	|	yD_READMEMH '(' expr ',' varRefMem ',' expr ',' expr ')'	{ $$ = new AstReadMem($1,true, $3,$5,$7,$9); }
	;

system_f_call<nodep>:		// IEEE: system_tf_call (as func)
		yD_aIGNORE '(' ')'			{ $$ = new AstConst($1,V3Number($1,"'b0")); } // Unsized 0
	|	yD_aIGNORE '(' exprList ')'		{ $$ = new AstConst($1,V3Number($1,"'b0")); } // Unsized 0
	//
	|	yD_BITS '(' expr ')'			{ $$ = new AstAttrOf($1,AstAttrType::BITS,$3); }
	|	yD_C '(' cStrList ')'			{ $$ = (v3Global.opt.ignc() ? NULL : new AstUCFunc($1,$3)); }
	|	yD_CLOG2 '(' expr ')'			{ $$ = new AstCLog2($1,$3); }
	|	yD_COUNTONES '(' expr ')'		{ $$ = new AstCountOnes($1,$3); }
	|	yD_FEOF '(' expr ')'			{ $$ = new AstFEof($1,$3); }
	|	yD_FGETC '(' expr ')'			{ $$ = new AstFGetC($1,$3); }
	|	yD_FGETS '(' idClassSel ',' expr ')'	{ $$ = new AstFGetS($1,$3,$5); }
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
	;

list_of_argumentsE<nodep>:	// IEEE: [list_of_arguments]
		/* empty */				{ $$ = NULL; }
	|	argsExprList				{ $$ = $1; }
	//UNSUP empty arguments with just ,,
	;

task_declaration<nodep>:	// ==IEEE: task_declaration
		yTASK lifetimeE taskId tfGuts yENDTASK endLabelE
			{ $$ = new AstTask ($1,*$3,$4);}
	;

function_declaration<funcp>:	// IEEE: function_declaration + function_body_declaration
	 	yFUNCTION lifetimeE funcTypeE tfIdScoped			 tfGuts yENDFUNCTION endLabelE { $$ = new AstFunc ($1,*$4,$5,$3); if ($3) $$->isSigned($3->isSigned()); }
	| 	yFUNCTION lifetimeE funcTypeE tfIdScoped yVL_ISOLATE_ASSIGNMENTS tfGuts yENDFUNCTION endLabelE { $$ = new AstFunc ($1,*$4,$6,$3); $$->attrIsolateAssign(true); if ($3) $$->isSigned($3->isSigned()); }
	//UNSUP: Generic function return types
	;

lifetimeE:			// IEEE: [lifetime]
		/* empty */		 		{ }
	|	lifetime		 		{ }
	;

lifetime:			// ==IEEE: lifetime
	//			// Note lifetime used by members is instead under memberQual
		ySTATIC			 		{ $1->v3error("Unsupported: Static in this context\n"); }
	|	yAUTOMATIC		 		{ }
	;

taskId<strp>:
		tfIdScoped				{ $$ = $1; }
	;

tfIdScoped<strp>:		// IEEE: part of function_body_declaration/task_body_declaration
	//			// IEEE: [ interface_identifier '.' | class_scope ] function_identifier
		id					{ $$ = $1; }
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

funcTypeE<rangep>:
		/* empty */				{ $$ = NULL; }
	|	yINTEGER				{ $$ = new AstRange($1,31,0); $$->isSigned(true); }
	|	ySIGNED					{ $$ = new AstRange($1,0,0); $$->isSigned(true); }
	|	ySIGNED '[' constExpr ':' constExpr ']'	{ $$ = new AstRange($1,$3,$5); $$->isSigned(true); }
	|	'[' constExpr ':' constExpr ']'		{ $$ = new AstRange($1,$2,$4); }
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
		yVL_PUBLIC				{ $$ = new AstPragma($1,AstPragmaType::PUBLIC_TASK); }
	|	yVL_NO_INLINE_TASK			{ $$ = new AstPragma($1,AstPragmaType::NO_INLINE_TASK); }
	;

tf_port_listE<nodep>:		// IEEE: tf_port_list + empty
	//			// Empty covered by tf_port_item
		{VARRESET_LIST(UNKNOWN);} tf_port_listList	{ $$ = $2; VARRESET_NONLIST(UNKNOWN); }
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
		data_type				{ VARTYPE($1); }
	|	signingE rangeList			{ VARTYPE($2); }
	|	signing					{ VARTYPE(NULL); }
	//UNSUP	yVAR data_type				{ VARTYPE($2); }
	//UNSUP	yVAR implicit_type			{ VARTYPE($2); }
	//
	|	tf_port_itemDir /*implicit*/		{ VARTYPE(NULL); /*default_nettype-see spec*/ }
	|	tf_port_itemDir data_type		{ VARTYPE($2); }
	|	tf_port_itemDir signingE rangeList	{ VARTYPE($3); }
	|	tf_port_itemDir signing			{ VARTYPE(NULL); }
	//UNSUP	tf_port_itemDir yVAR data_type		{ VARTYPE($3); }
	//UNSUP	tf_port_itemDir yVAR implicit_type	{ VARTYPE($3); }
	;

tf_port_itemDir:		// IEEE: part of tf_port_item, direction
		port_direction				{ }  // port_direction sets VARIO
	;

tf_port_itemAssignment<varp>:	// IEEE: part of tf_port_item, which has assignment
		id variable_dimensionListE sigAttrListE
			{ $$ = VARDONEA(*$1, $2, $3); }
	|	id variable_dimensionListE sigAttrListE '=' expr
			{ $$ = VARDONEA(*$1, $2, $3); $$->initp($5); }
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
	|	'-' ~r~expr	%prec prUNARYARITH	{ $$ = new AstUnaryMin	($1,$2); }
	|	'!' ~r~expr	%prec prNEGATION	{ $$ = new AstLogNot	($1,$2); }
	|	'&' ~r~expr	%prec prREDUCTION	{ $$ = new AstRedAnd	($1,$2); }
	|	'~' ~r~expr	%prec prNEGATION	{ $$ = new AstNot	($1,$2); }
	|	'|' ~r~expr	%prec prREDUCTION	{ $$ = new AstRedOr	($1,$2); }
	|	'^' ~r~expr	%prec prREDUCTION	{ $$ = new AstRedXor	($1,$2); }
	|	yP_NAND ~r~expr	%prec prREDUCTION	{ $$ = new AstNot($1,new AstRedAnd($1,$2)); }
	|	yP_NOR  ~r~expr	%prec prREDUCTION	{ $$ = new AstNot($1,new AstRedOr ($1,$2)); }
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
	//UNSUP	~l~expr yINSIDE '{' open_range_list '}'	{ UNSUP }
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
	|	yaINTNUM				{ $$ = new AstConst(CRELINE(),*$1); }
	//UNSUP	yaFLOATNUM				{ UNSUP }
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
	//UNSUP	~l~expr '.' function_subroutine_callNoMethod	{ UNSUP }
	//			// method_call:array_method requires a '.'
	//UNSUP	~l~expr '.' array_methodNoRoot		{ UNSUP }
	//
	//			// IEEE: '(' mintypmax_expression ')'
	|	~noPar__IGNORE~'(' expr ')'		{ $$ = $2; }
	//UNSUP	~noPar__IGNORE~'(' expr ':' expr ':' expr ')'	{ $$ = $4; }
	//			// PSL rule
	|	'_' '(' statePushVlg expr statePop ')'	{ $$ = $4; }	// Arbitrary Verilog inside PSL
	//
	//			// IEEE: cast/constant_cast
	//UNSUP	casting_type yP_TICK '(' expr ')'	{ UNSUP }
	//			// Spec only allows primary with addition of a type reference
	//			// We'll be more general, and later assert LHS was a type.
	//UNSUP	~l~expr yP_TICK '(' expr ')'		{ UNSUP }
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

exprNoStr<nodep>:		// expression with string removed
		BISONPRE_COPY(expr,{s/~noStr__IGNORE~/Ignore/g;})	// {copied}
	;

exprOkLvalue<nodep>:		// expression that's also OK to use as a variable_lvalue
		~l~exprScope				{ $$ = $1; }
	//			// IEEE: concatenation/constant_concatenation
	|	'{' cateList '}'			{ $$ = $2; }
	//			// IEEE: assignment_pattern_expression
	//			// IEEE: [ assignment_pattern_expression_type ] == [ ps_type_id /ps_paremeter_id]
	//			// We allow more here than the spec requires
	//UNSUP	~l~exprScope assignment_pattern		{ UNSUP }
	//UNSUP	data_type assignment_pattern		{ UNSUP }
	//UNSUP	assignment_pattern			{ UNSUP }
	//
	//UNSUP	streaming_concatenation			{ UNSUP }
	;

exprScope<nodep>:		// scope and variable for use to inside an expression
	// 			// Here we've split method_call_root | implicit_class_handle | class_scope | package_scope
	//			// from the object being called and let expr's "." deal with resolving it.
	//
	//			// IEEE: [ implicit_class_handle . | class_scope | package_scope ] hierarchical_identifier select
	//			// Or method_call_body without parenthesis
	//			// See also varRefClassBit, which is the non-expr version of most of this
	//UNSUP	yTHIS					{ UNSUP }
		idClassSel				{ $$ = $1; }
	//UNSUP: idArrayed instead of idClassSel
	//UNSUP	package_scopeIdFollows idArrayed	{ UNSUP }
	//UNSUP	class_scopeIdFollows idArrayed		{ UNSUP }
	//UNSUP	~l~expr '.' idArrayed			{ UNSUP }
	//			// expr below must be a "yTHIS"
	//UNSUP	~l~expr '.' ySUPER			{ UNSUP }
	//			// Part of implicit_class_handle
	//UNSUP	ySUPER					{ UNSUP }
	;

// Psl excludes {}'s by lexer converting to different token
exprPsl<nodep>:
		expr					{ $$ = $1; }
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

gateBuf<assignwp>:
		gateIdE instRangeE '(' idClassSel ',' expr ')'		{ $$ = new AstAssignW ($3,$4,$6); $$->allowImplicit(true); }
	;
gateBufif0<assignwp>:
		gateIdE instRangeE '(' idClassSel ',' expr ',' expr ')'	{ $$ = new AstAssignW ($3,$4,new AstCond($3,$8, new AstConst($3,V3Number($3,"1'bz")), $6)); }
	;
gateBufif1<assignwp>:
		gateIdE instRangeE '(' idClassSel ',' expr ',' expr ')'	{ $$ = new AstAssignW ($3,$4,new AstCond($3,$8, $6, new AstConst($3,V3Number($3,"1'bz")))); }
	;
gateNot<assignwp>:
		gateIdE instRangeE '(' idClassSel ',' expr ')'		{ $$ = new AstAssignW ($3,$4,new AstNot($5,$6)); $$->allowImplicit(true); }
	;
gateNotif0<assignwp>:
		gateIdE instRangeE '(' idClassSel ',' expr ',' expr ')'	{ $$ = new AstAssignW ($3,$4,new AstCond($3,$8, new AstConst($3,V3Number($3,"1'bz")), new AstNot($3, $6))); }
	;
gateNotif1<assignwp>:
		gateIdE instRangeE '(' idClassSel ',' expr ',' expr ')'	{ $$ = new AstAssignW ($3,$4,new AstCond($3,$8, new AstNot($3,$6), new AstConst($3,V3Number($3,"1'bz")))); }
	;
gateAnd<assignwp>:
		gateIdE instRangeE '(' idClassSel ',' gateAndPinList ')'	{ $$ = new AstAssignW ($3,$4,$6); $$->allowImplicit(true); }
	;
gateNand<assignwp>:
	 	gateIdE instRangeE '(' idClassSel ',' gateAndPinList ')'	{ $$ = new AstAssignW ($3,$4,new AstNot($5,$6)); $$->allowImplicit(true); }
	;
gateOr<assignwp>:
		gateIdE instRangeE '(' idClassSel ',' gateOrPinList ')'		{ $$ = new AstAssignW ($3,$4,$6); $$->allowImplicit(true); }
	;
gateNor<assignwp>:
		gateIdE instRangeE '(' idClassSel ',' gateOrPinList ')'		{ $$ = new AstAssignW ($3,$4,new AstNot($5,$6)); $$->allowImplicit(true); }
	;
gateXor<assignwp>:
		gateIdE instRangeE '(' idClassSel ',' gateXorPinList ')'	{ $$ = new AstAssignW ($3,$4,$6); $$->allowImplicit(true); }
	;
gateXnor<assignwp>:
		gateIdE instRangeE '(' idClassSel ',' gateXorPinList ')'	{ $$ = new AstAssignW ($3,$4,new AstNot($5,$6)); $$->allowImplicit(true); }
	;
gatePullup<nodep>:
		gateIdE instRangeE '(' idClassSel ')'	{ $$ = new AstPull ($3, $4, true); }
	;
gatePulldown<nodep>:
		gateIdE instRangeE '(' idClassSel ')'	{ $$ = new AstPull ($3, $4, false); }
	;
gateIdE:
		/*empty*/				{}
	|	id					{}
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

strengthSpecE:			// IEEE: drive_strength + pullup_strength + pulldown_strength + charge_strength - plus empty
		/* empty */				{ }
	//UNSUP	strengthSpec				{ }
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

specparam_declaration<nodep>:		// ==IEEE: specparam_declaration
		ySPECPARAM junkToSemi ';'		{ $$ = NULL; }
	;

junkToSemi:
		BISONPRE_NOT(';',yENDSPECIFY,yENDMODULE)	{ }
	|	error {}
	;

//************************************************
// IDs

id<strp>:
		yaID__ETC				{ $$ = $1; }
	;

idAny<strp>:			// Any kind of identifier
	//UNSUP	yaID__aCLASS				{ $$ = $1; }
	//UNSUP	yaID__aCOVERGROUP			{ $$ = $1; }
	//UNSUP	yaID__aPACKAGE				{ $$ = $1; }
	//UNSUP	yaID__aTYPE				{ $$ = $1; }
		yaID__ETC				{ $$ = $1; }
	;

idSVKwd<strp>:			// Warn about non-forward compatible Verilog 2001 code
	//			// yBIT, yBYTE won't work here as causes conflicts
		yDO					{ static string s = "do"   ; $$ = &s; ERRSVKWD($1,*$$); }
	|	yFINAL					{ static string s = "final"; $$ = &s; ERRSVKWD($1,*$$); }
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
	;

variable_lvalueConcList<nodep>:	// IEEE: part of variable_lvalue: '{' variable_lvalue { ',' variable_lvalue } '}'
		variable_lvalue					{ $$ = $1; }
	|	variable_lvalueConcList ',' variable_lvalue	{ $$ = new AstConcat($2,$1,$3); }
	;

// VarRef to a Memory
varRefMem<parserefp>:
		idDotted				{ $$ = new AstParseRef($1->fileline(), AstParseRefExp::VAR_MEM, $1); }
	;

// VarRef to dotted, and/or arrayed, and/or bit-ranged variable
idClassSel<parserefp>:			// Misc Ref to dotted, and/or arrayed, and/or bit-ranged variable
		idDotted				{ $$ = new AstParseRef($1->fileline(), AstParseRefExp::VAR_ANY, $1); }
	//			// IEEE: [ implicit_class_handle . | package_scope ] hierarchical_variable_identifier select
	//UNSUP	yTHIS '.' idDotted			{ UNSUP }
	//UNSUP	ySUPER '.' idDotted			{ UNSUP }
	//UNSUP	yTHIS '.' ySUPER '.' idDotted		{ UNSUP }
	//			// Expanded: package_scope idDotted
	//UNSUP	package_scopeIdFollows idDotted		{ UNSUP }
	;

idDotted<nodep>:
	//UNSUP	yD_ROOT '.' idDottedMore		{ UNSUP }
		idDottedMore		 		{ $$ = $1; }
	;

idDottedMore<nodep>:
		idArrayed 				{ $$ = $1; }
	|	idDotted '.' idArrayed	 		{ $$ = new AstDot($2,$1,$3); }
	;

// Single component of dotted path, maybe [#].
// Due to lookahead constraints, we can't know if [:] or [+:] are valid (last dotted part),
// we'll assume so and cleanup later.
// id below includes:
//	 enum_identifier
idArrayed<nodep>:		// IEEE: id + select
		id						{ $$ = new AstText(CRELINE(),*$1); }
	//			// IEEE: id + part_select_range/constant_part_select_range
	|	idArrayed '[' expr ']'				{ $$ = new AstSelBit($2,$1,$3); }  // Or AstArraySel, don't know yet.
	|	idArrayed '[' constExpr ':' constExpr ']'	{ $$ = new AstSelExtract($2,$1,$3,$5); }
	//			// IEEE: id + indexed_range/constant_indexed_range
	|	idArrayed '[' expr yP_PLUSCOLON  constExpr ']'	{ $$ = new AstSelPlus($2,$1,$3,$5); }
	|	idArrayed '[' expr yP_MINUSCOLON constExpr ']'	{ $$ = new AstSelMinus($2,$1,$3,$5); }
	;

// VarRef without any dots or vectorizaion
varRefBase<varrefp>:
		id					{ $$ = new AstVarRef(CRELINE(),*$1,false);}
	;

strAsInt<nodep>:
		yaSTRING				{ $$ = new AstConst(CRELINE(),V3Number(V3Number::VerilogString(),CRELINE(),V3Parse::deQuote(CRELINE(),*$1)));}
	;

strAsIntIgnore<nodep>:		// strAsInt, but never matches for when expr shouldn't parse strings
		yaSTRING__IGNORE			{ $$ = NULL; yyerror("Impossible token"); }
	;

strAsText<nodep>:
		yaSTRING				{ $$ = V3Parse::createTextQuoted(CRELINE(),*$1);}
	;

endLabelE:
		/* empty */				{ }
	|	':' idAny				{ }
	//UNSUP	':' yNEW__ETC				{ }
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
	;

concurrent_assertion_statement<nodep>:	// ==IEEE: concurrent_assertion_statement
	//UNSUP: assert/assume
	//				// IEEE: cover_property_statement
		yCOVER yPROPERTY '(' property_spec ')' stmtBlock	{ $$ = new AstPslCover($1,$4,$6); }
	;

property_spec<nodep>:			// IEEE: property_spec
	//UNSUP: This rule has been super-specialized to what is supported now
		'@' '(' senitemEdge ')' property_specDisable expr	{ $$ = new AstPslClocked($1,$3,$5,$6); }
	|	'@' '(' senitemEdge ')' expr		{ $$ = new AstPslClocked($1,$3,NULL,$5); }
	|	property_specDisable expr	 	{ $$ = new AstPslClocked($2->fileline(),NULL,$1,$2); }
	|	expr	 				{ $$ = new AstPslClocked($1->fileline(),NULL,NULL,$1); }
	;

property_specDisable<nodep>:		// IEEE: part of property_spec
		yDISABLE yIFF '(' expr ')'		{ $$ = $4; }
	;

immediate_assert_statement<nodep>:	// ==IEEE: immediate_assert_statement
	//				// action_block expanded here, for compatibility with AstVAssert
		yASSERT '(' expr ')' stmtBlock %prec prLOWER_THAN_ELSE	{ $$ = new AstVAssert($1,$3,$5, V3Parse::createDisplayError($1)); }
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

ps_id_etc<strp>:		// package_scope + general id
		package_scopeIdFollowsE id		{ $$=$2; }
	;

//=== Below rules assume special scoping per above

package_scopeIdFollowsE:	// IEEE: [package_scope]
	//			// IMPORTANT: The lexer will parse the following ID to be in the found package
		/* empty */				{ }
	//UNSUP	package_scopeIdFollows			{ UNSUP }
	;

//************************************************
// PSL Statements

pslStmt<nodep>:
		yPSL pslDir  stateExitPsl		{ $$ = $2; }
	|	yPSL pslDecl stateExitPsl 		{ $$ = $2; }
	;

pslDir<nodep>:
		id ':' pslDirOne			{ $$ = $3; }
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

AstVar* V3Parse::createVariable(FileLine* fileline, string name, AstRange* arrayp, AstNode* attrsp) {
    AstVarType type = V3Parse::s_varIO;
    AstRange* rangep = V3Parse::s_varRangep;
    AstRange* cleanup_rangep = NULL;
    //UINFO(0,"CREVAR "<<fileline->ascii()<<" decl="<<V3Parse::s_varDecl.ascii()<<" io="<<V3Parse::s_varIO.ascii()<<endl);
    if (type == AstVarType::UNKNOWN || type == AstVarType::PORT) type = V3Parse::s_varDecl;
    if (type == AstVarType::PORT) {
	// Just wanted port decl; we've already made it.
	if (rangep) fileline->v3error("Unsupported: Ranges ignored in port-lists");
	return NULL;
    }
    if (type == AstVarType::UNKNOWN) fileline->v3fatalSrc("Unknown signal type declared");
    // Linting, because we allow parsing of a superset of the language
    if (type == AstVarType::INTEGER || V3Parse::s_varDecl == AstVarType::INTEGER
	|| type == AstVarType::GENVAR) {
	if (rangep) {
	    if (rangep->msbConst()==31 && rangep->lsbConst()==0) {
		// For backward compatibility with functions some INTEGERS are internally made as [31:0]
		rangep->deleteTree(); rangep=NULL; V3Parse::s_varRangep=NULL;
	    } else {
		fileline->v3error("Integers may not be ranged: "<<name);
	    }
	}
	cleanup_rangep = new AstRange(fileline, 31, 0);  // Integer == REG[31:0]
	rangep = cleanup_rangep;
    }
    if (type == AstVarType::GENVAR) {
	if (arrayp) fileline->v3error("Genvars may not be arrayed: "<<name);
    }
    AstVar* nodep = new AstVar(fileline, type, name,
			       rangep->cloneTree(false),
			       arrayp);
    nodep->addAttrsp(attrsp);
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

//YACC = /kits/sources/bison-2.4.1/src/bison --report=lookahead
// --report=lookahead
// --report=itemset
// --graph
//
// Local Variables:
// compile-command: "cd obj_dbg ; /usr/bin/bison -y -d -v ../verilog.y ; cat y.output"
// End:
