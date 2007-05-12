// $Id$ -*- C++ -*-
//*************************************************************************
// DESCRIPTION: Verilator: Bison grammer file
//
// Code available from: http://www.veripool.com/verilator
//
//*************************************************************************
//
// Copyright 2003-2007 by Wilson Snyder.  This program is free software; you can
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
/* $Id$ */
#include <stdio.h>
#include <stdlib.h>
#include <cstdarg>
#include <string.h>

#include "V3Read.h"
#include "V3Ast.h"
#include "V3Global.h"

#define YYERROR_VERBOSE
#define YYMAXDEPTH 500

// Pick up new lexer
#define yylex V3Read::yylex
#define PSLUNSUP(what) NULL; yyerror("Unsupported: PSL language feature not implemented");

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
#define VARRANGE(range) { V3Parse::s_varRangep=(range); }
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
    AstFuncRef*	funcrefp;
    AstModule*	modulep;
    AstNodeVarRef*	varnodep;
    AstParseRef*	parserefp;
    AstPin*	pinp;
    AstRange*	rangep;
    AstSenItem*	senitemp;
    AstSenTree*	sentreep;
    AstTaskRef*	taskrefp;
    AstVar*	varp;
    AstVarRef*	varrefp;
}

// Generic lexer tokens, for example a number
%token<cdouble>		yaFLOATNUM	"FLOATING-POINT NUMBER"
%token<fileline>	yaTIMINGSPEC	"TIMING SPEC ELEMENT"
%token<nump>		yaINTNUM	"INTEGER NUMBER"
%token<strp>		yaID		"IDENTIFIER"
%token<strp>		yaSTRING	"STRING"

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
%token<fileline>	yBEGIN		"begin"
%token<fileline>	yBUF		"buf"
%token<fileline>	yCASE		"case"
%token<fileline>	yCASEX		"casex"
%token<fileline>	yCASEZ		"casez"
%token<fileline>	yCLOCK		"clock"
%token<fileline>	yCOVER		"cover"
%token<fileline>	yDEFAULT	"default"
%token<fileline>	yDEFPARAM	"defparam"
%token<fileline>	yDO		"do"
%token<fileline>	yELSE		"else"
%token<fileline>	yEND		"bend"
%token<fileline>	yENDCASE	"endcase"
%token<fileline>	yENDFUNCTION	"endfunction"
%token<fileline>	yENDGENERATE	"endgenerate"
%token<fileline>	yENDMODULE	"endmodule"
%token<fileline>	yENDSPECIFY	"endspecify"
%token<fileline>	yENDTASK	"endtask"
%token<fileline>	yFINAL		"final"
%token<fileline>	yFOR		"for"
%token<fileline>	yFUNCTION	"function"
%token<fileline>	yGENERATE	"generate"
%token<fileline>	yGENVAR		"genvar"
%token<fileline>	yIF		"if"
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
%token<fileline>	yPARAM		"param"
%token<fileline>	yPOSEDGE	"posedge"
%token<fileline>	yPSL		"psl"
%token<fileline>	yREG		"reg"
%token<fileline>	yREPORT		"report"
%token<fileline>	ySCALARED	"scalared"
%token<fileline>	ySIGNED		"signed"
%token<fileline>	ySPECIFY	"specify"
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
%token<fileline>	yD_COUNTONES	"$countones"
%token<fileline>	yD_DISPLAY	"$display"
%token<fileline>	yD_ERROR	"$error"
%token<fileline>	yD_FATAL	"$fatal"
%token<fileline>	yD_FCLOSE	"$fclose"
%token<fileline>	yD_FDISPLAY	"$fdisplay"
%token<fileline>	yD_FINISH	"$finish"
%token<fileline>	yD_FOPEN	"$fopen"
%token<fileline>	yD_FWRITE	"$fwrite"
%token<fileline>	yD_INFO		"$info"
%token<fileline>	yD_ISUNKNOWN	"$isunknown"
%token<fileline>	yD_ONEHOT	"$onehot"
%token<fileline>	yD_ONEHOT0	"$onehot0"
%token<fileline>	yD_READMEMB	"$readmemb"
%token<fileline>	yD_READMEMH	"$readmemh"
%token<fileline>	yD_SIGNED	"$signed"
%token<fileline>	yD_STOP		"$stop"
%token<fileline>	yD_TIME		"$time"
%token<fileline>	yD_UNSIGNED	"$unsigned"
%token<fileline>	yD_WARNING	"$warning"
%token<fileline>	yD_WRITE	"$write"

%token<fileline>	yPSL_ASSERT	"PSL assert"

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

%token<fileline>	yP_PLUSCOLON	"+:"
%token<fileline>	yP_MINUSCOLON	"-:"

%token<fileline>	yPSL_BRA	"{"
%token<fileline>	yPSL_KET	"}"

%token<fileline>	';' '=' ',' '(' '.' '!' '~' '[' '@'

//********************
// PSL op precedence
%right<fileline> 	yP_LOGIF  yP_LOGIFF
%right<fileline>	yP_OR_MINUS_GT  yP_OR_EQ_GT
%left<fileline>		prPSLCLK

// Verilog op precedence
%left<fileline> ':'
%left<fileline> '?'
%left<fileline> yP_OROR
%left<fileline> yP_ANDAND
%left<fileline> '|' yP_NOR
%left<fileline> '^'
%left<fileline> yP_XNOR
%left<fileline> '&' yP_NAND
%left<fileline> yP_EQUAL yP_NOTEQUAL yP_CASEEQUAL yP_CASENOTEQUAL
%left<fileline> '>' '<' yP_GTE yP_LTE
%left<fileline> yP_SLEFT yP_SRIGHT yP_SSRIGHT
%left<fileline> '+' '-'
%left<fileline> '*' '/' '%'
%left<fileline> yP_POW
%left<fileline> '{' '}'
%left<fileline> prUNARYARITH
%left<fileline> prREDUCTION
%left<fileline> prNEGATION

%nonassoc prLOWER_THAN_ELSE
%nonassoc yELSE

// Types are in same order as declarations.
// Naming:
//	Trailing E indicates this type may have empty match
%type<modulep>	mheader
%type<nodep>	modportsE portList port
%type<nodep>	v2kPortList v2kPortSig
%type<nodep>	v2kPort ioDecl varDecl
%type<nodep>	modParDecl modParList modParE
%type<nodep>	modItem modItemList modItemListE modOrGenItem
%type<nodep>	genItem genItemList genItemBegin genItemBlock genTopBlock genCaseList
%type<nodep>	dterm
%type<varp>	onesig sigId sigIdRange paramId sigList regsig regsigList regSigId
%type<varp>	netSig netSigList
%type<rangep>	rangeListE regrangeE anyrange rangeList delayrange portrangeE
%type<varp>	param paramList
%type<nodep>	instnameList
%type<cellp>	instname
%type<pinp>	cellpinList cellpinlist2 cellpinitemE instparamListE
%type<nodep>	defpList defpOne
%type<sentreep>	sensitivityE
%type<senitemp>	senList senitem senitemEdge
%type<nodep>	stmtBlock stmtList stmt labeledStmt stateCaseForIf
%type<nodep>	assertStmt
%type<beginp>	beginNamed
%type<casep>	caseStmt
%type<caseitemp> caseList
%type<nodep>	casecondList assignList assignOne
%type<nodep>	constExpr exprNoStr expr exprPsl exprStrText
%type<nodep>	eList cateList cStrList
%type<varrefp>	varRefBase
%type<parserefp> varRefMem
%type<parserefp> varRefDotBit
%type<taskrefp>	taskRef
%type<funcrefp>	funcRef
%type<nodep>	idArrayed
%type<nodep>	idDotted
%type<nodep>	strAsInt strAsText concIdList
%type<nodep>	taskDecl
%type<nodep>	varDeclList
%type<funcp>	funcDecl
%type<nodep>	funcBody funcVarList funcVar
%type<rangep>	funcRange
%type<nodep>	gateDecl
%type<nodep>	gateBufList gateNotList gateAndList gateNandList
%type<nodep>	gateOrList gateNorList gateXorList gateXnorList
%type<assignwp>	gateBuf gateNot gateAnd gateNand gateOr gateNor gateXor gateXnor
%type<nodep>	gateAndPinList gateOrPinList gateXorPinList
%type<nodep>	commaEListE

%type<nodep>	pslStmt pslDir pslDirOne pslProp
%type<nodep>	pslDecl
%type<nodep>	pslSequence pslSere pslExpr

%start file

%%
//**********************************************************************
// Feedback to the Lexer

stateExitPsl:					 	{ V3Read::stateExitPsl(); }
	;
statePushVlg:					 	{ V3Read::statePushVlg(); }
	;
statePop:					 	{ V3Read::statePop(); }
	;

//**********************************************************************
// Modules

file:		mod
	|	file mod
	;

mod:		mheader modParE modportsE ';' modItemListE yENDMODULE
			{ $1->modTrace(V3Parse::s_trace);  // Stash for implicit wires, etc
			  if ($2) $1->addStmtp($2); if ($3) $1->addStmtp($3); if ($5) $1->addStmtp($5); }
	;

mheader:	yMODULE { V3Parse::s_trace=v3Global.opt.trace();}
			yaID				{ $$ = new AstModule($1,*$3); $$->inLibrary(V3Read::inLibrary());
							  $$->modTrace(v3Global.opt.trace());
							  V3Read::rootp()->addModulep($$); }
	;

modParE:	/* empty */					{ $$ = NULL; }
	|	'#' '(' ')'					{ $$ = NULL; }
	|	'#' '(' modParList ')'				{ $$ = $3; }
	|	'#' '(' modParList ';' ')'			{ $$ = $3; }
	;

modParList:	modParDecl				       	{ $$ = $1; }
	|	modParList ';' modParDecl 	 	   	{ $$ = $1->addNext($3); }
	;

modportsE:	/* empty */					{ $$ = NULL; }
	|	'(' ')'						{ $$ = NULL; }
	|	'(' {V3Parse::s_pinNum=1;} portList ')'		{ $$ = $3; }
	|	'(' {V3Parse::s_pinNum=1;} v2kPortList ')'	{ $$ = $3; }
	;

portList:	port				       	{ $$ = $1; }
	|	portList ',' port	  	   	{ $$ = $1->addNext($3); }
	;

port:		yaID portrangeE			       	{ $$ = new AstPort(CRELINE(),V3Parse::s_pinNum++,*$1); }
	;

v2kPortList:	v2kPort				       	{ $$ = $1; }
	|	v2kPortList ',' v2kPort	  	   	{ $$ = $1->addNext($3); }
	;

v2kPortSig:	onesig					{ $$=$1; $$->addNext(new AstPort(CRELINE(),V3Parse::s_pinNum++, V3Parse::s_varAttrp->name())); }
	;

//************************************************
// Variables

varRESET:	/* empty */ 				{ VARRESET(); }
	;

varNet:		ySUPPLY0				{ VARDECL(SUPPLY0); }
	|	ySUPPLY1				{ VARDECL(SUPPLY1); }
	|	yWIRE 					{ VARDECL(WIRE); }
	|	yTRI 					{ VARDECL(TRIWIRE); }
	;
varGParam:	yPARAM					{ VARDECL(GPARAM); }
	;
varLParam:	yLOCALPARAM				{ VARDECL(LPARAM); }
	;
varGenVar:	yGENVAR					{ VARDECL(GENVAR); }
	;
varReg:		yREG					{ VARDECL(REG); }
	|	yINTEGER				{ VARDECL(INTEGER); }
	;
varInput:	yINPUT					{ VARIO(INPUT); }
	;
varOutput:	yOUTPUT					{ VARIO(OUTPUT); }
	;
varInout:	yINOUT					{ VARIO(INOUT); }
	;

varSignedE:	/*empty*/ 				{ }
	|	ySIGNED					{ VARSIGNED(true); }
	|	yUNSIGNED				{ VARSIGNED(false); }
	;

v2kNetDeclE:	/*empty*/ 				{ }
	|	varNet 					{ }
	;

v2kVarDecl:	v2kNetDeclE 				{ }
	|	varReg 					{ }
	;

v2kPort:	varRESET varInput  varSignedE v2kNetDeclE regrangeE v2kPortSig	{ $$ = $6; }
	|	varRESET varInout  varSignedE v2kNetDeclE regrangeE v2kPortSig	{ $$ = $6; }
	|	varRESET varOutput varSignedE v2kVarDecl  regrangeE v2kPortSig	{ $$ = $6; }
	;

ioDecl:		varRESET varInput  varSignedE v2kNetDeclE regrangeE  sigList ';'	{ $$ = $6; }
     	|	varRESET varInout  varSignedE v2kNetDeclE regrangeE  sigList ';'	{ $$ = $6; }
     	|	varRESET varOutput varSignedE v2kVarDecl  regrangeE  sigList ';'	{ $$ = $6; }
	;

varDecl:	varRESET varReg     varSignedE regrangeE  regsigList ';'	{ $$ = $5; }
	|	varRESET varGParam  varSignedE regrangeE  paramList ';'		{ $$ = $5; }
	|	varRESET varLParam  varSignedE regrangeE  paramList ';'		{ $$ = $5; }
	|	varRESET varNet     varSignedE delayrange netSigList ';'	{ $$ = $5; }
	|	varRESET varGenVar  varSignedE            regsigList ';'	{ $$ = $4; }
	;

modParDecl:	varRESET varGParam  varSignedE regrangeE   paramList 	{ $$ = $5; }  /* No semicolon*/
	;

//************************************************
// modItemList

modItemListE:	/* empty */				{ $$ = NULL; }
	|	modItemList				{ $$ = $1; }
	;

modItemList:	modItem					{ $$ = $1; }
	|	modItemList modItem			{ $$ = $1->addNextNull($2); }
	;

modItem:	modOrGenItem 				{ $$ = $1; }
	|	yGENERATE genTopBlock yENDGENERATE	{ $$ = new AstGenerate($1, $2); }
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

modOrGenItem:	yALWAYS sensitivityE stmtBlock		{ $$ = new AstAlways($1,$2,$3); }
	|	yFINAL stmtBlock			{ $$ = new AstFinal($1,$2); }
	|	yINITIAL stmtBlock			{ $$ = new AstInitial($1,$2); }
	|	yASSIGN delayE assignList ';'		{ $$ = $3; }
	|	yDEFPARAM defpList ';'			{ $$ = $2; }
	|	yaID instparamListE {INSTPREP(*$1,$2);} instnameList ';'  { $$ = $4; V3Parse::s_impliedDecl=false;}
	|	taskDecl 				{ $$ = $1; }
	|	funcDecl 				{ $$ = $1; }
	|	gateDecl 				{ $$ = $1; }
	|	ioDecl	 				{ $$ = $1; }
	|	varDecl 				{ $$ = $1; }
	|	pslStmt 				{ $$ = $1; }
	;

//************************************************
// genmodItemList

// Because genItemList includes variable declarations, we don't need beginNamed
genItemBlock:	genItem					{ $$ = new AstBegin(CRELINE(),"genblk",$1); }
	|	genItemBegin				{ $$ = $1; }
	;

genTopBlock:	genItemList				{ $$ = $1; }
	|	genItemBegin				{ $$ = $1; }
	;

genItemBegin:	yBEGIN genItemList yEND		{ $$ = new AstBegin($1,"genblk",$2); }
	|	yBEGIN yEND				{ $$ = NULL; }
	|	yBEGIN ':' yaID genItemList yEND	{ $$ = new AstBegin($2,*$3,$4); }
	|	yBEGIN ':' yaID yEND			{ $$ = NULL; }
	;

genItemList:	genItem					{ $$ = $1; }
	|	genItemList genItem			{ $$ = $1->addNextNull($2); }
	;

genItem:	modOrGenItem 				{ $$ = $1; }
	|	yCASE  '(' expr ')' genCaseList yENDCASE	{ $$ = new AstGenCase($1,$3,$5); }
	|	yIF expr genItemBlock	%prec prLOWER_THAN_ELSE	{ $$ = new AstGenIf($1,$2,$3,NULL); }
	|	yIF expr genItemBlock yELSE genItemBlock	{ $$ = new AstGenIf($1,$2,$3,$5); }
	|	yFOR '(' varRefBase '=' expr ';' expr ';' varRefBase '=' expr ')' genItemBlock
							{ $$ = new AstGenFor($1, new AstAssign($4,$3,$5)
									     ,$7, new AstAssign($10,$9,$11)
									     ,$13);}
	;

genCaseList:	casecondList ':' genItemBlock		{ $$ = new AstCaseItem($2,$1,$3); }
	|	yDEFAULT ':' genItemBlock		{ $$ = new AstCaseItem($2,NULL,$3); }
	|	yDEFAULT genItemBlock			{ $$ = new AstCaseItem($1,NULL,$2); }
	|	genCaseList casecondList ':' genItemBlock	{ $$ = $1;$1->addNext(new AstCaseItem($3,$2,$4)); }
	|       genCaseList yDEFAULT genItemBlock		{ $$ = $1;$1->addNext(new AstCaseItem($2,NULL,$3)); }
	|	genCaseList yDEFAULT ':' genItemBlock		{ $$ = $1;$1->addNext(new AstCaseItem($3,NULL,$4)); }
	;

//************************************************
// modItems

varDeclList:	varDecl					{ $$ = $1; }
	|	varDecl varDeclList			{ $$ = $1->addNext($2); }
	;

assignList:	assignOne				{ $$ = $1; }
	|	assignList ',' assignOne		{ $$ = $1->addNext($3); }
	;

assignOne:	varRefDotBit '=' expr			{ $$ = new AstAssignW($2,$1,$3); }
	|	'{' concIdList '}' '=' expr		{ $$ = new AstAssignW($1,$2,$5); }
	;

delayE:		/* empty */
	|	'#' dterm				{} /* ignored */
	|	'#' '(' dterm ')'			{} /* ignored */
	|	'#' '(' dterm ',' dterm ')'		{} /* ignored */
	|	'#' '(' dterm ',' dterm ',' dterm ')'	{} /* ignored */
	;

dterm:		yaID 					{ $$ = NULL; }
	|	yaINTNUM 				{ $$ = NULL; }
	|	yaFLOATNUM 				{ $$ = NULL; }
	;

onesig:		sigId					{ $$=$1; }
	|	sigId sigAttrList			{ $$=$1; }
	;

sigId:		yaID					{ $$ = V3Parse::createVariable(CRELINE(), *$1, NULL); }
	;

sigIdRange:	yaID rangeList				{ $$ = V3Parse::createVariable(CRELINE(), *$1, $2); }
	;

regSigId:	yaID rangeListE				{ $$ = V3Parse::createVariable(CRELINE(), *$1, $2); }
	|	yaID rangeListE '=' constExpr		{ $$ = V3Parse::createVariable(CRELINE(), *$1, $2);
							  $$->addNext(new AstInitial($3,new AstAssign($3, new AstVarRef($3, $$, true), $4))); }
	;

paramId:	yaID 					{ $$ = V3Parse::createVariable(CRELINE(), *$1, NULL); }
	;

sigAttrListE:	/*empty*/				{}
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

sigList:	onesig					{ $$ = $1; }
	|	sigList ',' onesig			{ $$ = $1; $1->addNext($3); }
	;

netSig:		sigId sigAttrListE			{ $$ = $1; }
	|	sigId sigAttrListE '=' expr		{ $$ = $1; $1->addNext(new AstAssignW($3,new AstVarRef($3,$1->name(),true),$4)); }
	|	sigIdRange sigAttrListE			{ $$ = $1; }
	;

netSigList:	netSig  				{ $$ = $1; }
	|	netSigList ',' netSig		       	{ $$ = $1;$1->addNext($3); }
	;

regsig:		regSigId				{}
	|	regSigId sigAttrList			{}
	;

regsigList:	regsig  				{ $$ = $1; }
	|	regsigList ',' regsig		       	{ $$ = $1;$1->addNext($3); }
	;

rangeListE:	/* empty */    		               	{ $$ = NULL; }
	|	rangeList 				{ $$ = $1; }
	;

rangeList:	anyrange				{ $$ = $1; }
        |	rangeList anyrange			{ $$ = $1; $1->addNext($2); }
	;

regrangeE:	/* empty */    		               	{ $$ = NULL; VARRANGE($$); }
	|	anyrange 				{ $$ = $1; VARRANGE($$); }
	;

anyrange:	'[' constExpr ':' constExpr ']'		{ $$ = new AstRange($1,$2,$4); }
	;

delayrange:	delayE regrangeE			{ $$ = $2; }
	|	ySCALARED delayE regrangeE		{ $$ = $3; }
	|	yVECTORED delayE regrangeE		{ $$ = $3; }
	;

portrangeE:	/* empty */	                   	{ $$ = NULL; }
	|	'[' constExpr ']'              		{ $$ = NULL; $1->v3error("Ranges ignored on port-list.\n"); }
	|	'[' constExpr ':' constExpr  ']'    	{ $$ = NULL; $1->v3error("Ranges ignored on port-list.\n"); }
	;

// Parameters
param:		paramId sigAttrListE '=' expr		{ $$ = $1; $$->initp($4); }
	;

paramList:	param					{ $$ = $1; }
	|	paramList ',' param			{ $$ = $1; $1->addNext($3); }
	;

defpList:	defpOne					{ $$ = $1; }
	|	defpList ',' defpOne			{ $$ = $1->addNext($3); }
	;

defpOne:	yaID '.' yaID '=' expr 			{ $$ = new AstDefParam($4,*$1,*$3,$5); }
	;

// Instances
instparamListE:	/* empty */				{ $$ = NULL; }
	|	'#' '(' cellpinList ')'			{ $$ = $3; }
	;

instnameList:	instname				{ $$ = $1; }
	|	instnameList ',' instname		{ $$ = $1->addNext($3); }
	;

instname:	yaID funcRange '(' cellpinList ')'	{ $$ = new AstCell($3,*$1,V3Parse::s_instModule,$4,V3Parse::s_instParamp,$2); $$->pinStar(V3Parse::s_pinStar); }
	;

cellpinList:	{V3Parse::s_pinNum=1; V3Parse::s_pinStar=false; } cellpinlist2	{ $$ = $2; }
	;

cellpinlist2:	cellpinitemE				{ $$ = $1; }
	|	cellpinlist2 ',' cellpinitemE		{ $$ = $1->addNextNull($3)->castPin(); }
	;

cellpinitemE:	/* empty */				{ $$ = NULL; V3Parse::s_pinNum++; }
	|	'.' '*'					{ $$ = NULL; if (V3Parse::s_pinStar) $1->v3error("Duplicate .* in a cell"); V3Parse::s_pinStar=true; }
	|	'.' yaID				{ $$ = new AstPin($1,V3Parse::s_pinNum++,*$2,new AstVarRef($1,*$2,false)); $$->svImplicit(true);}
	|	'.' yaID '(' ')'			{ $$ = NULL; V3Parse::s_pinNum++; }
	|	'.' yaID '(' expr ')'			{ $$ = new AstPin($1,V3Parse::s_pinNum++,*$2,$4); }
	|	expr					{ $$ = new AstPin(CRELINE(),V3Parse::s_pinNum++,"",$1); }
	;

sensitivityE:	/* empty */				{ $$ = NULL; }
	|	'@' '(' senList ')'			{ $$ = new AstSenTree($1,$3); }
	|	'@' senitem				{ $$ = new AstSenTree($1,$2); }
	|	'@' '(' '*' ')'				{ $$ = NULL; $2->v3error("Use @*.  always @ (*) to be depreciated in Verilog 2005.\n"); }
	|	'@' '*'					{ $$ = NULL; }  /* Verilog 2001 */
	;

senList:	senitem					{ $$ = $1; }
	|	senList yOR senitem			{ $$ = $1;$1->addNext($3); }
	|	senList ',' senitem			{ $$ = $1;$1->addNext($3); }	/* Verilog 2001 */
	;

senitem:	senitemEdge				{ $$ = $1; }
//FIX need range ignoring to be stripped later, this was simple varXRef
	|	varRefDotBit				{ $$ = new AstSenItem(CRELINE(),AstEdgeType::ANYEDGE,$1); }
	;

senitemEdge:	yPOSEDGE varRefDotBit			{ $$ = new AstSenItem($1,AstEdgeType::POSEDGE,$2); }
	|	yNEGEDGE varRefDotBit			{ $$ = new AstSenItem($1,AstEdgeType::NEGEDGE,$2); }
	;

stmtBlock:	stmt					{ $$ = $1; }
	|	yBEGIN stmtList yEND			{ $$ = $2; }
	|	yBEGIN yEND				{ $$ = NULL; }
	|	beginNamed stmtList yEND		{ $$ = $1; $1->addStmtp($2); }
	|	beginNamed yEND				{ $$ = $1; }
	;

beginNamed:	yBEGIN ':' yaID varDeclList		{ $$ = new AstBegin($2,*$3,$4); }
	|	yBEGIN ':' yaID 			{ $$ = new AstBegin($2,*$3,NULL); }
	;

stmtList:	stmtBlock				{ $$ = $1; }
	|	stmtList stmtBlock			{ $$ = ($2==NULL)?($1):($1->addNext($2)); }
	;

stmt:		';'					{ $$ = NULL; }
	|	labeledStmt				{ $$ = $1; }
	|	yaID ':' labeledStmt			{ $$ = new AstBegin($2, *$1, $3); }  /*S05 block creation rule*/

	|	varRefDotBit yP_LTE delayE expr ';'	{ $$ = new AstAssignDly($2,$1,$4); }
	|	varRefDotBit '=' delayE expr ';'	{ $$ = new AstAssign($2,$1,$4); }
	|	varRefDotBit '=' yD_FOPEN '(' expr ',' expr ')' ';'	{ $$ = new AstFOpen($3,$1,$5,$7); }
	|	yASSIGN varRefDotBit '=' delayE expr ';'	{ $$ = new AstAssign($1,$2,$5); }
	|	'{' concIdList '}' yP_LTE delayE expr ';' { $$ = new AstAssignDly($4,$2,$6); }
	|	'{' concIdList '}' '=' delayE expr ';'  { $$ = new AstAssign($4,$2,$6); }
	|	yD_C '(' cStrList ')' ';'		{ $$ = (v3Global.opt.ignc() ? NULL : new AstUCStmt($1,$3)); }
	|	yD_FCLOSE '(' varRefDotBit ')' ';'	{ $$ = new AstFClose($1, $3); }
	|	yD_FINISH ';'				{ $$ = new AstFinish($1); }
	|	yD_STOP ';'				{ $$ = new AstStop($1); }
	|	yVL_COVER_OFF				{ $$ = new AstPragma($1,AstPragmaType::COVERAGE_BLOCK_OFF); }
	|	stateCaseForIf				{ $$ = $1; }
	|	taskRef ';' 				{ $$ = $1; }

	|	yD_DISPLAY  ';'							{ $$ = new AstDisplay($1,AstDisplayType::DISPLAY,"", NULL,NULL); }
	|	yD_DISPLAY  '(' yaSTRING commaEListE ')' ';'			{ $$ = new AstDisplay($1,AstDisplayType::DISPLAY,*$3,NULL,$4); }
	|	yD_WRITE    '(' yaSTRING commaEListE ')' ';'			{ $$ = new AstDisplay($1,AstDisplayType::WRITE,  *$3,NULL,$4); }
	|	yD_FDISPLAY '(' varRefDotBit ',' yaSTRING commaEListE ')' ';' 	{ $$ = new AstDisplay($1,AstDisplayType::DISPLAY,*$5,$3,$6); }
	|	yD_FWRITE   '(' varRefDotBit ',' yaSTRING commaEListE ')' ';'	{ $$ = new AstDisplay($1,AstDisplayType::WRITE,  *$5,$3,$6); }
	|	yD_INFO	    ';'							{ $$ = new AstDisplay($1,AstDisplayType::INFO,   "", NULL,NULL); }
	|	yD_INFO	    '(' yaSTRING commaEListE ')' ';'			{ $$ = new AstDisplay($1,AstDisplayType::INFO,   *$3,NULL,$4); }
	|	yD_WARNING  ';'							{ $$ = new AstDisplay($1,AstDisplayType::WARNING,"", NULL,NULL); }
	|	yD_WARNING  '(' yaSTRING commaEListE ')' ';'			{ $$ = new AstDisplay($1,AstDisplayType::WARNING,*$3,NULL,$4); }
	|	yD_ERROR    ';'							{ $$ = V3Parse::createDisplayError($1); }
	|	yD_ERROR    '(' yaSTRING commaEListE ')' ';'			{ $$ = new AstDisplay($1,AstDisplayType::ERROR,  *$3,NULL,$4);   $$->addNext(new AstStop($1)); }
	|	yD_FATAL    ';'							{ $$ = new AstDisplay($1,AstDisplayType::FATAL,  "", NULL,NULL); $$->addNext(new AstStop($1)); }
	|	yD_FATAL    '(' expr ')' ';'					{ $$ = new AstDisplay($1,AstDisplayType::FATAL,  "", NULL,NULL); $$->addNext(new AstStop($1)); }
	|	yD_FATAL    '(' expr ',' yaSTRING commaEListE ')' ';'		{ $$ = new AstDisplay($1,AstDisplayType::FATAL,  *$5,NULL,$6);   $$->addNext(new AstStop($1)); }

	|	yD_READMEMB '(' expr ',' varRefMem ')' ';'			{ $$ = new AstReadMem($1,false,$3,$5,NULL,NULL); }
	|	yD_READMEMB '(' expr ',' varRefMem ',' expr ')' ';'		{ $$ = new AstReadMem($1,false,$3,$5,$7,NULL); }
	|	yD_READMEMB '(' expr ',' varRefMem ',' expr ',' expr ')' ';'	{ $$ = new AstReadMem($1,false,$3,$5,$7,$9); }
	|	yD_READMEMH '(' expr ',' varRefMem ')' ';'			{ $$ = new AstReadMem($1,true, $3,$5,NULL,NULL); }
	|	yD_READMEMH '(' expr ',' varRefMem ',' expr ')' ';'		{ $$ = new AstReadMem($1,true, $3,$5,$7,NULL); }
	|	yD_READMEMH '(' expr ',' varRefMem ',' expr ',' expr ')' ';'	{ $$ = new AstReadMem($1,true, $3,$5,$7,$9); }

	;

labeledStmt:	assertStmt				{ $$ = $1; }
	;

stateCaseForIf: caseStmt caseAttrE caseList yENDCASE	{ $$ = $1; $1->addItemsp($3); }
	|	yIF expr stmtBlock	%prec prLOWER_THAN_ELSE	{ $$ = new AstIf($1,$2,$3,NULL); }
	|	yIF expr stmtBlock yELSE stmtBlock	{ $$ = new AstIf($1,$2,$3,$5); }
	|	yFOR '(' varRefBase '=' expr ';' expr ';' varRefBase '=' expr ')' stmtBlock
							{ $$ = new AstFor($1, new AstAssign($4,$3,$5)
									  ,$7, new AstAssign($10,$9,$11)
									  ,$13);}
	|	yWHILE '(' expr ')' stmtBlock		{ $$ = new AstWhile($1,$3,$5);}
	|	yDO stmtBlock yWHILE '(' expr ')'	{ $$ = $2->cloneTree(true); $$->addNext(new AstWhile($1,$5,$2));}
	;

assertStmt:	yASSERT '(' expr ')' stmtBlock %prec prLOWER_THAN_ELSE	{ $$ = new AstVAssert($1,$3,$5, V3Parse::createDisplayError($1)); }
	|	yASSERT '(' expr ')'           yELSE stmtBlock		{ $$ = new AstVAssert($1,$3,NULL,$6); }
	|	yASSERT '(' expr ')' stmtBlock yELSE stmtBlock		{ $$ = new AstVAssert($1,$3,$5,$7);   }
	;

caseStmt: 	yCASE  '(' expr ')' 			{ $$ = V3Parse::s_caseAttrp = new AstCase($1,false,$3,NULL); }
	|	yCASEX '(' expr ')' 			{ $$ = V3Parse::s_caseAttrp = new AstCase($1,true,$3,NULL); $1->v3warn(CASEX,"Suggest casez (with ?'s) in place of casex (with X's)\n"); }
	|	yCASEZ '(' expr ')'	 		{ $$ = V3Parse::s_caseAttrp = new AstCase($1,true,$3,NULL); }
	;

caseAttrE: 	/*empty*/				{ }
	|	caseAttrE yVL_FULL_CASE			{ V3Parse::s_caseAttrp->fullPragma(true); }
	|	caseAttrE yVL_PARALLEL_CASE		{ V3Parse::s_caseAttrp->parallelPragma(true); }
	;

caseList:	casecondList ':' stmtBlock		{ $$ = new AstCaseItem($2,$1,$3); }
	|	yDEFAULT ':' stmtBlock			{ $$ = new AstCaseItem($2,NULL,$3); }
	|	yDEFAULT stmtBlock			{ $$ = new AstCaseItem($1,NULL,$2); }
	|	caseList casecondList ':' stmtBlock	{ $$ = $1;$1->addNext(new AstCaseItem($3,$2,$4)); }
	|       caseList yDEFAULT stmtBlock		{ $$ = $1;$1->addNext(new AstCaseItem($2,NULL,$3)); }
	|	caseList yDEFAULT ':' stmtBlock		{ $$ = $1;$1->addNext(new AstCaseItem($3,NULL,$4)); }
	;

casecondList:	expr 					{ $$ = $1; }
	|	casecondList ',' expr			{ $$ = $1;$1->addNext($3); }
	;

taskDecl: 	yTASK yaID ';'             stmtBlock yENDTASK	{ $$ = new AstTask ($1,*$2,$4);}
	| 	yTASK yaID ';' funcVarList stmtBlock yENDTASK	{ $$ = new AstTask ($1,*$2,$4); $4->addNextNull($5); }
	;

funcDecl: 	yFUNCTION         funcRange yaID				';' funcBody yENDFUNCTION { $$ = new AstFunc ($1,*$3,$5,$2); }
	|	yFUNCTION ySIGNED funcRange yaID				';' funcBody yENDFUNCTION { $$ = new AstFunc ($1,*$4,$6,$3); $$->isSigned(true); }
	| 	yFUNCTION         funcRange yaID yVL_ISOLATE_ASSIGNMENTS ';' funcBody yENDFUNCTION { $$ = new AstFunc ($1,*$3,$6,$2); $$->attrIsolateAssign(true);}
	|	yFUNCTION ySIGNED funcRange yaID yVL_ISOLATE_ASSIGNMENTS ';' funcBody yENDFUNCTION { $$ = new AstFunc ($1,*$4,$7,$3); $$->attrIsolateAssign(true); $$->isSigned(true); }
	;

funcBody:	funcVarList stmtBlock			{ $$ = $1;$1->addNextNull($2); }
	;

funcRange:	'[' constExpr ':' constExpr ']'		{ $$ = new AstRange($1,$2,$4); }
	|						{ $$ = NULL; }
	;

funcVarList:	funcVar					{ $$ = $1; }
	|	funcVarList funcVar			{ $$ = $1;$1->addNext($2); }
	;

funcVar: 	ioDecl					{ $$ = $1; }
	|	varDecl 				{ $$ = $1; }
	|	yVL_PUBLIC				{ $$ = new AstPragma($1,AstPragmaType::PUBLIC_TASK); }
	|	yVL_NO_INLINE_TASK			{ $$ = new AstPragma($1,AstPragmaType::NO_INLINE_TASK); }
	;

constExpr:	expr					{ $$ = $1; }
	;

exprNoStr:	expr yP_OROR expr			{ $$ = new AstLogOr	($2,$1,$3); }
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
	|	expr yP_LOGIF expr			{ $$ = new AstLogIf	($2,$1,$3); }
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
	|	yD_COUNTONES '(' expr ')'		{ $$ = new AstCountOnes($1,$3); }
	|	yD_ISUNKNOWN '(' expr ')'		{ $$ = new AstIsUnknown($1,$3); }
	|	yD_ONEHOT '(' expr ')'			{ $$ = new AstOneHot($1,$3); }
	|	yD_ONEHOT0 '(' expr ')'			{ $$ = new AstOneHot0($1,$3); }
	|	yD_SIGNED '(' expr ')'			{ $$ = new AstSigned($1,$3); }
	|	yD_TIME					{ $$ = new AstTime($1); }
	|	yD_UNSIGNED '(' expr ')'		{ $$ = new AstUnsigned($1,$3); }

	|	funcRef					{ $$ = $1; }

	|	yaINTNUM				{ $$ = new AstConst(CRELINE(),*$1); }

	|	varRefDotBit	  			{ $$ = $1; }
	;

// Generic expressions
expr:		exprNoStr				{ $$ = $1; }
	|	strAsInt				{ $$ = $1; }
	;

// Psl excludes {}'s by lexer converting to different token
exprPsl:	exprNoStr				{ $$ = $1; }
	|	strAsInt				{ $$ = $1; }
	;

// PLI calls exclude "" as integers, they're strings
// For $c("foo","bar") we want "bar" as a string, not a Verilog integer.
exprStrText:	exprNoStr				{ $$ = $1; }
	|	strAsText				{ $$ = $1; }
	;

cStrList:	exprStrText				{ $$ = $1; }
	|	exprStrText ',' cStrList		{ $$ = $1;$1->addNext($3); }
	;

cateList:	expr					{ $$ = $1; }
	|	cateList ',' expr			{ $$ = new AstConcat($2,$1,$3); }
	;

eList:		expr					{ $$ = $1; }
	|	eList ',' expr				{ $$ = $1;$1->addNext($3); }
	;

commaEListE:	/* empty */				{ $$ = NULL; }
	|	',' eList				{ $$ = $2; }
	;

// Gate declarations
gateDecl: 	yBUF  gateBufList ';'			{ $$ = $2; }
	|	yNOT  gateNotList ';'			{ $$ = $2; }
	|	yAND  gateAndList ';'			{ $$ = $2; }
	|	yNAND gateNandList ';'			{ $$ = $2; }
	|	yOR   gateOrList ';'			{ $$ = $2; }
	|	yNOR  gateNorList ';'			{ $$ = $2; }
	|	yXOR  gateXorList ';'			{ $$ = $2; }
	|	yXNOR gateXnorList ';'			{ $$ = $2; }
	;

gateBufList:	gateBuf 				{ $$ = $1; }
	|	gateBuf ',' gateBuf			{ $$ = $1->addNext($3); }
	;
gateNotList:	gateNot 				{ $$ = $1; }
	|	gateNot ',' gateNot			{ $$ = $1->addNext($3); }
	;
gateAndList:	gateAnd 				{ $$ = $1; }
	|	gateAnd ',' gateAnd			{ $$ = $1->addNext($3); }
	;
gateNandList:	gateNand 				{ $$ = $1; }
	|	gateNand ',' gateNand			{ $$ = $1->addNext($3); }
	;
gateOrList:	gateOr 					{ $$ = $1; }
	|	gateOr ',' gateOr			{ $$ = $1->addNext($3); }
	;
gateNorList:	gateNor 				{ $$ = $1; }
	|	gateNor ',' gateNor			{ $$ = $1->addNext($3); }
	;
gateXorList:	gateXor 				{ $$ = $1; }
	|	gateXor ',' gateXor			{ $$ = $1->addNext($3); }
	;
gateXnorList:	gateXnor 				{ $$ = $1; }
	|	gateXnor ',' gateXnor			{ $$ = $1->addNext($3); }
	;

gateIdE:	/*empty*/				{}
	|	yaID					{}
	;

gateBuf: 	gateIdE '(' varRefDotBit ',' expr ')'		{ $$ = new AstAssignW ($2,$3,$5); $$->allowImplicit(true); }
	;
gateNot:	gateIdE '(' varRefDotBit ',' expr ')'		{ $$ = new AstAssignW ($2,$3,new AstNot($4,$5)); $$->allowImplicit(true); }
	;
gateAnd:	gateIdE '(' varRefDotBit ',' gateAndPinList ')'	{ $$ = new AstAssignW ($2,$3,$5); $$->allowImplicit(true); }
	;
gateNand:	gateIdE '(' varRefDotBit ',' gateAndPinList ')'	{ $$ = new AstAssignW ($2,$3,new AstNot($4,$5)); $$->allowImplicit(true); }
	;
gateOr:		gateIdE '(' varRefDotBit ',' gateOrPinList ')'	{ $$ = new AstAssignW ($2,$3,$5); $$->allowImplicit(true); }
	;
gateNor:	gateIdE '(' varRefDotBit ',' gateOrPinList ')'	{ $$ = new AstAssignW ($2,$3,new AstNot($4,$5)); $$->allowImplicit(true); }
	;
gateXor:	gateIdE '(' varRefDotBit ',' gateXorPinList ')'	{ $$ = new AstAssignW ($2,$3,$5); $$->allowImplicit(true); }
	;
gateXnor:	gateIdE '(' varRefDotBit ',' gateXorPinList ')'	{ $$ = new AstAssignW ($2,$3,new AstNot($4,$5)); $$->allowImplicit(true); }
	;

gateAndPinList:	expr 					{ $$ = $1; }
	|	gateAndPinList ',' expr			{ $$ = new AstAnd($2,$1,$3); }
	;
gateOrPinList:	expr 					{ $$ = $1; }
	|	gateOrPinList ',' expr			{ $$ = new AstOr($2,$1,$3); }
	;
gateXorPinList:	expr 					{ $$ = $1; }
	|	gateXorPinList ',' expr			{ $$ = new AstXor($2,$1,$3); }
	;

//************************************************
// Specify
specifyJunkList:	specifyJunk 			/* ignored */
	|	specifyJunkList specifyJunk		/* ignored */
	;

specifyJunk:	dterm 	{} /* ignored */
	|	';' {}
	|	'!' {}
	|	'&' {}
	|	'(' {}
	|	')' {}
	|	'*' {} | '/' {} | '%' {} | yP_POW {}
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

	|	yIF {}
	|	yNEGEDGE {}
	|	yPOSEDGE {}

	|	yaSTRING {}
	|	yaTIMINGSPEC {}

	|	yP_ANDAND {} | yP_GTE {} | yP_LTE {}
	|	yP_EQUAL {} | yP_NOTEQUAL {}
	|	yP_XNOR {} | yP_NOR {} | yP_NAND {}
	|	yP_OROR {}
	|	yP_SLEFT {} | yP_SRIGHT {} | yP_SSRIGHT {}
	|	yP_PLUSCOLON {} | yP_MINUSCOLON {}

	|	yP_LOGIF {}
	|	yP_LOGIFF {}
	|	yPSL_BRA {}
	|	yPSL_KET {}
	|	yP_OR_MINUS_GT {}
	|	yP_OR_EQ_GT {}
	;

//************************************************
// IDs

// Single component of dotted path, maybe [#].
// Due to lookahead constraints, we can't know if [:] or [+:] are valid (last dotted part),
// we'll assume so and cleanup later.
idArrayed:	yaID						{ $$ = new AstText(CRELINE(),*$1); }
	|	idArrayed '[' expr ']'				{ $$ = new AstSelBit($2,$1,$3); }  // Or AstArraySel, don't know yet.
	|	idArrayed '[' constExpr ':' constExpr ']'	{ $$ = new AstSelExtract($2,$1,$3,$5); }
	|	idArrayed '[' expr yP_PLUSCOLON constExpr ']'	{ $$ = new AstSelPlus($2,$1,$3,$5); }
	|	idArrayed '[' expr yP_MINUSCOLON constExpr ']'	{ $$ = new AstSelMinus($2,$1,$3,$5); }
	;

idDotted:	idArrayed 				{ $$ = $1; }
	|	idDotted '.' idArrayed	 		{ $$ = new AstDot($2,$1,$3); }
	;

// VarRef without any dots or vectorizaion
varRefBase:	yaID					{ $$ = new AstVarRef(CRELINE(),*$1,false);}
	;

// VarRef to a Memory
varRefMem:	idDotted				{ $$ = new AstParseRef($1->fileline(), AstParseRefExp::VAR_MEM, $1); }
	;

// VarRef to dotted, and/or arrayed, and/or bit-ranged variable
varRefDotBit:	idDotted				{ $$ = new AstParseRef($1->fileline(), AstParseRefExp::VAR_ANY, $1); }
	;

taskRef:	idDotted		 		{ $$ = new AstTaskRef(CRELINE(),new AstParseRef($1->fileline(), AstParseRefExp::TASK, $1),NULL);}
	|	idDotted '(' eList ')'			{ $$ = new AstTaskRef(CRELINE(),new AstParseRef($1->fileline(), AstParseRefExp::TASK, $1),$3);}
	;

funcRef:	idDotted '(' eList ')'			{ $$ = new AstFuncRef($2,new AstParseRef($1->fileline(), AstParseRefExp::FUNC, $1), $3); }
	;

strAsInt:	yaSTRING				{ $$ = new AstConst(CRELINE(),V3Number(V3Number::VerilogString(),CRELINE(),V3Parse::deQuote(CRELINE(),*$1)));}
	;

strAsText:	yaSTRING				{ $$ = V3Parse::createTextQuoted(CRELINE(),*$1);}
	;

concIdList:	varRefDotBit				{ $$ = $1; }
	|	concIdList ',' varRefDotBit		{ $$ = new AstConcat($2,$1,$3); }
	;

//************************************************
// PSL Statements

pslStmt:	yPSL pslDir  stateExitPsl		{ $$ = $2; }
	|	yPSL pslDecl stateExitPsl 		{ $$ = $2; }
	;

pslDir:		yaID ':' pslDirOne			{ $$ = $3; }  // ADD: Create label on $1
	|	pslDirOne		       		{ $$ = $1; }
	;

//ADD:	|	yRESTRICT pslSequence ';'		{ $$ = PSLUNSUP(new AstPslRestrict($1,$2)); }
pslDirOne:	yPSL_ASSERT pslProp ';'			{ $$ = new AstPslAssert($1,$2); }
	|	yPSL_ASSERT pslProp yREPORT yaSTRING ';'	{ $$ = new AstPslAssert($1,$2,*$4); }
	|	yCOVER  pslProp ';'			{ $$ = new AstPslCover($1,$2); }
	|	yCOVER  pslProp yREPORT yaSTRING ';'	{ $$ = new AstPslCover($1,$2,*$4); }
	;

pslDecl:	yDEFAULT yCLOCK '=' senitemEdge ';'		{ $$ = new AstPslDefClock($3, $4); }
	|	yDEFAULT yCLOCK '=' '(' senitemEdge ')' ';'	{ $$ = new AstPslDefClock($3, $5); }
	;

//************************************************
// PSL Properties, Sequences and SEREs
// Don't use '{' or '}'; in PSL they're yPSL_BRA and yPSL_KET to avoid expr concatenates

pslProp:	pslSequence				{ $$ = $1; }
	|	pslSequence '@' %prec prPSLCLK '(' senitemEdge ')' { $$ = new AstPslClocked($2, $4, $1); }  // or pslSequence @ ...?
	;

//ADD:	|	pslCallSeq				{ $$ = PSLUNSUP($1); }
//ADD:	|	pslRepeat				{ $$ = PSLUNSUP($1); }
pslSequence:	yPSL_BRA pslSere yPSL_KET		{ $$ = $2; }
	;

//ADD:	|	pslSere ';' pslSere	%prec prPSLCONC	{ $$ = PSLUNSUP(new AstPslSeqConcat($2, $1, $3)); }
//ADD:	|	pslSere ':' pslSere	%prec prPSLFUS	{ $$ = PSLUNSUP(new AstPslSeqFusion($2, $1, $3)); }
//ADD:	|	pslSereCpnd				{ $$ = $1; }
pslSere:	pslExpr					{ $$ = $1; }
	|	pslSequence				{ $$ = $1; }  // Sequence containing sequence
	;

// Undocumented PSL rule is that {} is always a SERE; concatenation is not allowed.
// This can be bypassed with the _(...) embedding of any arbitrary expression.
//ADD:	|	pslFunc					{ $$ = UNSUP($1); }
//ADD:	|	pslExpr yUNION pslExpr			{ $$ = UNSUP(new AstPslUnion($2, $1, $3)); }
pslExpr:	exprPsl					{ $$ = new AstPslBool($1->fileline(), $1); }
	|	yTRUE					{ $$ = new AstPslBool($1, new AstConst($1, V3Number($1,1,1))); }
	;

//**********************************************************************
%%

AstNode* V3Parse::createSupplyExpr(FileLine* fileline, string name, int value) {
    FileLine* newfl = new FileLine (fileline);
    newfl->warnOff(V3ErrorCode::WIDTH, true);
    AstNode* nodep = new AstConst(newfl, V3Number(fileline));
    // Adding a NOT is less work then figuring out how wide to make it
    if (value) nodep = new AstNot(newfl, nodep);
    nodep = new AstAssignW(newfl, new AstVarRef(fileline, name, true),
			   nodep);
    return nodep;
}

AstVar* V3Parse::createVariable(FileLine* fileline, string name, AstRange* arrayp) {
    AstVarType type = V3Parse::s_varIO;
    AstRange* rangep = V3Parse::s_varRangep;
    if (type == AstVarType::UNKNOWN) type = V3Parse::s_varDecl;
    if (type == AstVarType::UNKNOWN) fileline->v3fatalSrc("Unknown signal type declared");
    // Linting, because we allow parsing of a superset of the language
    if (type == AstVarType::INTEGER || type == AstVarType::GENVAR) {
	if (rangep) fileline->v3error("Integers may not be ranged: "<<name);
	rangep = new AstRange(fileline, 31, 0);  // Integer == REG[31:0]
    }
    if (type == AstVarType::GENVAR) {
	if (arrayp) fileline->v3error("Genvars may not be arrayed: "<<name);
    }
    AstVar* nodep = new AstVar(fileline, type, name,
			       rangep->cloneTree(false),
			       arrayp);
    nodep->isSigned(V3Parse::s_varSigned);
    if (type == AstVarType::INTEGER) nodep->isSigned(true);
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
		    fileline->v3error("Non-three digit octal escape code (\\###)");
		    octal_digits = 0;
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
