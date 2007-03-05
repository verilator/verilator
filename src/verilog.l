/* $Id$ -*- C++ -*- */
/**************************************************************************
 * DESCRIPTION: Verilator: Flex input file
 *
 * Code available from: http://www.veripool.com/verilator
 *
 **************************************************************************
 *
 * Copyright 2003-2007 by Wilson Snyder.  This program is free software; you can
 * redistribute it and/or modify it under the terms of either the GNU
 * General Public License or the Perl Artistic License.
 *
 * Verilator is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 **************************************************************************/

%option interactive c++ stack noyywrap
%{
/* %option nodefault */
/* $Id$ */

#include <stdio.h>
#include <string.h>
#include "V3Read.h"
#include "V3Number.h"
#include "y.tab.h"

extern void yyerror(char*);
extern void yyerrorf(const char* format, ...);

#define STATE_VERILOG_RECENT  S05		// State name for most recent Verilog Version

//======================================================================

#define NEXTLINE() {V3Read::incLineno();}
#define CRELINE() (V3Read::copyOrSameFileLine())

void V3Read::ppline (const char* textp) {
    // Handle `line directive
    fileline()->lineDirective(textp);
}

void V3Read::verilatorCmtLint(const char* textp, bool warnOff) {
    const char* sp = textp;
    while (*sp && !isspace(*sp)) sp++;  while (*sp && isspace(*sp)) sp++;
    while (*sp && !isspace(*sp)) sp++;  while (*sp && isspace(*sp)) sp++;
    string msg = sp;
    string::size_type pos;
    if ((pos=msg.find("*")) != string::npos) { msg.erase(pos); }
    if (!(V3Read::fileline()->warnOff(msg, warnOff))) {
	yyerrorf("Unknown verilator lint message code: %s, in %s",msg.c_str(), textp);
    }
}
void V3Read::verilatorCmtBad(const char* textp) {
    yyerrorf("Unknown verilator comment: %s",textp);
}

// See V3Read.cpp
//void V3Read::stateExitPsl() { BEGIN VLG; }
//void V3Read::statePushVlg() { yy_push_state(VLG); }
//void V3Read::statePop() { yy_pop_state(); }

//======================================================================

void yyerror(char* errmsg) {
    yyerrorf("%s",errmsg);
}

void yyerrorf(const char* format, ...) {
    char msg[1024];

    va_list ap;
    va_start(ap,format);
    vsprintf(msg,format,ap);
    va_end(ap);

    V3Read::fileline()->v3error(msg);
}

//======================================================================
%}

%e 2000
%p 5000
%n 2500
%k 1000
%a 15000
%o 25000

%s V95 V01 V05 S05
%s PSL STRING
%s SYSCHDR SYSCINT SYSCIMP SYSCIMPH SYSCCTOR SYSCDTOR
%s IGNORE

ws	[ \t\f\r]+
	/* identifier */
id	[a-zA-Z_][a-zA-Z0-9_$]*
	/* escaped identifier */
escid	\\[^ \t\f\r\n]+

%%

<INITIAL>.|\n 		{BEGIN STATE_VERILOG_RECENT; yyless(0); }

<V95,V01,V05,S05,PSL>{
  {ws}			;			/* ignore white-space */
  \n			{NEXTLINE();}		/* Count line numbers */
  "always"		{yylval.fileline = CRELINE(); return yALWAYS;}
  "and"			{yylval.fileline = CRELINE(); return yAND;}
  "assign"		{yylval.fileline = CRELINE(); return yASSIGN;}
  "begin"		{yylval.fileline = CRELINE(); return yBBEGIN;}
  "buf"			{yylval.fileline = CRELINE(); return yBUF;}
  "case"		{yylval.fileline = CRELINE(); return yCASE;}
  "casex"		{yylval.fileline = CRELINE(); return yCASEX;}
  "casez"		{yylval.fileline = CRELINE(); return yCASEZ;}
  "default"		{yylval.fileline = CRELINE(); return yDEFAULT;}
  "defparam"		{yylval.fileline = CRELINE(); return yDEFPARAM;}
  "else"		{yylval.fileline = CRELINE(); return yELSE;}
  "end"			{yylval.fileline = CRELINE(); return yBEND;}
  "endcase"		{yylval.fileline = CRELINE(); return yENDCASE;}
  "endfunction"		{yylval.fileline = CRELINE(); return yENDFUNCTION;}
  "endmodule"		{yylval.fileline = CRELINE(); return yENDMODULE;}
  "endspecify"		{yylval.fileline = CRELINE(); return yENDSPECIFY;}
  "endtask"		{yylval.fileline = CRELINE(); return yENDTASK;}
  "for"			{yylval.fileline = CRELINE(); return yFOR;}
  "function"		{yylval.fileline = CRELINE(); return yFUNCTION;}
  "if"			{yylval.fileline = CRELINE(); return yIF;}
  "initial"		{yylval.fileline = CRELINE(); return yINITIAL;}
  "inout"		{yylval.fileline = CRELINE(); return yINOUT;}
  "input"		{yylval.fileline = CRELINE(); return yINPUT;}
  "integer"		{yylval.fileline = CRELINE(); return yINTEGER;}
  "macromodule"		{yylval.fileline = CRELINE(); return yMODULE;}
  "module"		{yylval.fileline = CRELINE(); return yMODULE;}
  "nand"		{yylval.fileline = CRELINE(); return yNAND;}
  "negedge"		{yylval.fileline = CRELINE(); return yNEGEDGE;}
  "nor"			{yylval.fileline = CRELINE(); return yNOR;}
  "not"			{yylval.fileline = CRELINE(); return yNOT;}
  "or"			{yylval.fileline = CRELINE(); return yOR;}
  "output"		{yylval.fileline = CRELINE(); return yOUTPUT;}
  "parameter"		{yylval.fileline = CRELINE(); return yPARAM;}
  "posedge"		{yylval.fileline = CRELINE(); return yPOSEDGE;}
  "reg"			{yylval.fileline = CRELINE(); return yREG;}
  "scalared"		{yylval.fileline = CRELINE(); return ySCALARED;}
  "specify"		{yylval.fileline = CRELINE(); return ySPECIFY;}
  "specparam"		{yylval.fileline = CRELINE(); return yTIMINGSPEC;}
  "supply0"		{yylval.fileline = CRELINE(); return ySUPPLY0;}
  "supply1"		{yylval.fileline = CRELINE(); return ySUPPLY1;}
  "task"		{yylval.fileline = CRELINE(); return yTASK;}
  "tri"			{yylval.fileline = CRELINE(); return yTRI;}
  "vectored"		{yylval.fileline = CRELINE(); return yVECTORED;}
  "wire"		{yylval.fileline = CRELINE(); return yWIRE;}
  "xnor"		{yylval.fileline = CRELINE(); return yXNOR;}
  "xor"			{yylval.fileline = CRELINE(); return yXOR;}
}

<V01,V05,S05,PSL>{
  "endgenerate"		{yylval.fileline = CRELINE(); return yENDGENERATE;}
  "generate"		{yylval.fileline = CRELINE(); return yGENERATE;}
  "genvar"		{yylval.fileline = CRELINE(); return yGENVAR;}
  "localparam"		{yylval.fileline = CRELINE(); return yLOCALPARAM;}
  "signed"		{yylval.fileline = CRELINE(); return ySIGNED;}
}

<V05,S05,PSL>{
  "uwire"		{yylval.fileline = CRELINE(); return yWIRE;}
}

<S05,PSL>{
  "always_comb"		{yylval.fileline = CRELINE(); return yALWAYS;}
  "always_ff"		{yylval.fileline = CRELINE(); return yALWAYS;}
  "always_latch"	{yylval.fileline = CRELINE(); return yALWAYS;}
  "final"		{yylval.fileline = CRELINE(); return yFINAL;}
}

<V95,V01,V05,S05,PSL>{
    /* Extensions to Verilog set, some specified by PSL */
  "$bits"		{yylval.fileline = CRELINE(); return yD_BITS;}		/*Verilator only*/
  "$c"[0-9]*		{yylval.fileline = CRELINE(); return yD_C;}		/*Verilator only*/
  "$countones"		{yylval.fileline = CRELINE(); return yD_COUNTONES;}	/*Verilator only*/
  "$isunknown"		{yylval.fileline = CRELINE(); return yD_ISUNKNOWN;}	/*Verilator only*/
  "$onehot"		{yylval.fileline = CRELINE(); return yD_ONEHOT;}	/*Verilator only*/
  "$onehot0"		{yylval.fileline = CRELINE(); return yD_ONEHOT0;}	/*Verilator only*/
    /* Standard ones */
  "$display"		{yylval.fileline = CRELINE(); return yD_DISPLAY;}
  "$fclose"		{yylval.fileline = CRELINE(); return yD_FCLOSE;}
  "$fdisplay"		{yylval.fileline = CRELINE(); return yD_FDISPLAY;}
  "$finish"		{yylval.fileline = CRELINE(); return yD_FINISH;}
  "$fopen"		{yylval.fileline = CRELINE(); return yD_FOPEN;}
  "$fullskew"		{yylval.fileline = CRELINE(); return yTIMINGSPEC;}
  "$fwrite"		{yylval.fileline = CRELINE(); return yD_FWRITE;}
  "$hold"		{yylval.fileline = CRELINE(); return yTIMINGSPEC;}
  "$nochange"		{yylval.fileline = CRELINE(); return yTIMINGSPEC;}
  "$period"		{yylval.fileline = CRELINE(); return yTIMINGSPEC;}
  "$readmemb"		{yylval.fileline = CRELINE(); return yD_READMEMB;}
  "$readmemh"		{yylval.fileline = CRELINE(); return yD_READMEMH;}
  "$realtime"		{yylval.fileline = CRELINE(); return yD_TIME;}
  "$recovery"		{yylval.fileline = CRELINE(); return yTIMINGSPEC;}
  "$recrem"		{yylval.fileline = CRELINE(); return yTIMINGSPEC;}
  "$removal"		{yylval.fileline = CRELINE(); return yTIMINGSPEC;}
  "$setup"		{yylval.fileline = CRELINE(); return yTIMINGSPEC;}
  "$setuphold"		{yylval.fileline = CRELINE(); return yTIMINGSPEC;}
  "$skew"		{yylval.fileline = CRELINE(); return yTIMINGSPEC;}
  "$stop"		{yylval.fileline = CRELINE(); return yD_STOP;}
  "$time"		{yylval.fileline = CRELINE(); return yD_TIME;}
  "$timeskew"		{yylval.fileline = CRELINE(); return yTIMINGSPEC;}
  "$width"		{yylval.fileline = CRELINE(); return yTIMINGSPEC;}
  "$write"		{yylval.fileline = CRELINE(); return yD_WRITE;}
    /* Special errors */
  "$displayb"		{yyerrorf("Unsupported: Use $display with %%b format instead: %s",yytext);}
  "$displayh"		{yyerrorf("Unsupported: Use $display with %%x format instead: %s",yytext);}
  "$displayo"		{yyerrorf("Unsupported: Use $display with %%o format instead: %s",yytext);}
  "$fdisplayb"		{yyerrorf("Unsupported: Use $fdisplay with %%b format instead: %s",yytext);}
  "$fdisplayh"		{yyerrorf("Unsupported: Use $fdisplay with %%x format instead: %s",yytext);}
  "$fdisplayo"		{yyerrorf("Unsupported: Use $fdisplay with %%o format instead: %s",yytext);}
  "$fwriteb"		{yyerrorf("Unsupported: Use $fwrite with %%b format instead: %s",yytext);}
  "$fwriteh"		{yyerrorf("Unsupported: Use $fwrite with %%x format instead: %s",yytext);}
  "$fwriteo"		{yyerrorf("Unsupported: Use $fwrite with %%o format instead: %s",yytext);}
  "$writeb"		{yyerrorf("Unsupported: Use $write with %%b format instead: %s",yytext);}
  "$writeh"		{yyerrorf("Unsupported: Use $write with %%x format instead: %s",yytext);}
  "$writeo"		{yyerrorf("Unsupported: Use $write with %%o format instead: %s",yytext);}
}

<V01,V05,S05,PSL>{
  "$signed"		{yylval.fileline = CRELINE(); return yD_SIGNED;}
  "$unsigned"		{yylval.fileline = CRELINE(); return yD_UNSIGNED;}
}

<V95,V01,V05,S05,PSL>{
  "$"[a-zA-Z_$]+	{yyerrorf("Unsupported or unknown PLI call: %s",yytext);}
}

 /*Entry into PSL; mode change */
<V95,V01,V05,S05>{
  "psl"			{ yy_push_state(PSL); yylval.fileline = CRELINE(); return yPSL; }
}

<PSL>{
  "psl"			{ ; }	// 'psl' may occur in middle of statement, so easier just to suppress

  "assert"		{yylval.fileline = CRELINE(); return yASSERT;}
  "assume"		{yylval.fileline = CRELINE(); return yASSERT;} //==assert
  "before_!"		{yyerrorf("Illegal syntax, use before!_ instead of %s",yytext);}
  "clock"		{yylval.fileline = CRELINE(); return yCLOCK;}
  "countones"		{yylval.fileline = CRELINE(); return yD_COUNTONES;}
  "cover"		{yylval.fileline = CRELINE(); return yCOVER;}
  "isunknown"		{yylval.fileline = CRELINE(); return yD_ISUNKNOWN;}
  "onehot"		{yylval.fileline = CRELINE(); return yD_ONEHOT; }
  "onehot0"		{yylval.fileline = CRELINE(); return yD_ONEHOT0; }
  "until_!"		{yyerrorf("Illegal syntax, use until!_ instead of %s",yytext);}
  "report"		{yylval.fileline = CRELINE(); return yREPORT; }
  "true"		{yylval.fileline = CRELINE(); return yTRUE; }
}

 /*Verilog Reserved*/
<V95,V01,V05,S05,PSL>{
  "bufif0"		{yyerrorf("Unsupported: Verilog 1995 reserved word not implemented: %s",yytext);}
  "bufif1"		{yyerrorf("Unsupported: Verilog 1995 reserved word not implemented: %s",yytext);}
  "cmos"		{yyerrorf("Unsupported: Verilog 1995 reserved word not implemented: %s",yytext);}
  "deassign"		{yyerrorf("Unsupported: Verilog 1995 reserved word not implemented: %s",yytext);}
  "disable"		{yyerrorf("Unsupported: Verilog 1995 reserved word not implemented: %s",yytext);}
  "edge"		{yyerrorf("Unsupported: Verilog 1995 reserved word not implemented: %s",yytext);}
  "endprimitive"	{yyerrorf("Unsupported: Verilog 1995 reserved word not implemented: %s",yytext);}
  "endtable"		{yyerrorf("Unsupported: Verilog 1995 reserved word not implemented: %s",yytext);}
  "event"		{yyerrorf("Unsupported: Verilog 1995 reserved word not implemented: %s",yytext);}
  "force"		{yyerrorf("Unsupported: Verilog 1995 reserved word not implemented: %s",yytext);}
  "forever"		{yyerrorf("Unsupported: Verilog 1995 reserved word not implemented: %s",yytext);}
  "fork"		{yyerrorf("Unsupported: Verilog 1995 reserved word not implemented: %s",yytext);}
  "highz0"		{yyerrorf("Unsupported: Verilog 1995 reserved word not implemented: %s",yytext);}
  "highz1"		{yyerrorf("Unsupported: Verilog 1995 reserved word not implemented: %s",yytext);}
  "join"		{yyerrorf("Unsupported: Verilog 1995 reserved word not implemented: %s",yytext);}
  "large"		{yyerrorf("Unsupported: Verilog 1995 reserved word not implemented: %s",yytext);}
  "medium"		{yyerrorf("Unsupported: Verilog 1995 reserved word not implemented: %s",yytext);}
  "nmos"		{yyerrorf("Unsupported: Verilog 1995 reserved word not implemented: %s",yytext);}
  "notif0"		{yyerrorf("Unsupported: Verilog 1995 reserved word not implemented: %s",yytext);}
  "notif1"		{yyerrorf("Unsupported: Verilog 1995 reserved word not implemented: %s",yytext);}
  "pmos"		{yyerrorf("Unsupported: Verilog 1995 reserved word not implemented: %s",yytext);}
  "primitive"		{yyerrorf("Unsupported: Verilog 1995 reserved word not implemented: %s",yytext);}
  "pulldown"		{yyerrorf("Unsupported: Verilog 1995 reserved word not implemented: %s",yytext);}
  "pullup"		{yyerrorf("Unsupported: Verilog 1995 reserved word not implemented: %s",yytext);}
  "pull0"		{yyerrorf("Unsupported: Verilog 1995 reserved word not implemented: %s",yytext);}
  "pull1"		{yyerrorf("Unsupported: Verilog 1995 reserved word not implemented: %s",yytext);}
  "rcmos"		{yyerrorf("Unsupported: Verilog 1995 reserved word not implemented: %s",yytext);}
  "real"		{yyerrorf("Unsupported: Verilog 1995 reserved word not implemented: %s",yytext);}
  "realtime"		{yyerrorf("Unsupported: Verilog 1995 reserved word not implemented: %s",yytext);}
  "release"		{yyerrorf("Unsupported: Verilog 1995 reserved word not implemented: %s",yytext);}
  "repeat"		{yyerrorf("Unsupported: Verilog 1995 reserved word not implemented: %s",yytext);}
  "rnmos"		{yyerrorf("Unsupported: Verilog 1995 reserved word not implemented: %s",yytext);}
  "rpmos"		{yyerrorf("Unsupported: Verilog 1995 reserved word not implemented: %s",yytext);}
  "rtran"		{yyerrorf("Unsupported: Verilog 1995 reserved word not implemented: %s",yytext);}
  "rtranif0"		{yyerrorf("Unsupported: Verilog 1995 reserved word not implemented: %s",yytext);}
  "rtranif1"		{yyerrorf("Unsupported: Verilog 1995 reserved word not implemented: %s",yytext);}
  "small"		{yyerrorf("Unsupported: Verilog 1995 reserved word not implemented: %s",yytext);}
  "strong0"		{yyerrorf("Unsupported: Verilog 1995 reserved word not implemented: %s",yytext);}
  "strong1"		{yyerrorf("Unsupported: Verilog 1995 reserved word not implemented: %s",yytext);}
  "table"		{yyerrorf("Unsupported: Verilog 1995 reserved word not implemented: %s",yytext);}
  "time"		{yyerrorf("Unsupported: Verilog 1995 reserved word not implemented: %s",yytext);}
  "tran"		{yyerrorf("Unsupported: Verilog 1995 reserved word not implemented: %s",yytext);}
  "tranif0"		{yyerrorf("Unsupported: Verilog 1995 reserved word not implemented: %s",yytext);}
  "tranif1"		{yyerrorf("Unsupported: Verilog 1995 reserved word not implemented: %s",yytext);}
  "triand"		{yyerrorf("Unsupported: Verilog 1995 reserved word not implemented: %s",yytext);}
  "trior"		{yyerrorf("Unsupported: Verilog 1995 reserved word not implemented: %s",yytext);}
  "trireg"		{yyerrorf("Unsupported: Verilog 1995 reserved word not implemented: %s",yytext);}
  "tri0"		{yyerrorf("Unsupported: Verilog 1995 reserved word not implemented: %s",yytext);}
  "tri1"		{yyerrorf("Unsupported: Verilog 1995 reserved word not implemented: %s",yytext);}
  "wait"		{yyerrorf("Unsupported: Verilog 1995 reserved word not implemented: %s",yytext);}
  "wand"		{yyerrorf("Unsupported: Verilog 1995 reserved word not implemented: %s",yytext);}
  "weak0"		{yyerrorf("Unsupported: Verilog 1995 reserved word not implemented: %s",yytext);}
  "weak1"		{yyerrorf("Unsupported: Verilog 1995 reserved word not implemented: %s",yytext);}
  "while"		{yyerrorf("Unsupported: Verilog 1995 reserved word not implemented: %s",yytext);}
  "wor"			{yyerrorf("Unsupported: Verilog 1995 reserved word not implemented: %s",yytext);}
}

  /* Verilog 2001 */
<V01,V05,S05,PSL>{
  /*     Special hints */
  "include"		{yyerrorf("Unsupported: Verilog 2001 reserved word not implemented; probably you want `include instead: %s",yytext);}
  /*     Generic warnings */
  "automatic"		{yyerrorf("Unsupported: Verilog 2001 reserved word not implemented: %s",yytext);}
  "cell"		{yyerrorf("Unsupported: Verilog 2001 reserved word not implemented: %s",yytext);}
  "config"		{yyerrorf("Unsupported: Verilog 2001 reserved word not implemented: %s",yytext);}
  "design"		{yyerrorf("Unsupported: Verilog 2001 reserved word not implemented: %s",yytext);}
  "endconfig"		{yyerrorf("Unsupported: Verilog 2001 reserved word not implemented: %s",yytext);}
  "ifnone"		{yyerrorf("Unsupported: Verilog 2001 reserved word not implemented: %s",yytext);}
  "incdir"		{yyerrorf("Unsupported: Verilog 2001 reserved word not implemented: %s",yytext);}
  "instance"		{yyerrorf("Unsupported: Verilog 2001 reserved word not implemented: %s",yytext);}
  "liblist"		{yyerrorf("Unsupported: Verilog 2001 reserved word not implemented: %s",yytext);}
  "library"		{yyerrorf("Unsupported: Verilog 2001 reserved word not implemented: %s",yytext);}
  "noshowcancelled"	{yyerrorf("Unsupported: Verilog 2001 reserved word not implemented: %s",yytext);}
  "pulsestyle_ondetect"	{yyerrorf("Unsupported: Verilog 2001 reserved word not implemented: %s",yytext);}
  "pulsestyle_onevent"	{yyerrorf("Unsupported: Verilog 2001 reserved word not implemented: %s",yytext);}
  "showcancelled"	{yyerrorf("Unsupported: Verilog 2001 reserved word not implemented: %s",yytext);}
  "unsigned"		{yyerrorf("Unsupported: Verilog 2001 reserved word not implemented: %s",yytext);}
  "use"			{yyerrorf("Unsupported: Verilog 2001 reserved word not implemented: %s",yytext);}
}

  /* System Verilog */
<S05,PSL>{
  /* Note assert_strobe was in SystemVerilog 3.1, but removed for SystemVerilog 2005 */
  "alias"		{yyerrorf("Unsupported: SystemVerilog 2005 reserved word not implemented: %s",yytext);}
  "bind"		{yyerrorf("Unsupported: SystemVerilog 2005 reserved word not implemented: %s",yytext);}
  "bins"		{yyerrorf("Unsupported: SystemVerilog 2005 reserved word not implemented: %s",yytext);}
  "binsof"		{yyerrorf("Unsupported: SystemVerilog 2005 reserved word not implemented: %s",yytext);}
  "bit"			{yyerrorf("Unsupported: SystemVerilog 2005 reserved word not implemented: %s",yytext);}
  "break"		{yyerrorf("Unsupported: SystemVerilog 2005 reserved word not implemented: %s",yytext);}
  "byte"		{yyerrorf("Unsupported: SystemVerilog 2005 reserved word not implemented: %s",yytext);}
  "chandle"		{yyerrorf("Unsupported: SystemVerilog 2005 reserved word not implemented: %s",yytext);}
  "class"		{yyerrorf("Unsupported: SystemVerilog 2005 reserved word not implemented: %s",yytext);}
  "clocking"		{yyerrorf("Unsupported: SystemVerilog 2005 reserved word not implemented: %s",yytext);}
  "constraint"		{yyerrorf("Unsupported: SystemVerilog 2005 reserved word not implemented: %s",yytext);}
  "context"		{yyerrorf("Unsupported: SystemVerilog 2005 reserved word not implemented: %s",yytext);}
  "continue"		{yyerrorf("Unsupported: SystemVerilog 2005 reserved word not implemented: %s",yytext);}
  "covergroup"		{yyerrorf("Unsupported: SystemVerilog 2005 reserved word not implemented: %s",yytext);}
  "coverpoint"		{yyerrorf("Unsupported: SystemVerilog 2005 reserved word not implemented: %s",yytext);}
  "cross"		{yyerrorf("Unsupported: SystemVerilog 2005 reserved word not implemented: %s",yytext);}
  "dist"		{yyerrorf("Unsupported: SystemVerilog 2005 reserved word not implemented: %s",yytext);}
  "do"			{yyerrorf("Unsupported: SystemVerilog 2005 reserved word not implemented: %s",yytext);}
  "endcass"		{yyerrorf("Unsupported: SystemVerilog 2005 reserved word not implemented: %s",yytext);}
  "endclocking"		{yyerrorf("Unsupported: SystemVerilog 2005 reserved word not implemented: %s",yytext);}
  "endgroup"		{yyerrorf("Unsupported: SystemVerilog 2005 reserved word not implemented: %s",yytext);}
  "endinterface"	{yyerrorf("Unsupported: SystemVerilog 2005 reserved word not implemented: %s",yytext);}
  "endpackage"		{yyerrorf("Unsupported: SystemVerilog 2005 reserved word not implemented: %s",yytext);}
  "endprogram"		{yyerrorf("Unsupported: SystemVerilog 2005 reserved word not implemented: %s",yytext);}
  "endproperty"		{yyerrorf("Unsupported: SystemVerilog 2005 reserved word not implemented: %s",yytext);}
  "endsequence"		{yyerrorf("Unsupported: SystemVerilog 2005 reserved word not implemented: %s",yytext);}
  "enum"		{yyerrorf("Unsupported: SystemVerilog 2005 reserved word not implemented: %s",yytext);}
  "expect"		{yyerrorf("Unsupported: SystemVerilog 2005 reserved word not implemented: %s",yytext);}
  "export"		{yyerrorf("Unsupported: SystemVerilog 2005 reserved word not implemented: %s",yytext);}
  "extends"		{yyerrorf("Unsupported: SystemVerilog 2005 reserved word not implemented: %s",yytext);}
  "extern"		{yyerrorf("Unsupported: SystemVerilog 2005 reserved word not implemented: %s",yytext);}
  "first_match"		{yyerrorf("Unsupported: SystemVerilog 2005 reserved word not implemented: %s",yytext);}
  "foreach"		{yyerrorf("Unsupported: SystemVerilog 2005 reserved word not implemented: %s",yytext);}
  "forkjoin"		{yyerrorf("Unsupported: SystemVerilog 2005 reserved word not implemented: %s",yytext);}
  "iff"			{yyerrorf("Unsupported: SystemVerilog 2005 reserved word not implemented: %s",yytext);}
  "ignore_bins"		{yyerrorf("Unsupported: SystemVerilog 2005 reserved word not implemented: %s",yytext);}
  "illegal_bins"	{yyerrorf("Unsupported: SystemVerilog 2005 reserved word not implemented: %s",yytext);}
  "import"		{yyerrorf("Unsupported: SystemVerilog 2005 reserved word not implemented: %s",yytext);}
  "inside"		{yyerrorf("Unsupported: SystemVerilog 2005 reserved word not implemented: %s",yytext);}
  "int"			{yyerrorf("Unsupported: SystemVerilog 2005 reserved word not implemented: %s",yytext);}
  "interface"		{yyerrorf("Unsupported: SystemVerilog 2005 reserved word not implemented: %s",yytext);}
  "intersect"		{yyerrorf("Unsupported: SystemVerilog 2005 reserved word not implemented: %s",yytext);}
  "join_any"		{yyerrorf("Unsupported: SystemVerilog 2005 reserved word not implemented: %s",yytext);}
  "join_none"		{yyerrorf("Unsupported: SystemVerilog 2005 reserved word not implemented: %s",yytext);}
  "local"		{yyerrorf("Unsupported: SystemVerilog 2005 reserved word not implemented: %s",yytext);}
  "logic"		{yyerrorf("Unsupported: SystemVerilog 2005 reserved word not implemented: %s",yytext);}
  "longint"		{yyerrorf("Unsupported: SystemVerilog 2005 reserved word not implemented: %s",yytext);}
  "matches"		{yyerrorf("Unsupported: SystemVerilog 2005 reserved word not implemented: %s",yytext);}
  "modport"		{yyerrorf("Unsupported: SystemVerilog 2005 reserved word not implemented: %s",yytext);}
  "new"			{yyerrorf("Unsupported: SystemVerilog 2005 reserved word not implemented: %s",yytext);}
  "null"		{yyerrorf("Unsupported: SystemVerilog 2005 reserved word not implemented: %s",yytext);}
  "package"		{yyerrorf("Unsupported: SystemVerilog 2005 reserved word not implemented: %s",yytext);}
  "packed"		{yyerrorf("Unsupported: SystemVerilog 2005 reserved word not implemented: %s",yytext);}
  "priority"		{yyerrorf("Unsupported: SystemVerilog 2005 reserved word not implemented: %s",yytext);}
  "program"		{yyerrorf("Unsupported: SystemVerilog 2005 reserved word not implemented: %s",yytext);}
  "protected"		{yyerrorf("Unsupported: SystemVerilog 2005 reserved word not implemented: %s",yytext);}
  "pure"		{yyerrorf("Unsupported: SystemVerilog 2005 reserved word not implemented: %s",yytext);}
  "rand"		{yyerrorf("Unsupported: SystemVerilog 2005 reserved word not implemented: %s",yytext);}
  "randc"		{yyerrorf("Unsupported: SystemVerilog 2005 reserved word not implemented: %s",yytext);}
  "randcase"		{yyerrorf("Unsupported: SystemVerilog 2005 reserved word not implemented: %s",yytext);}
  "randsequence"	{yyerrorf("Unsupported: SystemVerilog 2005 reserved word not implemented: %s",yytext);}
  "ref"			{yyerrorf("Unsupported: SystemVerilog 2005 reserved word not implemented: %s",yytext);}
  "return"		{yyerrorf("Unsupported: SystemVerilog 2005 reserved word not implemented: %s",yytext);}
  "shortint"		{yyerrorf("Unsupported: SystemVerilog 2005 reserved word not implemented: %s",yytext);}
  "shortreal"		{yyerrorf("Unsupported: SystemVerilog 2005 reserved word not implemented: %s",yytext);}
  "solve"		{yyerrorf("Unsupported: SystemVerilog 2005 reserved word not implemented: %s",yytext);}
  "static"		{yyerrorf("Unsupported: SystemVerilog 2005 reserved word not implemented: %s",yytext);}
  "string"		{yyerrorf("Unsupported: SystemVerilog 2005 reserved word not implemented: %s",yytext);}
  "struct"		{yyerrorf("Unsupported: SystemVerilog 2005 reserved word not implemented: %s",yytext);}
  "super"		{yyerrorf("Unsupported: SystemVerilog 2005 reserved word not implemented: %s",yytext);}
  "tagged"		{yyerrorf("Unsupported: SystemVerilog 2005 reserved word not implemented: %s",yytext);}
  "this"		{yyerrorf("Unsupported: SystemVerilog 2005 reserved word not implemented: %s",yytext);}
  "throughout"		{yyerrorf("Unsupported: SystemVerilog 2005 reserved word not implemented: %s",yytext);}
  "timeprecision"	{yyerrorf("Unsupported: SystemVerilog 2005 reserved word not implemented: %s",yytext);}
  "timeunit"		{yyerrorf("Unsupported: SystemVerilog 2005 reserved word not implemented: %s",yytext);}
  "type"		{yyerrorf("Unsupported: SystemVerilog 2005 reserved word not implemented: %s",yytext);}
  "typedef"		{yyerrorf("Unsupported: SystemVerilog 2005 reserved word not implemented: %s",yytext);}
  "unique"		{yyerrorf("Unsupported: SystemVerilog 2005 reserved word not implemented: %s",yytext);}
  "var"			{yyerrorf("Unsupported: SystemVerilog 2005 reserved word not implemented: %s",yytext);}
  "virtual"		{yyerrorf("Unsupported: SystemVerilog 2005 reserved word not implemented: %s",yytext);}
  "void"		{yyerrorf("Unsupported: SystemVerilog 2005 reserved word not implemented: %s",yytext);}
  "wait_order"		{yyerrorf("Unsupported: SystemVerilog 2005 reserved word not implemented: %s",yytext);}
  "wildcard"		{yyerrorf("Unsupported: SystemVerilog 2005 reserved word not implemented: %s",yytext);}
  "with"		{yyerrorf("Unsupported: SystemVerilog 2005 reserved word not implemented: %s",yytext);}
}

<S05>{
  /* Verilog ONLY not PSL; different rules for PSL as specified below */
  "assert"		{yyerrorf("Unsupported: SystemVerilog 2005 reserved word not implemented in non-PSL context: %s",yytext);}
  "assume"		{yyerrorf("Unsupported: SystemVerilog 2005 reserved word not implemented in non-PSL context: %s",yytext);}
  "before"		{yyerrorf("Unsupported: SystemVerilog 2005 reserved word not implemented in non-PSL context: %s",yytext);}
  "const"		{yyerrorf("Unsupported: SystemVerilog 2005 reserved word not implemented in non-PSL context: %s",yytext);}
  "cover"		{yyerrorf("Unsupported: SystemVerilog 2005 reserved word not implemented in non-PSL context: %s",yytext);}
  "property"		{yyerrorf("Unsupported: SystemVerilog 2005 reserved word not implemented in non-PSL context: %s",yytext);}
  "sequence"		{yyerrorf("Unsupported: SystemVerilog 2005 reserved word not implemented in non-PSL context: %s",yytext);}
  "union"		{yyerrorf("Unsupported: SystemVerilog 2005 reserved word not implemented in non-PSL context: %s",yytext);}
  "within"		{yyerrorf("Unsupported: SystemVerilog 2005 reserved word not implemented in non-PSL context: %s",yytext);}
}

<PSL>{
  /* PSL reserved */
  /*"A"			{yyerrorf("Unsupported: PSL branching reserved word not implemented: %s",yytext);} */
  /*"AF"		{yyerrorf("Unsupported: PSL branching reserved word not implemented: %s",yytext);} */
  /*"AG"		{yyerrorf("Unsupported: PSL branching reserved word not implemented: %s",yytext);} */
  /*"AX"		{yyerrorf("Unsupported: PSL branching reserved word not implemented: %s",yytext);} */
  /*"E"			{yyerrorf("Unsupported: PSL branching reserved word not implemented: %s",yytext);} */
  /*"EF"		{yyerrorf("Unsupported: PSL branching reserved word not implemented: %s",yytext);} */
  /*"EG"		{yyerrorf("Unsupported: PSL branching reserved word not implemented: %s",yytext);} */
  /*"EX"		{yyerrorf("Unsupported: PSL branching reserved word not implemented: %s",yytext);} */
  /*"F"			{yylval.fileline = CRELINE(); return yEVENTUALLYB; } */
  /*"G"			{yylval.fileline = CRELINE(); return yALWAYS; } */
  /*"U"			{yylval.fileline = CRELINE(); return yUNTILB; } */
  /*"W"			{yylval.fileline = CRELINE(); return yUNTIL; } */
  /*"X"			{yylval.fileline = CRELINE(); return yNEXT; } */
  /*"X!"		{yylval.fileline = CRELINE(); return yNEXTB; } */
  "%for"		{yyerrorf("Unsupported: PSL reserved word not implemented: %s",yytext);}
  "%if"			{yyerrorf("Unsupported: PSL reserved word not implemented: %s",yytext);}
  "abort"		{yyerrorf("Unsupported: PSL reserved word not implemented: %s",yytext);}
  "assume_guarantee"	{yyerrorf("Unsupported: PSL reserved word not implemented: %s",yytext);} //Unsup in other tools
  "before"		{yyerrorf("Unsupported: PSL reserved word not implemented: %s",yytext);}
  "before!"		{yyerrorf("Unsupported: PSL reserved word not implemented: %s",yytext);}
  "before!_"		{yyerrorf("Unsupported: PSL reserved word not implemented: %s",yytext);}
  "before_"		{yyerrorf("Unsupported: PSL reserved word not implemented: %s",yytext);}
  "boolean"		{yyerrorf("Unsupported: PSL reserved word not implemented: %s",yytext);}
  "const"		{yyerrorf("Unsupported: PSL reserved word not implemented: %s",yytext);}
  "endpoint"		{yyerrorf("Unsupported: PSL reserved word not implemented: %s",yytext);}
  "eventually!"		{yyerrorf("Unsupported: PSL reserved word not implemented: %s",yytext);}
  "fairness"		{yyerrorf("Unsupported: PSL reserved word not implemented: %s",yytext);} //Unsup in other tools
  "fell"		{yyerrorf("Unsupported: PSL reserved word not implemented: %s",yytext);}
  "forall"		{yyerrorf("Unsupported: PSL reserved word not implemented: %s",yytext);} //Unsup in other tools
  "in"			{yyerrorf("Unsupported: PSL reserved word not implemented: %s",yytext);}
  "inf"			{yyerrorf("Unsupported: PSL reserved word not implemented: %s",yytext);}
  "inherit"		{yyerrorf("Unsupported: PSL reserved word not implemented: %s",yytext);} //Unsup in other tools
  "never"		{yyerrorf("Unsupported: PSL reserved word not implemented: %s",yytext);}
  "next"		{yyerrorf("Unsupported: PSL reserved word not implemented: %s",yytext);}
  "next!"		{yyerrorf("Unsupported: PSL reserved word not implemented: %s",yytext);}
  "next_a"		{yyerrorf("Unsupported: PSL reserved word not implemented: %s",yytext);}
  "next_a!"		{yyerrorf("Unsupported: PSL reserved word not implemented: %s",yytext);}
  "next_e"		{yyerrorf("Unsupported: PSL reserved word not implemented: %s",yytext);}
  "next_e!"		{yyerrorf("Unsupported: PSL reserved word not implemented: %s",yytext);}
  "next_event"		{yyerrorf("Unsupported: PSL reserved word not implemented: %s",yytext);}
  "next_event!"		{yyerrorf("Unsupported: PSL reserved word not implemented: %s",yytext);}
  "next_event_a"	{yyerrorf("Unsupported: PSL reserved word not implemented: %s",yytext);}
  "next_event_a!"	{yyerrorf("Unsupported: PSL reserved word not implemented: %s",yytext);}
  "next_event_e"	{yyerrorf("Unsupported: PSL reserved word not implemented: %s",yytext);}
  "next_event_e!"	{yyerrorf("Unsupported: PSL reserved word not implemented: %s",yytext);}
  "prev"		{yyerrorf("Unsupported: PSL reserved word not implemented: %s",yytext);}
  "property"		{yyerrorf("Unsupported: PSL reserved word not implemented: %s",yytext);}
  "restrict"		{yyerrorf("Unsupported: PSL reserved word not implemented: %s",yytext);}
  "restrict_guarantee"	{yyerrorf("Unsupported: PSL reserved word not implemented: %s",yytext);} //Unsup in other tools
  "rose"		{yyerrorf("Unsupported: PSL reserved word not implemented: %s",yytext);}
  "sequence"		{yyerrorf("Unsupported: PSL reserved word not implemented: %s",yytext);}
  "stable"		{yyerrorf("Unsupported: PSL reserved word not implemented: %s",yytext);}
  "strong"		{yyerrorf("Unsupported: PSL reserved word not implemented: %s",yytext);} //Unsup in other tools
  "union"		{yyerrorf("Unsupported: PSL reserved word not implemented: %s",yytext);}
  "until"		{yyerrorf("Unsupported: PSL reserved word not implemented: %s",yytext);}
  "until!"		{yyerrorf("Unsupported: PSL reserved word not implemented: %s",yytext);}
  "until!_"		{yyerrorf("Unsupported: PSL reserved word not implemented: %s",yytext);}
  "until_"		{yyerrorf("Unsupported: PSL reserved word not implemented: %s",yytext);}
  "vmode"		{yyerrorf("Unsupported: PSL reserved word not implemented: %s",yytext);} //Unsup in other tools
  "vprop"		{yyerrorf("Unsupported: PSL reserved word not implemented: %s",yytext);} //Unsup in other tools
  "vunit"		{yyerrorf("Unsupported: PSL reserved word not implemented: %s",yytext);}
  "within"		{yyerrorf("Unsupported: PSL reserved word not implemented: %s",yytext);}
}

  /* Converted from //{cmt}verilator ...{cmt} by preprocessor */
<V95,V01,V05,S05,PSL>{
  "/*verilator clock_enable*/"		{yylval.fileline = CRELINE(); return yVL_CLOCK_ENABLE;}
  "/*verilator coverage_block_off*/"	{yylval.fileline = CRELINE(); return yVL_COVER_OFF;}
  "/*verilator full_case*/"		{yylval.fileline = CRELINE(); return yVL_FULL_CASE;}
  "/*verilator inline_module*/"		{yylval.fileline = CRELINE(); return yVL_INLINE_MODULE;}
  "/*verilator no_inline_module*/"	{yylval.fileline = CRELINE(); return yVL_NO_INLINE_MODULE;}
  "/*verilator no_inline_task*/"	{yylval.fileline = CRELINE(); return yVL_NO_INLINE_TASK;}
  "/*verilator parallel_case*/"		{yylval.fileline = CRELINE(); return yVL_PARALLEL_CASE;}
  "/*verilator public*/"		{yylval.fileline = CRELINE(); return yVL_PUBLIC;}
  "/*verilator public_flat*/"		{yylval.fileline = CRELINE(); return yVL_PUBLIC_FLAT;}
  "/*verilator public_module*/"		{yylval.fileline = CRELINE(); return yVL_PUBLIC_MODULE;}
  "/*verilator sc_clock*/"		{yylval.fileline = CRELINE(); return yVL_CLOCK;}
  "/*verilator isolate_assignments*/"	{yylval.fileline = CRELINE(); return yVL_ISOLATE_ASSIGNMENTS;}
  "/*verilator systemc_clock*/"		{yylval.fileline = CRELINE(); return yVL_CLOCK;}
  "/*verilator tracing_off*/"		{yylval.fileline = CRELINE(); return yVL_TRACING_OFF;}
  "/*verilator tracing_on*/"		{yylval.fileline = CRELINE(); return yVL_TRACING_ON;}
  "/*verilator lint_off"[^*]*"*/"	{V3Read::verilatorCmtLint(yytext, true); }
  "/*verilator lint_on"[^*]*"*/"	{V3Read::verilatorCmtLint(yytext, false); }

  "/*"[^*]*"*/"				{V3Read::verilatorCmtBad(yytext); }
}

  /* Verilog 1995 Operators */
<V95,V01,V05,S05,PSL>{
  "&&"			{yylval.fileline = CRELINE(); return yANDAND;}
  "||"			{yylval.fileline = CRELINE(); return yOROR;}
  "<="			{yylval.fileline = CRELINE(); return yLTE;}
  ">="			{yylval.fileline = CRELINE(); return yGTE;}
  "<<"			{yylval.fileline = CRELINE(); return ySLEFT;}
  ">>"			{yylval.fileline = CRELINE(); return ySRIGHT;}
  "=="			{yylval.fileline = CRELINE(); return yEQUAL;}
  "!="			{yylval.fileline = CRELINE(); return yNOTEQUAL;}
  "==="			{yylval.fileline = CRELINE(); return yCASEEQUAL;}
  "!=="			{yylval.fileline = CRELINE(); return yCASENOTEQUAL;}
  "^~"			{yylval.fileline = CRELINE(); return yOP_XNOR;}
  "~^"			{yylval.fileline = CRELINE(); return yOP_XNOR;}
  "~&"			{yylval.fileline = CRELINE(); return yOP_NAND;}
  "~|"			{yylval.fileline = CRELINE(); return yOP_NOR;}
}

  /* Verilog 2001 Operators */
<V01,V05,S05,PSL>{
  "<<<"			{yylval.fileline = CRELINE(); return ySLEFT;}
  ">>>"			{yylval.fileline = CRELINE(); return ySSRIGHT;}
  "**"			{yylval.fileline = CRELINE(); return yPOW;}
  "+:"			{yylval.fileline = CRELINE(); return yPLUSCOLON;}
  "-:"			{yylval.fileline = CRELINE(); return yMINUSCOLON;}
}

  /* PSL Operators */
<PSL>{
  "{"			{yylval.fileline = CRELINE(); return yPSL_BRA;}	// Avoid parser hitting concatenate.
  "}"			{yylval.fileline = CRELINE(); return yPSL_KET;}	// Avoid parser hitting concatenate.
  "->"			{yylval.fileline = CRELINE(); return yOP_LOGIF;}
  "<->"			{yyerrorf("Unsupported: PSL operator not implemented: %s",yytext);} //Unsup in other tools
  "[*"			{yyerrorf("Unsupported: PSL operator not implemented: %s",yytext);} // yBRA_STAR
  "[*]"			{yyerrorf("Unsupported: PSL operator not implemented: %s",yytext);} // yBRA_STAR_KET
  "[+]"			{yyerrorf("Unsupported: PSL operator not implemented: %s",yytext);} // yBRA_PLUS_KET
  "[->"			{yyerrorf("Unsupported: PSL operator not implemented: %s",yytext);} // yBRA_MINUS_GT
  "[->]"		{yyerrorf("Unsupported: PSL operator not implemented: %s",yytext);} // yBRA_MINUS_GT_KET
  "[="			{yyerrorf("Unsupported: PSL operator not implemented: %s",yytext);} // yBRA_EQ
  "|->"			{yyerrorf("Unsupported: PSL operator not implemented: %s",yytext);} // yOR_MINUS_GT
  "|=>"			{yyerrorf("Unsupported: PSL operator not implemented: %s",yytext);} // yOR_EQ_GT
}

  /* Identifiers and numbers */
<V95,V01,V05,S05,PSL>{
  {escid}		{  int i;
			   for (i=0; yytext[i] != 0; i++)
			       if (!isalnum(yytext[i]))
				   yytext[i] = '_';
			   if (isalpha(yytext[1])) {
			       yylval.strp = V3Read::newString(yytext+1); // +1 to skip the backslash
			   } else {
			       yylval.strp = V3Read::newString(yytext); // Need _ as "6..." isn't legal ID
			   }
			   return yID;
			 }

  {id}			{  yylval.strp = V3Read::newString(yytext);
			   return yID;
			 }

  \"[^\"\\]*\"		{  yylval.strp = V3Read::newString(yytext+1,yyleng-2);
			   return ySTRING;
			}
  \" 			{ yy_push_state(STRING); yymore(); }


  [0-9]*?['']s?[bcodhBCODH][ \t]*[A-Fa-f0-9xXzZ_?]*	{
			  yylval.nump = V3Read::newNumber(V3Read::fileline(),(char*)yytext);
                          return yINTNUM;
			}
  [0-9]*?['']s?[01xXzZ]	{	/* SystemVerilog */
			  yylval.nump = V3Read::newNumber(V3Read::fileline(),(char*)yytext);
                          return yINTNUM;
			}
  [0-9]+[_0-9]*[ \t]*['']s?[bcodhBCODH]?[ \t]*[A-Fa-f0-9xXzZ_?]*	{
			  yylval.nump = V3Read::newNumber(V3Read::fileline(),(char*)yytext);
                          return yINTNUM;
			}
  [0-9]*		{ yylval.nump = V3Read::newNumber(V3Read::fileline(),(char*)yytext);
                          return yINTNUM;
			}
  [-+]?[0-9]+(\.[0-9]+)([eE][-+]?[0-9]+)? {
    			  yylval.cdouble = 0;  /* Only for delays, not used yet */
                          return yFLOATNUM;
			}
  [-+]?[0-9]+(\.[0-9]+)?([eE][-+]?[0-9]+) {
    			  yylval.cdouble = 0;  /* Only for delays, not used yet */
                          return yFLOATNUM;
			}

  "`timescale"{ws}+[^\n]*	{}
  "`line"{ws}+[^\n]*\n		{V3Read::ppline(yytext);}
}

  /************************************************************************/
  /* STRINGS */
<STRING>\n 		{ yyerror("Unterminated string\n"); }
<STRING>\r		;
<STRING>[^\"\\]* 	{ yymore(); }
<STRING>\\.	 	{ yymore(); }
<STRING>\" 		{ yy_pop_state();
			  yylval.strp = V3Read::newString(yytext+1,yyleng-2);
			  return ySTRING; }

  /************************************************************************/
  /* Common for all SYSC header states */
  /* OPTIMIZE: we return one per line, make it one for the entire block */
<V95,V01,V05,S05,PSL,SYSCHDR,SYSCINT,SYSCIMP,SYSCIMPH,SYSCCTOR,SYSCDTOR,IGNORE>{
  [ \t]*"`verilog"			{ BEGIN V95; }
  [ \t]*"`psl"				{ if (V3Read::optPsl()) { BEGIN PSL; } else { BEGIN IGNORE; } }
  [ \t]*"`systemc_header"		{ BEGIN SYSCHDR; }
  [ \t]*"`systemc_ctor"			{ BEGIN SYSCCTOR; }
  [ \t]*"`systemc_dtor"			{ BEGIN SYSCDTOR; }
  [ \t]*"`systemc_interface"		{ BEGIN SYSCINT; }
  [ \t]*"`systemc_implementation"	{ BEGIN SYSCIMP; }
  [ \t]*"`systemc_imp_header"		{ BEGIN SYSCIMPH; }

  [ \t]*"`begin_keywords"[ \t]*\"1364-1995\"		{ yy_push_state(V95); V3Read::pushBeginKeywords();}
  [ \t]*"`begin_keywords"[ \t]*\"1364-2001\"		{ yy_push_state(V01); V3Read::pushBeginKeywords();}
  [ \t]*"`begin_keywords"[ \t]*\"1364-2001-noconfig\"	{ yy_push_state(V01); V3Read::pushBeginKeywords();}
  [ \t]*"`begin_keywords"[ \t]*\"1364-2005\"		{ yy_push_state(V05); V3Read::pushBeginKeywords();}
  [ \t]*"`begin_keywords"[ \t]*\"1800-2005\"		{ yy_push_state(S05); V3Read::pushBeginKeywords();}
  [ \t]*"`end_keywords"					{ yy_pop_state(); if (!V3Read::popBeginKeywords()) yyerrorf("`end_keywords when not inside `begin_keywords block"); }

  "`line"[ \t][^\n]*\n			{V3Read::ppline(yytext);}
}

<SYSCHDR>[ \t]*[^` \t\n][^\n]*\n	{ NEXTLINE(); yylval.strp = V3Read::newString(yytext); return ySCHDR;}
<SYSCINT>[ \t]*[^` \t\n][^\n]*\n	{ NEXTLINE(); yylval.strp = V3Read::newString(yytext); return ySCINT;}
<SYSCIMP>[ \t]*[^` \t\n][^\n]*\n	{ NEXTLINE(); yylval.strp = V3Read::newString(yytext); return ySCIMP;}
<SYSCIMPH>[ \t]*[^` \t\n][^\n]*\n	{ NEXTLINE(); yylval.strp = V3Read::newString(yytext); return ySCIMPH;}
<SYSCCTOR>[ \t]*[^` \t\n][^\n]*\n	{ NEXTLINE(); yylval.strp = V3Read::newString(yytext); return ySCCTOR;}
<SYSCDTOR>[ \t]*[^` \t\n][^\n]*\n	{ NEXTLINE(); yylval.strp = V3Read::newString(yytext); return ySCDTOR;}
<IGNORE>[ \t]*[^` \t\n][^\n]*\n		{ NEXTLINE(); }

  /* Pick up text-type data */
<SYSCHDR,SYSCINT,SYSCIMP,SYSCIMPH,SYSCCTOR,SYSCDTOR,IGNORE>{
  [ \t]*\n		{ NEXTLINE(); yymore();}
  \r			;
}

  /************************************************************************/
  /* Default rules - leave last */

<V95,V01,V05,S05,PSL>{
  "`"[a-zA-Z_0-9]+	{ yyerrorf("Define or directive not defined: %s",yytext); }

  "//"[^\n]+		{ }  /* throw away single line comments */

  .			{yylval.fileline = CRELINE(); return yytext[0];}	/* return single char ops. */
}

  /* Catch all - absolutely last */
<*>.|\n     		{ yyerrorf("Missing verilog.l rule: Default rule invoked in state %d: %s", YY_START, yytext); }
%%

