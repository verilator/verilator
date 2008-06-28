/* -*- C++ -*- */
/**************************************************************************
 * DESCRIPTION: Verilator: Flex input file
 *
 * Code available from: http://www.veripool.org/verilator
 *
 **************************************************************************
 *
 * Copyright 2003-2008 by Wilson Snyder.  This program is free software; you can
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

#include <cstdio>
#include <cstring>
#include <cstdlib>
#include "V3Read.h"
#include "V3Number.h"
#include "y.tab.h"

extern void yyerror(char*);
extern void yyerrorf(const char* format, ...);

#define STATE_VERILOG_RECENT  S05		// State name for most recent Verilog Version

#define YY_INPUT(buf,result,max_size) \
    result = V3Read::flexPpInputToLex(buf,max_size);

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

void V3Read::verilatorCmtLintSave() {
    s_readp->m_lintState.push_back(*V3Read::fileline());
}
void V3Read::verilatorCmtLintRestore() {
    if (s_readp->m_lintState.empty()) {
	yyerrorf("/*verilator lint_restore*/ without matching save.");
	return;
    }
    V3Read::fileline()->warnStateFrom(s_readp->m_lintState.back());
    s_readp->m_lintState.pop_back();
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
%s PSL STRING ATTRMODE
%s SYSCHDR SYSCINT SYSCIMP SYSCIMPH SYSCCTOR SYSCDTOR
%s IGNORE

ws	[ \t\f\r]+
wsnr	[ \t\f]+
	/* identifier */
id	[a-zA-Z_][a-zA-Z0-9_$]*
	/* escaped identifier */
escid	\\[^ \t\f\r\n]+

%%

<INITIAL>.|\n 		{BEGIN STATE_VERILOG_RECENT; yyless(0); }

  /* Verilog 1995 */
<V95,V01,V05,S05,PSL>{
  {ws}			;			/* ignore white-space */
  \n			{NEXTLINE();}		/* Count line numbers */
  /*     Extensions to Verilog set, some specified by PSL */
  "$c"[0-9]*		{yylval.fileline = CRELINE(); return yD_C;}		/*Verilator only*/
  /*     System Tasks */
  "$display"		{yylval.fileline = CRELINE(); return yD_DISPLAY;}
  "$fclose"		{yylval.fileline = CRELINE(); return yD_FCLOSE;}
  "$fdisplay"		{yylval.fileline = CRELINE(); return yD_FDISPLAY;}
  "$feof"		{yylval.fileline = CRELINE(); return yD_FEOF;}
  "$fflush"		{yylval.fileline = CRELINE(); return yD_FFLUSH;}
  "$fgetc"		{yylval.fileline = CRELINE(); return yD_FGETC;}
  "$fgets"		{yylval.fileline = CRELINE(); return yD_FGETS;}
  "$finish"		{yylval.fileline = CRELINE(); return yD_FINISH;}
  "$fopen"		{yylval.fileline = CRELINE(); return yD_FOPEN;}
  "$fullskew"		{yylval.fileline = CRELINE(); return yaTIMINGSPEC;}
  "$fwrite"		{yylval.fileline = CRELINE(); return yD_FWRITE;}
  "$hold"		{yylval.fileline = CRELINE(); return yaTIMINGSPEC;}
  "$nochange"		{yylval.fileline = CRELINE(); return yaTIMINGSPEC;}
  "$period"		{yylval.fileline = CRELINE(); return yaTIMINGSPEC;}
  "$random"		{yylval.fileline = CRELINE(); return yD_RANDOM;}
  "$readmemb"		{yylval.fileline = CRELINE(); return yD_READMEMB;}
  "$readmemh"		{yylval.fileline = CRELINE(); return yD_READMEMH;}
  "$realtime"		{yylval.fileline = CRELINE(); return yD_TIME;}
  "$recovery"		{yylval.fileline = CRELINE(); return yaTIMINGSPEC;}
  "$recrem"		{yylval.fileline = CRELINE(); return yaTIMINGSPEC;}
  "$removal"		{yylval.fileline = CRELINE(); return yaTIMINGSPEC;}
  "$setup"		{yylval.fileline = CRELINE(); return yaTIMINGSPEC;}
  "$setuphold"		{yylval.fileline = CRELINE(); return yaTIMINGSPEC;}
  "$skew"		{yylval.fileline = CRELINE(); return yaTIMINGSPEC;}
  "$stop"		{yylval.fileline = CRELINE(); return yD_STOP;}
  "$time"		{yylval.fileline = CRELINE(); return yD_TIME;}
  "$timeskew"		{yylval.fileline = CRELINE(); return yaTIMINGSPEC;}
  "$width"		{yylval.fileline = CRELINE(); return yaTIMINGSPEC;}
  "$write"		{yylval.fileline = CRELINE(); return yD_WRITE;}
  /*     Keywords */
  "always"		{yylval.fileline = CRELINE(); return yALWAYS;}
  "and"			{yylval.fileline = CRELINE(); return yAND;}
  "assign"		{yylval.fileline = CRELINE(); return yASSIGN;}
  "begin"		{yylval.fileline = CRELINE(); return yBEGIN;}
  "buf"			{yylval.fileline = CRELINE(); return yBUF;}
  "case"		{yylval.fileline = CRELINE(); return yCASE;}
  "casex"		{yylval.fileline = CRELINE(); return yCASEX;}
  "casez"		{yylval.fileline = CRELINE(); return yCASEZ;}
  "default"		{yylval.fileline = CRELINE(); return yDEFAULT;}
  "defparam"		{yylval.fileline = CRELINE(); return yDEFPARAM;}
  "edge"		{yylval.fileline = CRELINE(); return yaTIMINGSPEC;}
  "else"		{yylval.fileline = CRELINE(); return yELSE;}
  "end"			{yylval.fileline = CRELINE(); return yEND;}
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
  "parameter"		{yylval.fileline = CRELINE(); return yPARAMETER;}
  "posedge"		{yylval.fileline = CRELINE(); return yPOSEDGE;}
  "reg"			{yylval.fileline = CRELINE(); return yREG;}
  "scalared"		{yylval.fileline = CRELINE(); return ySCALARED;}
  "specify"		{yylval.fileline = CRELINE(); return ySPECIFY;}
  "specparam"		{yylval.fileline = CRELINE(); return yaTIMINGSPEC;}
  "supply0"		{yylval.fileline = CRELINE(); return ySUPPLY0;}
  "supply1"		{yylval.fileline = CRELINE(); return ySUPPLY1;}
  "task"		{yylval.fileline = CRELINE(); return yTASK;}
  "tri"			{yylval.fileline = CRELINE(); return yTRI;}
  "vectored"		{yylval.fileline = CRELINE(); return yVECTORED;}
  "while"		{yylval.fileline = CRELINE(); return yWHILE;}
  "wire"		{yylval.fileline = CRELINE(); return yWIRE;}
  "xnor"		{yylval.fileline = CRELINE(); return yXNOR;}
  "xor"			{yylval.fileline = CRELINE(); return yXOR;}
  /*     Special errors */
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
  /*     Generic unsupported warnings */
  "bufif0"		{yyerrorf("Unsupported: Verilog 1995 reserved word not implemented: %s",yytext);}
  "bufif1"		{yyerrorf("Unsupported: Verilog 1995 reserved word not implemented: %s",yytext);}
  "cmos"		{yyerrorf("Unsupported: Verilog 1995 reserved word not implemented: %s",yytext);}
  "deassign"		{yyerrorf("Unsupported: Verilog 1995 reserved word not implemented: %s",yytext);}
  "disable"		{yyerrorf("Unsupported: Verilog 1995 reserved word not implemented: %s",yytext);}
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
  "wor"			{yyerrorf("Unsupported: Verilog 1995 reserved word not implemented: %s",yytext);}
}

  /* Verilog 2001 */
<V01,V05,S05,PSL>{
  /*     System Tasks */
  "$signed"		{yylval.fileline = CRELINE(); return yD_SIGNED;}
  "$unsigned"		{yylval.fileline = CRELINE(); return yD_UNSIGNED;}
  /*     Keywords */
  "automatic"		{yylval.fileline = CRELINE(); return yAUTOMATIC;}
  "endgenerate"		{yylval.fileline = CRELINE(); return yENDGENERATE;}
  "generate"		{yylval.fileline = CRELINE(); return yGENERATE;}
  "genvar"		{yylval.fileline = CRELINE(); return yGENVAR;}
  "ifnone"		{yylval.fileline = CRELINE(); return yaTIMINGSPEC;}
  "localparam"		{yylval.fileline = CRELINE(); return yLOCALPARAM;}
  "noshowcancelled"	{yylval.fileline = CRELINE(); return yaTIMINGSPEC;}
  "pulsestyle_ondetect"	{yylval.fileline = CRELINE(); return yaTIMINGSPEC;}
  "pulsestyle_onevent"	{yylval.fileline = CRELINE(); return yaTIMINGSPEC;}
  "showcancelled"	{yylval.fileline = CRELINE(); return yaTIMINGSPEC;}
  "signed"		{yylval.fileline = CRELINE(); return ySIGNED;}
  "unsigned"		{yylval.fileline = CRELINE(); return yUNSIGNED;}
  /*     Special errors */
  "include"		{yyerrorf("Unsupported: Verilog 2001-config reserved word not implemented; probably you want `include instead: %s",yytext);}
  /*     Generic unsupported warnings */
  "cell"		{yyerrorf("Unsupported: Verilog 2001-config reserved word not implemented: %s",yytext);}
  "config"		{yyerrorf("Unsupported: Verilog 2001-config reserved word not implemented: %s",yytext);}
  "design"		{yyerrorf("Unsupported: Verilog 2001-config reserved word not implemented: %s",yytext);}
  "endconfig"		{yyerrorf("Unsupported: Verilog 2001-config reserved word not implemented: %s",yytext);}
  "incdir"		{yyerrorf("Unsupported: Verilog 2001-config reserved word not implemented: %s",yytext);}
  "instance"		{yyerrorf("Unsupported: Verilog 2001-config reserved word not implemented: %s",yytext);}
  "liblist"		{yyerrorf("Unsupported: Verilog 2001-config reserved word not implemented: %s",yytext);}
  "library"		{yyerrorf("Unsupported: Verilog 2001-config reserved word not implemented: %s",yytext);}
  "use"			{yyerrorf("Unsupported: Verilog 2001-config reserved word not implemented: %s",yytext);}
}

  /* Verilog 2005 */
<V05,S05,PSL>{
  /*     Keywords */
  "uwire"		{yylval.fileline = CRELINE(); return yWIRE;}
}

  /* System Verilog 2005 */
<S05,PSL>{
  /*     System Tasks */
  "$bits"		{yylval.fileline = CRELINE(); return yD_BITS;}
  "$clog2"		{yylval.fileline = CRELINE(); return yD_CLOG2;}
  "$countones"		{yylval.fileline = CRELINE(); return yD_COUNTONES;}
  "$error"		{yylval.fileline = CRELINE(); return yD_ERROR;}
  "$fatal"		{yylval.fileline = CRELINE(); return yD_FATAL;}
  "$info"		{yylval.fileline = CRELINE(); return yD_INFO;}
  "$isunknown"		{yylval.fileline = CRELINE(); return yD_ISUNKNOWN;}
  "$onehot"		{yylval.fileline = CRELINE(); return yD_ONEHOT;}
  "$onehot0"		{yylval.fileline = CRELINE(); return yD_ONEHOT0;}
  "$warning"		{yylval.fileline = CRELINE(); return yD_WARNING;}
  /*     Keywords */
  "always_comb"		{yylval.fileline = CRELINE(); return yALWAYS;}
  "always_ff"		{yylval.fileline = CRELINE(); return yALWAYS;}
  "always_latch"	{yylval.fileline = CRELINE(); return yALWAYS;}
  "do"			{yylval.fileline = CRELINE(); return yDO;}
  "final"		{yylval.fileline = CRELINE(); return yFINAL;}
  "static"		{yylval.fileline = CRELINE(); return ySTATIC;}
  /*     Generic unsupported warnings */
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
  "endclass"		{yyerrorf("Unsupported: SystemVerilog 2005 reserved word not implemented: %s",yytext);}
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

  /* SystemVerilog ONLY not PSL; different rules for PSL as specified below */
<S05>{
  /*     Keywords */
  "assert"		{yylval.fileline = CRELINE(); return yASSERT;}
  /*     Generic unsupported warnings */
  "assume"		{yyerrorf("Unsupported: SystemVerilog 2005 reserved word not implemented in non-PSL context: %s",yytext);}
  "before"		{yyerrorf("Unsupported: SystemVerilog 2005 reserved word not implemented in non-PSL context: %s",yytext);}
  "const"		{yyerrorf("Unsupported: SystemVerilog 2005 reserved word not implemented in non-PSL context: %s",yytext);}
  "cover"		{yyerrorf("Unsupported: SystemVerilog 2005 reserved word not implemented in non-PSL context: %s",yytext);}
  "property"		{yyerrorf("Unsupported: SystemVerilog 2005 reserved word not implemented in non-PSL context: %s",yytext);}
  "sequence"		{yyerrorf("Unsupported: SystemVerilog 2005 reserved word not implemented in non-PSL context: %s",yytext);}
  "union"		{yyerrorf("Unsupported: SystemVerilog 2005 reserved word not implemented in non-PSL context: %s",yytext);}
  "within"		{yyerrorf("Unsupported: SystemVerilog 2005 reserved word not implemented in non-PSL context: %s",yytext);}
}

  /* Default PLI rule */
<V95,V01,V05,S05,PSL>{
  "$"[a-zA-Z_$][a-zA-Z0-9_$]*	{yyerrorf("Unsupported or unknown PLI call: %s",yytext);}
}

  /************************************************************************/
  /* PSL */

  /*Entry into PSL; mode change */
<V95,V01,V05,S05>{
  "psl"			{ yy_push_state(PSL); yylval.fileline = CRELINE(); return yPSL; }
}

<PSL>{
  /*     Special things */
  "psl"			{ ; }	// 'psl' may occur in middle of statement, so easier just to suppress
  /*     Keywords */
  "assert"		{yylval.fileline = CRELINE(); return yPSL_ASSERT;}
  "assume"		{yylval.fileline = CRELINE(); return yPSL_ASSERT;} //==assert
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
  /*     Generic unsupported warnings */
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

  /************************************************************************/
  /* Meta comments */

  /* Converted from //{cmt}verilator ...{cmt} by preprocessor */
<V95,V01,V05,S05,PSL>{
  "/*verilator"{ws}*"*/"		{}	/* Ignore empty comments, may be `endif // verilator */
  "/*verilator clock_enable*/"		{yylval.fileline = CRELINE(); return yVL_CLOCK_ENABLE;}
  "/*verilator coverage_block_off*/"	{yylval.fileline = CRELINE(); return yVL_COVER_OFF;}
  "/*verilator full_case*/"		{yylval.fileline = CRELINE(); return yVL_FULL_CASE;}
  "/*verilator inline_module*/"		{yylval.fileline = CRELINE(); return yVL_INLINE_MODULE;}
  "/*verilator isolate_assignments*/"	{yylval.fileline = CRELINE(); return yVL_ISOLATE_ASSIGNMENTS;}
  "/*verilator no_inline_module*/"	{yylval.fileline = CRELINE(); return yVL_NO_INLINE_MODULE;}
  "/*verilator no_inline_task*/"	{yylval.fileline = CRELINE(); return yVL_NO_INLINE_TASK;}
  "/*verilator parallel_case*/"		{yylval.fileline = CRELINE(); return yVL_PARALLEL_CASE;}
  "/*verilator public*/"		{yylval.fileline = CRELINE(); return yVL_PUBLIC;}
  "/*verilator public_flat*/"		{yylval.fileline = CRELINE(); return yVL_PUBLIC_FLAT;}
  "/*verilator public_module*/"		{yylval.fileline = CRELINE(); return yVL_PUBLIC_MODULE;}
  "/*verilator sc_clock*/"		{yylval.fileline = CRELINE(); return yVL_CLOCK;}
  "/*verilator systemc_clock*/"		{yylval.fileline = CRELINE(); return yVL_CLOCK;}
  "/*verilator tracing_off*/"		{yylval.fileline = CRELINE(); return yVL_TRACING_OFF;}
  "/*verilator tracing_on*/"		{yylval.fileline = CRELINE(); return yVL_TRACING_ON;}
  "/*verilator lint_off"[^*]*"*/"	{V3Read::verilatorCmtLint(yytext, true); }
  "/*verilator lint_on"[^*]*"*/"	{V3Read::verilatorCmtLint(yytext, false); }
  "/*verilator lint_restore*/"		{V3Read::verilatorCmtLintRestore(); }
  "/*verilator lint_save*/"		{V3Read::verilatorCmtLintSave(); }

  "/*"[^*]*"*/"				{V3Read::verilatorCmtBad(yytext); }
}

  /************************************************************************/
  /* Operators */

  /* Verilog 1995 Operators */
<V95,V01,V05,S05,PSL>{
  "&&"			{yylval.fileline = CRELINE(); return yP_ANDAND;}
  "||"			{yylval.fileline = CRELINE(); return yP_OROR;}
  "<="			{yylval.fileline = CRELINE(); return yP_LTE;}
  ">="			{yylval.fileline = CRELINE(); return yP_GTE;}
  "<<"			{yylval.fileline = CRELINE(); return yP_SLEFT;}
  ">>"			{yylval.fileline = CRELINE(); return yP_SRIGHT;}
  "=="			{yylval.fileline = CRELINE(); return yP_EQUAL;}
  "!="			{yylval.fileline = CRELINE(); return yP_NOTEQUAL;}
  "==="			{yylval.fileline = CRELINE(); return yP_CASEEQUAL;}
  "!=="			{yylval.fileline = CRELINE(); return yP_CASENOTEQUAL;}
  "^~"			{yylval.fileline = CRELINE(); return yP_XNOR;}
  "~^"			{yylval.fileline = CRELINE(); return yP_XNOR;}
  "~&"			{yylval.fileline = CRELINE(); return yP_NAND;}
  "~|"			{yylval.fileline = CRELINE(); return yP_NOR;}
  "->"			{yylval.fileline = CRELINE(); return yP_MINUSGT;}
  "=>"                  {yylval.fileline = CRELINE(); return yP_EQGT; }
  "*>"                  {yylval.fileline = CRELINE(); return yP_ASTGT; }
  "&&&"			{yylval.fileline = CRELINE(); return yP_ANDANDAND; }
}

  /* Verilog 2001 Operators */
<V01,V05,S05,PSL>{
  "<<<"			{yylval.fileline = CRELINE(); return yP_SLEFT;}
  ">>>"			{yylval.fileline = CRELINE(); return yP_SSRIGHT;}
  "**"			{yylval.fileline = CRELINE(); return yP_POW;}
  "+:"			{yylval.fileline = CRELINE(); return yP_PLUSCOLON;}
  "-:"			{yylval.fileline = CRELINE(); return yP_MINUSCOLON;}
  ".*"			{yylval.fileline = CRELINE(); return yP_DOTSTAR;}
}

  /* SystemVerilog Operators */
<S05>{
  "==?"			{yylval.fileline = CRELINE(); return yP_WILDEQUAL;}
  "!=?"			{yylval.fileline = CRELINE(); return yP_WILDNOTEQUAL;}
  "+="			{yylval.fileline = CRELINE(); return yP_PLUSEQ; }
  "-="			{yylval.fileline = CRELINE(); return yP_MINUSEQ; }
  "*="			{yylval.fileline = CRELINE(); return yP_TIMESEQ; }
  "/="			{yylval.fileline = CRELINE(); return yP_DIVEQ; }
  "%="			{yylval.fileline = CRELINE(); return yP_MODEQ; }
  "&="			{yylval.fileline = CRELINE(); return yP_ANDEQ; }
  "|="			{yylval.fileline = CRELINE(); return yP_OREQ; }
  "^="			{yylval.fileline = CRELINE(); return yP_XOREQ; }
  "<<="			{yylval.fileline = CRELINE(); return yP_SLEFTEQ; }
  ">>="			{yylval.fileline = CRELINE(); return yP_SRIGHTEQ; }
  "<<<="		{yylval.fileline = CRELINE(); return yP_SLEFTEQ; }
  ">>>="		{yylval.fileline = CRELINE(); return yP_SSRIGHTEQ; }
  "->>"			{yylval.fileline = CRELINE(); return yP_MINUSGTGT; }
  "##"			{yylval.fileline = CRELINE(); return yP_POUNDPOUND; }
  "@@"			{yylval.fileline = CRELINE(); return yP_ATAT; }
  "::"			{yylval.fileline = CRELINE(); return yP_COLONCOLON; }
  ":="			{yylval.fileline = CRELINE(); return yP_COLONEQ; }
  ":/"			{yylval.fileline = CRELINE(); return yP_COLONDIV; }
  "|->"			{yylval.fileline = CRELINE(); return yP_ORMINUSGT; }
  "|=>"			{yylval.fileline = CRELINE(); return yP_OREQGT; }
}

  /* PSL Operators */
<PSL>{
  "{"			{yylval.fileline = CRELINE(); return yPSL_BRA;}	// Avoid parser hitting concatenate.
  "}"			{yylval.fileline = CRELINE(); return yPSL_KET;}	// Avoid parser hitting concatenate.
  "<->"			{yyerrorf("Unsupported: PSL operator not implemented: %s",yytext);} //Unsup in other tools
  "[*"			{yyerrorf("Unsupported: PSL operator not implemented: %s",yytext);} // yP_BRA_STAR
  "[*]"			{yyerrorf("Unsupported: PSL operator not implemented: %s",yytext);} // yP_BRA_STAR_KET
  "[+]"			{yyerrorf("Unsupported: PSL operator not implemented: %s",yytext);} // yP_BRA_PLUS_KET
  "[->"			{yyerrorf("Unsupported: PSL operator not implemented: %s",yytext);} // yP_BRA_MINUS_GT
  "[->]"		{yyerrorf("Unsupported: PSL operator not implemented: %s",yytext);} // yP_BRA_MINUS_GT_KET
  "[="			{yyerrorf("Unsupported: PSL operator not implemented: %s",yytext);} // yP_BRA_EQ
  "|->"			{yyerrorf("Unsupported: PSL operator not implemented: %s",yytext);} // yP_ORMINUSGT
  "|=>"			{yyerrorf("Unsupported: PSL operator not implemented: %s",yytext);} // yP_OREQGT
}

  /* Identifiers and numbers */
<V95,V01,V05,S05,PSL>{
  {escid}		{  int i;
			   for (i=0; yytext[i] != 0; i++)
			       if (!isalnum(yytext[i]))
				   yytext[i] = '_';
			   if (isalpha(yytext[1])) {
			       yylval.strp = V3Read::newString(
				   AstNode::encodeName(
				       string(yytext+1))); // +1 to skip the backslash
			   } else {
			       yylval.strp = V3Read::newString(
				   AstNode::encodeName(
				       yytext)); // Need _ as "6..." isn't legal ID
			   }
			   return yaID;
			 }

  {id}			{  yylval.strp = V3Read::newString(AstNode::encodeName(string(yytext)));
			   return yaID;
			 }

  \"[^\"\\]*\"		{  yylval.strp = V3Read::newString(yytext+1,yyleng-2);
			   return yaSTRING;
			}
  \" 			{ yy_push_state(STRING); yymore(); }


  [0-9]*?['']s?[bcodhBCODH][ \t]*[A-Fa-f0-9xXzZ_?]*	{
			  yylval.nump = V3Read::newNumber(V3Read::fileline(),(char*)yytext);
                          return yaINTNUM;
			}
  [0-9]*?['']s?[01xXzZ]	{	/* SystemVerilog */
			  yylval.nump = V3Read::newNumber(V3Read::fileline(),(char*)yytext);
                          return yaINTNUM;
			}
  [0-9][_0-9]*[ \t]*['']s?[bcodhBCODH]?[ \t]*[A-Fa-f0-9xXzZ_?]*	{
			  yylval.nump = V3Read::newNumber(V3Read::fileline(),(char*)yytext);
                          return yaINTNUM;
			}
  [0-9][_0-9]*		{ yylval.nump = V3Read::newNumber(V3Read::fileline(),(char*)yytext);
                          return yaINTNUM;
			}
  [0-9][_0-9]*(\.[_0-9]+)([eE][-+]?[_0-9]+)? {
			  yylval.cdouble = 0;  /* Only for delays, not used yet */
                          return yaFLOATNUM;
			}
  [0-9][_0-9]*(\.[_0-9]+)?([eE][-+]?[_0-9]+) {
			  yylval.cdouble = 0;  /* Only for delays, not used yet */
                          return yaFLOATNUM;
			}
  [0-9][_0-9]*(\.[_0-9]+)?(fs|ps|ns|us|ms|s|step) {
			  yylval.cdouble = 0;  /* Only for times, not used yet */
                          return yaFLOATNUM;
			}
}

  /************************************************************************/
  /* STRINGS */
<STRING>\n 		{ yyerrorf("Unterminated string\n"); }
<STRING>\r		;
<STRING>[^\"\\]* 	{ yymore(); }
<STRING>\\.	 	{ yymore(); }
<STRING>\" 		{ yy_pop_state();
			  yylval.strp = V3Read::newString(yytext+1,yyleng-2);
			  return yaSTRING; }

  /************************************************************************/
  /* Attributes */
<ATTRMODE>\n		{ yymore(); NEXTLINE(); }
<ATTRMODE>"*)"		{ yy_pop_state(); }
<ATTRMODE>. 		{ yymore(); }
<ATTRMODE><<EOF>>	{ yyerrorf("EOF in (*");
			  yyleng = 0; yy_pop_state(); }

  /************************************************************************/
  /* Attributes */
<V95,V01,V05,S05>{
    "(*"/{ws}*[^)]	{ yymore(); yy_push_state(ATTRMODE); }	// Doesn't match (*)
}

  /************************************************************************/
  /* Preprocessor*/
  /* Common for all SYSC header states */
  /* OPTIMIZE: we return one per line, make it one for the entire block */
<V95,V01,V05,S05,PSL,SYSCHDR,SYSCINT,SYSCIMP,SYSCIMPH,SYSCCTOR,SYSCDTOR,IGNORE>{
  "`accelerate"				{ } // Verilog-XL compatibility
  "`autoexpand_vectornets"		{ } // Verilog-XL compatibility
  "`celldefine"				{ V3Read::inCellDefine(true); }
  "`default_decay_time"{ws}+[^\n]*	{ } // Verilog spec - delays only
  "`delay_mode_distributed"		{ } // Verilog spec - delays only
  "`delay_mode_path"			{ } // Verilog spec - delays only
  "`delay_mode_unit"			{ } // Verilog spec - delays only
  "`delay_mode_zero"			{ } // Verilog spec - delays only
  "`disable_portfaults"			{ } // Verilog-XL compatibility
  "`enable_portfaults"			{ } // Verilog-XL compatibility
  "`endcelldefine"			{ V3Read::inCellDefine(false); }
  "`endprotect"				{ }
  "`expand_vectornets"			{ } // Verilog-XL compatibility
  "`inline"				{ }
  "`line"{ws}+[^\n]*\n			{ V3Read::ppline(yytext); }
  "`noaccelerate"			{ } // Verilog-XL compatibility
  "`noexpand_vectornets"		{ } // Verilog-XL compatibility
  "`noremove_gatenames"			{ } // Verilog-XL compatibility
  "`noremove_netnames"			{ } // Verilog-XL compatibility
  "`nosuppress_faults"			{ } // Verilog-XL compatibility
  "`nounconnected_drive"		{ } // Verilog-XL compatibility
  "`portcoerce"				{ }
  "`protect"				{ }
  "`psl"				{ if (V3Read::optPsl()) { BEGIN PSL; } else { BEGIN IGNORE; } }
  "`remove_gatenames"			{ } // Verilog-XL compatibility
  "`remove_netnames"			{ } // Verilog-XL compatibility
  "`resetall"				{ }
  "`suppress_faults"			{ } // Verilog-XL compatibility
  "`systemc_ctor"			{ BEGIN SYSCCTOR; }
  "`systemc_dtor"			{ BEGIN SYSCDTOR; }
  "`systemc_header"			{ BEGIN SYSCHDR; }
  "`systemc_imp_header"			{ BEGIN SYSCIMPH; }
  "`systemc_implementation"		{ BEGIN SYSCIMP; }
  "`systemc_interface"			{ BEGIN SYSCINT; }
  "`timescale"{ws}+[^\n]*		{ } // Verilog spec - not supported
  "`verilog"				{ BEGIN V3Read::lastVerilogState(); }

  "`begin_keywords"[ \t]*\"1364-1995\"		{ yy_push_state(V95); V3Read::pushBeginKeywords(YY_START);}
  "`begin_keywords"[ \t]*\"1364-2001\"		{ yy_push_state(V01); V3Read::pushBeginKeywords(YY_START);}
  "`begin_keywords"[ \t]*\"1364-2001-noconfig\"	{ yy_push_state(V01); V3Read::pushBeginKeywords(YY_START);}
  "`begin_keywords"[ \t]*\"1364-2005\"		{ yy_push_state(V05); V3Read::pushBeginKeywords(YY_START);}
  "`begin_keywords"[ \t]*\"1800-2005\"		{ yy_push_state(S05); V3Read::pushBeginKeywords(YY_START);}
  "`end_keywords"				{ yy_pop_state(); if (!V3Read::popBeginKeywords()) yyerrorf("`end_keywords when not inside `begin_keywords block"); }
}

<SYSCHDR>[ \t]*[^` \t\n][^\n]*\n	{ NEXTLINE(); yylval.strp = V3Read::newString(yytext); return yaSCHDR;}
<SYSCINT>[ \t]*[^` \t\n][^\n]*\n	{ NEXTLINE(); yylval.strp = V3Read::newString(yytext); return yaSCINT;}
<SYSCIMP>[ \t]*[^` \t\n][^\n]*\n	{ NEXTLINE(); yylval.strp = V3Read::newString(yytext); return yaSCIMP;}
<SYSCIMPH>[ \t]*[^` \t\n][^\n]*\n	{ NEXTLINE(); yylval.strp = V3Read::newString(yytext); return yaSCIMPH;}
<SYSCCTOR>[ \t]*[^` \t\n][^\n]*\n	{ NEXTLINE(); yylval.strp = V3Read::newString(yytext); return yaSCCTOR;}
<SYSCDTOR>[ \t]*[^` \t\n][^\n]*\n	{ NEXTLINE(); yylval.strp = V3Read::newString(yytext); return yaSCDTOR;}
<IGNORE>[ \t]*[^` \t\n][^\n]*\n		{ NEXTLINE(); }

  /* Pick up text-type data */
<SYSCHDR,SYSCINT,SYSCIMP,SYSCIMPH,SYSCCTOR,SYSCDTOR,IGNORE>{
  {wsnr}*		{ yymore();}
  \n			{ NEXTLINE(); yymore();}
  \r			;
}

  /************************************************************************/
  /* Default rules - leave last */

<V95,V01,V05,S05,PSL>{
  "`"[a-zA-Z_0-9]+	{ yyerrorf("Define or directive not defined: %s",yytext); }
  "//"[^\n]*		{ }  /* throw away single line comments */
  .			{yylval.fileline = CRELINE(); return yytext[0];}	/* return single char ops. */
}

  /* Catch all - absolutely last */
<*>.|\n     		{ yyerrorf("Missing verilog.l rule: Default rule invoked in state %d: %s", YY_START, yytext); }
%%
int V3Read::stateVerilogRecent() { return STATE_VERILOG_RECENT; }
