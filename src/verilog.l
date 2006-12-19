/* $Id$ -*- C++ -*- */
/**************************************************************************
 * DESCRIPTION: Verilator: Flex input file
 *
 * Code available from: http://www.veripool.com/verilator
 *
 **************************************************************************
 *
 * Copyright 2003-2006 by Wilson Snyder.  This program is free software; you can
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

%s VLG PSL STRING   SYSCHDR SYSCINT SYSCIMP SYSCIMPH SYSCCTOR SYSCDTOR  IGNORE

ws	[ \t\f\r]+
	/* identifier */
id	[a-zA-Z_][a-zA-Z0-9_$]*
	/* escaped identifier */
escid	\\[^ \t\f\r\n]+

%%

<INITIAL>.|\n 		{BEGIN VLG; yyless(0); }

<VLG,PSL>{ws}		;			/* ignore white-space */
<VLG,PSL>\n		{NEXTLINE();}		/* Count line numbers */
<VLG,PSL>always		{yylval.fileline = CRELINE(); return yALWAYS;}
<VLG,PSL>always_comb	{yylval.fileline = CRELINE(); return yALWAYS;}
<VLG,PSL>always_ff	{yylval.fileline = CRELINE(); return yALWAYS;}
<VLG,PSL>always_latch	{yylval.fileline = CRELINE(); return yALWAYS;}
<VLG,PSL>and		{yylval.fileline = CRELINE(); return yAND;}
<VLG,PSL>assign		{yylval.fileline = CRELINE(); return yASSIGN;}
<VLG,PSL>begin		{yylval.fileline = CRELINE(); return yBBEGIN;}
<VLG,PSL>buf		{yylval.fileline = CRELINE(); return yBUF;}
<VLG,PSL>case		{yylval.fileline = CRELINE(); return yCASE;}
<VLG,PSL>casex		{yylval.fileline = CRELINE(); return yCASEX;}
<VLG,PSL>casez		{yylval.fileline = CRELINE(); return yCASEZ;}
<VLG,PSL>default	{yylval.fileline = CRELINE(); return yDEFAULT;}
<VLG,PSL>defparam	{yylval.fileline = CRELINE(); return yDEFPARAM;}
<VLG,PSL>else		{yylval.fileline = CRELINE(); return yELSE;}
<VLG,PSL>end		{yylval.fileline = CRELINE(); return yBEND;}
<VLG,PSL>endcase	{yylval.fileline = CRELINE(); return yENDCASE;}
<VLG,PSL>endfunction	{yylval.fileline = CRELINE(); return yENDFUNCTION;}
<VLG,PSL>endgenerate	{yylval.fileline = CRELINE(); return yENDGENERATE;}
<VLG,PSL>endmodule	{yylval.fileline = CRELINE(); return yENDMODULE;}
<VLG,PSL>endspecify	{yylval.fileline = CRELINE(); return yENDSPECIFY;}
<VLG,PSL>endtask	{yylval.fileline = CRELINE(); return yENDTASK;}
<VLG,PSL>final		{yylval.fileline = CRELINE(); return yFINAL;}
<VLG,PSL>for		{yylval.fileline = CRELINE(); return yFOR;}
<VLG,PSL>function	{yylval.fileline = CRELINE(); return yFUNCTION;}
<VLG,PSL>generate	{yylval.fileline = CRELINE(); return yGENERATE;}
<VLG,PSL>genvar		{yylval.fileline = CRELINE(); return yGENVAR;}
<VLG,PSL>if		{yylval.fileline = CRELINE(); return yIF;}
<VLG,PSL>initial	{yylval.fileline = CRELINE(); return yINITIAL;}
<VLG,PSL>inout		{yylval.fileline = CRELINE(); return yINOUT;}
<VLG,PSL>input		{yylval.fileline = CRELINE(); return yINPUT;}
<VLG,PSL>integer	{yylval.fileline = CRELINE(); return yINTEGER;}
<VLG,PSL>localparam	{yylval.fileline = CRELINE(); return yLOCALPARAM;}
<VLG,PSL>macromodule	{yylval.fileline = CRELINE(); return yMODULE;}
<VLG,PSL>module		{yylval.fileline = CRELINE(); return yMODULE;}
<VLG,PSL>nand		{yylval.fileline = CRELINE(); return yNAND;}
<VLG,PSL>negedge	{yylval.fileline = CRELINE(); return yNEGEDGE;}
<VLG,PSL>nor		{yylval.fileline = CRELINE(); return yNOR;}
<VLG,PSL>not		{yylval.fileline = CRELINE(); return yNOT;}
<VLG,PSL>or		{yylval.fileline = CRELINE(); return yOR;}
<VLG,PSL>output		{yylval.fileline = CRELINE(); return yOUTPUT;}
<VLG,PSL>parameter	{yylval.fileline = CRELINE(); return yPARAM;}
<VLG,PSL>posedge	{yylval.fileline = CRELINE(); return yPOSEDGE;}
<VLG,PSL>reg		{yylval.fileline = CRELINE(); return yREG;}
<VLG,PSL>scalared	{yylval.fileline = CRELINE(); return ySCALARED;}
<VLG,PSL>signed		{yylval.fileline = CRELINE(); return ySIGNED;}
<VLG,PSL>specify	{yylval.fileline = CRELINE(); return ySPECIFY;}
<VLG,PSL>specparam	{yylval.fileline = CRELINE(); return yTIMINGSPEC;}
<VLG,PSL>supply0	{yylval.fileline = CRELINE(); return ySUPPLY0;}
<VLG,PSL>supply1	{yylval.fileline = CRELINE(); return ySUPPLY1;}
<VLG,PSL>task		{yylval.fileline = CRELINE(); return yTASK;}
<VLG,PSL>tri		{yylval.fileline = CRELINE(); return yTRI;}
<VLG,PSL>vectored	{yylval.fileline = CRELINE(); return yVECTORED;}
<VLG,PSL>wire		{yylval.fileline = CRELINE(); return yWIRE;}
<VLG,PSL>xnor		{yylval.fileline = CRELINE(); return yXNOR;}
<VLG,PSL>xor		{yylval.fileline = CRELINE(); return yXOR;}
<VLG,PSL>"$bits"	{yylval.fileline = CRELINE(); return yD_BITS;}
<VLG,PSL>"$c"[0-9]*	{yylval.fileline = CRELINE(); return yD_C;}
<VLG,PSL>"$countones"	{yylval.fileline = CRELINE(); return yD_COUNTONES;}
<VLG,PSL>"$display"	{yylval.fileline = CRELINE(); return yD_DISPLAY;}
<VLG,PSL>"$fclose"	{yylval.fileline = CRELINE(); return yD_FCLOSE;}
<VLG,PSL>"$fdisplay"	{yylval.fileline = CRELINE(); return yD_FDISPLAY;}
<VLG,PSL>"$finish"	{yylval.fileline = CRELINE(); return yD_FINISH;}
<VLG,PSL>"$fopen"	{yylval.fileline = CRELINE(); return yD_FOPEN;}
<VLG,PSL>"$fullskew"	{yylval.fileline = CRELINE(); return yTIMINGSPEC;}
<VLG,PSL>"$fwrite"	{yylval.fileline = CRELINE(); return yD_FWRITE;}
<VLG,PSL>"$hold"	{yylval.fileline = CRELINE(); return yTIMINGSPEC;}
<VLG,PSL>"$isunknown"	{yylval.fileline = CRELINE(); return yD_ISUNKNOWN;}
<VLG,PSL>"$nochange"	{yylval.fileline = CRELINE(); return yTIMINGSPEC;}
<VLG,PSL>"$onehot"	{yylval.fileline = CRELINE(); return yD_ONEHOT;}
<VLG,PSL>"$onehot0"	{yylval.fileline = CRELINE(); return yD_ONEHOT0;}
<VLG,PSL>"$period"	{yylval.fileline = CRELINE(); return yTIMINGSPEC;}
<VLG,PSL>"$realtime"	{yylval.fileline = CRELINE(); return yD_TIME;}
<VLG,PSL>"$readmemb"	{yylval.fileline = CRELINE(); return yD_READMEMB;}
<VLG,PSL>"$readmemh"	{yylval.fileline = CRELINE(); return yD_READMEMH;}
<VLG,PSL>"$recovery"	{yylval.fileline = CRELINE(); return yTIMINGSPEC;}
<VLG,PSL>"$recrem"	{yylval.fileline = CRELINE(); return yTIMINGSPEC;}
<VLG,PSL>"$removal"	{yylval.fileline = CRELINE(); return yTIMINGSPEC;}
<VLG,PSL>"$setup"	{yylval.fileline = CRELINE(); return yTIMINGSPEC;}
<VLG,PSL>"$setuphold"	{yylval.fileline = CRELINE(); return yTIMINGSPEC;}
<VLG,PSL>"$signed"	{yylval.fileline = CRELINE(); return yD_SIGNED;}
<VLG,PSL>"$skew"	{yylval.fileline = CRELINE(); return yTIMINGSPEC;}
<VLG,PSL>"$stop"	{yylval.fileline = CRELINE(); return yD_STOP;}
<VLG,PSL>"$time"	{yylval.fileline = CRELINE(); return yD_TIME;}
<VLG,PSL>"$timeskew"	{yylval.fileline = CRELINE(); return yTIMINGSPEC;}
<VLG,PSL>"$unsigned"	{yylval.fileline = CRELINE(); return yD_UNSIGNED;}
<VLG,PSL>"$width"	{yylval.fileline = CRELINE(); return yTIMINGSPEC;}
<VLG,PSL>"$write"	{yylval.fileline = CRELINE(); return yD_WRITE;}
<VLG,PSL>"$"[a-zA-Z_$]+ {yyerrorf("Unsupported or unknown PLI call: %s",yytext);}

 /*PSL Implemented */
<VLG>psl		{ BEGIN PSL; yylval.fileline = CRELINE(); return yPSL; }
<PSL>psl		{ ; }	// 'psl' may occur in middle of statement, so easier just to suppress

<PSL>assert		{yylval.fileline = CRELINE(); return yASSERT;}
<PSL>assume		{yylval.fileline = CRELINE(); return yASSERT;} //==assert
<PSL>before_!		{yyerrorf("Illegal syntax, use before!_ instead of %s",yytext);}
<PSL>clock		{yylval.fileline = CRELINE(); return yCLOCK;}
<PSL>countones		{yylval.fileline = CRELINE(); return yD_COUNTONES;}
<PSL>cover		{yylval.fileline = CRELINE(); return yCOVER;}
<PSL>isunknown		{yylval.fileline = CRELINE(); return yD_ISUNKNOWN;}
<PSL>onehot		{yylval.fileline = CRELINE(); return yD_ONEHOT; }
<PSL>onehot0		{yylval.fileline = CRELINE(); return yD_ONEHOT0; }
<PSL>until_!		{yyerrorf("Illegal syntax, use until!_ instead of %s",yytext);}
<PSL>report		{yylval.fileline = CRELINE(); return yREPORT; }
<PSL>true		{yylval.fileline = CRELINE(); return yTRUE; }

 /*Verilog Reserved*/
<VLG,PSL>bufif0		{yyerrorf("Unsupported: Verilog reserved word not implemented: %s",yytext);}
<VLG,PSL>bufif1		{yyerrorf("Unsupported: Verilog reserved word not implemented: %s",yytext);}
<VLG,PSL>cmos		{yyerrorf("Unsupported: Verilog reserved word not implemented: %s",yytext);}
<VLG,PSL>deassign	{yyerrorf("Unsupported: Verilog reserved word not implemented: %s",yytext);}
<VLG,PSL>disable	{yyerrorf("Unsupported: Verilog reserved word not implemented: %s",yytext);}
<VLG,PSL>endprimitive	{yyerrorf("Unsupported: Verilog reserved word not implemented: %s",yytext);}
<VLG,PSL>endtable	{yyerrorf("Unsupported: Verilog reserved word not implemented: %s",yytext);}
<VLG,PSL>event		{yyerrorf("Unsupported: Verilog reserved word not implemented: %s",yytext);}
<VLG,PSL>force		{yyerrorf("Unsupported: Verilog reserved word not implemented: %s",yytext);}
<VLG,PSL>forever	{yyerrorf("Unsupported: Verilog reserved word not implemented: %s",yytext);}
<VLG,PSL>fork		{yyerrorf("Unsupported: Verilog reserved word not implemented: %s",yytext);}
<VLG,PSL>highz0		{yyerrorf("Unsupported: Verilog reserved word not implemented: %s",yytext);}
<VLG,PSL>highz1		{yyerrorf("Unsupported: Verilog reserved word not implemented: %s",yytext);}
<VLG,PSL>join		{yyerrorf("Unsupported: Verilog reserved word not implemented: %s",yytext);}
<VLG,PSL>large		{yyerrorf("Unsupported: Verilog reserved word not implemented: %s",yytext);}
<VLG,PSL>medium		{yyerrorf("Unsupported: Verilog reserved word not implemented: %s",yytext);}
<VLG,PSL>nmos		{yyerrorf("Unsupported: Verilog reserved word not implemented: %s",yytext);}
<VLG,PSL>notif0		{yyerrorf("Unsupported: Verilog reserved word not implemented: %s",yytext);}
<VLG,PSL>notif1		{yyerrorf("Unsupported: Verilog reserved word not implemented: %s",yytext);}
<VLG,PSL>pmos		{yyerrorf("Unsupported: Verilog reserved word not implemented: %s",yytext);}
<VLG,PSL>primitive	{yyerrorf("Unsupported: Verilog reserved word not implemented: %s",yytext);}
<VLG,PSL>pulldown	{yyerrorf("Unsupported: Verilog reserved word not implemented: %s",yytext);}
<VLG,PSL>pullup		{yyerrorf("Unsupported: Verilog reserved word not implemented: %s",yytext);}
<VLG,PSL>pull0		{yyerrorf("Unsupported: Verilog reserved word not implemented: %s",yytext);}
<VLG,PSL>pull1		{yyerrorf("Unsupported: Verilog reserved word not implemented: %s",yytext);}
<VLG,PSL>rcmos		{yyerrorf("Unsupported: Verilog reserved word not implemented: %s",yytext);}
<VLG,PSL>real		{yyerrorf("Unsupported: Verilog reserved word not implemented: %s",yytext);}
<VLG,PSL>realtime	{yyerrorf("Unsupported: Verilog reserved word not implemented: %s",yytext);}
<VLG,PSL>release	{yyerrorf("Unsupported: Verilog reserved word not implemented: %s",yytext);}
<VLG,PSL>repeat		{yyerrorf("Unsupported: Verilog reserved word not implemented: %s",yytext);}
<VLG,PSL>rnmos		{yyerrorf("Unsupported: Verilog reserved word not implemented: %s",yytext);}
<VLG,PSL>rpmos		{yyerrorf("Unsupported: Verilog reserved word not implemented: %s",yytext);}
<VLG,PSL>rtran		{yyerrorf("Unsupported: Verilog reserved word not implemented: %s",yytext);}
<VLG,PSL>rtranif0	{yyerrorf("Unsupported: Verilog reserved word not implemented: %s",yytext);}
<VLG,PSL>rtranif1	{yyerrorf("Unsupported: Verilog reserved word not implemented: %s",yytext);}
<VLG,PSL>small		{yyerrorf("Unsupported: Verilog reserved word not implemented: %s",yytext);}
<VLG,PSL>strong0	{yyerrorf("Unsupported: Verilog reserved word not implemented: %s",yytext);}
<VLG,PSL>strong1	{yyerrorf("Unsupported: Verilog reserved word not implemented: %s",yytext);}
<VLG,PSL>table		{yyerrorf("Unsupported: Verilog reserved word not implemented: %s",yytext);}
<VLG,PSL>time		{yyerrorf("Unsupported: Verilog reserved word not implemented: %s",yytext);}
<VLG,PSL>tran		{yyerrorf("Unsupported: Verilog reserved word not implemented: %s",yytext);}
<VLG,PSL>tranif0	{yyerrorf("Unsupported: Verilog reserved word not implemented: %s",yytext);}
<VLG,PSL>tranif1	{yyerrorf("Unsupported: Verilog reserved word not implemented: %s",yytext);}
<VLG,PSL>triand		{yyerrorf("Unsupported: Verilog reserved word not implemented: %s",yytext);}
<VLG,PSL>trior		{yyerrorf("Unsupported: Verilog reserved word not implemented: %s",yytext);}
<VLG,PSL>trireg		{yyerrorf("Unsupported: Verilog reserved word not implemented: %s",yytext);}
<VLG,PSL>tri0		{yyerrorf("Unsupported: Verilog reserved word not implemented: %s",yytext);}
<VLG,PSL>tri1		{yyerrorf("Unsupported: Verilog reserved word not implemented: %s",yytext);}
<VLG,PSL>wait		{yyerrorf("Unsupported: Verilog reserved word not implemented: %s",yytext);}
<VLG,PSL>wand		{yyerrorf("Unsupported: Verilog reserved word not implemented: %s",yytext);}
<VLG,PSL>weak0		{yyerrorf("Unsupported: Verilog reserved word not implemented: %s",yytext);}
<VLG,PSL>weak1		{yyerrorf("Unsupported: Verilog reserved word not implemented: %s",yytext);}
<VLG,PSL>while		{yyerrorf("Unsupported: Verilog reserved word not implemented: %s",yytext);}
<VLG,PSL>wor		{yyerrorf("Unsupported: Verilog reserved word not implemented: %s",yytext);}

  /* Verilog 2001 */
<VLG,PSL>automatic	{yyerrorf("Unsupported: Verilog 2001 reserved word not implemented: %s",yytext);}
<VLG,PSL>cell		{yyerrorf("Unsupported: Verilog 2001 reserved word not implemented: %s",yytext);}
<VLG,PSL>config		{yyerrorf("Unsupported: Verilog 2001 reserved word not implemented: %s",yytext);}
<VLG,PSL>design		{yyerrorf("Unsupported: Verilog 2001 reserved word not implemented: %s",yytext);}
<VLG,PSL>edge		{yyerrorf("Unsupported: Verilog 2001 reserved word not implemented: %s",yytext);}
<VLG,PSL>endconfig	{yyerrorf("Unsupported: Verilog 2001 reserved word not implemented: %s",yytext);}
<VLG,PSL>ifnone		{yyerrorf("Unsupported: Verilog 2001 reserved word not implemented: %s",yytext);}
<VLG,PSL>instance	{yyerrorf("Unsupported: Verilog 2001 reserved word not implemented: %s",yytext);}
<VLG,PSL>liblist	{yyerrorf("Unsupported: Verilog 2001 reserved word not implemented: %s",yytext);}
<VLG,PSL>noshowcancelled	{yyerrorf("Unsupported: Verilog 2001 reserved word not implemented: %s",yytext);}
<VLG,PSL>pulsestyle_ondetect	{yyerrorf("Unsupported: Verilog 2001 reserved word not implemented: %s",yytext);}
<VLG,PSL>pulsestyle_onevent	{yyerrorf("Unsupported: Verilog 2001 reserved word not implemented: %s",yytext);}
<VLG,PSL>showcancelled	{yyerrorf("Unsupported: Verilog 2001 reserved word not implemented: %s",yytext);}
<VLG,PSL>strength	{yyerrorf("Unsupported: Verilog 2001 reserved word not implemented: %s",yytext);}
<VLG,PSL>unsigned	{yyerrorf("Unsupported: Verilog 2001 reserved word not implemented: %s",yytext);}
<VLG,PSL>use		{yyerrorf("Unsupported: Verilog 2001 reserved word not implemented: %s",yytext);}

  /* System Verilog */
<VLG,PSL>alias		{yyerrorf("Unsupported: SystemVerilog reserved word not implemented: %s",yytext);}
<VLG,PSL>assert_strobe	{yyerrorf("Unsupported: SystemVerilog reserved word not implemented: %s",yytext);}
<VLG,PSL>bind		{yyerrorf("Unsupported: SystemVerilog reserved word not implemented: %s",yytext);}
<VLG,PSL>bit		{yyerrorf("Unsupported: SystemVerilog reserved word not implemented: %s",yytext);}
<VLG,PSL>break		{yyerrorf("Unsupported: SystemVerilog reserved word not implemented: %s",yytext);}
<VLG,PSL>byte		{yyerrorf("Unsupported: SystemVerilog reserved word not implemented: %s",yytext);}
<VLG,PSL>chandle	{yyerrorf("Unsupported: SystemVerilog reserved word not implemented: %s",yytext);}
<VLG,PSL>class		{yyerrorf("Unsupported: SystemVerilog reserved word not implemented: %s",yytext);}
<VLG,PSL>clocking	{yyerrorf("Unsupported: SystemVerilog reserved word not implemented: %s",yytext);}
<VLG,PSL>constraint	{yyerrorf("Unsupported: SystemVerilog reserved word not implemented: %s",yytext);}
<VLG,PSL>context	{yyerrorf("Unsupported: SystemVerilog reserved word not implemented: %s",yytext);}
<VLG,PSL>continue	{yyerrorf("Unsupported: SystemVerilog reserved word not implemented: %s",yytext);}
<VLG,PSL>dist		{yyerrorf("Unsupported: SystemVerilog reserved word not implemented: %s",yytext);}
<VLG,PSL>do		{yyerrorf("Unsupported: SystemVerilog reserved word not implemented: %s",yytext);}
<VLG,PSL>endcass	{yyerrorf("Unsupported: SystemVerilog reserved word not implemented: %s",yytext);}
<VLG,PSL>endclocking	{yyerrorf("Unsupported: SystemVerilog reserved word not implemented: %s",yytext);}
<VLG,PSL>endinterface	{yyerrorf("Unsupported: SystemVerilog reserved word not implemented: %s",yytext);}
<VLG,PSL>endprogram	{yyerrorf("Unsupported: SystemVerilog reserved word not implemented: %s",yytext);}
<VLG,PSL>endproperty	{yyerrorf("Unsupported: SystemVerilog reserved word not implemented: %s",yytext);}
<VLG,PSL>endsequence	{yyerrorf("Unsupported: SystemVerilog reserved word not implemented: %s",yytext);}
<VLG,PSL>enum		{yyerrorf("Unsupported: SystemVerilog reserved word not implemented: %s",yytext);}
<VLG,PSL>export		{yyerrorf("Unsupported: SystemVerilog reserved word not implemented: %s",yytext);}
<VLG,PSL>extends	{yyerrorf("Unsupported: SystemVerilog reserved word not implemented: %s",yytext);}
<VLG,PSL>extern		{yyerrorf("Unsupported: SystemVerilog reserved word not implemented: %s",yytext);}
<VLG,PSL>first_match	{yyerrorf("Unsupported: SystemVerilog reserved word not implemented: %s",yytext);}
<VLG,PSL>forkjoin	{yyerrorf("Unsupported: SystemVerilog reserved word not implemented: %s",yytext);}
<VLG,PSL>iff		{yyerrorf("Unsupported: SystemVerilog reserved word not implemented: %s",yytext);}
<VLG,PSL>import		{yyerrorf("Unsupported: SystemVerilog reserved word not implemented: %s",yytext);}
<VLG,PSL>inside		{yyerrorf("Unsupported: SystemVerilog reserved word not implemented: %s",yytext);}
<VLG,PSL>int		{yyerrorf("Unsupported: SystemVerilog reserved word not implemented: %s",yytext);}
<VLG,PSL>interface	{yyerrorf("Unsupported: SystemVerilog reserved word not implemented: %s",yytext);}
<VLG,PSL>intersect	{yyerrorf("Unsupported: SystemVerilog reserved word not implemented: %s",yytext);}
<VLG,PSL>join_any	{yyerrorf("Unsupported: SystemVerilog reserved word not implemented: %s",yytext);}
<VLG,PSL>join_none	{yyerrorf("Unsupported: SystemVerilog reserved word not implemented: %s",yytext);}
<VLG,PSL>local		{yyerrorf("Unsupported: SystemVerilog reserved word not implemented: %s",yytext);}
<VLG,PSL>logic		{yyerrorf("Unsupported: SystemVerilog reserved word not implemented: %s",yytext);}
<VLG,PSL>longint	{yyerrorf("Unsupported: SystemVerilog reserved word not implemented: %s",yytext);}
<VLG,PSL>modport	{yyerrorf("Unsupported: SystemVerilog reserved word not implemented: %s",yytext);}
<VLG,PSL>new		{yyerrorf("Unsupported: SystemVerilog reserved word not implemented: %s",yytext);}
<VLG,PSL>null		{yyerrorf("Unsupported: SystemVerilog reserved word not implemented: %s",yytext);}
<VLG,PSL>packed		{yyerrorf("Unsupported: SystemVerilog reserved word not implemented: %s",yytext);}
<VLG,PSL>priority	{yyerrorf("Unsupported: SystemVerilog reserved word not implemented: %s",yytext);}
<VLG,PSL>program	{yyerrorf("Unsupported: SystemVerilog reserved word not implemented: %s",yytext);}
<VLG,PSL>protected	{yyerrorf("Unsupported: SystemVerilog reserved word not implemented: %s",yytext);}
<VLG,PSL>pure		{yyerrorf("Unsupported: SystemVerilog reserved word not implemented: %s",yytext);}
<VLG,PSL>rand		{yyerrorf("Unsupported: SystemVerilog reserved word not implemented: %s",yytext);}
<VLG,PSL>randc		{yyerrorf("Unsupported: SystemVerilog reserved word not implemented: %s",yytext);}
<VLG,PSL>ref		{yyerrorf("Unsupported: SystemVerilog reserved word not implemented: %s",yytext);}
<VLG,PSL>shortint	{yyerrorf("Unsupported: SystemVerilog reserved word not implemented: %s",yytext);}
<VLG,PSL>shortreal	{yyerrorf("Unsupported: SystemVerilog reserved word not implemented: %s",yytext);}
<VLG,PSL>solve		{yyerrorf("Unsupported: SystemVerilog reserved word not implemented: %s",yytext);}
<VLG,PSL>static		{yyerrorf("Unsupported: SystemVerilog reserved word not implemented: %s",yytext);}
<VLG,PSL>string		{yyerrorf("Unsupported: SystemVerilog reserved word not implemented: %s",yytext);}
<VLG,PSL>struct		{yyerrorf("Unsupported: SystemVerilog reserved word not implemented: %s",yytext);}
<VLG,PSL>super		{yyerrorf("Unsupported: SystemVerilog reserved word not implemented: %s",yytext);}
<VLG,PSL>this		{yyerrorf("Unsupported: SystemVerilog reserved word not implemented: %s",yytext);}
<VLG,PSL>throughout	{yyerrorf("Unsupported: SystemVerilog reserved word not implemented: %s",yytext);}
<VLG,PSL>timeprecision	{yyerrorf("Unsupported: SystemVerilog reserved word not implemented: %s",yytext);}
<VLG,PSL>timeunit	{yyerrorf("Unsupported: SystemVerilog reserved word not implemented: %s",yytext);}
<VLG,PSL>type		{yyerrorf("Unsupported: SystemVerilog reserved word not implemented: %s",yytext);}
<VLG,PSL>typedef	{yyerrorf("Unsupported: SystemVerilog reserved word not implemented: %s",yytext);}
<VLG,PSL>unique		{yyerrorf("Unsupported: SystemVerilog reserved word not implemented: %s",yytext);}
<VLG,PSL>var		{yyerrorf("Unsupported: SystemVerilog reserved word not implemented: %s",yytext);}
<VLG,PSL>virtual	{yyerrorf("Unsupported: SystemVerilog reserved word not implemented: %s",yytext);}
<VLG,PSL>void		{yyerrorf("Unsupported: SystemVerilog reserved word not implemented: %s",yytext);}
<VLG,PSL>wait_order	{yyerrorf("Unsupported: SystemVerilog reserved word not implemented: %s",yytext);}
<VLG,PSL>with		{yyerrorf("Unsupported: SystemVerilog reserved word not implemented: %s",yytext);}

  /* Verilog, also as PSL below PSL */
<VLG>assert		{yyerrorf("Unsupported: SystemVerilog reserved word not implemented in non-PSL context: %s",yytext);}
<VLG>before		{yyerrorf("Unsupported: SystemVerilog reserved word not implemented in non-PSL context: %s",yytext);}
<VLG>const		{yyerrorf("Unsupported: SystemVerilog reserved word not implemented in non-PSL context: %s",yytext);}
<VLG>cover		{yyerrorf("Unsupported: SystemVerilog reserved word not implemented in non-PSL context: %s",yytext);}
<VLG>property		{yyerrorf("Unsupported: SystemVerilog reserved word not implemented in non-PSL context: %s",yytext);}
<VLG>sequence		{yyerrorf("Unsupported: SystemVerilog reserved word not implemented in non-PSL context: %s",yytext);}
<VLG>union		{yyerrorf("Unsupported: SystemVerilog reserved word not implemented in non-PSL context: %s",yytext);}
<VLG>within		{yyerrorf("Unsupported: SystemVerilog reserved word not implemented in non-PSL context: %s",yytext);}

  /* PSL reserved */
 /*<PSL>A		{yyerrorf("Unsupported: PSL branching reserved word not implemented: %s",yytext);} */
 /*<PSL>AF		{yyerrorf("Unsupported: PSL branching reserved word not implemented: %s",yytext);} */
 /*<PSL>AG		{yyerrorf("Unsupported: PSL branching reserved word not implemented: %s",yytext);} */
 /*<PSL>AX		{yyerrorf("Unsupported: PSL branching reserved word not implemented: %s",yytext);} */
 /*<PSL>E		{yyerrorf("Unsupported: PSL branching reserved word not implemented: %s",yytext);} */
 /*<PSL>EF		{yyerrorf("Unsupported: PSL branching reserved word not implemented: %s",yytext);} */
 /*<PSL>EG		{yyerrorf("Unsupported: PSL branching reserved word not implemented: %s",yytext);} */
 /*<PSL>EX		{yyerrorf("Unsupported: PSL branching reserved word not implemented: %s",yytext);} */
 /*<PSL>F		{yylval.fileline = CRELINE(); return yEVENTUALLYB; } */
 /*<PSL>G		{yylval.fileline = CRELINE(); return yALWAYS; } */
 /*<PSL>U		{yylval.fileline = CRELINE(); return yUNTILB; } */
 /*<PSL>W		{yylval.fileline = CRELINE(); return yUNTIL; } */
 /*<PSL>X		{yylval.fileline = CRELINE(); return yNEXT; } */
 /*<PSL>X!		{yylval.fileline = CRELINE(); return yNEXTB; } */
<PSL>%for		{yyerrorf("Unsupported: PSL reserved word not implemented: %s",yytext);}
<PSL>%if		{yyerrorf("Unsupported: PSL reserved word not implemented: %s",yytext);}
<PSL>abort		{yyerrorf("Unsupported: PSL reserved word not implemented: %s",yytext);}
<PSL>assume_guarantee	{yyerrorf("Unsupported: PSL reserved word not implemented: %s",yytext);} //Unsup in other tools
<PSL>before		{yyerrorf("Unsupported: PSL reserved word not implemented: %s",yytext);}
<PSL>before!		{yyerrorf("Unsupported: PSL reserved word not implemented: %s",yytext);}
<PSL>before!_		{yyerrorf("Unsupported: PSL reserved word not implemented: %s",yytext);}
<PSL>before_		{yyerrorf("Unsupported: PSL reserved word not implemented: %s",yytext);}
<PSL>boolean		{yyerrorf("Unsupported: PSL reserved word not implemented: %s",yytext);}
<PSL>const		{yyerrorf("Unsupported: PSL reserved word not implemented: %s",yytext);}
<PSL>endpoint		{yyerrorf("Unsupported: PSL reserved word not implemented: %s",yytext);}
<PSL>eventually!	{yyerrorf("Unsupported: PSL reserved word not implemented: %s",yytext);}
<PSL>fairness		{yyerrorf("Unsupported: PSL reserved word not implemented: %s",yytext);} //Unsup in other tools
<PSL>fell		{yyerrorf("Unsupported: PSL reserved word not implemented: %s",yytext);}
<PSL>forall		{yyerrorf("Unsupported: PSL reserved word not implemented: %s",yytext);} //Unsup in other tools
<PSL>in			{yyerrorf("Unsupported: PSL reserved word not implemented: %s",yytext);}
<PSL>inf		{yyerrorf("Unsupported: PSL reserved word not implemented: %s",yytext);}
<PSL>inherit		{yyerrorf("Unsupported: PSL reserved word not implemented: %s",yytext);} //Unsup in other tools
<PSL>never		{yyerrorf("Unsupported: PSL reserved word not implemented: %s",yytext);}
<PSL>next		{yyerrorf("Unsupported: PSL reserved word not implemented: %s",yytext);}
<PSL>next!		{yyerrorf("Unsupported: PSL reserved word not implemented: %s",yytext);}
<PSL>next_a		{yyerrorf("Unsupported: PSL reserved word not implemented: %s",yytext);}
<PSL>next_a!		{yyerrorf("Unsupported: PSL reserved word not implemented: %s",yytext);}
<PSL>next_e		{yyerrorf("Unsupported: PSL reserved word not implemented: %s",yytext);}
<PSL>next_e!		{yyerrorf("Unsupported: PSL reserved word not implemented: %s",yytext);}
<PSL>next_event		{yyerrorf("Unsupported: PSL reserved word not implemented: %s",yytext);}
<PSL>next_event!	{yyerrorf("Unsupported: PSL reserved word not implemented: %s",yytext);}
<PSL>next_event_a	{yyerrorf("Unsupported: PSL reserved word not implemented: %s",yytext);}
<PSL>next_event_a!	{yyerrorf("Unsupported: PSL reserved word not implemented: %s",yytext);}
<PSL>next_event_e	{yyerrorf("Unsupported: PSL reserved word not implemented: %s",yytext);}
<PSL>next_event_e!	{yyerrorf("Unsupported: PSL reserved word not implemented: %s",yytext);}
<PSL>prev		{yyerrorf("Unsupported: PSL reserved word not implemented: %s",yytext);}
<PSL>property		{yyerrorf("Unsupported: PSL reserved word not implemented: %s",yytext);}
<PSL>restrict		{yyerrorf("Unsupported: PSL reserved word not implemented: %s",yytext);}
<PSL>restrict_guarantee	{yyerrorf("Unsupported: PSL reserved word not implemented: %s",yytext);} //Unsup in other tools
<PSL>rose		{yyerrorf("Unsupported: PSL reserved word not implemented: %s",yytext);}
<PSL>sequence		{yyerrorf("Unsupported: PSL reserved word not implemented: %s",yytext);}
<PSL>stable		{yyerrorf("Unsupported: PSL reserved word not implemented: %s",yytext);}
<PSL>strong		{yyerrorf("Unsupported: PSL reserved word not implemented: %s",yytext);} //Unsup in other tools
<PSL>union		{yyerrorf("Unsupported: PSL reserved word not implemented: %s",yytext);}
<PSL>until		{yyerrorf("Unsupported: PSL reserved word not implemented: %s",yytext);}
<PSL>until!		{yyerrorf("Unsupported: PSL reserved word not implemented: %s",yytext);}
<PSL>until!_		{yyerrorf("Unsupported: PSL reserved word not implemented: %s",yytext);}
<PSL>until_		{yyerrorf("Unsupported: PSL reserved word not implemented: %s",yytext);}
<PSL>vmode		{yyerrorf("Unsupported: PSL reserved word not implemented: %s",yytext);} //Unsup in other tools
<PSL>vprop		{yyerrorf("Unsupported: PSL reserved word not implemented: %s",yytext);} //Unsup in other tools
<PSL>vunit		{yyerrorf("Unsupported: PSL reserved word not implemented: %s",yytext);}
<PSL>within		{yyerrorf("Unsupported: PSL reserved word not implemented: %s",yytext);}

  /* Converted from //{cmt}verilator ...{cmt} by vpp */
<VLG,PSL>"/*verilator clock_enable*/"		{yylval.fileline = CRELINE(); return yVL_CLOCK_ENABLE;}
<VLG,PSL>"/*verilator coverage_block_off*/"	{yylval.fileline = CRELINE(); return yVL_COVER_OFF;}
<VLG,PSL>"/*verilator full_case*/"		{yylval.fileline = CRELINE(); return yVL_FULL_CASE;}
<VLG,PSL>"/*verilator inline_module*/"		{yylval.fileline = CRELINE(); return yVL_INLINE_MODULE;}
<VLG,PSL>"/*verilator no_inline_module*/"	{yylval.fileline = CRELINE(); return yVL_NO_INLINE_MODULE;}
<VLG,PSL>"/*verilator no_inline_task*/"		{yylval.fileline = CRELINE(); return yVL_NO_INLINE_TASK;}
<VLG,PSL>"/*verilator one_cold*/"		{yylval.fileline = CRELINE(); return yVL_ONE_COLD;}
<VLG,PSL>"/*verilator one_hot*/"		{yylval.fileline = CRELINE(); return yVL_ONE_HOT;}
<VLG,PSL>"/*verilator parallel_case*/"		{yylval.fileline = CRELINE(); return yVL_PARALLEL_CASE;}
<VLG,PSL>"/*verilator public*/"			{yylval.fileline = CRELINE(); return yVL_PUBLIC;}
<VLG,PSL>"/*verilator public_module*/"		{yylval.fileline = CRELINE(); return yVL_PUBLIC_MODULE;}
<VLG,PSL>"/*verilator sc_clock*/"		{yylval.fileline = CRELINE(); return yVL_CLOCK;}
<VLG,PSL>"/*verilator systemc_clock*/"		{yylval.fileline = CRELINE(); return yVL_CLOCK;}
<VLG,PSL>"/*verilator tracing_off*/"		{yylval.fileline = CRELINE(); return yVL_TRACING_OFF;}
<VLG,PSL>"/*verilator tracing_on*/"		{yylval.fileline = CRELINE(); return yVL_TRACING_ON;}
<VLG,PSL>"/*verilator lint_off"[^*]*"*/"	{V3Read::verilatorCmtLint(yytext, true); }
<VLG,PSL>"/*verilator lint_on"[^*]*"*/"		{V3Read::verilatorCmtLint(yytext, false); }
<VLG,PSL>"/*"[^*]*"*/"				{V3Read::verilatorCmtBad(yytext); }

<VLG,PSL>"&&"		{yylval.fileline = CRELINE(); return yANDAND;}
<VLG,PSL>"||"		{yylval.fileline = CRELINE(); return yOROR;}
<VLG,PSL>"<="		{yylval.fileline = CRELINE(); return yLTE;}
<VLG,PSL>">="		{yylval.fileline = CRELINE(); return yGTE;}
<VLG,PSL>"<<<"		{yylval.fileline = CRELINE(); return ySLEFT;}
<VLG,PSL>"<<"		{yylval.fileline = CRELINE(); return ySLEFT;}
<VLG,PSL>">>>"		{yylval.fileline = CRELINE(); return ySSRIGHT;}
<VLG,PSL>">>"		{yylval.fileline = CRELINE(); return ySRIGHT;}
<VLG,PSL>"=="		{yylval.fileline = CRELINE(); return yEQUAL;}
<VLG,PSL>"!="		{yylval.fileline = CRELINE(); return yNOTEQUAL;}
<VLG,PSL>"==="		{yylval.fileline = CRELINE(); return yCASEEQUAL;}
<VLG,PSL>"!=="		{yylval.fileline = CRELINE(); return yCASENOTEQUAL;}
<VLG,PSL>"^~"		{yylval.fileline = CRELINE(); return yOP_XNOR;}
<VLG,PSL>"~^"		{yylval.fileline = CRELINE(); return yOP_XNOR;}
<VLG,PSL>"~&"		{yylval.fileline = CRELINE(); return yOP_NAND;}
<VLG,PSL>"~|"		{yylval.fileline = CRELINE(); return yOP_NOR;}
<VLG,PSL>"**"		{yylval.fileline = CRELINE(); return yPOW;}
<VLG,PSL>"+:"		{yylval.fileline = CRELINE(); return yPLUSCOLON;}
<VLG,PSL>"-:"		{yylval.fileline = CRELINE(); return yMINUSCOLON;}

<PSL>"{"		{yylval.fileline = CRELINE(); return yPSL_BRA;}	// Avoid parser hitting concatenate.
<PSL>"}"		{yylval.fileline = CRELINE(); return yPSL_KET;}	// Avoid parser hitting concatenate.
<PSL>"->"		{yylval.fileline = CRELINE(); return yOP_LOGIF;}
<PSL>"<->"		{yyerrorf("Unsupported: PSL operator not implemented: %s",yytext);} //Unsup in other tools
<PSL>"[*"		{yyerrorf("Unsupported: PSL operator not implemented: %s",yytext);} // yBRA_STAR
<PSL>"[*]"		{yyerrorf("Unsupported: PSL operator not implemented: %s",yytext);} // yBRA_STAR_KET
<PSL>"[+]"		{yyerrorf("Unsupported: PSL operator not implemented: %s",yytext);} // yBRA_PLUS_KET
<PSL>"[->"		{yyerrorf("Unsupported: PSL operator not implemented: %s",yytext);} // yBRA_MINUS_GT
<PSL>"[->]"		{yyerrorf("Unsupported: PSL operator not implemented: %s",yytext);} // yBRA_MINUS_GT_KET
<PSL>"[="		{yyerrorf("Unsupported: PSL operator not implemented: %s",yytext);} // yBRA_EQ
<PSL>"|->"		{yyerrorf("Unsupported: PSL operator not implemented: %s",yytext);} // yOR_MINUS_GT
<PSL>"|=>"		{yyerrorf("Unsupported: PSL operator not implemented: %s",yytext);} // yOR_EQ_GT

<VLG,PSL>{escid}	{  int i;
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

<VLG,PSL>{id}		{  yylval.strp = V3Read::newString(yytext);
			   return yID;
			 }

<VLG,PSL>\"[^\"\\]*\"	{  yylval.strp = V3Read::newString(yytext+1,yyleng-2);
			   return ySTRING;
			}
<VLG,PSL>\" 		{ yy_push_state(STRING); yymore(); }


<VLG,PSL>[0-9]*?['']s?[bcodhBCODH][ \t]*[A-Fa-f0-9xXzZ_?]*	{
			  yylval.nump = V3Read::newNumber(V3Read::fileline(),(char*)yytext);
                          return yINTNUM;
			}
<VLG,PSL>[0-9]*?['']s?[01xXzZ]	{	/* SystemVerilog */
			  yylval.nump = V3Read::newNumber(V3Read::fileline(),(char*)yytext);
                          return yINTNUM;
			}
<VLG,PSL>[0-9]+[_0-9]*[ \t]*['']s?[bcodhBCODH]?[ \t]*[A-Fa-f0-9xXzZ_?]*	{
			  yylval.nump = V3Read::newNumber(V3Read::fileline(),(char*)yytext);
                          return yINTNUM;
			}
<VLG,PSL>[0-9]*		{ yylval.nump = V3Read::newNumber(V3Read::fileline(),(char*)yytext);
                          return yINTNUM;
			}
<VLG,PSL>[-+]?[0-9]+(\.[0-9]+)([eE][-+]?[0-9]+)? {
    			  yylval.cdouble = 0;  /* Only for delays, not used yet */
                          return yFLOATNUM;
			}
<VLG,PSL>[-+]?[0-9]+(\.[0-9]+)?([eE][-+]?[0-9]+) {
    			  yylval.cdouble = 0;  /* Only for delays, not used yet */
                          return yFLOATNUM;
			}

<VLG,PSL>"`timescale"{ws}+[^\n]*	{}
<VLG,PSL>"`line"{ws}+[^\n]*\n		{V3Read::ppline(yytext);}

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
<VLG,PSL,SYSCHDR,SYSCINT,SYSCIMP,SYSCIMPH,SYSCCTOR,SYSCDTOR,IGNORE>{
  [ \t]*"`verilog"			{ BEGIN VLG; }
  [ \t]*"`psl"				{ if (V3Read::optPsl()) { BEGIN PSL; } else { BEGIN IGNORE; } }
  [ \t]*"`systemc_header"		{ BEGIN SYSCHDR; }
  [ \t]*"`systemc_ctor"			{ BEGIN SYSCCTOR; }
  [ \t]*"`systemc_dtor"			{ BEGIN SYSCDTOR; }
  [ \t]*"`systemc_interface"		{ BEGIN SYSCINT; }
  [ \t]*"`systemc_implementation"	{ BEGIN SYSCIMP; }
  [ \t]*"`systemc_imp_header"		{ BEGIN SYSCIMPH; }
  "`line"[ \t][^\n]*\n			{V3Read::ppline(yytext);}
}

<SYSCHDR>[ \t]*[^` \t\n][^\n]*\n	{ NEXTLINE(); yylval.strp = V3Read::newString(yytext); return ySCHDR;}
<SYSCINT>[ \t]*[^` \t\n][^\n]*\n	{ NEXTLINE(); yylval.strp = V3Read::newString(yytext); return ySCINT;}
<SYSCIMP>[ \t]*[^` \t\n][^\n]*\n	{ NEXTLINE(); yylval.strp = V3Read::newString(yytext); return ySCIMP;}
<SYSCIMPH>[ \t]*[^` \t\n][^\n]*\n	{ NEXTLINE(); yylval.strp = V3Read::newString(yytext); return ySCIMPH;}
<SYSCCTOR>[ \t]*[^` \t\n][^\n]*\n	{ NEXTLINE(); yylval.strp = V3Read::newString(yytext); return ySCCTOR;}
<SYSCDTOR>[ \t]*[^` \t\n][^\n]*\n	{ NEXTLINE(); yylval.strp = V3Read::newString(yytext); return ySCDTOR;}
<IGNORE>[ \t]*[^` \t\n][^\n]*\n		{ NEXTLINE(); }

<SYSCHDR,SYSCINT,SYSCIMP,SYSCIMPH,SYSCCTOR,SYSCDTOR,IGNORE>[ \t]*\n	{ NEXTLINE(); yymore();}
<SYSCHDR,SYSCINT,SYSCIMP,SYSCIMPH,SYSCCTOR,SYSCDTOR,IGNORE>\r		;

  /************************************************************************/
  /* Default rules - leave last */

<VLG,PSL>"`"[a-zA-Z_0-9]+		{ yyerrorf("Define or directive not defined: %s",yytext); }

<VLG,PSL>"//"[^\n]+	{ }  /* throw away single line comments */

<VLG,PSL>.		{yylval.fileline = CRELINE(); return yytext[0];}	/* return single char ops. */

<*>.|\n     		{ yyerrorf("Missing verilog.l rule: Default rule invoked in state %d: %s", YY_START, yytext); }
%%

