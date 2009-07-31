/* -*- C++ -*- */
/**************************************************************************
 * DESCRIPTION: Verilator: Flex verilog preprocessor
 *
 * Code available from: http://www.veripool.org/verilator
 *
 **************************************************************************
 *
 * Copyright 2003-2009 by Wilson Snyder.  This program is free software; you can
 * redistribute it and/or modify it under the terms of either the GNU
 * General Public License or the Perl Artistic License.
 *
 * Verilator is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 **************************************************************************
 * Do not use Flex in C++ mode.  It has bugs with yyunput() which result in
 * lost characters.
 **************************************************************************/

%option noyywrap align interactive
%option stack
%option noc++
%option prefix="V3PreLex"
%{

#include "V3PreProc.h"
#include "V3PreLex.h"

V3PreLex* V3PreLex::s_currentLexp = NULL;	// Current lexing point

// Prevent conflicts from perl version
static void linenoInc()  {V3PreLex::s_currentLexp->incLineno();}
static bool optPsl() { return V3PreProc::optPsl(); }
static bool pedantic() { return V3PreLex::s_currentLexp->m_pedantic; }
static void yyerror(char* msg) { V3PreLex::s_currentLexp->m_curFilelinep->v3error(msg); }
static void yyerrorf(const char* msg) { V3PreLex::s_currentLexp->m_curFilelinep->v3error(msg); }
static void appendDefValue(const char* t,int l) { V3PreLex::s_currentLexp->appendDefValue(t,l); }
static int  pslParenLevel()    { return V3PreLex::s_currentLexp->m_pslParenLevel; }
static void pslParenLevelInc() { V3PreLex::s_currentLexp->m_pslParenLevel++; }
static void pslParenLevelDec() { if (pslParenLevel()) V3PreLex::s_currentLexp->m_pslParenLevel--; }
static bool pslMoreNeeded()    { return V3PreLex::s_currentLexp->m_pslMoreNeeded; }
static void pslMoreNeeded(bool flag) { V3PreLex::s_currentLexp->m_pslMoreNeeded = flag; }

/**********************************************************************/
%}

%x PSLONEM
%x PSLONEE
%x PSLMULM
%x PSLMUL1
%x CMTONEM
%x CMTBEGM
%x CMTMODE
%x STRMODE
%x DEFFPAR
%x DEFFORM
%x DEFVAL
%x ARGMODE
%x INCMODE
%x PRTMODE

/* drop: Drop Ctrl-Z - can't pass thru or may EOF the output too soon */

ws		[ \t\f\r]
wsn		[ \t\f]
crnl		[\r]*[\n]
quote		[\"]
backslash	[\\]
symb		([a-zA-Z_][a-zA-Z0-9_$]*|\\[^ \t\f\r\n]+)
drop		[\032]
psl		[p]sl

	/**************************************************************/
%%

<INITIAL>^{ws}*"`line"{ws}+.*{crnl}	{ V3PreLex::s_currentLexp->lineDirective(yytext);
					  return(VP_LINE); }

	/* Special directives we recognize */
<INITIAL>"`include"	{ return(VP_INCLUDE); }
<INITIAL>"`ifdef"	{ return(VP_IFDEF); }
<INITIAL>"`ifndef"	{ return(VP_IFNDEF); }
<INITIAL>"`else"	{ return(VP_ELSE); }
<INITIAL>"`elsif"	{ return(VP_ELSIF); }
<INITIAL>"`endif"	{ return(VP_ENDIF); }
<INITIAL>"`undef"	{ return(VP_UNDEF); }
<INITIAL>"`define"	{ return(VP_DEFINE); }

	/* Optional directives we recognize */
<INITIAL>"`__FILE__"	{ if (!pedantic()) {
			     static string rtnfile;
			     rtnfile = '"'; rtnfile += V3PreLex::s_currentLexp->m_curFilelinep->cfilename();
			     rtnfile += '"'; yytext=(char*)rtnfile.c_str(); yyleng = rtnfile.length();
			     return (VP_STRING);
	                  } else return(VP_DEFREF); }
<INITIAL>"`__LINE__"	{ if (!pedantic()) {
	                     static char buf[10];
			     sprintf(buf, "%d",V3PreLex::s_currentLexp->m_curFilelinep->lineno());
	                     yytext = buf; yyleng = strlen(yytext); return (VP_TEXT);
	                  } else return(VP_DEFREF); }
<INITIAL>"`error"	{ if (!pedantic()) return (VP_ERROR); else return(VP_DEFREF); }

	/* Pass-through strings */
<INITIAL,PSLMULM,PSLONEM>{quote}	{ yy_push_state(STRMODE); yymore(); }
<STRMODE><<EOF>>	{ linenoInc(); yyerrorf("EOF in unterminated string"); yyleng=0; yyterminate(); }
<STRMODE>{crnl}		{ linenoInc(); yyerrorf("Unterminated string"); BEGIN(INITIAL); }
<STRMODE>[^\"\\]	{ yymore(); }
<STRMODE>{backslash}.	{ yymore(); }
<STRMODE>{quote} 	{ yy_pop_state();
			  if (V3PreLex::s_currentLexp->m_parenLevel) appendDefValue(yytext,yyleng);
			  else return (VP_STRING); }

	/* Protected blocks */
<INITIAL>"`protected"	{ yy_push_state(PRTMODE); yymore(); }
<PRTMODE><<EOF>>	{ linenoInc(); yyerrorf("EOF in `protected"); yyleng=0; yyterminate(); }
<PRTMODE>{crnl}		{ linenoInc(); yymore(); }
<PRTMODE>.	 	{ yymore(); }
<PRTMODE>"`endprotected" { yy_pop_state(); return (VP_TEXT); }

	/* Pass-through include <> filenames */
<INCMODE><<EOF>>	{ linenoInc(); yyerrorf("EOF in unterminated include filename"); yyleng=0; yyterminate(); }
<INCMODE>{crnl}		{ linenoInc(); yyerrorf("Unterminated include filename"); BEGIN(INITIAL); }
<INCMODE>[^\>\\]	{ yymore(); }
<INCMODE>{backslash}.	{ yymore(); }
<INCMODE>[\>]	 	{ yy_pop_state(); return (VP_STRING); }

	/* Reading definition formal parenthesis (or not) to begin formal arguments */
	/* Note '(' must IMMEDIATELY follow definition name */
<DEFFPAR>[(]		{ appendDefValue("(",1); BEGIN(DEFFORM); }
<DEFFPAR>{crnl}		{ yy_pop_state(); unput('\n'); yyleng=0; return VP_DEFFORM; } /* DEFVAL will later grab the return */
<DEFFPAR>.		{ yy_pop_state(); unput(yytext[yyleng-1]); yyleng=0; return VP_DEFFORM; }  /* empty formals */
 
	/* Reading definition formals */
<DEFFORM>[(]		{ yy_pop_state(); yyerrorf("Extra ( in define formal arguments.\n"); yyleng=0; return VP_DEFFORM; }
<DEFFORM>[)]		{ yy_pop_state(); appendDefValue(yytext,yyleng); yyleng=0; return VP_DEFFORM; }
<DEFFORM>"/*"		{ yy_push_state(CMTMODE); yymore(); }
<DEFFORM>"//"[^\n\r]*	{ return (VP_COMMENT);}
<DEFFORM>{drop}	{ }
<DEFFORM><<EOF>>	{ linenoInc(); yy_pop_state(); yyerrorf("Unterminated ( in define formal arguments."); yyleng=0; return VP_DEFFORM; }
<DEFFORM>{crnl}		{ linenoInc(); appendDefValue((char*)"\n",1); } /* Include return so can maintain output line count */
<DEFFORM>[\\]{crnl}	{ linenoInc(); appendDefValue((char*)"\n",1); } /* Include return so can maintain output line count */
<DEFFORM>[^\/\*\n\r\\()]+	|
<DEFFORM>[\\][^\n\r]	|
<DEFFORM>.		{ appendDefValue(yytext,yyleng); }

	/* Reading definition value */
<DEFVAL>"/*"		{ yy_push_state(CMTMODE); yymore(); }
<DEFVAL>"//"[^\n\r]*	{ return (VP_COMMENT);}
<DEFVAL>{drop}		{ }
<DEFVAL><<EOF>>		{ linenoInc(); yy_pop_state(); yytext=(char*)"\n"; yyleng=1; return (VP_DEFVALUE); } /* Technically illegal, but people complained */
<DEFVAL>{crnl}		{ linenoInc(); yy_pop_state(); yytext=(char*)"\n"; yyleng=1; return (VP_DEFVALUE); }
<DEFVAL>[\\]{crnl}	{ linenoInc(); appendDefValue((char*)"\n",1); } /* Include return so can maintain output line count */
<DEFVAL>[^\/\*\n\r\\]+	|
<DEFVAL>[\\][^\n\r]	|
<DEFVAL>.		{ appendDefValue(yytext,yyleng); }

	/* Define arguments */
<ARGMODE>"/*"		{ yy_push_state(CMTMODE); yymore(); }
<ARGMODE>"//"[^\n\r]*	{ return (VP_COMMENT);}
<ARGMODE>{drop}		{ }
<ARGMODE><<EOF>>	{ yyerrorf("EOF in define argument list\n"); yyleng = 0; yyterminate(); }
<ARGMODE>{crnl}		{ linenoInc(); yytext=(char*)"\n"; yyleng=1; return(VP_WHITE); }
<ARGMODE>{quote}	{ yy_push_state(STRMODE); yymore(); }
<ARGMODE>[{\[]		{ V3PreLex::s_currentLexp->m_parenLevel++;
			  appendDefValue(yytext,yyleng); }
<ARGMODE>[}\]]		{ V3PreLex::s_currentLexp->m_parenLevel--;
			  appendDefValue(yytext,yyleng); }
<ARGMODE>[(]		{ V3PreLex::s_currentLexp->m_parenLevel++;
			  // Note paren level 0 means before "(" of starting args
			  // Level 1 means "," between arguments
			  // Level 2+ means one argument's internal ()
			  if (V3PreLex::s_currentLexp->m_parenLevel>1) {
			      appendDefValue(yytext,yyleng);
			  } else {
			      return (VP_TEXT);
			}}
<ARGMODE>[)]		{ V3PreLex::s_currentLexp->m_parenLevel--;
			  if (V3PreLex::s_currentLexp->m_parenLevel>0) {
			      appendDefValue(yytext,yyleng);
			  } else {
			      yy_pop_state(); return (VP_DEFARG);
			}}
<ARGMODE>[,]		{ if (V3PreLex::s_currentLexp->m_parenLevel>1) {
			      appendDefValue(yytext,yyleng);
			  } else {
			      yy_pop_state(); return (VP_DEFARG);
			}}
<ARGMODE>"`"{symb}	{ return (VP_DEFREF); }  /* defref in defref */
<ARGMODE>[^\/\*\n\r\\(,){}\[\]\"`]+	|
<ARGMODE>.		{ appendDefValue(yytext,yyleng); }

	/* One line comments. */
<INITIAL>"//"{ws}*{psl} { if (optPsl())        { pslMoreNeeded(true); yy_push_state(PSLONEM); return(VP_PSL); }
			  else { yy_push_state(CMTONEM); yymore(); } }
<INITIAL>"//"{ws}*{crnl} { linenoInc(); yytext=(char*)"\n"; yyleng=1; return (VP_WHITE); }
<INITIAL>"//" 		{ if (pslMoreNeeded()) { pslMoreNeeded(true); yy_push_state(PSLONEM); return(VP_PSL); }
			  else { yy_push_state(CMTONEM); yymore(); } }
<CMTONEM>[^\n\r]* 	{ yy_pop_state(); return (VP_COMMENT); }

	/* Psl oneline comments */
<PSLONEM>[{(]		{ pslParenLevelInc(); return (VP_TEXT); }
<PSLONEM>[})]		{ pslParenLevelDec(); return (VP_TEXT); }
<PSLONEM>[;]		{ if (!pslParenLevel()) {BEGIN PSLONEE; pslMoreNeeded(false);} return (VP_TEXT); }
<PSLONEM><<EOF>>	{ yyerrorf("EOF in '/* ... */' psl comment\n"); yyleng=0; yyterminate(); }
<PSLONEM>{crnl}		{ linenoInc(); yy_pop_state(); yytext=(char*)"\n"; yyleng=1; return(VP_WHITE); }

	/* Completed psl oneline comments */
<PSLONEE>{crnl}		{ linenoInc(); yy_pop_state(); yytext=(char*)"\n"; yyleng=1; return(VP_WHITE); }
<PSLONEE>{ws}+		{ yymore(); }
<PSLONEE>.		{ yyerrorf("Unexpected text following psl assertion\n"); }

	/* C-style comments. */
	/* We distinguish between the start of a comment, and later, so we may find a "psl" prefix */
<INITIAL>"/*"		{ yy_push_state(optPsl() ? CMTBEGM : CMTMODE); yymore(); }
<CMTBEGM>{psl}		{ yyleng -= 3; BEGIN PSLMUL1; return (VP_COMMENT); }
<CMTBEGM>{ws}+		{ yymore(); }
<CMTBEGM,CMTMODE>"*/"		{ yy_pop_state(); return(VP_COMMENT); }
<CMTBEGM,CMTMODE>{crnl}		{ linenoInc(); yymore(); }
<CMTBEGM,CMTMODE><<EOF>>	{ yyerrorf("EOF in '/* ... */' block comment\n"); yyleng=0; yyterminate(); }
<CMTBEGM>.			{ BEGIN CMTMODE; yymore(); }	/* Non 'psl' beginning in comment */
<CMTMODE>.			{ yymore(); }

	/* Psl C-style comments. */
<PSLMUL1>.|{crnl}	{ yyless(0); BEGIN PSLMULM; return(VP_PSL); }
<PSLMULM>"*/"		{ yy_pop_state(); return(VP_COMMENT); }
<PSLMULM>"//"[^\n\r]*	{ return (VP_COMMENT); }	/* Comments inside block comments get literal inclusion (later removal) */
<PSLMULM><<EOF>>	{ yyerrorf("EOF in '/* ... */' psl comment\n"); yyleng=0; yyterminate(); }

	/* Define calls */
<INITIAL,PSLMULM,PSLONEM>"`"{symb}	{ return (VP_DEFREF); }

	/* Generics */
<INITIAL,PSLMULM>{crnl}		{ linenoInc(); yytext=(char*)"\n"; yyleng=1; return(VP_WHITE); }
<INITIAL,PSLMULM,PSLONEM>{symb}	{ return (VP_SYMBOL); }
<INITIAL,PSLMULM,PSLONEM>{wsn}+	{ return (VP_WHITE); }
<INITIAL,PSLMULM,PSLONEM>{drop}	{ }
<INITIAL,PSLMULM,PSLONEM>[\r]	{ }
<INITIAL,PSLMULM,PSLONEM>.	{ return (VP_TEXT); }
%%

void V3PreLex::pushStateDefArg(int level) {
    // Enter define substitution argument state
    yy_push_state(ARGMODE);
    m_parenLevel = level;
    m_defValue = "";
}

void V3PreLex::pushStateDefForm() {
    // Enter define formal arguments state
    yy_push_state(DEFFPAR);  // First is an optional ( to begin args
    m_parenLevel = 0;
    m_defValue = "";
}

void V3PreLex::pushStateDefValue() {
    // Enter define value state
    yy_push_state(DEFVAL);
    m_parenLevel = 0;
    m_defValue = "";
}

void V3PreLex::pushStateIncFilename() {
    // Enter include <> filename state
    yy_push_state(INCMODE);
    yymore();
}

void V3PreLex::unputString(const char* textp) {
    // Add characters to input stream in back-to-front order
    const char* cp;
    for (cp = textp; *cp; cp++);
    for (cp--; cp >= textp; cp--) {
	unput(*cp);
    }
}

void V3PreLex::appendDefValue(const char* textp, int len) {
    // Append given text to current definition value being formed
    m_defValue.append(textp,len);
}

int V3PreLex::currentStartState() {
    return YY_START;
}

void V3PreLex::lineDirective(const char* textp) {
    m_curFilelinep->lineDirective(textp);
    // Make sure we have a dependency on whatever file was specified
    V3File::addSrcDepend(m_curFilelinep->filename());
}
