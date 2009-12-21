// -*- C++ -*-
//*************************************************************************
// DESCRIPTION: Verilog::Preproc: Internal header for lex interfacing
//
// Code available from: http://www.veripool.org/verilator
//
// Authors: Wilson Snyder
//
//*************************************************************************
//
// Copyright 2000-2009 by Wilson Snyder.  This program is free software;
// you can redistribute it and/or modify it under the terms of either the GNU
// General Public License or the Perl Artistic License.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
//*************************************************************************
// This header provides the interface between the lex proper V3PreLex.l/.cpp
// and the class implementation file V3Pre.cpp
// It is not intended for user applications.
//*************************************************************************

#ifndef _VPREPROCLEX_H_		// Guard
#define _VPREPROCLEX_H_ 1

#include <stack>

#include "V3Error.h"

// Token codes
// If changing, see V3Pre.cpp's V3PreImp::tokenName()
#define VP_EOF		0

#define VP_INCLUDE	256
#define VP_IFDEF	257
#define VP_IFNDEF	258
#define VP_ENDIF	259
#define VP_UNDEF	260
#define VP_DEFINE	261
#define VP_ELSE		262
#define VP_ELSIF	263
#define VP_LINE		264
#define VP_UNDEFINEALL	265

#define VP_SYMBOL	300
#define VP_STRING	301
#define VP_DEFVALUE	302
#define VP_COMMENT	303
#define VP_TEXT		304
#define VP_WHITE	305
#define VP_DEFREF	306
#define VP_DEFARG	307
#define VP_ERROR	308
#define VP_DEFFORM	309

#define VP_PSL		350


//======================================================================
// Externs created by flex
// We add a prefix so that other lexers/flexers in the same program won't collide.
#ifndef yy_create_buffer
# define yy_create_buffer V3PreLex_create_buffer
# define yy_delete_buffer V3PreLex_delete_buffer
# define yy_scan_buffer V3PreLex_scan_buffer
# define yy_scan_string V3PreLex_scan_string
# define yy_scan_bytes V3PreLex_scan_bytes
# define yy_flex_debug V3PreLex_flex_debug
# define yy_init_buffer V3PreLex_init_buffer
# define yy_flush_buffer V3PreLex_flush_buffer
# define yy_load_buffer_state V3PreLex_load_buffer_state
# define yy_switch_to_buffer V3PreLex_switch_to_buffer
# define yyin V3PreLexin
# define yyleng V3PreLexleng
# define yylex V3PreLexlex
# define yyout V3PreLexout
# define yyrestart V3PreLexrestart
# define yytext V3PreLextext
# define yyerror V3PreLexerror
# define yyerrorf V3PreLexerrorf
#endif

#ifndef YY_BUFFER_STATE
struct yy_buffer_state;
typedef struct yy_buffer_state *YY_BUFFER_STATE;
# define YY_BUF_SIZE 16384
#endif

extern int yylex();
extern void yyrestart(FILE*);
extern char* yytext;
extern int yyleng;
YY_BUFFER_STATE yy_create_buffer ( FILE *file, int size );
void yy_switch_to_buffer( YY_BUFFER_STATE new_buffer );
void yy_delete_buffer( YY_BUFFER_STATE b );

//======================================================================
// Class entry for each per-lexter state

#define KEEPCMT_SUB 2

class V3PreLex {
  public:	// Used only by V3PreLex.cpp and V3PreProc.cpp
    FileLine*	m_curFilelinep;	// Current processing point

    // Parse state
    FILE*	m_fp;		// File state is for
    stack<YY_BUFFER_STATE> m_bufferStack; // Stack of inserted text above current point

    // State to lexer
    static V3PreLex* s_currentLexp;	// Current lexing point
    int		m_keepComments;	// Emit comments in output text
    bool	m_pedantic;	// Obey standard; don't Substitute `__FILE__ and `__LINE__

    // State from lexer
    int		m_parenLevel;	// Parenthesis counting inside def args
    int		m_pslParenLevel;// PSL Parenthesis (){} counting, so we can find final ;
    bool	m_pslMoreNeeded;// Next // comment is really psl
    string	m_defValue;	// Definition value being built.

    // CONSTRUCTORS
    V3PreLex(FILE* fp) {
	m_fp = fp;
	m_keepComments = 0;
	m_pedantic = false;
	m_parenLevel = 0;
	m_pslParenLevel = 0;
	m_pslMoreNeeded = false;
	m_bufferStack.push(yy_create_buffer (fp, YY_BUF_SIZE));
	yy_switch_to_buffer(m_bufferStack.top());
    }
    ~V3PreLex() {
	fclose(m_fp);
	while (!m_bufferStack.empty()) { yy_delete_buffer(m_bufferStack.top()); m_bufferStack.pop(); }
    }

    // Called by V3PreLex.l from lexer
    void appendDefValue(const char* text, int len);
    void lineDirective(const char* text);
    void incLineno() { m_curFilelinep->incLineno(); }
    // Called by V3PreProc.cpp to inform lexer
    void pushStateDefArg(int level);
    void pushStateDefForm();
    void pushStateDefValue();
    void pushStateIncFilename();
    void scanBytes(const string& strg);
    /// Called by VPreproc.cpp to get data from lexer
    YY_BUFFER_STATE currentBuffer();
    int	 currentStartState();
    void dumpStack();
};

#endif // Guard
