//*************************************************************************
// DESCRIPTION: Verilator: Netlist (top level) functions
//
// Code available from: http://www.veripool.org/verilator
//
// AUTHORS: Wilson Snyder with Paul Wasson, Duane Gabli
//
//*************************************************************************
//
// Copyright 2003-2012 by Wilson Snyder.  This program is free software; you can
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

#include "config_build.h"
#include "verilatedos.h"
#include <cstdio>
#include <cstdarg>
#include <unistd.h>
#include <fstream>

#include "V3Error.h"
#include "V3Global.h"
#include "V3File.h"
#include "V3ParseImp.h"

//======================================================================
// Build in LEX script

#define yyFlexLexer V3LexerBase
#include "V3Lexer.yy.cpp"
#undef yyFlexLexer

//######################################################################
// Lex-derived class

/// Override the base lexer class so we can add some access functions
class V3Lexer : public V3LexerBase {
public:
    // CONSTRUCTORS
    V3Lexer() : V3LexerBase(NULL) {}
    ~V3Lexer() {}
    // METHODS
    void stateExitPsl() {
	if (YY_START != PSL) yyerrorf("Internal error: Exiting PSL state when not in PSL state");
	yy_pop_state();
    }
    void statePushVlg() {
	yy_push_state(STATE_VERILOG_RECENT);
    }
    void statePop() {
	yy_pop_state();
    }
};
void V3ParseImp::stateExitPsl() { parsep()->m_lexerp->stateExitPsl(); }
void V3ParseImp::statePushVlg() { parsep()->m_lexerp->stateExitPsl(); }
void V3ParseImp::statePop()	{ parsep()->m_lexerp->statePop(); }
int V3ParseImp::yylexThis() {     return parsep()->m_lexerp->yylex(); }

//######################################################################
// Read class functions

void V3ParseImp::lexNew(int debug) {
    if (m_lexerp) delete m_lexerp;	// Restart from clean slate.
    m_lexerp = new V3Lexer();
    if (debugFlex()>=9) { m_lexerp->set_debug(~0);  }
}

void V3ParseImp::lexDestroy() {
    if (m_lexerp) { delete m_lexerp; m_lexerp = NULL; }
}
