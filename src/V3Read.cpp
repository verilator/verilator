// $Id$
//*************************************************************************
// DESCRIPTION: Verilator: Netlist (top level) functions
//
// Code available from: http://www.veripool.com/verilator
//
// AUTHORS: Wilson Snyder with Paul Wasson, Duane Gabli
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

#include "config_build.h"
#include "verilatedos.h"
#include <stdio.h>
#include <stdarg.h>
#include <unistd.h>
#include <fstream>

#include "V3Error.h"
#include "V3Global.h"
#include "V3Ast.h"
#include "V3File.h"
#include "V3Read.h"
#include "V3PreShell.h"

//======================================================================
// Build in LEX script

#define yyFlexLexer V3LexerBase
#include "V3Lexer.yy.cpp"
#undef yyFlexLexer

//YYSTYPE yylval;

//======================================================================
// Globals

V3Read*	V3Read::s_readp = NULL;

extern bool yyparse();
extern int yydebug;

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
	if (YY_START != PSL) yyerror("Internal error: Exiting PSL state when not in PSL state");
	yy_pop_state();
    }
    void statePushVlg() {
	yy_push_state(STATE_VERILOG_RECENT);
    }
    void statePop() {
	yy_pop_state();
    }
};
void V3Read::stateExitPsl() { s_readp->m_lexerp->stateExitPsl(); }
void V3Read::statePushVlg() { s_readp->m_lexerp->stateExitPsl(); }
void V3Read::statePop()	    { s_readp->m_lexerp->statePop(); }

//######################################################################
// Read class functions

V3Read::~V3Read() {
    for (deque<string*>::iterator it = m_stringps.begin(); it != m_stringps.end(); ++it) {
	delete (*it);
    }
    m_stringps.clear();
    for (deque<V3Number*>::iterator it = m_numberps.begin(); it != m_numberps.end(); ++it) {
	delete (*it);
    }
    m_numberps.clear();
    if (m_lexerp) { delete m_lexerp; m_lexerp = NULL; }
    parserClear();
}

int V3Read::ppInputToLex(char* buf, int max_size) {
    int got = 0;
    while (got < max_size	// Haven't got enough
	   && !m_ppBuffers.empty()) {	// And something buffered
	string front = m_ppBuffers.front(); m_ppBuffers.pop_front();
	int len = front.length();
	if (len > (max_size-got)) {  // Front string too big
	    string remainder = front.substr(max_size-got);
	    front = front.substr(0, max_size-got);
	    m_ppBuffers.push_front(remainder);  // Put back remainder for next time
	    len = (max_size-got);
	}
	strncpy(buf+got, front.c_str(), len);
	got += len;
    }
    if (debug()>=9) {
	string out = string(buf,got);
	cout<<"   inputToLex  got="<<got<<" '"<<out<<"'"<<endl;
    }
    // Note returns 0 at EOF
    return got;
}

void V3Read::readFile(FileLine* fileline, const string& modfilename, bool inLibrary) {
    string modname = V3Options::filenameNonExt(modfilename);

    UINFO(2,__FUNCTION__<<": "<<modname<<(inLibrary?" [LIB]":"")<<endl);
    m_fileline = new FileLine(fileline);
    m_inLibrary = inLibrary;

    // Preprocess into m_ppBuffer
    V3PreShell::preproc(fileline, modfilename, this);

    if (v3Global.opt.preprocOnly() || v3Global.opt.keepTempFiles()) {
	// Create output file with all the preprocessor output we buffered up
	string vppfilename = v3Global.opt.makeDir()+"/"+v3Global.opt.prefix()+"_"+modname+".vpp";
	ofstream* ofp = NULL;
	ostream* osp;
	if (v3Global.opt.preprocOnly()) {
	    osp = &cout;
	} else {
	    osp = ofp = V3File::new_ofstream(vppfilename);
	}
	if (osp->fail()) {
	    fileline->v3error("Cannot write preprocessor output: "+vppfilename);
	    return;
	} else {
	    for (deque<string>::iterator it = m_ppBuffers.begin(); it!=m_ppBuffers.end(); ++it) {
		*osp << *it;
	    }
	    if (ofp) {
		ofp->close();
		delete ofp; ofp = NULL;
	    }
	}
    }

    // Parse it
    if (!v3Global.opt.preprocOnly()) {
	lexFile (modfilename);
    }
}

void V3Read::lexFile(const string& modname) {
    // Prepare for lexing
    UINFO(3,"Lexing "<<modname<<endl);
    V3Read::s_readp = this;
    V3Read::fileline()->warnResetDefault();	// Reenable warnings on each file
    if (m_lexerp) delete m_lexerp;	// Restart from clean slate.
    m_lexerp = new V3Lexer();
    // if (debug()) { m_lexerp->set_debug(~0);  }
    // if (debug()) yydebug = 1;
    UINFO(4,"Lexing Done "<<modname<<endl);

    // Lex it
    if (yyparse()) v3fatal("Cannot continue\n");
}

//======================================================================
// Lex accessors

bool V3Read::optPsl() {
    return v3Global.opt.psl();
}

//======================================================================
// Lex internal functions

int V3Read::yylexThis() {
    int token = m_lexerp->yylex();
    UINFO(5,m_fileline<<" TOKEN="<<dec<<token<<" "<<endl);
    return (token);
}
