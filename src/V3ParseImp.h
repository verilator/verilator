// -*- C++ -*-
//*************************************************************************
// DESCRIPTION: Verilator: Common header between parser and lex
//
// Code available from: http://www.veripool.org/verilator
//
// AUTHORS: Wilson Snyder with Paul Wasson, Duane Gabli
//
//*************************************************************************
//
// Copyright 2009-2009 by Wilson Snyder.  This program is free software; you can
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

#ifndef _V3PARSEIMP_H_
#define _V3PARSEIMP_H_ 1
#include "config_build.h"
#include "verilatedos.h"
#include "V3Error.h"
#include "V3Global.h"
#include "V3Parse.h"
#include "V3SymTable.h"
#include <deque>

class V3Lexer;

// IMPORTANT: Don't include this file other than in the bison and flex,
// as it's definitions will confuse other parsers

//======================================================================
// Types (between parser & lexer)

typedef enum { uniq_NONE, uniq_UNIQUE, uniq_PRIORITY } V3UniqState;

//============================================================================
// We can't use bison's %union as we want to pass the fileline with all tokens

struct V3ParseBisonYYSType {
    FileLine*	fl;
    union {
	V3Number*	nump;
	string*		strp;
	int 		cint;
	double		cdouble;
	V3UniqState	uniqstate;

	AstNode*	nodep;

	AstBegin*	beginp;
	AstCase*	casep;
	AstCaseItem*	caseitemp;
	AstConst*	constp;
	AstFunc*	funcp;
	AstModule*	modulep;
	AstNodeSenItem*	senitemp;
	AstNodeVarRef*	varnodep;
	AstParseRef*	parserefp;
	AstPin*		pinp;
	AstRange*	rangep;
	AstSenTree*	sentreep;
	AstTask*	taskp;
	AstVar*		varp;
    };
};

#define YYSTYPE V3ParseBisonYYSType

//######################################################################

class V3ParseImp {
    // MEMBERS
    AstNetlist* m_rootp;	// Root of the design
    V3Lexer*	m_lexerp;	// Current FlexLexer
    static V3ParseImp*	s_parsep;	// Current THIS, bison() isn't class based
    FileLine*	m_fileline;		// Filename/linenumber currently active

    bool	m_inCellDefine;		// Inside a `celldefine
    bool	m_inLibrary;		// Currently reading a library vs. regular file
    int		m_inBeginKwd;		// Inside a `begin_keywords
    int		m_lastVerilogState;	// Last LEX state in `begin_keywords

    deque<string*> m_stringps;		// Created strings for later cleanup
    deque<V3Number*> m_numberps;	// Created numbers for later cleanup
    deque<FileLine>  m_lintState;	// Current lint state for save/restore
    deque<string> m_ppBuffers;		// Preprocessor->lex buffer of characters to process

public:
    // Note these are an exception to using the filename as the debug type
    static int debugBison() {
	static int level = -1;
	if (VL_UNLIKELY(level < 0)) level = v3Global.opt.debugSrcLevel("bison");
	return level;
    }
    static int debugFlex() {
	static int level = -1;
	if (VL_UNLIKELY(level < 0)) level = v3Global.opt.debugSrcLevel("flex");
	return level;
    }
    static int debug() { return debugBison() ? debugFlex() : 0; }

    // Functions called by lex rules:
    int yylexThis();
    static bool optPsl() { return v3Global.opt.psl(); }
    static bool optFuture(const string& flag) { return v3Global.opt.isFuture(flag); }

    void ppline (const char* text);
    void incLineno() { fileline()->incLineno(); }
    void verilatorCmtLint(const char* text, bool on);
    void verilatorCmtLintSave();
    void verilatorCmtLintRestore();
    void verilatorCmtBad(const char* text);
    void pushBeginKeywords(int state) { m_inBeginKwd++; m_lastVerilogState=state; }
    bool popBeginKeywords() { if (m_inBeginKwd) { m_inBeginKwd--; return true; } else return false; }
    int lastVerilogState() { return m_lastVerilogState; }
    static const char* tokenName(int tok);

    void ppPushText(const string& text) { m_ppBuffers.push_back(text); }
    int ppInputToLex(char* buf, int max_size);

    static V3ParseImp* parsep() { return s_parsep; }

    // TODO: Many of these functions are the old interface; they'd be better as non-static
    // and called as READP->newString(...) etc.
    string* newString(const string& text) {
	// Allocate a string, remembering it so we can reclaim storage at lex end
	string* strp = new string (text);
	m_stringps.push_back(strp);
	return strp;
    }
    string* newString(const char* text) {
	// Allocate a string, remembering it so we can reclaim storage at lex end
	string* strp = new string (text);
	m_stringps.push_back(strp);
	return strp;
    }
    string* newString(const char* text, int length) {
	string* strp = new string (text, length);
	m_stringps.push_back(strp);
	return strp;
    }
    V3Number* newNumber(FileLine* fl, const char* text) {
	V3Number* nump = new V3Number (fl, text);
	m_numberps.push_back(nump);
	return nump;
    }

    // Return next token, for bison, since bison isn't class based, use a global THIS
    FileLine* fileline() { return m_fileline; }
    AstNetlist* rootp() { return m_rootp; }
    FileLine* copyOrSameFileLine() { return fileline()->copyOrSameFileLine(); }
    bool inCellDefine() { return m_inCellDefine; }
    void inCellDefine(bool flag) { m_inCellDefine = flag; }
    bool inLibrary() { return m_inLibrary; }

    // Interactions with parser
    int  bisonParse();

    // Interactions with lexer
    void lexNew(int debug);
    void lexDestroy();
    void stateExitPsl();	// Parser -> lexer communication
    void statePushVlg();	// Parser -> lexer communication
    void statePop();	// Parser -> lexer communication
    int stateVerilogRecent();	// Parser -> lexer communication
    int flexPpInputToLex(char* buf, int max_size) { return ppInputToLex(buf,max_size); }

public:
    // CREATORS
    V3ParseImp(AstNetlist* rootp) {
	m_rootp = rootp; m_lexerp = NULL;
	m_inCellDefine = false;
	m_inLibrary = false;
	m_inBeginKwd = 0;
	m_lastVerilogState = stateVerilogRecent();
    }
    ~V3ParseImp();
    void parserClear();

    // METHODS
    // Preprocess and read the Verilog file specified into the netlist database
    int lexToBison();  // Pass token to bison

    void parseFile(FileLine* fileline, const string& modfilename, bool inLibrary);

private:
    void lexFile(const string& modname);
    int lexToken(); // Internal; called from lexToBison
};

#endif // Guard
