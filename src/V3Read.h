// $Id$ //-*- C++ -*-
//*************************************************************************
// DESCRIPTION: Verilator: Reading of Verilog files
//
// Code available from: http://www.veripool.com/verilator
//
// AUTHORS: Wilson Snyder with Paul Wasson, Duane Gabli
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

#ifndef _V3READ_H_
#define _V3READ_H_ 1
#include "config_build.h"
#include "verilatedos.h"
#include "V3Error.h"
#include <deque>

class AstNetlist;
class V3Lexer;
class V3Number;
class AstNode;

//============================================================================

class V3Read {
    AstNetlist* m_rootp;	// Root of the design
    V3Lexer*	m_lexerp;	// Current FlexLexer
    static V3Read*	s_readp;	// Current THIS, bison() isn't class based
    FileLine*	m_fileline;	// Filename/linenumber currently active
    bool	m_inLibrary;	// Currently reading a library vs. regular file
    int		m_inBeginKwd;		// Inside a `begin_keywords
    int		m_lastVerilogState;	// Last LEX state in `begin_keywords
    deque<string*> m_stringps;		// Created strings for later cleanup
    deque<V3Number*> m_numberps;	// Created numbers for later cleanup
    //int debug() { return 9; }

protected:
    // Functions called by lex rules:
    friend class V3Lexer;
    friend class V3LexerBase;
    friend class FileLine;
    int yylexThis();
    static bool optPsl();
    static void ppline (const char* text);
    static void incLineno() { s_readp->fileline()->incLineno(); }
    static void verilatorCmtLint(const char* text, bool on);
    static void verilatorCmtBad(const char* text);
    static void pushBeginKeywords(int state) { s_readp->m_inBeginKwd++; s_readp->m_lastVerilogState=state; }
    static bool popBeginKeywords() { if (s_readp->m_inBeginKwd) { s_readp->m_inBeginKwd--; return true; } else return false; }
    static int lastVerilogState() { return s_readp->m_lastVerilogState; }

public: // But for internal use only
    static string* newString(const string& text) {
	// Allocate a string, remembering it so we can reclaim storage at lex end
	string* strp = new string (text);
	s_readp->m_stringps.push_back(strp);
	return strp;
    }
    static string* newString(const char* text) {
	// Allocate a string, remembering it so we can reclaim storage at lex end
	string* strp = new string (text);
	s_readp->m_stringps.push_back(strp);
	return strp;
    }
    static string* newString(const char* text, int length) {
	string* strp = new string (text, length);
	s_readp->m_stringps.push_back(strp);
	return strp;
    }
    static V3Number* newNumber(FileLine* fl, const char* text) {
	V3Number* nump = new V3Number (fl, text);
	s_readp->m_numberps.push_back(nump);
	return nump;
    }

    // Return next token, for bison, since bison isn't class based, use a global THIS
    static int yylex() { return s_readp->yylexThis(); };
    static FileLine* fileline() { return s_readp->m_fileline; }
    static AstNetlist* rootp() { return s_readp->m_rootp; }
    static FileLine* copyOrSameFileLine() { return s_readp->fileline()->copyOrSameFileLine(); }
    static bool inLibrary() { return s_readp->m_inLibrary; }
    static void stateExitPsl();	// Parser -> lexer communication
    static void statePushVlg();	// Parser -> lexer communication
    static void statePop();	// Parser -> lexer communication
    static int stateVerilogRecent();	// Parser -> lexer communication

public:
    // CREATORS
    V3Read(AstNetlist* rootp) {
	m_rootp = rootp; m_lexerp = NULL;
	m_inLibrary = false;
	m_inBeginKwd = 0;
	m_lastVerilogState = stateVerilogRecent();
    }
    ~V3Read() {
	for (deque<string*>::iterator it = m_stringps.begin(); it != m_stringps.end(); ++it) {
	    delete (*it);
	}
	m_stringps.clear();
	for (deque<V3Number*>::iterator it = m_numberps.begin(); it != m_numberps.end(); ++it) {
	    delete (*it);
	}
	m_numberps.clear();
    }

    // METHODS
    // Preprocess and read the Verilog file specified into the netlist database
    void readFile(FileLine* fileline, const string& modname, bool inLibrary);

private:
    void lexFile(const string& vppfilename, const string& modname);
};

#endif // Guard
