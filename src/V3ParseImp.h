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
    //V3SymTable*	scp;	// Symbol table scope for future lookups
    union {
	V3Number*	nump;
	string*		strp;
	int 		cint;
	double		cdouble;
	V3UniqState	uniqstate;
	AstSignedState	signstate;

	AstNode*	nodep;

	AstBasicDType*	bdtypep;
	AstBegin*	beginp;
	AstCase*	casep;
	AstCaseItem*	caseitemp;
	AstConst*	constp;
	AstModule*	modulep;
	AstNodeDType*	typep;
	AstNodeFTask*	ftaskp;
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
// Symbol table for parsing

class V3ParseSym {
    // TYPES
    typedef vector<V3SymTable*>	SymStack;

private:
    // MEMBERS
    static int	s_anonNum;		// Number of next anonymous object
    V3SymTable*	m_symTableNextId;	// Symbol table for next lexer lookup
    V3SymTable*	m_symCurrentp;		// Node with active symbol table for additions/lookups
    SymStack	m_sympStack;		// Stack of nodes with symbol tables
    SymStack	m_symsp;		// All symbol tables, to cleanup

private:
    // METHODS
    static V3SymTable* getTable(AstNode* nodep) {
	if (!nodep->user4p()) nodep->v3fatalSrc("Current symtable not found");
	return nodep->user4p()->castSymTable();
    }

public:
    V3SymTable* nextId() const { return m_symTableNextId; }
    V3SymTable* symCurrentp() const { return m_symCurrentp; }

    V3SymTable* findNewTable(AstNode* nodep, V3SymTable* parentp) {
	if (!nodep->user4p()) {
	    V3SymTable* symsp = new V3SymTable(nodep, parentp);
	    nodep->user4p(symsp);
	    m_symsp.push_back(symsp);
	}
	return getTable(nodep);
    }
    void nextId(AstNode* entp) {
	if (entp) { UINFO(9,"symTableNextId under "<<entp<<"-"<<entp->type().ascii()<<endl); }
	else { UINFO(9,"symTableNextId under NULL"<<endl); }
	m_symTableNextId = getTable(entp);
    }
    void reinsert(AstNode* nodep, V3SymTable* parentp=NULL) {
	if (!parentp) parentp = symCurrentp();
	string name = nodep->name();
	if (name == "") {  // New name with space in name so can't collide with users
	    name = string(" anon") + nodep->type().ascii() + cvtToStr(++s_anonNum);
	}
	parentp->reinsert(name,nodep);
    }
    void pushNew(AstNode* nodep) { pushNewUnder(nodep, NULL); }
    void pushNewUnder(AstNode* nodep, V3SymTable* parentp) {
	if (!parentp) parentp = symCurrentp();
	V3SymTable* symp = findNewTable(nodep, parentp);  // Will set user4p, which is how we connect table to node
	reinsert(nodep, parentp);
	pushScope(symp);
    }
    void pushScope(V3SymTable* symp) {
	m_sympStack.push_back(symp);
	m_symCurrentp = symp;
    }
    void popScope(AstNode* nodep) {
	if (symCurrentp()->ownerp() != nodep) {
	    if (debug()) { showUpward(); dump(cout,"-mism: "); }
	    nodep->v3fatalSrc("Symbols suggest ending "<<symCurrentp()->ownerp()->prettyTypeName()
			      <<" but parser thinks ending "<<nodep->prettyTypeName());
	    return;
	}
	m_sympStack.pop_back();
	if (m_sympStack.empty()) { nodep->v3fatalSrc("symbol stack underflow"); return; }
	m_symCurrentp = m_sympStack.back();
    }
    void showUpward () {
	UINFO(1,"ParseSym Stack:\n");
	for (SymStack::reverse_iterator it=m_sympStack.rbegin(); it!=m_sympStack.rend(); ++it) {
	    V3SymTable* symp = *it;
	    UINFO(1,"\t"<<symp->ownerp()<<endl);
	}
	UINFO(1,"ParseSym Current: "<<symCurrentp()->ownerp()<<endl);
    }
    void dump(ostream& os, const string& indent="") {
	os<<"ParseSym Dump:\n";
	m_sympStack[0]->dump(os, indent, true);
    }
    AstNode* findEntUpward (const string& name) {
	// Lookup the given string as an identifier, return type of the id, scanning upward
	return symCurrentp()->findIdUpward(name);
    }
    void import(AstNode* nodep, const string& pkg, const string& id_or_star) {
	// Import from package::id_or_star to this
	AstNode* entp = findEntUpward(pkg);
	if (!entp) {  // Internal problem, because we earlier found pkg to label it an ID__aPACKAGE
	    nodep->v3fatalSrc("Import package not found: "+pkg);
	    return;
	}
	// Walk old sym table and reinsert into current table
	nodep->v3fatalSrc("Unimplemented: import");
    }
public:
    // CREATORS
    V3ParseSym(AstNetlist* rootp) {
	s_anonNum = 0;		// Number of next anonymous object
	pushScope(findNewTable(rootp, NULL));
	m_symTableNextId = symCurrentp();
    }
    ~V3ParseSym() {
	for (SymStack::iterator it = m_symsp.begin(); it != m_symsp.end(); ++it) {
	    delete (*it);
	}
    }
};

//######################################################################

class V3ParseImp {
    // MEMBERS
    AstNetlist* m_rootp;	// Root of the design
    V3Lexer*	m_lexerp;	// Current FlexLexer
    static V3ParseImp*	s_parsep;	// Current THIS, bison() isn't class based
    FileLine*	m_fileline;		// Filename/linenumber currently active

    V3ParseSym	m_sym;			// Symbol table
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

    //==== Symbol tables
    V3ParseSym* symp() { return &m_sym; }

public:
    // CREATORS
    V3ParseImp(AstNetlist* rootp) : m_sym(rootp) {
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
