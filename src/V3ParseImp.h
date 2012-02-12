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
// Copyright 2009-2012 by Wilson Snyder.  This program is free software; you can
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

typedef enum { uniq_NONE, uniq_UNIQUE, uniq_UNIQUE0, uniq_PRIORITY } V3UniqState;

typedef enum { iprop_NONE, iprop_CONTEXT, iprop_PURE } V3ImportProperty;

//============================================================================
// We can't use bison's %union as we want to pass the fileline with all tokens

struct V3ParseBisonYYSType {
    FileLine*	fl;
    AstNode*	scp;	// Symbol table scope for future lookups
    union {
	V3Number*	nump;
	string*		strp;
	int 		cint;
	double		cdouble;
	bool		cbool;
	V3UniqState	uniqstate;
	AstSignedState	signstate;
	V3ImportProperty iprop;
	V3ErrorCode::en	errcodeen;

	AstNode*	nodep;

	AstBasicDType*	bdtypep;
	AstBegin*	beginp;
	AstCase*	casep;
	AstCaseItem*	caseitemp;
	AstConst*	constp;
	AstNodeModule*	modulep;
	AstNodeDType*	dtypep;
	AstNodeFTask*	ftaskp;
	AstNodeFTaskRef* ftaskrefp;
	AstNodeSenItem*	senitemp;
	AstNodeVarRef*	varnodep;
	AstPackage*	packagep;
	AstParseRef*	parserefp;
	AstPin*		pinp;
	AstRange*	rangep;
	AstSenTree*	sentreep;
	AstVar*		varp;
	AstVarRef*	varrefp;
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
    V3SymTable*	m_symCurrentp;		// Active symbol table for additions/lookups
    V3SymTable*	m_symRootp;		// Root symbol table
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
    V3SymTable*	symRootp() const { return m_symRootp; }

    V3SymTable* findNewTable(AstNode* nodep, V3SymTable* parentp) {
	if (!nodep->user4p()) {
	    V3SymTable* symsp = new V3SymTable(nodep, parentp);
	    nodep->user4p(symsp);
	    m_symsp.push_back(symsp);
	}
	return getTable(nodep);
    }
    void nextId(AstNode* entp) {
	if (entp) {
	    UINFO(9,"symTableNextId under "<<entp<<"-"<<entp->type().ascii()<<endl);
	    m_symTableNextId = getTable(entp);
	}
	else {
	    UINFO(9,"symTableNextId under NULL"<<endl);
	    m_symTableNextId = NULL;
	}
    }
    void reinsert(AstNode* nodep, V3SymTable* parentp=NULL) {
	reinsert(nodep, parentp, nodep->name());
    }
    void reinsert(AstNode* nodep, V3SymTable* parentp, string name) {
	if (!parentp) parentp = symCurrentp();
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
    void import(AstNode* packagep, const string& id_or_star) {
	// Import from package::id_or_star to this
	V3SymTable* symp = getTable(packagep);
	if (!symp) {  // Internal problem, because we earlier found pkg to label it an ID__aPACKAGE
	    packagep->v3fatalSrc("Import package not found");
	    return;
	}
	// Walk old sym table and reinsert into current table
	// We let V3Link report the error instead of us
	symCurrentp()->import(symp, id_or_star);
    }
public:
    // CREATORS
    V3ParseSym(AstNetlist* rootp) {
	s_anonNum = 0;		// Number of next anonymous object
	pushScope(findNewTable(rootp, NULL));
	m_symTableNextId = NULL;
	m_symCurrentp = symCurrentp();
	m_symRootp = symCurrentp();
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
    AstNetlist* 	m_rootp;	// Root of the design
    V3InFilter*		m_filterp;	// Reading filter
    V3Lexer*		m_lexerp;	// Current FlexLexer
    static V3ParseImp*	s_parsep;	// Current THIS, bison() isn't class based
    FileLine*		m_fileline;	// Filename/linenumber currently active

    V3ParseSym	m_sym;			// Symbol table
    bool	m_inCellDefine;		// Inside a `celldefine
    bool	m_inLibrary;		// Currently reading a library vs. regular file
    int		m_inBeginKwd;		// Inside a `begin_keywords
    int		m_lastVerilogState;	// Last LEX state in `begin_keywords

    bool	m_ahead;		// aheadToken is valid
    int		m_aheadToken;		// Token we read ahead
    V3ParseBisonYYSType m_aheadVal;	// aheadToken's value

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
    void linenoInc() { fileline()->linenoInc(); }
    void verilatorCmtLint(const char* text, bool on);
    void verilatorCmtLintSave();
    void verilatorCmtLintRestore();
    void verilatorCmtBad(const char* text);
    double parseDouble(const char* text, size_t length);
    void pushBeginKeywords(int state) { m_inBeginKwd++; m_lastVerilogState=state; }
    bool popBeginKeywords() { if (m_inBeginKwd) { m_inBeginKwd--; return true; } else return false; }
    int lastVerilogState() const { return m_lastVerilogState; }
    static const char* tokenName(int tok);

    void ppPushText(const string& text) { m_ppBuffers.push_back(text); }
    size_t ppInputToLex(char* buf, size_t max_size);

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
    string* newString(const char* text, size_t length) {
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
    FileLine* fileline() const { return m_fileline; }
    AstNetlist* rootp() const { return m_rootp; }
    FileLine* copyOrSameFileLine() { return fileline()->copyOrSameFileLine(); }
    bool inCellDefine() const { return m_inCellDefine; }
    void inCellDefine(bool flag) { m_inCellDefine = flag; }
    bool inLibrary() const { return m_inLibrary; }

    // Interactions with parser
    int  bisonParse();

    // Interactions with lexer
    void lexNew(int debug);
    void lexDestroy();
    void stateExitPsl();	// Parser -> lexer communication
    void statePushVlg();	// Parser -> lexer communication
    void statePop();		// Parser -> lexer communication
    static int stateVerilogRecent();	// Parser -> lexer communication
    size_t flexPpInputToLex(char* buf, size_t max_size) { return ppInputToLex(buf,max_size); }

    //==== Symbol tables
    V3ParseSym* symp() { return &m_sym; }

public:
    // CREATORS
    V3ParseImp(AstNetlist* rootp, V3InFilter* filterp)
	: m_filterp(filterp), m_sym(rootp) {
	m_fileline = NULL;
	m_rootp = rootp; m_lexerp = NULL;
	m_inCellDefine = false;
	m_inLibrary = false;
	m_inBeginKwd = 0;
	m_lastVerilogState = stateVerilogRecent();
	m_ahead = false;
	m_aheadToken = 0;
    }
    ~V3ParseImp();
    void parserClear();

    // METHODS
    // Preprocess and read the Verilog file specified into the netlist database
    int lexToBison();  // Pass token to bison

    void parseFile(FileLine* fileline, const string& modfilename, bool inLibrary,
		   const string& errmsg);

private:
    void lexFile(const string& modname);
    int lexToken(); // Internal; called from lexToBison
};

#endif // Guard
