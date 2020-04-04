// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Common header between parser and lex
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2009-2020 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#ifndef _V3PARSEIMP_H_
#define _V3PARSEIMP_H_ 1

#include "config_build.h"
#include "verilatedos.h"

#include "V3Error.h"
#include "V3FileLine.h"
#include "V3Global.h"
#include "V3Parse.h"
#include "V3ParseSym.h"

#include <deque>

class V3Lexer;

// IMPORTANT: Don't include this file other than in the bison and flex,
// as it's definitions will confuse other parsers

//======================================================================
// Types (between parser & lexer)

typedef enum { uniq_NONE, uniq_UNIQUE, uniq_UNIQUE0, uniq_PRIORITY } V3UniqState;

typedef enum { iprop_NONE, iprop_CONTEXT, iprop_PURE } V3ImportProperty;

//============================================================================
// Parser YYSType, e.g. for parser's yylval
// We can't use bison's %union as we want to pass the fileline with all tokens

struct V3ParseBisonYYSType {
    FileLine*   fl;
    AstNode*    scp;    // Symbol table scope for future lookups
    int         token;  // Read token, aka tok
    union {
        V3Number*       nump;
        string*         strp;
        int             cint;
        double          cdouble;
        bool            cbool;
        V3UniqState     uniqstate;
        VSignedState    signstate;
        V3ImportProperty iprop;
        V3ErrorCode::en errcodeen;
        AstAttrType::en attrtypeen;

        AstNode*        nodep;

        AstBasicDType*  bdtypep;
        AstBegin*       beginp;
        AstCase*        casep;
        AstCaseItem*    caseitemp;
        AstCell*        cellp;
        AstClass*       classp;
        AstConst*       constp;
        AstMemberDType* memberp;
        AstNodeModule*  modulep;
        AstNodeUOrStructDType* uorstructp;
        AstNodeDType*   dtypep;
        AstNodeFTask*   ftaskp;
        AstNodeFTaskRef* ftaskrefp;
        AstNodeRange*   rangep;
        AstNodeSenItem* senitemp;
        AstNodeVarRef*  varnodep;
        AstPackage*     packagep;
        AstPackageRef*  packagerefp;
        AstParseRef*    parserefp;
        AstPatMember*   patmemberp;
        AstPattern*     patternp;
        AstPin*         pinp;
        AstRefDType*    refdtypep;
        AstSenTree*     sentreep;
        AstVar*         varp;
        AstVarRef*      varrefp;
    };
};

#define YYSTYPE V3ParseBisonYYSType

//######################################################################

class V3ParseImp {
    // MEMBERS
    AstNetlist*         m_rootp;        // Root of the design
    VInFilter*          m_filterp;      // Reading filter
    V3ParseSym*         m_symp;         // Symbol table

    V3Lexer*            m_lexerp;       // Current FlexLexer
    static V3ParseImp*  s_parsep;       // Current THIS, bison() isn't class based
    FileLine*           m_fileline;     // Filename/linenumber currently active

    bool        m_inCellDefine;         // Inside a `celldefine
    bool        m_inLibrary;            // Currently reading a library vs. regular file
    int         m_inBeginKwd;           // Inside a `begin_keywords
    int         m_lastVerilogState;     // Last LEX state in `begin_keywords

    int         m_prevLexToken;         // previous parsed token (for lexer)
    bool        m_ahead;                // aheadval is valid
    V3ParseBisonYYSType m_aheadVal;     // ahead token value
    V3ParseBisonYYSType m_curBisonVal;  // current token for error reporting
    V3ParseBisonYYSType m_prevBisonVal; // previous token for error reporting

    std::deque<string*> m_stringps;     // Created strings for later cleanup
    std::deque<V3Number*> m_numberps;   // Created numbers for later cleanup
    std::deque<FileLine> m_lintState;   // Current lint state for save/restore
    std::deque<string> m_ppBuffers;     // Preprocessor->lex buffer of characters to process

    string m_tag;                       // Contents (if any) of current verilator tag
    AstNode* m_tagNodep;                // Points to the node to set to m_tag or NULL to not set.
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
    static bool optFuture(const string& flag) { return v3Global.opt.isFuture(flag); }

    void ppline(const char* textp);
    void linenoInc() { fileline()->linenoInc(); }
    void verilatorCmtLint(const char* textp, bool on);
    void verilatorCmtLintSave();
    void verilatorCmtLintRestore();
    void verilatorCmtBad(const char* textp);
    void errorPreprocDirective(const char* textp);
    void tag(const char* text);
    void tagNodep(AstNode* nodep) { m_tagNodep = nodep; }
    AstNode* tagNodep() const { return m_tagNodep;}

    static double parseDouble(const char* text, size_t length, bool* successp = NULL);
    void pushBeginKeywords(int state) { m_inBeginKwd++; m_lastVerilogState = state; }
    bool popBeginKeywords() {
        if (m_inBeginKwd) { m_inBeginKwd--; return true; } else return false; }
    int lastVerilogState() const { return m_lastVerilogState; }
    static const char* tokenName(int tok);

    void ppPushText(const string& text) {
        m_ppBuffers.push_back(text);
        if (fileline()->contentp()) fileline()->contentp()->pushText(text);
    }
    size_t ppInputToLex(char* buf, size_t max_size);

    static V3ParseImp* parsep() { return s_parsep; }

    // TODO: Many of these functions are the old interface; they'd be better as non-static
    // and called as READP->newString(...) etc.
    string* newString(const string& text) {
        // Allocate a string, remembering it so we can reclaim storage at lex end
        string* strp = new string(text);
        m_stringps.push_back(strp);
        return strp;
    }
    string* newString(const char* text) {
        // Allocate a string, remembering it so we can reclaim storage at lex end
        string* strp = new string(text);
        m_stringps.push_back(strp);
        return strp;
    }
    string* newString(const char* text, size_t length) {
        string* strp = new string(text, length);
        m_stringps.push_back(strp);
        return strp;
    }
    V3Number* newNumber(FileLine* fl, const char* text) {
        V3Number* nump = new V3Number(V3Number::FileLined(), fl, text);
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
    void lexNew();
    void lexDestroy();
    void statePop();  // Parser -> lexer communication
    static int stateVerilogRecent();  // Parser -> lexer communication
    int prevLexToken() { return m_prevLexToken; }  // Parser -> lexer communication
    size_t flexPpInputToLex(char* buf, size_t max_size) { return ppInputToLex(buf, max_size); }
    const V3ParseBisonYYSType curBisonVal() const { return m_curBisonVal; }
    const V3ParseBisonYYSType prevBisonVal() const { return m_prevBisonVal; }

    //==== Symbol tables
    V3ParseSym* symp() { return m_symp; }

public:
    // CONSTRUCTORS
    V3ParseImp(AstNetlist* rootp, VInFilter* filterp, V3ParseSym* parserSymp)
        : m_rootp(rootp), m_filterp(filterp), m_symp(parserSymp) {
        m_fileline = NULL;
        m_lexerp = NULL;
        m_inCellDefine = false;
        m_inLibrary = false;
        m_inBeginKwd = 0;
        m_lastVerilogState = stateVerilogRecent();
        m_prevLexToken = 0;
        m_ahead = false;
        m_curBisonVal.token = 0;
        m_prevBisonVal.token = 0;
        // m_aheadVal not used as m_ahead = false, and not all compilers support initing it
        m_tagNodep = NULL;
    }
    ~V3ParseImp();
    void parserClear();
    void unputString(const char* textp, size_t length);

    // METHODS
    // Preprocess and read the Verilog file specified into the netlist database
    int lexToBison();  // Pass token to bison

    void parseFile(FileLine* fileline, const string& modfilename, bool inLibrary,
                   const string& errmsg);

private:
    void lexFile(const string& modname);
    int yylexReadTok();
    void lexToken();  // Internal; called from lexToBison
    void preprocDumps(std::ostream& os);
};

#endif  // Guard
