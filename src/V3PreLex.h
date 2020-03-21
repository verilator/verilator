// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilog::Preproc: Internal header for lex interfacing
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2000-2020 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
// This header provides the interface between the lex proper V3PreLex.l/.cpp
// and the class implementation file V3Pre.cpp
// It is not intended for user applications.
//*************************************************************************

#ifndef _VPREPROCLEX_H_  // Guard
#define _VPREPROCLEX_H_ 1

#include "V3Error.h"
#include "V3FileLine.h"

#include <deque>
#include <stack>

//======================================================================

class V3PreLex;
class V3PreProcImp;

// Token codes
// If changing, see V3PreProc.cpp's V3PreProcImp::tokenName()
#define VP_EOF          0     // Must be zero, a.k.a. YY_NULL, a.k.a. yy_terminate();
#define VP_EOF_ERROR    400

#define VP_INCLUDE      256
#define VP_IFDEF        257
#define VP_IFNDEF       258
#define VP_ENDIF        259
#define VP_UNDEF        260
#define VP_DEFINE       261
#define VP_ELSE         262
#define VP_ELSIF        263
#define VP_LINE         264
#define VP_UNDEFINEALL  265

#define VP_SYMBOL       300
#define VP_STRING       301
#define VP_DEFVALUE     302
#define VP_COMMENT      303
#define VP_TEXT         304
#define VP_WHITE        305
#define VP_DEFREF       306
#define VP_DEFARG       307
#define VP_ERROR        308
#define VP_DEFFORM      309
#define VP_STRIFY       310
#define VP_BACKQUOTE    311
#define VP_SYMBOL_JOIN  312
#define VP_DEFREF_JOIN  313
#define VP_JOIN         314

#define VP_PSL          350

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

#ifndef yyourleng
# define yyourleng V3PreLexourleng
# define yyourtext V3PreLexourtext
#endif

#ifndef YY_BUFFER_STATE
struct yy_buffer_state;
typedef struct yy_buffer_state *YY_BUFFER_STATE;
# define YY_BUF_SIZE 16384
#endif

extern int yylex();
extern void yyrestart(FILE*);

// Accessors, because flex keeps changing the type of yyleng
extern char* yyourtext();
extern size_t yyourleng();
extern void yyourtext(const char* textp, size_t size);  // Must call with static

YY_BUFFER_STATE yy_create_buffer(FILE *file, int size);
void yy_switch_to_buffer(YY_BUFFER_STATE new_buffer);
void yy_delete_buffer(YY_BUFFER_STATE b);

//======================================================================

#define KEEPCMT_SUB 2
#define KEEPCMT_EXP 3

//======================================================================
// Entry for each file processed; a stack of entries included

class VPreStream {
public:
    FileLine*           m_curFilelinep; // Current processing point (see also m_tokFilelinep)
    V3PreLex*           m_lexp;         // Lexer, for resource tracking
    std::deque<string>  m_buffers;      // Buffer of characters to process
    int                 m_ignNewlines;  // Ignore multiline newlines
    bool                m_eof;          // "EOF" buffer
    bool                m_file;         // Buffer is start of new file
    int                 m_termState;    // Termination fsm
    VPreStream(FileLine* fl, V3PreLex* lexp)
        : m_curFilelinep(fl), m_lexp(lexp),
          m_ignNewlines(0),
          m_eof(false), m_file(false), m_termState(0) {
        lexStreamDepthAdd(1);
    }
    ~VPreStream() {
        lexStreamDepthAdd(-1);
    }
private:
    void lexStreamDepthAdd(int delta);
};

//======================================================================
// Class entry for each per-lexer state

class V3PreLex {
  public:  // Used only by V3PreLex.cpp and V3PreProc.cpp
    V3PreProcImp*       m_preimpp;      // Preprocessor lexor belongs to
    std::stack<VPreStream*> m_streampStack;  // Stack of processing files
    int                 m_streamDepth;  // Depth of stream processing
    YY_BUFFER_STATE     m_bufferState;  // Flex state
    FileLine*           m_tokFilelinep; // Starting position of current token

    // State to lexer
    static V3PreLex* s_currentLexp;     ///< Current lexing point
    int         m_keepComments;         ///< Emit comments in output text
    int         m_keepWhitespace;       ///< Emit all whitespace in output text
    bool        m_pedantic;             ///< Obey standard; don't Substitute `error

    // State from lexer
    int         m_formalLevel;  // Parenthesis counting inside def formals
    int         m_parenLevel;   // Parenthesis counting inside def args
    bool        m_defCmtSlash;  // /*...*/ comment in define had \ ending
    bool        m_defQuote;     // Definition value inside quote
    string      m_defValue;     // Definition value being built.
    int         m_enterExit;    // For VL_LINE, the enter/exit level

    // CONSTRUCTORS
    V3PreLex(V3PreProcImp* preimpp, FileLine* filelinep) {
        m_preimpp = preimpp;
        m_streamDepth = 0;
        m_keepComments = 0;
        m_keepWhitespace = 1;
        m_pedantic = false;
        m_formalLevel = 0;
        m_parenLevel = 0;
        m_defQuote = false;
        m_defCmtSlash = false;
        m_tokFilelinep = filelinep;
        m_enterExit = 0;
        initFirstBuffer(filelinep);
    }
    ~V3PreLex() {
        while (!m_streampStack.empty()) { delete m_streampStack.top(); m_streampStack.pop(); }
        VL_DO_CLEAR(yy_delete_buffer(m_bufferState), m_bufferState = NULL);
    }

    // Called by V3PreLex.l from lexer
    VPreStream* curStreamp() { return m_streampStack.top(); }  // Can't be empty, "EOF" is on top
    FileLine* curFilelinep() { return curStreamp()->m_curFilelinep; }
    void curFilelinep(FileLine* fl) { curStreamp()->m_curFilelinep = fl; }
    void appendDefValue(const char* textp, size_t len) { m_defValue.append(textp, len); }
    void lineDirective(const char* textp);
    void linenoInc() { if (curStreamp()->m_ignNewlines) curStreamp()->m_ignNewlines--;
        else curFilelinep()->linenoInc(); }
    void warnBackslashSpace();
    // Called by V3PreProc.cpp to inform lexer
    void pushStateDefArg(int level);
    void pushStateDefForm();
    void pushStateDefValue();
    void pushStateIncFilename();
    void scanNewFile(FileLine* filelinep);
    void scanBytes(const string& str);
    void scanBytesBack(const string& str);
    size_t inputToLex(char* buf, size_t max_size);
    /// Called by V3PreProc.cpp to get data from lexer
    YY_BUFFER_STATE currentBuffer();
    int  lex();
    int  currentStartState() const;
    void dumpSummary();
    void dumpStack();
    void unused();
    // Called by VPreStream
    void streamDepthAdd(int delta) { m_streamDepth += delta; }
    int streamDepth() const { return m_streamDepth; }
    /// Utility
    static int debug();
    static void debug(int level);
    static string cleanDbgStrg(const string& in);

private:
    string currentUnreadChars();
    string endOfStream(bool& againr);
    void initFirstBuffer(FileLine* filelinep);
    void scanSwitchStream(VPreStream* streamp);
};

inline void VPreStream::lexStreamDepthAdd(int delta) { m_lexp->streamDepthAdd(delta); }

#endif  // Guard
