// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Netlist (top level) functions
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2020 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3Error.h"
#include "V3Global.h"
#include "V3File.h"
#include "V3ParseImp.h"

#include <cstdarg>
#include <fstream>

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
    void statePop() {
        yy_pop_state();
    }
    void unputString(const char* textp, size_t length) {
        // Add characters to input stream in back-to-front order
        const char* cp = textp;
        for (cp += length - 1; length--; cp--) {
            unput(*cp);
        }
    }
};

void V3ParseImp::statePop() { parsep()->m_lexerp->statePop(); }

void V3ParseImp::unputString(const char* textp, size_t length) {
    parsep()->m_lexerp->unputString(textp, length);
}

int V3ParseImp::yylexReadTok() {
    // Call yylex() remembering last non-whitespace token
    parsep()->fileline()->startToken();
    int token = parsep()->m_lexerp->yylex();
    m_prevLexToken = token;  // Save so can find '#' to parse following number
    return token;
}

//######################################################################
// Read class functions

void V3ParseImp::lexNew() {
    if (m_lexerp) delete m_lexerp;  // Restart from clean slate.
    m_lexerp = new V3Lexer();
    if (debugFlex()>=9) { m_lexerp->set_debug(~0);  }
}

void V3ParseImp::lexDestroy() {
    if (m_lexerp) VL_DO_CLEAR(delete m_lexerp, m_lexerp = NULL);
}
