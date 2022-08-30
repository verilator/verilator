// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Netlist (top level) functions
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2022 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3ParseImp.h"

#include <fstream>

//======================================================================
// Build in LEX script

#define yyFlexLexer V3LexerBase
#include "V3Lexer.yy.cpp"
#undef yyFlexLexer

//######################################################################
// Lex-derived class

/// Override the base lexer class so we can add some access functions
class V3Lexer final : public V3LexerBase {
public:
    // CONSTRUCTORS
    V3Lexer()
        : V3LexerBase{nullptr} {}
    ~V3Lexer() override = default;
    // METHODS
    void unputString(const char* textp, size_t length) {
        // Add characters to input stream in back-to-front order
        const char* cp = textp;
        for (cp += length - 1; length--; cp--) unput(*cp);
    }
};

void V3ParseImp::lexUnputString(const char* textp, size_t length) {
    parsep()->m_lexerp->unputString(textp, length);
}

void V3ParseImp::yylexReadTok() {
    // Call yylex() remembering last non-whitespace token
    parsep()->lexFileline()->startToken();
    const int token = parsep()->m_lexerp->yylex();
    m_lexPrevToken = token;  // Save so can find '#' to parse following number
    yylval.token = token;
}

//######################################################################
// Read class functions

void V3ParseImp::lexNew() {
    if (m_lexerp) delete m_lexerp;  // Restart from clean slate.
    m_lexerp = new V3Lexer;
    if (debugFlex() >= 9) m_lexerp->set_debug(~0);
}

void V3ParseImp::lexDestroy() {
    if (m_lexerp) VL_DO_CLEAR(delete m_lexerp, m_lexerp = nullptr);
}
