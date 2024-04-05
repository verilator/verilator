// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilog::Preproc: Preprocess verilog code
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2000-2023 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only LOR Artistic-2.0
//
//*************************************************************************

#ifndef VERILATOR_V3PREEXPR_H_
#define VERILATOR_V3PREEXPR_H_

#include "config_build.h"
#include "verilatedos.h"

#include "V3FileLine.h"
#include "V3Global.h"

#include <deque>

using namespace std;

class V3PreExprToken final {
public:
    // TYPES
    // Order of enum must match token table
    enum token_t : uint8_t { ZERO, ONE, END, BRA, KET, LNOT, LAND, LOR, IMP, EQV, MAX };

private:
    // MEMBERS
    FileLine* const m_fileline;  // Token fileline
    token_t const m_token;  // Token value
public:
    // METHODS
    V3PreExprToken(FileLine* fileline, token_t token)
        : m_fileline{fileline}
        , m_token{token} {}
    V3PreExprToken(FileLine* fileline, bool value)
        : m_fileline{fileline}
        , m_token{value ? ONE : ZERO} {}
    ~V3PreExprToken() = default;
    const char* ascii() const {
        static const char* names[] = {"0", "1", "$", "(", ")", "!", "&&", "||", "->", "<->"};
        return names[m_token];
    }
    FileLine* fileline() const { return m_fileline; }
    token_t token() const { return m_token; }
    bool isValue() const { return m_token == ZERO || m_token == ONE; }
    bool value() const {
        UASSERT(isValue(), "preproc expr fetch of non-value");
        return m_token == ONE;
    }
};

class V3PreExpr final {
    // MEMBERS
    std::deque<V3PreExprToken> m_inputs;  // Input stack
    std::deque<V3PreExprToken> m_values;  // Value stack
    std::deque<V3PreExprToken> m_ops;  // Operator stack
    FileLine* m_firstFileline = nullptr;

    VL_DEFINE_DEBUG_FUNCTIONS;

    // PARSER DEFINITION
    enum action_t : uint8_t {
        VV,  // Value
        AA,  // Accept
        RR,  // Reduce
        SS,  // Shift
        EE  // Error
    };
    static const char* actionAscii(action_t en) {
        static const char* names[] = {"VV", "AA", "RR", "SS", "EE"};
        return names[en];
    }

    //  Operators  Associativity  Precedence
    //  ---------  -------------  ----------
    //  ()         Left           Highest
    //  !          (unary)
    //  &&         Left
    //  ||         Left
    //  -> <->     Right          Lowest
    //
    //  If different op precedence, shift for higher to input, else reduce for lower
    //  If same op precedence, shift for right assoc, reduce for left assoc

    action_t parseTable[V3PreExprToken::MAX][V3PreExprToken::MAX] = {
        // stack   ------------- inputs ------------------
        //         0   1   $   (   )   !   &&  ||  ->  <->
        /* 0   */ {EE, EE, EE, EE, EE, EE, EE, EE, EE, EE},  // 0 never on op stack
        /* 1   */ {EE, EE, EE, EE, EE, EE, EE, EE, EE, EE},  // 1 never on op stack
        /* $   */ {VV, VV, AA, SS, EE, SS, SS, SS, SS, SS},
        /* (   */ {VV, VV, EE, SS, RR, SS, SS, SS, SS, SS},
        /* )   */ {VV, VV, RR, EE, RR, RR, RR, RR, RR, RR},
        /* !   */ {VV, VV, RR, SS, RR, SS, RR, RR, RR, RR},
        /* &&  */ {VV, VV, RR, SS, RR, SS, SS, RR, RR, RR},
        /* ||  */ {VV, VV, RR, SS, RR, SS, SS, SS, RR, RR},
        /* ->  */ {VV, VV, RR, SS, RR, SS, SS, SS, RR, RR},
        /* <-> */ {VV, VV, RR, SS, RR, SS, SS, SS, RR, RR}};

    static void selfTestImp() {
        selfTestOne("0", false);
        selfTestOne("1", true);
        selfTestOne("! 0", true);
        selfTestOne("! 1", false);
        selfTestOne("0 || 0", false);
        selfTestOne("0 || 1", true);
        selfTestOne("1 || 0", true);
        selfTestOne("1 || 1", true);
        selfTestOne("0 && 0", false);
        selfTestOne("0 && 1", false);
        selfTestOne("1 && 0", false);
        selfTestOne("1 && 1", true);
        selfTestOne("0 -> 0", true);
        selfTestOne("0 -> 1", true);
        selfTestOne("1 -> 0", false);
        selfTestOne("1 -> 1", true);
        selfTestOne("0 <-> 0", true);
        selfTestOne("0 <-> 1", false);
        selfTestOne("1 <-> 0", false);
        selfTestOne("1 <-> 1", true);
        selfTestOne("1 || 0 && 1", false);
        selfTestOne("( 1 || 0 ) && 1", true);
        selfTestOne("! 1 || ! 1", false);
        selfTestOne("! 0 && ! 0", true);
    }

    static void selfTestOne(const string& expr, bool expect) {
        // This hacky self-test parser just looks at first character of
        // operator, and requires space separation of operators/values
        UINFO(9, "V3PreExpr selfTestOne " << expr << endl);
        FileLine* const flp = nullptr;
        V3PreExpr parser;
        parser.reset(flp);
        bool tstart = true;
        for (const char* cp = expr.c_str(); *cp; ++cp) {
            if (tstart) {
                tstart = false;
                switch (*cp) {
                case '0': parser.pushInput(V3PreExprToken{flp, V3PreExprToken::ZERO}); break;
                case '1': parser.pushInput(V3PreExprToken{flp, V3PreExprToken::ONE}); break;
                case '!': parser.pushInput(V3PreExprToken{flp, V3PreExprToken::LNOT}); break;
                case '|': parser.pushInput(V3PreExprToken{flp, V3PreExprToken::LOR}); break;
                case '&': parser.pushInput(V3PreExprToken{flp, V3PreExprToken::LAND}); break;
                case '-': parser.pushInput(V3PreExprToken{flp, V3PreExprToken::IMP}); break;
                case '<': parser.pushInput(V3PreExprToken{flp, V3PreExprToken::EQV}); break;
                case '(': parser.pushInput(V3PreExprToken{flp, V3PreExprToken::BRA}); break;
                case ')': parser.pushInput(V3PreExprToken{flp, V3PreExprToken::KET}); break;
                default: break;
                }
            } else if (*cp == ' ') {
                tstart = true;
            }
        }
        const bool got = parser.result();
        UASSERT_SELFTEST(bool, got, expect);
    }

    // METHODS
    void pushOp(const V3PreExprToken& token) {
        // UINFO(9, "  pushOp " << token.ascii() << endl);
        m_ops.push_back(token);
    }
    void pushValue(const V3PreExprToken& token) {
        // UINFO(9, "  pushValue " << token.ascii() << endl);
        m_values.push_back(token);
    }
    V3PreExprToken popValue() {
        if (m_values.empty()) {
            m_firstFileline->v3error("Syntax error in `ifdef () expression");
            return V3PreExprToken{m_firstFileline, false};
        }
        const V3PreExprToken tok = m_values.back();
        m_values.pop_back();
        // UINFO(9, "  popValue " << tok.ascii() << endl;
        return tok;
    }
    void reduce() {
        UASSERT(!m_ops.empty(), "lost op stack beginning END");
        V3PreExprToken tok = m_ops.back();
        // UINFO(9, "Reduce " << tok.ascii() << endl);
        m_ops.pop_back();
        switch (tok.token()) {
        case V3PreExprToken::KET: {
            while (m_ops.back().token() != V3PreExprToken::END
                   && m_ops.back().token() != V3PreExprToken::BRA)
                reduce();
            if (m_ops.back().token() == V3PreExprToken::BRA) {
                m_ops.pop_back();
            } else {
                tok.fileline()->v3error("Syntax error in `ifdef () expression:"  // LCOV_EXCL_LINE
                                        " ) without matching )");
                return;
            }
            break;
        }
        case V3PreExprToken::LNOT: {
            const V3PreExprToken lhs = popValue();
            pushValue(V3PreExprToken{tok.fileline(), !lhs.value()});
            break;
        }
        case V3PreExprToken::LAND: {
            const V3PreExprToken rhs = popValue();
            const V3PreExprToken lhs = popValue();
            pushValue(V3PreExprToken{tok.fileline(), lhs.value() && rhs.value()});
            break;
        }
        case V3PreExprToken::LOR: {
            const V3PreExprToken rhs = popValue();
            const V3PreExprToken lhs = popValue();
            pushValue(V3PreExprToken{tok.fileline(), lhs.value() || rhs.value()});
            break;
        }
        case V3PreExprToken::IMP: {
            const V3PreExprToken rhs = popValue();
            const V3PreExprToken lhs = popValue();
            pushValue(V3PreExprToken{tok.fileline(), !lhs.value() || rhs.value()});
            break;
        }
        case V3PreExprToken::EQV: {
            const V3PreExprToken rhs = popValue();
            const V3PreExprToken lhs = popValue();
            pushValue(V3PreExprToken{tok.fileline(), lhs.value() == rhs.value()});
            break;
        }
        default: {
            v3fatalSrc("bad case on operand stack");
            break;
        }
        }
    }
    void parse() {
        while (!m_inputs.empty()) {
            V3PreExprToken tok = m_inputs.front();
            m_inputs.pop_front();
            UINFO(9, "input read " << tok.ascii() << endl);
            if (tok.isValue()) {
                pushValue(tok);
                continue;
            }

            UASSERT(!m_ops.empty(), "lost op stack beginning END");
            V3PreExprToken topTok = m_ops.back();
            auto action = parseTable[topTok.token()][tok.token()];
            UINFO(9, "pop action " << actionAscii(action) << " from parseTable[" << topTok.ascii()
                                   << "][" << tok.ascii() << "]\n");
            switch (action) {
            case RR:  // Reduce
                reduce();
                break;
            case SS:  // Shift
                m_ops.push_back(tok);
                break;
            case AA:  // Accept
                break;
            default: tok.fileline()->v3error("Syntax error in `ifdef () expression"); return;
            }
        }
    }

public:
    // METHODS
    V3PreExpr() {}
    ~V3PreExpr() = default;
    void reset(FileLine* flp) {
        m_inputs.clear();
        m_values.clear();
        m_ops.clear();
        m_firstFileline = flp;
        pushOp(V3PreExprToken{flp, V3PreExprToken::END});
    }
    void pushInput(const V3PreExprToken& token) {
        if (!m_firstFileline) m_firstFileline = token.fileline();
        UINFO(9, "pushInput " << token.ascii() << endl);
        m_inputs.push_back(token);
    }
    bool result() {
        pushInput(V3PreExprToken{m_firstFileline, V3PreExprToken::END});
        parse();
        return popValue().value();
    }
    static void selfTest() VL_MT_DISABLED { selfTestImp(); }
};

#endif  // Guard
