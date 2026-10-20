// struct_netlist.h - parser, AST and flattening bit-level elaborator for the
// structural primitive netlists written by `verilator --struct-only-output`
// (structural_primitives.sv / RTL_* vocabularies).  Shared by svs_sat_equiv
// (CNF backend, CaDiCaL) and Verilator's V3EmitMap (AIG backend, libabc).
//
// The gate backend B must provide:
//   using Vec = std::vector<int>;  int newVar(); int T(); int F();
//   bool isConst(int), isTrue(int), isFalse(int); void equate(int, int);
//   int AND/OR/XOR(int,int), MUX(int s,int a0,int a1);
//   Vec constVec(ull,int), resize(Vec,int,bool), NOTv, ANDv, ORv, XORv, MUXv(int,Vec,Vec);
//   int redAnd/redOr/redXor(Vec); Vec add(Vec,Vec,int cin=0), sub, neg, mul, shl(Vec,Vec),
//   shr(Vec,Vec,bool arith); int eq(Vec,Vec), ltU, ltS; pair<Vec,Vec> divmodU, divmodS.
#ifndef SVS_STRUCT_NETLIST_H_
#define SVS_STRUCT_NETLIST_H_

#include <algorithm>
#include <cctype>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <fstream>
#include <functional>
#include <iostream>
#include <map>
#include <memory>
#include <set>
#include <sstream>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

namespace svs_netlist {

inline bool g_verbose = false;

[[noreturn]] inline void die(const std::string& msg) {
    std::cerr << "struct_netlist: error: " << msg << "\n";
    std::exit(2);
}
inline void warn(const std::string& msg) { std::cerr << "struct_netlist: warning: " << msg << "\n"; }
//######################################################################
// Lexer

enum class Tok { End, Ident, Number, Punct };

struct Token {
    Tok kind = Tok::End;
    std::string text;
    int line = 0;
};

class Lexer {
public:
    Lexer(const std::string& src, const std::string& file)
        : m_s{src}
        , m_file{file} {}
    std::vector<Token> run() {
        std::vector<Token> out;
        while (true) {
            skipSpace();
            if (m_pendingBlackbox) {  // a (* blackbox *) attribute was skipped
                m_pendingBlackbox = false;
                Token a;
                a.line = m_line;
                a.kind = Tok::Ident;
                a.text = "__blackbox__";
                out.push_back(a);
            }
            if (m_i >= m_s.size()) break;
            Token t;
            t.line = m_line;
            const char c = m_s[m_i];
            if (std::isalpha(static_cast<unsigned char>(c)) || c == '_' || c == '$') {
                size_t j = m_i;
                while (j < m_s.size()
                       && (std::isalnum(static_cast<unsigned char>(m_s[j])) || m_s[j] == '_'
                           || m_s[j] == '$'))
                    ++j;
                t.kind = Tok::Ident;
                t.text = m_s.substr(m_i, j - m_i);
                m_i = j;
            } else if (c == '\\') {  // escaped identifier
                size_t j = m_i + 1;
                while (j < m_s.size() && !std::isspace(static_cast<unsigned char>(m_s[j]))) ++j;
                t.kind = Tok::Ident;
                t.text = m_s.substr(m_i + 1, j - m_i - 1);
                m_i = j;
            } else if (std::isdigit(static_cast<unsigned char>(c)) || c == '\'') {
                // number: [size]'[s]base digits  |  decimal
                size_t j = m_i;
                while (j < m_s.size()
                       && (std::isalnum(static_cast<unsigned char>(m_s[j])) || m_s[j] == '_'
                           || m_s[j] == '\'' || m_s[j] == '?'
                           || (m_s[j] == '.' && j + 1 < m_s.size()
                               && std::isdigit(static_cast<unsigned char>(m_s[j + 1])))))  // real: 20.0
                    ++j;
                t.kind = Tok::Number;
                t.text = m_s.substr(m_i, j - m_i);
                m_i = j;
            } else if (c == '"') {
                size_t j = m_i + 1;
                while (j < m_s.size() && m_s[j] != '"') ++j;
                t.kind = Tok::Number;  // string literal: treated as an opaque constant
                t.text = m_s.substr(m_i, j + 1 - m_i);
                m_i = j + 1;
            } else {
                static const char* const multi[]
                    = {"+:", "-:", "<<<", ">>>", "<<", ">>", "<=", ">=", "==", "!=", "&&",
                       "||", "===", "!==", "**", nullptr};
                t.kind = Tok::Punct;
                t.text = std::string(1, c);
                for (int k = 0; multi[k]; ++k) {
                    const size_t n = std::strlen(multi[k]);
                    if (m_s.compare(m_i, n, multi[k]) == 0 && n > t.text.size()) t.text = multi[k];
                }
                m_i += t.text.size();
            }
            out.push_back(t);
        }
        Token e;
        e.kind = Tok::End;
        e.line = m_line;
        out.push_back(e);
        return out;
    }

private:
    const std::string& m_s;
    const std::string m_file;
    size_t m_i = 0;
    int m_line = 1;
    bool m_pendingBlackbox = false;
    void skipSpace() {
        while (m_i < m_s.size()) {
            const char c = m_s[m_i];
            if (c == '\n') {
                ++m_line;
                ++m_i;
            } else if (std::isspace(static_cast<unsigned char>(c))) {
                ++m_i;
            } else if (c == '/' && m_i + 1 < m_s.size() && m_s[m_i + 1] == '/') {
                while (m_i < m_s.size() && m_s[m_i] != '\n') ++m_i;
            } else if (c == '/' && m_i + 1 < m_s.size() && m_s[m_i + 1] == '*') {
                m_i += 2;
                while (m_i + 1 < m_s.size() && !(m_s[m_i] == '*' && m_s[m_i + 1] == '/')) {
                    if (m_s[m_i] == '\n') ++m_line;
                    ++m_i;
                }
                m_i += 2;
            } else if (c == '(' && m_i + 1 < m_s.size() && m_s[m_i + 1] == '*') {
                // attribute (* ... *): skipped, except that blackbox is remembered
                const size_t b = m_i + 2;
                m_i += 2;
                while (m_i + 1 < m_s.size() && !(m_s[m_i] == '*' && m_s[m_i + 1] == ')')) ++m_i;
                if (m_s.substr(b, m_i - b).find("blackbox") != std::string::npos) m_pendingBlackbox = true;
                m_i += 2;
            } else if (c == '`') {
                // compiler directive: skip the line
                while (m_i < m_s.size() && m_s[m_i] != '\n') ++m_i;
            } else {
                break;
            }
        }
    }
};

//######################################################################
// AST

struct Expr;
using ExprP = std::shared_ptr<Expr>;

struct Expr {
    enum Kind { IDENT, CONST, BITSEL, PARTSEL, PARTSEL_UP, CONCAT, REPL, UNARY, BINARY, COND };
    Kind kind;
    std::string name;  // IDENT; op for UNARY/BINARY
    std::vector<char> bits;  // CONST, LSB first: '0','1','x','z'
    std::string text;  // CONST: the literal as written ("str", 20.0, 256'h..)
    bool isSigned = false;  // CONST
    bool sized = true;  // CONST
    std::vector<ExprP> args;  // operands
    int ival = 0;  // PARTSEL: msb ; PARTSEL_UP: width ; REPL: count
    int ival2 = 0;  // PARTSEL: lsb
};

struct NetDecl {
    std::string name;
    int width = 1;
    int lsb = 0;  // declared [msb:lsb] lsb (part selects are relative to it)
    bool isSigned = false;
    int depth = 1;  // unpacked array elements (1 = scalar)
    int dir = 0;  // 0 internal, 1 input, 2 output, 3 inout
};

struct Pin {
    std::string name;
    ExprP expr;  // null = unconnected
};

struct Item {
    enum Kind { ASSIGN, CELL } kind;
    ExprP lhs, rhs;  // ASSIGN
    std::string modName, instName;  // CELL
    std::vector<std::pair<std::string, ExprP>> params;
    std::vector<Pin> pins;
    int line = 0;
};

struct Module {
    std::string name;
    bool blackbox = false;  // (* blackbox *): ports only; instances are kept, directions known
    std::vector<NetDecl> nets;  // in declaration order
    std::vector<std::string> ports;  // port names in order
    std::vector<Item> items;
    std::map<std::string, ExprP> params;  // localparam/parameter constants
};

//######################################################################
// Parser

class Parser {
public:
    Parser(std::vector<Token> toks, const std::string& file)
        : m_t{std::move(toks)}
        , m_file{file} {}

    void parseFile(std::map<std::string, Module>& mods) {
        bool bb = false;
        while (peek().kind != Tok::End) {
            if (accept("__blackbox__")) {
                bb = true;
            } else if (accept("module")) {
                Module m = parseModule();
                m.blackbox = bb;
                bb = false;
                if (mods.count(m.name)) warn("module " + m.name + " redefined; keeping the first");
                else mods[m.name] = std::move(m);
            } else {
                // skip anything else (packages, timescale remnants, ...) up to next module
                next();
            }
        }
    }

private:
    std::vector<Token> m_t;
    size_t m_p = 0;
    const std::string m_file;

    const Token& peek(int k = 0) const { return m_t[std::min(m_p + k, m_t.size() - 1)]; }
    Token next() {
        Token t = peek();
        if (m_p < m_t.size() - 1) ++m_p;
        return t;
    }
    bool is(const char* s, int k = 0) const { return peek(k).text == s && peek(k).kind != Tok::Number; }
    bool accept(const char* s) {
        if (is(s)) {
            next();
            return true;
        }
        return false;
    }
    void expect(const char* s) {
        if (!accept(s)) err(std::string("expected '") + s + "' but found '" + peek().text + "'");
    }
    [[noreturn]] void err(const std::string& msg) {
        die(m_file + ":" + std::to_string(peek().line) + ": " + msg);
    }
    std::string ident() {
        if (peek().kind != Tok::Ident) err("expected identifier, found '" + peek().text + "'");
        return next().text;
    }

    static bool isTypeKw(const std::string& s) {
        return s == "logic" || s == "wire" || s == "reg" || s == "bit" || s == "integer"
               || s == "int" || s == "tri" || s == "wand" || s == "wor";
    }

    // Parse an optional packed range; returns (width, lsb)
    bool parseRange(int& width, int& lsb) {
        if (!is("[")) return false;
        next();
        const ExprP a = parseExpr();
        expect(":");
        const ExprP b = parseExpr();
        expect("]");
        const long long hi = constEval(a);
        const long long lo = constEval(b);
        width = static_cast<int>(std::llabs(hi - lo) + 1);
        lsb = static_cast<int>(std::min(hi, lo));
        return true;
    }

    long long constEval(const ExprP& e) {
        switch (e->kind) {
        case Expr::CONST: {
            long long v = 0;
            for (int i = static_cast<int>(e->bits.size()) - 1; i >= 0; --i) {
                v = (v << 1) | (e->bits[i] == '1' ? 1 : 0);
            }
            return v;
        }
        case Expr::IDENT: {
            const auto it = m_curParams.find(e->name);
            if (it == m_curParams.end()) err("non-constant identifier '" + e->name + "' in constant expression");
            return constEval(it->second);
        }
        case Expr::UNARY: {
            const long long a = constEval(e->args[0]);
            if (e->name == "-") return -a;
            if (e->name == "~") return ~a;
            if (e->name == "!") return !a;
            if (e->name == "+") return a;
            break;
        }
        case Expr::BINARY: {
            const long long a = constEval(e->args[0]);
            const long long b = constEval(e->args[1]);
            const std::string& o = e->name;
            if (o == "+") return a + b;
            if (o == "-") return a - b;
            if (o == "*") return a * b;
            if (o == "/") return b ? a / b : 0;
            if (o == "%") return b ? a % b : 0;
            if (o == "<<") return a << b;
            if (o == ">>") return a >> b;
            if (o == "&") return a & b;
            if (o == "|") return a | b;
            if (o == "^") return a ^ b;
            if (o == "==") return a == b;
            if (o == "!=") return a != b;
            if (o == "<") return a < b;
            if (o == "<=") return a <= b;
            if (o == ">") return a > b;
            if (o == ">=") return a >= b;
            if (o == "**") {
                long long r = 1;
                for (long long i = 0; i < b; ++i) r *= a;
                return r;
            }
            break;
        }
        case Expr::COND: return constEval(e->args[0]) ? constEval(e->args[1]) : constEval(e->args[2]);
        default: break;
        }
        err("unsupported constant expression");
    }
    std::map<std::string, ExprP> m_curParams;

    Module parseModule() {
        Module m;
        m.name = ident();
        m_curParams.clear();
        if (accept("#")) {  // #( parameter ... )
            expect("(");
            while (!is(")")) {
                accept("parameter");
                accept("localparam");
                while (peek().kind == Tok::Ident && isTypeKw(peek().text)) next();
                accept("signed");
                int w, l;
                parseRange(w, l);
                const std::string n = ident();
                ExprP v;
                if (accept("=")) v = parseExpr();
                if (v) {
                    m.params[n] = v;
                    m_curParams[n] = v;
                }
                if (!accept(",")) break;
            }
            expect(")");
        }
        std::set<std::string> declared;
        if (accept("(")) {
            int dir = 0;
            while (!is(")")) {
                if (accept("input")) dir = 1;
                else if (accept("output")) dir = 2;
                else if (accept("inout")) dir = 3;
                NetDecl d;
                while (peek().kind == Tok::Ident && isTypeKw(peek().text)) next();
                if (accept("signed")) d.isSigned = true;
                accept("unsigned");
                parseRange(d.width, d.lsb);
                d.name = ident();
                d.dir = dir;
                parseUnpacked(d);
                m.ports.push_back(d.name);
                if (dir == 0) {
                    // non-ANSI name list; direction given in the body
                    m.ports.push_back(d.name);
                } else {
                    m.nets.push_back(d);
                    declared.insert(d.name);
                }
                if (!accept(",")) break;
            }
            expect(")");
        }
        expect(";");
        while (!accept("endmodule")) {
            if (peek().kind == Tok::End) err("unexpected end of file in module " + m.name);
            if (is("input") || is("output") || is("inout")) {
                const int dir = is("input") ? 1 : is("output") ? 2 : 3;
                next();
                NetDecl d;
                while (peek().kind == Tok::Ident && isTypeKw(peek().text)) next();
                if (accept("signed")) d.isSigned = true;
                parseRange(d.width, d.lsb);
                do {
                    NetDecl e = d;
                    e.name = ident();
                    e.dir = dir;
                    parseUnpacked(e);
                    if (!declared.count(e.name)) {
                        m.nets.push_back(e);
                        declared.insert(e.name);
                    }
                } while (accept(","));
                expect(";");
            } else if (is("localparam") || is("parameter")) {
                next();
                while (peek().kind == Tok::Ident && isTypeKw(peek().text)) next();
                accept("signed");
                int w, l;
                parseRange(w, l);
                do {
                    const std::string n = ident();
                    expect("=");
                    const ExprP v = parseExpr();
                    m.params[n] = v;
                    m_curParams[n] = v;
                } while (accept(","));
                expect(";");
            } else if (peek().kind == Tok::Ident && isTypeKw(peek().text)) {
                while (peek().kind == Tok::Ident && isTypeKw(peek().text)) next();
                NetDecl d;
                if (accept("signed")) d.isSigned = true;
                accept("unsigned");
                parseRange(d.width, d.lsb);
                do {
                    NetDecl e = d;
                    e.name = ident();
                    parseUnpacked(e);
                    if (accept("=")) parseExpr();  // net initialiser ignored
                    if (!declared.count(e.name)) {
                        m.nets.push_back(e);
                        declared.insert(e.name);
                    }
                } while (accept(","));
                expect(";");
            } else if (accept("assign")) {
                do {
                    Item it;
                    it.kind = Item::ASSIGN;
                    it.line = peek().line;
                    it.lhs = parseExpr();
                    expect("=");
                    it.rhs = parseExpr();
                    m.items.push_back(it);
                } while (accept(","));
                expect(";");
            } else if (accept("generate") || accept("endgenerate")) {
                // flattened output never has these, tolerate anyway
            } else if (peek().kind == Tok::Ident) {
                // cell instance:  MOD [#(...)] INST ( .pin(expr), ... );
                Item it;
                it.kind = Item::CELL;
                it.line = peek().line;
                it.modName = ident();
                if (accept("#")) {
                    expect("(");
                    while (!is(")")) {
                        if (accept(".")) {
                            const std::string pn = ident();
                            expect("(");
                            ExprP v;
                            if (!is(")")) v = parseExpr();
                            expect(")");
                            it.params.emplace_back(pn, v);
                        } else {
                            it.params.emplace_back("", parseExpr());
                        }
                        if (!accept(",")) break;
                    }
                    expect(")");
                }
                it.instName = ident();
                int w, l;
                if (parseRange(w, l)) err("arrayed instances are not supported");
                expect("(");
                while (!is(")")) {
                    Pin p;
                    if (accept(".")) {
                        p.name = ident();
                        expect("(");
                        if (!is(")")) p.expr = parseExpr();
                        expect(")");
                    } else {
                        p.expr = parseExpr();  // positional
                    }
                    it.pins.push_back(p);
                    if (!accept(",")) break;
                }
                expect(")");
                expect(";");
                m.items.push_back(it);
            } else {
                err("unexpected token '" + peek().text + "' in module " + m.name);
            }
        }
        return m;
    }

    void parseUnpacked(NetDecl& d) {
        while (is("[")) {
            next();
            const ExprP a = parseExpr();
            long long lo = 0, hi = 0;
            if (accept(":")) {
                const ExprP b = parseExpr();
                lo = constEval(a);
                hi = constEval(b);
            } else {
                hi = constEval(a) - 1;
            }
            expect("]");
            d.depth *= static_cast<int>(std::llabs(hi - lo) + 1);
        }
    }

    // ---- expressions (precedence climbing) ----
    static int prec(const std::string& op) {
        if (op == "**") return 12;
        if (op == "*" || op == "/" || op == "%") return 11;
        if (op == "+" || op == "-") return 10;
        if (op == "<<" || op == ">>" || op == "<<<" || op == ">>>") return 9;
        if (op == "<" || op == "<=" || op == ">" || op == ">=") return 8;
        if (op == "==" || op == "!=" || op == "===" || op == "!==") return 7;
        if (op == "&") return 6;
        if (op == "^") return 5;
        if (op == "|") return 4;
        if (op == "&&") return 3;
        if (op == "||") return 2;
        return -1;
    }
    ExprP parseExpr() { return parseCond(); }
    ExprP parseCond() {
        ExprP c = parseBinary(0);
        if (accept("?")) {
            ExprP t = parseExpr();
            expect(":");
            ExprP e = parseExpr();
            auto r = std::make_shared<Expr>();
            r->kind = Expr::COND;
            r->args = {c, t, e};
            return r;
        }
        return c;
    }
    ExprP parseBinary(int minPrec) {
        ExprP lhs = parseUnary();
        while (peek().kind == Tok::Punct && prec(peek().text) >= minPrec && prec(peek().text) > 0) {
            const std::string op = next().text;
            ExprP rhs = parseBinary(prec(op) + 1);
            auto r = std::make_shared<Expr>();
            r->kind = Expr::BINARY;
            r->name = op;
            r->args = {lhs, rhs};
            lhs = r;
        }
        return lhs;
    }
    ExprP parseUnary() {
        if (peek().kind == Tok::Punct) {
            const std::string& t = peek().text;
            if (t == "~" || t == "!" || t == "-" || t == "+" || t == "&" || t == "|" || t == "^") {
                next();
                auto r = std::make_shared<Expr>();
                r->kind = Expr::UNARY;
                r->name = t;
                r->args = {parseUnary()};
                return r;
            }
        }
        return parsePostfix(parsePrimary());
    }
    ExprP parsePostfix(ExprP base) {
        while (is("[")) {
            next();
            ExprP a = parseExpr();
            if (accept(":")) {
                ExprP b = parseExpr();
                expect("]");
                auto r = std::make_shared<Expr>();
                r->kind = Expr::PARTSEL;
                r->args = {base};
                r->ival = static_cast<int>(constEval(a));
                r->ival2 = static_cast<int>(constEval(b));
                base = r;
            } else if (is("+:") || is("-:")) {
                const bool up = next().text == "+:";
                ExprP w = parseExpr();
                expect("]");
                auto r = std::make_shared<Expr>();
                r->kind = Expr::PARTSEL_UP;
                r->args = {base, a};
                r->ival = static_cast<int>(constEval(w));
                if (!up) r->ival2 = 1;  // [i -: w]
                base = r;
            } else {
                expect("]");
                auto r = std::make_shared<Expr>();
                r->kind = Expr::BITSEL;
                r->args = {base, a};
                base = r;
            }
        }
        return base;
    }
    ExprP parsePrimary() {
        if (accept("(")) {
            ExprP e = parseExpr();
            expect(")");
            return e;
        }
        if (accept("{")) {
            ExprP first = parseExpr();
            if (accept("{")) {  // replicate {N{x}}
                ExprP inner = parseExpr();
                expect("}");
                expect("}");
                auto r = std::make_shared<Expr>();
                r->kind = Expr::REPL;
                r->ival = static_cast<int>(constEval(first));
                r->args = {inner};
                return r;
            }
            auto r = std::make_shared<Expr>();
            r->kind = Expr::CONCAT;
            r->args.push_back(first);
            while (accept(",")) r->args.push_back(parseExpr());
            expect("}");
            return r;
        }
        if (peek().kind == Tok::Number) return parseNumber(next().text);
        if (peek().kind == Tok::Ident) {
            auto r = std::make_shared<Expr>();
            r->kind = Expr::IDENT;
            r->name = next().text;
            return r;
        }
        err("unexpected token '" + peek().text + "' in expression");
    }

    ExprP parseNumber(const std::string& txt) {
        auto r = std::make_shared<Expr>();
        r->kind = Expr::CONST;
        r->text = txt;
        if (txt.find('\'') == std::string::npos && txt.find('.') != std::string::npos) {
            // real literal (a black-box parameter such as CLKFBOUT_MULT_F): its
            // integer part as a 32-bit value, the text kept for the emitter
            const long long v = static_cast<long long>(std::strtod(txt.c_str(), nullptr));
            for (int i = 0; i < 32; ++i) r->bits.push_back(((v >> i) & 1) ? '1' : '0');
            r->sized = false;
            r->isSigned = true;
            return r;
        }
        if (!txt.empty() && txt[0] == '"') {  // string: opaque, 8 bits per char
            for (int i = static_cast<int>(txt.size()) - 2; i >= 1; --i) {
                for (int b = 0; b < 8; ++b) r->bits.push_back(((txt[i] >> b) & 1) ? '1' : '0');
            }
            if (r->bits.empty()) r->bits.push_back('0');
            return r;
        }
        std::string s;
        for (const char c : txt) if (c != '_') s += c;
        const size_t q = s.find('\'');
        if (q == std::string::npos) {  // plain decimal, 32-bit unsized signed
            unsigned long long v = std::strtoull(s.c_str(), nullptr, 10);
            for (int i = 0; i < 32; ++i) r->bits.push_back(((v >> i) & 1) ? '1' : '0');
            r->sized = false;
            r->isSigned = true;
            return r;
        }
        int width = q == 0 ? -1 : std::atoi(s.substr(0, q).c_str());
        size_t i = q + 1;
        if (i < s.size() && (s[i] == 's' || s[i] == 'S')) {
            r->isSigned = true;
            ++i;
        }
        char base = 'd';
        if (i < s.size() && std::isalpha(static_cast<unsigned char>(s[i]))) base = static_cast<char>(std::tolower(s[i++]));
        else if (width == -1) base = 'b';  // '0 / '1 / 'x
        const std::string digits = s.substr(i);
        std::vector<char> bits;  // LSB first
        if (base == 'd') {
            unsigned long long v = 0;
            bool xz = false;
            for (const char c : digits) {
                if (c == 'x' || c == 'X' || c == 'z' || c == 'Z' || c == '?') xz = true;
                else v = v * 10 + (c - '0');
            }
            for (int b = 0; b < 64; ++b) bits.push_back(xz ? 'x' : (((v >> b) & 1) ? '1' : '0'));
        } else {
            const int bpd = base == 'h' ? 4 : base == 'o' ? 3 : 1;
            for (int k = static_cast<int>(digits.size()) - 1; k >= 0; --k) {
                const char c = static_cast<char>(std::tolower(digits[k]));
                if (c == 'x' || c == 'z' || c == '?') {
                    for (int b = 0; b < bpd; ++b) bits.push_back(c == 'x' ? 'x' : 'z');
                } else {
                    const int v = std::isdigit(static_cast<unsigned char>(c)) ? c - '0' : c - 'a' + 10;
                    for (int b = 0; b < bpd; ++b) bits.push_back(((v >> b) & 1) ? '1' : '0');
                }
            }
        }
        if (width == -1) {
            // unsized: '0 '1 'x fill one bit (extended on use); 'h.. unsized = 32
            if (q == 0) {
                r->sized = false;
                width = 1;
                if (bits.empty()) bits.push_back('0');
                bits.resize(1);
            } else {
                width = 32;
                r->sized = false;
            }
        }
        // resize to width (zero / x / z extend from the top digit)
        const char ext = (!bits.empty() && (bits.back() == 'x' || bits.back() == 'z')) ? bits.back() : '0';
        bits.resize(width, ext);
        r->bits = bits;
        return r;
    }
};


using Vec = std::vector<int>;  // literals, LSB first (backend-specific encoding)
//######################################################################
// Design elaboration: flatten + bit-blast one netlist

struct NetBits {
    Vec bits;
    std::vector<int> drivers;  // per-bit driver count
    int width = 1;
    int lsb = 0;
    bool isSigned = false;
    int depth = 1;
};

struct Design {
    std::string label;
    std::map<std::string, NetBits> nets;  // hierarchical name -> bits
    std::map<std::string, Vec> inputs;  // top primary inputs
    std::map<std::string, Vec> outputs;  // top primary outputs (+ inouts)
    std::set<std::string> inouts;  // which of `outputs` are inout ports
    std::map<std::string, Vec> regNext;  // register Q name -> next-state function
    std::map<std::string, Vec> regQ;  // register Q name -> Q bits (free)
    std::map<std::string, Vec> bbIn;  // "inst.pin" -> black-box input pin value
    std::map<std::string, Vec> bbOut;  // "inst.pin" -> black-box output pin bits (free)
    int cells = 0;
    // Structural records for mappers (filled alongside the comparison view)
    struct Reg {
        std::string name;  // register (Q lvalue text)
        Vec q, d;  // per-bit Q (free) and D (next-state function without rst/en)
        int en = 0, rst = 0, clk = 0;  // literals (en/rst may be constants)
        bool async = false, negedge = false;
        unsigned long long resetVal = 0;
        unsigned long long initVal = 0;  // power-up value (INIT_VAL)
    };
    std::vector<Reg> regs;
    struct Cell {  // memory or black-box instance kept as-is
        std::string type, name;
        std::vector<std::pair<std::string, std::string>> params;
        std::vector<std::pair<std::string, Vec>> ins;  // pin -> bits (values)
        std::vector<std::pair<std::string, Vec>> outs;  // pin -> bits (free)
    };
    std::vector<Cell> cells2;
    std::vector<std::pair<std::string, int>> clocks;  // hint: nets used as register clocks
};

template <class GB>
class Elaborator {
public:
    Elaborator(GB& bl, const std::map<std::string, Module>& mods,
               const std::set<std::string>& blackboxes, bool ffrip)
        : m_bl{bl}
        , m_mods{mods}
        , m_bb{blackboxes}
        , m_ffrip{ffrip} {}

    void run(const std::string& top, Design& d) {
        m_d = &d;
        const auto it = m_mods.find(top);
        if (it == m_mods.end()) die("top module '" + top + "' not found in " + d.label);
        elaborate(it->second, "", nullptr, nullptr);
        // top ports
        for (const std::string& p : it->second.ports) {
            const NetBits* nb = findNet(p);
            if (!nb) continue;
            const NetDecl* decl = nullptr;
            for (const NetDecl& nd : it->second.nets) if (nd.name == p) decl = &nd;
            if (!decl) continue;
            if (decl->dir == 1) d.inputs[p] = nb->bits;
            else d.outputs[p] = nb->bits;
            if (decl->dir == 3) d.inouts.insert(p);
        }
        // undriven internal nets stay free: report them
        for (const auto& kv : d.nets) {
            if (kv.second.depth != 1) continue;
            int undriven = 0;
            for (const int c : kv.second.drivers) if (c == 0) ++undriven;
            if (undriven == kv.second.width && !d.inputs.count(kv.first) && !d.regQ.count(kv.first)
                && !m_bbOutNets.count(kv.first)) {
                if (g_verbose) warn(d.label + ": net " + kv.first + " is undriven (free)");
            }
        }
    }

private:
    GB& m_bl;
    const std::map<std::string, Module>& m_mods;
    const std::set<std::string>& m_bb;
    const bool m_ffrip;
    Design* m_d = nullptr;
    std::set<std::string> m_bbOutNets;

    struct Scope {
        std::string prefix;
        const Module* mod;
    };

    NetBits* findNet(const std::string& hname) {
        const auto it = m_d->nets.find(hname);
        return it == m_d->nets.end() ? nullptr : &it->second;
    }

    // ---- primitive knowledge ----
    static bool isRegPrim(const std::string& n) {
        return n == "dff_en" || n == "dffn_en" || n == "dff" || n == "latch_en"
               || n.rfind("RTL_REG", 0) == 0;
    }
    static bool isKnownPrim(const std::string& n) {
        static const std::set<std::string> k = {
            "adder", "adder_carry", "subtractor", "multiplier", "multiplier_signed", "divider",
            "divider_signed", "modulo", "modulo_signed", "negator", "incrementer", "decrementer",
            "bitwise_and", "bitwise_or", "bitwise_xor", "bitwise_not", "reduction_and",
            "reduction_or", "reduction_xor", "logical_not", "comparator_eq", "comparator_neq",
            "comparator_lt", "comparator_lte", "comparator_gt", "comparator_gte",
            "comparator_lt_signed", "comparator_lte_signed", "comparator_gt_signed",
            "comparator_gte_signed", "shifter_left", "shifter_right", "shifter_right_arith",
            "mux2", "mux4", "sign_extender", "RTL_INV", "RTL_AND", "RTL_OR", "RTL_XOR",
            "RTL_MUX", "RTL_ADD", "RTL_SUB", "RTL_MUL", "RTL_LSHIFT", "RTL_RSHIFT", "RTL_EQ",
            "RTL_NEQ", "RTL_LT", "RTL_LEQ", "RTL_GT", "RTL_GEQ"};
        return k.count(n) > 0 || isRegPrim(n);
    }

    // ---- expression evaluation in a scope ----
    int exprWidth(const ExprP& e, const Scope& sc) {
        switch (e->kind) {
        case Expr::IDENT: {
            const NetBits* nb = findNet(sc.prefix + e->name);
            if (nb) return nb->width;
            const auto p = sc.mod->params.find(e->name);
            if (p != sc.mod->params.end()) return exprWidth(p->second, sc);
            return 1;
        }
        case Expr::CONST: return e->bits.size();
        case Expr::BITSEL: return 1;
        case Expr::PARTSEL: return std::abs(e->ival - e->ival2) + 1;
        case Expr::PARTSEL_UP: return e->ival;
        case Expr::CONCAT: {
            int w = 0;
            for (const ExprP& a : e->args) w += exprWidth(a, sc);
            return w;
        }
        case Expr::REPL: return e->ival * exprWidth(e->args[0], sc);
        case Expr::UNARY:
            if (e->name == "!" || e->name == "&" || e->name == "|" || e->name == "^") return 1;
            return exprWidth(e->args[0], sc);
        case Expr::BINARY: {
            const std::string& o = e->name;
            if (o == "==" || o == "!=" || o == "<" || o == "<=" || o == ">" || o == ">=" || o == "&&"
                || o == "||" || o == "===" || o == "!==")
                return 1;
            if (o == "<<" || o == ">>" || o == "<<<" || o == ">>>" || o == "**") return exprWidth(e->args[0], sc);
            return std::max(exprWidth(e->args[0], sc), exprWidth(e->args[1], sc));
        }
        case Expr::COND: return std::max(exprWidth(e->args[1], sc), exprWidth(e->args[2], sc));
        }
        return 1;
    }
    bool exprSigned(const ExprP& e, const Scope& sc) {
        switch (e->kind) {
        case Expr::IDENT: {
            const NetBits* nb = findNet(sc.prefix + e->name);
            return nb ? nb->isSigned : false;
        }
        case Expr::CONST: return e->isSigned;
        case Expr::UNARY: return (e->name == "-" || e->name == "~" || e->name == "+") && exprSigned(e->args[0], sc);
        case Expr::BINARY: {
            const std::string& o = e->name;
            if (o == "+" || o == "-" || o == "*" || o == "/" || o == "%" || o == "&" || o == "|" || o == "^")
                return exprSigned(e->args[0], sc) && exprSigned(e->args[1], sc);
            if (o == "<<" || o == ">>" || o == "<<<" || o == ">>>") return exprSigned(e->args[0], sc);
            return false;
        }
        case Expr::COND: return exprSigned(e->args[1], sc) && exprSigned(e->args[2], sc);
        default: return false;
        }
    }

    Vec eval(const ExprP& e, const Scope& sc, int ctxWidth = -1) {
        switch (e->kind) {
        case Expr::IDENT: {
            const NetBits* nb = findNet(sc.prefix + e->name);
            if (nb) return nb->bits;
            const auto p = sc.mod->params.find(e->name);
            if (p != sc.mod->params.end()) return eval(p->second, sc, ctxWidth);
            die(m_d->label + ": undeclared identifier '" + e->name + "' in " + sc.mod->name);
        }
        case Expr::CONST: {
            Vec r(e->bits.size());
            for (size_t i = 0; i < e->bits.size(); ++i) r[i] = e->bits[i] == '1' ? m_bl.T() : m_bl.F();
            if (!e->sized && ctxWidth > 0 && static_cast<int>(r.size()) < ctxWidth) {
                // '0 / '1 fill; unsized decimal sign-extends if signed
                const bool fill = e->bits.size() == 1 ? e->bits[0] == '1' : (e->isSigned && e->bits.back() == '1');
                r.resize(ctxWidth, fill ? m_bl.T() : m_bl.F());
            }
            return r;
        }
        case Expr::BITSEL: {
            const Vec base = eval(e->args[0], sc);
            const int lsb = baseLsb(e->args[0], sc);
            const ExprP& ie = e->args[1];
            if (isConstExpr(ie, sc)) {
                const long long i = constOf(ie, sc) - lsb;
                return {(i >= 0 && i < static_cast<long long>(base.size())) ? base[i] : m_bl.F()};
            }
            const Vec idx = eval(ie, sc);
            // dynamic bit select: mux over all positions
            int r = m_bl.F();
            for (size_t i = 0; i < base.size(); ++i) {
                r = m_bl.MUX(m_bl.eq(idx, m_bl.constVec(i + lsb, idx.size())), r, base[i]);
            }
            return {r};
        }
        case Expr::PARTSEL: {
            const Vec base = eval(e->args[0], sc);
            const int lsb = baseLsb(e->args[0], sc);
            const int hi = std::max(e->ival, e->ival2) - lsb;
            const int lo = std::min(e->ival, e->ival2) - lsb;
            Vec r;
            for (int i = lo; i <= hi; ++i) r.push_back((i >= 0 && i < static_cast<int>(base.size())) ? base[i] : m_bl.F());
            return r;
        }
        case Expr::PARTSEL_UP: {
            const Vec base = eval(e->args[0], sc);
            const int lsb = baseLsb(e->args[0], sc);
            const int w = e->ival;
            const ExprP& ie = e->args[1];
            if (isConstExpr(ie, sc)) {
                long long lo = constOf(ie, sc) - lsb;
                if (e->ival2) lo = lo - w + 1;  // [i -: w]
                Vec r;
                for (int i = 0; i < w; ++i) {
                    const long long k = lo + i;
                    r.push_back((k >= 0 && k < static_cast<long long>(base.size())) ? base[k] : m_bl.F());
                }
                return r;
            }
            const Vec idx = eval(ie, sc);
            Vec r(w, m_bl.F());
            for (size_t s = 0; s < base.size(); ++s) {
                const int hit = m_bl.eq(idx, m_bl.constVec(s + lsb + (e->ival2 ? w - 1 : 0), idx.size()));
                for (int i = 0; i < w; ++i) {
                    const size_t k = s + i;
                    r[i] = m_bl.MUX(hit, r[i], k < base.size() ? base[k] : m_bl.F());
                }
            }
            return r;
        }
        case Expr::CONCAT: {
            Vec r;
            for (int i = static_cast<int>(e->args.size()) - 1; i >= 0; --i) {
                const Vec a = eval(e->args[i], sc);
                r.insert(r.end(), a.begin(), a.end());
            }
            return r;
        }
        case Expr::REPL: {
            const Vec a = eval(e->args[0], sc);
            Vec r;
            for (int i = 0; i < e->ival; ++i) r.insert(r.end(), a.begin(), a.end());
            return r;
        }
        case Expr::UNARY: {
            const std::string& o = e->name;
            if (o == "!" || o == "&" || o == "|" || o == "^") {
                const Vec a = eval(e->args[0], sc);
                if (o == "!") return {m_bl.NOT(m_bl.redOr(a))};
                if (o == "&") return {m_bl.redAnd(a)};
                if (o == "|") return {m_bl.redOr(a)};
                return {m_bl.redXor(a)};
            }
            const int w = ctxWidth > 0 ? std::max(ctxWidth, exprWidth(e, sc)) : exprWidth(e, sc);
            const Vec a = m_bl.resize(eval(e->args[0], sc, w), w, exprSigned(e->args[0], sc));
            if (o == "~") return m_bl.NOTv(a);
            if (o == "-") return m_bl.neg(a);
            return a;
        }
        case Expr::BINARY: return evalBinary(e, sc, ctxWidth);
        case Expr::COND: {
            const int w = ctxWidth > 0 ? std::max(ctxWidth, exprWidth(e, sc)) : exprWidth(e, sc);
            const int c = m_bl.redOr(eval(e->args[0], sc));
            const Vec t = m_bl.resize(eval(e->args[1], sc, w), w, exprSigned(e->args[1], sc));
            const Vec f = m_bl.resize(eval(e->args[2], sc, w), w, exprSigned(e->args[2], sc));
            return m_bl.MUXv(c, f, t);
        }
        }
        return {};
    }
    Vec evalBinary(const ExprP& e, const Scope& sc, int ctxWidth) {
        const std::string& o = e->name;
        const bool sg = exprSigned(e->args[0], sc) && exprSigned(e->args[1], sc);
        if (o == "&&" || o == "||") {
            const int a = m_bl.redOr(eval(e->args[0], sc));
            const int b = m_bl.redOr(eval(e->args[1], sc));
            return {o == "&&" ? m_bl.AND(a, b) : m_bl.OR(a, b)};
        }
        if (o == "<<" || o == ">>" || o == "<<<" || o == ">>>") {
            const int w = ctxWidth > 0 ? std::max(ctxWidth, exprWidth(e, sc)) : exprWidth(e, sc);
            const Vec a = m_bl.resize(eval(e->args[0], sc, w), w, exprSigned(e->args[0], sc));
            const Vec b = eval(e->args[1], sc);
            if (o == "<<" || o == "<<<") return m_bl.shl(a, b);
            return m_bl.shr(a, b, o == ">>>" && exprSigned(e->args[0], sc));
        }
        const bool cmp = o == "==" || o == "!=" || o == "<" || o == "<=" || o == ">" || o == ">=" || o == "===" || o == "!==";
        const int ow = std::max(exprWidth(e->args[0], sc), exprWidth(e->args[1], sc));
        const int w = cmp ? ow : (ctxWidth > 0 ? std::max(ctxWidth, ow) : ow);
        const Vec a = m_bl.resize(eval(e->args[0], sc, w), w, sg);
        const Vec b = m_bl.resize(eval(e->args[1], sc, w), w, sg);
        if (o == "+") return m_bl.add(a, b);
        if (o == "-") return m_bl.sub(a, b);
        if (o == "*") return m_bl.mul(a, b);
        if (o == "/") return sg ? m_bl.divmodS(a, b).first : m_bl.divmodU(a, b).first;
        if (o == "%") return sg ? m_bl.divmodS(a, b).second : m_bl.divmodU(a, b).second;
        if (o == "&") return m_bl.ANDv(a, b);
        if (o == "|") return m_bl.ORv(a, b);
        if (o == "^") return m_bl.XORv(a, b);
        if (o == "==" || o == "===") return {m_bl.eq(a, b)};
        if (o == "!=" || o == "!==") return {m_bl.NOT(m_bl.eq(a, b))};
        if (o == "<") return {sg ? m_bl.ltS(a, b) : m_bl.ltU(a, b)};
        if (o == ">") return {sg ? m_bl.ltS(b, a) : m_bl.ltU(b, a)};
        if (o == "<=") return {-(sg ? m_bl.ltS(b, a) : m_bl.ltU(b, a))};
        if (o == ">=") return {-(sg ? m_bl.ltS(a, b) : m_bl.ltU(a, b))};
        die("unsupported operator '" + o + "'");
    }
    int baseLsb(const ExprP& base, const Scope& sc) {
        if (base->kind == Expr::IDENT) {
            const NetBits* nb = findNet(sc.prefix + base->name);
            if (nb) return nb->lsb;
        }
        return 0;
    }
    bool isConstExpr(const ExprP& e, const Scope& sc) {
        switch (e->kind) {
        case Expr::CONST: return true;
        case Expr::IDENT: return sc.mod->params.count(e->name) > 0;
        case Expr::UNARY: return isConstExpr(e->args[0], sc);
        case Expr::BINARY: return isConstExpr(e->args[0], sc) && isConstExpr(e->args[1], sc);
        case Expr::COND: return isConstExpr(e->args[0], sc) && isConstExpr(e->args[1], sc) && isConstExpr(e->args[2], sc);
        default: return false;
        }
    }
    long long constOf(const ExprP& e, const Scope& sc) {
        const Vec v = eval(e, sc);
        long long r = 0;
        for (int i = static_cast<int>(v.size()) - 1; i >= 0; --i) r = (r << 1) | (m_bl.isTrue(v[i]) ? 1 : 0);
        if (exprSigned(e, sc) && !v.empty() && m_bl.isTrue(v.back()) && v.size() < 64) r -= (1LL << v.size());
        return r;
    }

    // ---- lvalues ----
    // Drive the target bits of an lvalue expression with `val`
    void driveLValue(const ExprP& lhs, const Vec& val, const Scope& sc, const std::string& what) {
        switch (lhs->kind) {
        case Expr::IDENT: {
            NetBits* nb = findNet(sc.prefix + lhs->name);
            if (!nb) die(m_d->label + ": assignment to undeclared '" + lhs->name + "' in " + sc.mod->name);
            driveBits(*nb, 0, val, sc.prefix + lhs->name, what, true);
            return;
        }
        case Expr::BITSEL:
        case Expr::PARTSEL:
        case Expr::PARTSEL_UP: {
            const ExprP& base = lhs->args[0];
            if (base->kind != Expr::IDENT) die("unsupported nested lvalue select");
            NetBits* nb = findNet(sc.prefix + base->name);
            if (!nb) die(m_d->label + ": assignment to undeclared '" + base->name + "'");
            long long lo;
            if (lhs->kind == Expr::PARTSEL) lo = std::min(lhs->ival, lhs->ival2) - nb->lsb;
            else {
                if (!isConstExpr(lhs->args[1], sc)) {
                    // dynamic part-select write: every candidate slot gets a mux
                    // (idx==k ? val : old).  Rare; treat as unsupported for now.
                    die(m_d->label + ": dynamic index on assignment target '" + base->name + "' unsupported");
                }
                lo = constOf(lhs->args[1], sc) - nb->lsb;
                if (lhs->kind == Expr::PARTSEL_UP && lhs->ival2) lo = lo - lhs->ival + 1;
            }
            // only the selected bits are driven: a wider driver (a 32-bit
            // DOADO into qa[i]) is truncated, a narrower one zero-extended
            const int selW = lhs->kind == Expr::BITSEL ? 1
                             : lhs->kind == Expr::PARTSEL ? std::abs(lhs->ival - lhs->ival2) + 1
                                                          : lhs->ival;
            driveBits(*nb, static_cast<int>(lo), m_bl.resize(val, selW, false), sc.prefix + base->name, what);
            return;
        }
        case Expr::CONCAT: {
            int lsb = 0;
            for (int i = static_cast<int>(lhs->args.size()) - 1; i >= 0; --i) {
                const int w = exprWidth(lhs->args[i], sc);
                Vec part;
                for (int k = 0; k < w; ++k) part.push_back(lsb + k < static_cast<int>(val.size()) ? val[lsb + k] : m_bl.F());
                driveLValue(lhs->args[i], part, sc, what);
                lsb += w;
            }
            return;
        }
        default: die("unsupported assignment target in " + sc.mod->name);
        }
    }
    // A net bit with two drivers would put two contradictory definitions
    // into the solver (and make any miter vacuously UNSAT), so it is an error.
    void driveBits(NetBits& nb, int lo, const Vec& val, const std::string& hname, const std::string& what,
                   bool whole = false) {
        for (size_t i = 0; i < val.size(); ++i) {
            const long long k = lo + static_cast<long long>(i);
            if (k < 0 || k >= nb.width) continue;  // width mismatch: truncate
            if (nb.drivers[k]++ > 0) {
                die(m_d->label + ": multiple drivers on " + hname + "[" + std::to_string(k) + "] (" + what + ")");
            }
            m_bl.equate(nb.bits[k], val[i]);
        }
        // missing upper bits of a whole-net assign: zero-extend the driver
        // (Verilog assign semantics); a part-select drives only its bits
        if (!whole || val.empty()) return;
        for (long long k = static_cast<long long>(val.size()); k < nb.width; ++k) {
            if (nb.drivers[k]++ > 0) die(m_d->label + ": multiple drivers on " + hname + "[" + std::to_string(k) + "] (" + what + ")");
            m_bl.equate(nb.bits[k], m_bl.F());
        }
    }

    // ---- elaboration ----
    void elaborate(const Module& m, const std::string& prefix, const Item* instItem, const Scope* parent) {
        Scope sc{prefix, &m};
        // Allocate nets
        for (const NetDecl& d : m.nets) {
            NetBits nb;
            nb.width = d.width;
            nb.lsb = d.lsb;
            nb.isSigned = d.isSigned;
            nb.depth = d.depth;
            const int total = d.width * d.depth;
            nb.bits.resize(total);
            nb.drivers.assign(total, 0);
            for (int i = 0; i < total; ++i) nb.bits[i] = m_bl.newVar();
            if (d.depth != 1) warn(m_d->label + ": unpacked array net " + prefix + d.name + " kept as a flat " + std::to_string(total) + "-bit vector");
            nb.width = total;
            m_d->nets[prefix + d.name] = nb;
        }
        // Connect ports to the parent
        if (instItem) {
            std::map<std::string, const NetDecl*> decls;
            for (const NetDecl& d : m.nets) decls[d.name] = &d;
            size_t pos = 0;
            for (const Pin& p : instItem->pins) {
                std::string pname = p.name;
                if (pname.empty()) {
                    if (pos < m.ports.size()) pname = m.ports[pos];
                    ++pos;
                }
                const auto dit = decls.find(pname);
                if (dit == decls.end()) {
                    warn(m_d->label + ": pin ." + pname + " not a port of " + m.name);
                    continue;
                }
                if (!p.expr) continue;
                NetBits* child = findNet(prefix + pname);
                if (dit->second->dir == 1) {
                    const Vec v = eval(p.expr, *parent, child->width);
                    driveBits(*child, 0, m_bl.resize(v, child->width, false), prefix + pname, "port input");
                } else {
                    // output / inout: child net drives the parent lvalue
                    driveLValue(p.expr, child->bits, *parent, "port output of " + prefix);
                }
            }
        }
        for (const Item& it : m.items) {
            if (it.kind == Item::ASSIGN) {
                const int w = exprWidth(it.lhs, sc);
                const Vec v = eval(it.rhs, sc, w);
                driveLValue(it.lhs, m_bl.resize(v, w, exprSigned(it.rhs, sc)), sc, "assign at line " + std::to_string(it.line));
            } else {
                elaborateCell(it, sc);
            }
        }
    }

    long long paramInt(const Item& it, const char* name, long long dflt, const Scope& sc) {
        for (const auto& kv : it.params) {
            if (kv.first == name && kv.second) return constOf(kv.second, sc);
        }
        return dflt;
    }
    const ExprP pinExpr(const Item& it, const char* name) {
        for (const Pin& p : it.pins) if (p.name == name) return p.expr;
        return nullptr;
    }
    Vec pinIn(const Item& it, const char* name, const Scope& sc, int width) {
        const ExprP e = pinExpr(it, name);
        if (!e) return m_bl.constVec(0, width);
        return m_bl.resize(eval(e, sc, width), width, false);
    }
    int pinWidth(const Item& it, const char* name, const Scope& sc) {
        const ExprP e = pinExpr(it, name);
        return e ? exprWidth(e, sc) : 1;
    }
    void pinOut(const Item& it, const char* name, const Vec& v, const Scope& sc) {
        const ExprP e = pinExpr(it, name);
        if (!e) return;
        driveLValue(e, v, sc, "output pin ." + std::string(name) + " of " + it.instName);
    }

    void elaborateCell(const Item& it, const Scope& sc) {
        const std::string& mn = it.modName;
        const std::string inst = sc.prefix + it.instName;
        ++m_d->cells;
        if (!m_bb.count(mn) && mn.rfind("memory_", 0) == 0) {
            memoryCell(it, sc, inst);
            return;
        }
        if (!m_bb.count(mn) && !isKnownPrim(mn)) {
            const auto mit = m_mods.find(mn);
            if (mit != m_mods.end() && mit->second.blackbox) {
                blackBox(it, sc, inst, &mit->second);
                return;
            }
            if (mit != m_mods.end()) {
                elaborate(mit->second, inst + ".", &it, &sc);
                return;
            }
            if (mn.rfind("memory_", 0) != 0) warn(m_d->label + ": module '" + mn + "' (instance " + inst + ") has no definition; treated as a black box");
            blackBox(it, sc, inst);
            return;
        }
        if (m_bb.count(mn)) {
            blackBox(it, sc, inst);
            return;
        }
        if (isRegPrim(mn)) {
            registerCell(it, sc, inst);
            return;
        }
        // ---- combinational primitives ----
        auto two = [&](const char* a, const char* b, const char* o, int w) {
            return std::make_pair(pinIn(it, a, sc, w), pinIn(it, b, sc, w));
        };
        const bool rtl = mn.rfind("RTL_", 0) == 0;
        const char* A = rtl ? "I0" : "a";
        const char* B = rtl ? "I1" : "b";
        const char* O = rtl ? "O" : "out";
        const char* IN = rtl ? "I0" : "in";
        int W = static_cast<int>(paramInt(it, "WIDTH", -1, sc));
        if (W < 0) {
            // RTL_* cells carry no parameters: take the width from the pins
            W = std::max({pinWidth(it, A, sc), pinWidth(it, B, sc), pinWidth(it, IN, sc)});
            if (mn == "RTL_MUX" || mn == "RTL_ADD" || mn == "RTL_SUB" || mn == "RTL_MUL" || mn == "RTL_LSHIFT"
                || mn == "RTL_RSHIFT" || mn == "RTL_INV" || mn == "RTL_AND" || mn == "RTL_OR" || mn == "RTL_XOR")
                W = std::max(W, pinWidth(it, O, sc));
        }
        if (mn == "adder" || mn == "RTL_ADD") { auto p = two(A, B, O, W); pinOut(it, O, m_bl.add(p.first, p.second), sc); }
        else if (mn == "adder_carry") {
            auto p = two("a", "b", "out", W + 1);
            Vec s = m_bl.add(p.first, p.second, m_bl.redOr(pinIn(it, "cin", sc, 1)));
            pinOut(it, "out", Vec(s.begin(), s.begin() + W), sc);
            pinOut(it, "cout", {s[W]}, sc);
        }
        else if (mn == "subtractor" || mn == "RTL_SUB") { auto p = two(A, B, O, W); pinOut(it, O, m_bl.sub(p.first, p.second), sc); }
        else if (mn == "multiplier" || mn == "multiplier_signed" || mn == "RTL_MUL") { auto p = two(A, B, O, W); pinOut(it, O, m_bl.mul(p.first, p.second), sc); }
        else if (mn == "divider") { auto p = two(A, B, O, W); pinOut(it, O, m_bl.divmodU(p.first, p.second).first, sc); }
        else if (mn == "divider_signed") { auto p = two(A, B, O, W); pinOut(it, O, m_bl.divmodS(p.first, p.second).first, sc); }
        else if (mn == "modulo") { auto p = two(A, B, O, W); pinOut(it, O, m_bl.divmodU(p.first, p.second).second, sc); }
        else if (mn == "modulo_signed") { auto p = two(A, B, O, W); pinOut(it, O, m_bl.divmodS(p.first, p.second).second, sc); }
        else if (mn == "negator") pinOut(it, "out", m_bl.neg(pinIn(it, "in", sc, W)), sc);
        else if (mn == "incrementer") pinOut(it, "out", m_bl.add(pinIn(it, "in", sc, W), m_bl.constVec(1, W)), sc);
        else if (mn == "decrementer") pinOut(it, "out", m_bl.sub(pinIn(it, "in", sc, W), m_bl.constVec(1, W)), sc);
        else if (mn == "bitwise_and" || mn == "RTL_AND") { auto p = two(A, B, O, W); pinOut(it, O, m_bl.ANDv(p.first, p.second), sc); }
        else if (mn == "bitwise_or" || mn == "RTL_OR") { auto p = two(A, B, O, W); pinOut(it, O, m_bl.ORv(p.first, p.second), sc); }
        else if (mn == "bitwise_xor" || mn == "RTL_XOR") { auto p = two(A, B, O, W); pinOut(it, O, m_bl.XORv(p.first, p.second), sc); }
        else if (mn == "bitwise_not" || mn == "RTL_INV") pinOut(it, O, m_bl.NOTv(pinIn(it, IN, sc, W)), sc);
        else if (mn == "reduction_and") pinOut(it, "out", {m_bl.redAnd(pinIn(it, "in", sc, W))}, sc);
        else if (mn == "reduction_or") pinOut(it, "out", {m_bl.redOr(pinIn(it, "in", sc, W))}, sc);
        else if (mn == "reduction_xor") pinOut(it, "out", {m_bl.redXor(pinIn(it, "in", sc, W))}, sc);
        else if (mn == "logical_not") pinOut(it, "out", {m_bl.NOT(m_bl.redOr(pinIn(it, "in", sc, pinWidth(it, "in", sc))))}, sc);
        else if (mn == "comparator_eq" || mn == "RTL_EQ") { auto p = two(A, B, O, W); pinOut(it, O, {m_bl.eq(p.first, p.second)}, sc); }
        else if (mn == "comparator_neq" || mn == "RTL_NEQ") { auto p = two(A, B, O, W); pinOut(it, O, {m_bl.NOT(m_bl.eq(p.first, p.second))}, sc); }
        else if (mn == "comparator_lt" || mn == "RTL_LT") { auto p = two(A, B, O, W); pinOut(it, O, {m_bl.ltU(p.first, p.second)}, sc); }
        else if (mn == "comparator_lte" || mn == "RTL_LEQ") { auto p = two(A, B, O, W); pinOut(it, O, {m_bl.NOT(m_bl.ltU(p.second, p.first))}, sc); }
        else if (mn == "comparator_gt" || mn == "RTL_GT") { auto p = two(A, B, O, W); pinOut(it, O, {m_bl.ltU(p.second, p.first)}, sc); }
        else if (mn == "comparator_gte" || mn == "RTL_GEQ") { auto p = two(A, B, O, W); pinOut(it, O, {m_bl.NOT(m_bl.ltU(p.first, p.second))}, sc); }
        else if (mn == "comparator_lt_signed") { auto p = two(A, B, O, W); pinOut(it, O, {m_bl.ltS(p.first, p.second)}, sc); }
        else if (mn == "comparator_lte_signed") { auto p = two(A, B, O, W); pinOut(it, O, {m_bl.NOT(m_bl.ltS(p.second, p.first))}, sc); }
        else if (mn == "comparator_gt_signed") { auto p = two(A, B, O, W); pinOut(it, O, {m_bl.ltS(p.second, p.first)}, sc); }
        else if (mn == "comparator_gte_signed") { auto p = two(A, B, O, W); pinOut(it, O, {m_bl.NOT(m_bl.ltS(p.first, p.second))}, sc); }
        else if (mn == "shifter_left" || mn == "RTL_LSHIFT") pinOut(it, O, m_bl.shl(pinIn(it, A, sc, W), pinIn(it, B, sc, pinWidth(it, B, sc))), sc);
        else if (mn == "shifter_right" || mn == "RTL_RSHIFT") pinOut(it, O, m_bl.shr(pinIn(it, A, sc, W), pinIn(it, B, sc, pinWidth(it, B, sc)), false), sc);
        else if (mn == "shifter_right_arith") pinOut(it, O, m_bl.shr(pinIn(it, A, sc, W), pinIn(it, B, sc, pinWidth(it, B, sc)), true), sc);
        else if (mn == "mux2" || mn == "RTL_MUX") {
            const int s = m_bl.redOr(pinIn(it, rtl ? "S" : "sel", sc, 1));
            pinOut(it, O, m_bl.MUXv(s, pinIn(it, rtl ? "I0" : "in0", sc, W), pinIn(it, rtl ? "I1" : "in1", sc, W)), sc);
        }
        else if (mn == "mux4") {
            const Vec s = pinIn(it, "sel", sc, 2);
            const Vec a = m_bl.MUXv(s[0], pinIn(it, "in0", sc, W), pinIn(it, "in1", sc, W));
            const Vec b = m_bl.MUXv(s[0], pinIn(it, "in2", sc, W), pinIn(it, "in3", sc, W));
            pinOut(it, "out", m_bl.MUXv(s[1], a, b), sc);
        }
        else if (mn == "sign_extender") {
            const int wi = static_cast<int>(paramInt(it, "WIDTH_IN", 8, sc));
            const int wo = static_cast<int>(paramInt(it, "WIDTH_OUT", 16, sc));
            pinOut(it, "out", m_bl.resize(pinIn(it, "in", sc, wi), wo, true), sc);
        }
        else die("internal: primitive " + mn + " listed but not modelled");
    }

    void registerCell(const Item& it, const Scope& sc, const std::string& inst) {
        const std::string& mn = it.modName;
        const bool rtl = mn.rfind("RTL_", 0) == 0;
        const ExprP qe = pinExpr(it, rtl ? "Q" : "q");
        if (!qe) {
            warn(m_d->label + ": register " + inst + " has no Q pin; ignored");
            return;
        }
        int W = static_cast<int>(paramInt(it, "WIDTH", -1, sc));
        if (W < 0) W = exprWidth(qe, sc);
        const Vec q = m_bl.resize(eval(qe, sc), W, false);  // Q bits stay free (FF-rip)
        Vec d = pinIn(it, rtl ? "D" : "d", sc, W);
        int en = m_bl.T();
        if (pinExpr(it, rtl ? "CE" : "en")) en = m_bl.redOr(pinIn(it, rtl ? "CE" : "en", sc, 1));
        {
            typename Design::Reg r;
            r.name = sc.prefix + lvalText(qe);
            r.q = q;
            r.d = d;
            r.en = en;
            r.async = mn.rfind("RTL_REG_ASYNC", 0) == 0 || paramInt(it, "IS_ASYNC", 0, sc) == 1;
            r.negedge = mn == "dffn_en" || mn.find("_N__") != std::string::npos;
            r.resetVal = static_cast<unsigned long long>(paramInt(it, "RESET_VAL", 0, sc));
            r.initVal = static_cast<unsigned long long>(paramInt(it, "INIT_VAL", 0, sc));
            const ExprP re0 = pinExpr(it, rtl ? "RST" : "rst");
            r.rst = re0 ? m_bl.redOr(eval(re0, sc)) : m_bl.F();
            const ExprP ce0 = pinExpr(it, rtl ? "C" : "clk");
            r.clk = ce0 ? m_bl.redOr(eval(ce0, sc)) : m_bl.F();
            if (ce0 && ce0->kind == Expr::IDENT) m_d->clocks.emplace_back(sc.prefix + ce0->name, r.clk);
            m_d->regs.push_back(r);
        }
        Vec next = m_bl.MUXv(en, q, d);
        if (mn == "latch_en") {
            // latch: modelled like a transparent register for next-state purposes
        } else {
            const ExprP re = pinExpr(it, rtl ? "RST" : "rst");
            if (re) {
                const int rst = m_bl.redOr(eval(re, sc));
                const Vec rv = m_bl.constVec(static_cast<unsigned long long>(paramInt(it, "RESET_VAL", 0, sc)), W);
                next = m_bl.MUXv(rst, next, rv);
            }
        }
        // Name the register after its Q target (lvalue text)
        const std::string qname = sc.prefix + lvalText(qe);
        if (m_d->regNext.count(qname)) warn(m_d->label + ": two registers drive " + qname);
        m_d->regNext[qname] = next;
        m_d->regQ[qname] = q;
        if (!m_ffrip) {
            // without FF-rip the register is opaque: Q is free, D is still compared
        }
        // mark the Q bits as driven so they are not reported undriven
        if (qe->kind == Expr::IDENT) {
            NetBits* nb = findNet(sc.prefix + qe->name);
            if (nb) for (int& c : nb->drivers) if (c == 0) c = 1;
        }
    }
    static std::string lvalText(const ExprP& e) {
        switch (e->kind) {
        case Expr::IDENT: return e->name;
        case Expr::BITSEL: return lvalText(e->args[0]) + "[" + exprText(e->args[1]) + "]";
        case Expr::PARTSEL: return lvalText(e->args[0]) + "[" + std::to_string(e->ival) + ":" + std::to_string(e->ival2) + "]";
        case Expr::PARTSEL_UP: return lvalText(e->args[0]) + "[" + exprText(e->args[1]) + "+:" + std::to_string(e->ival) + "]";
        case Expr::CONCAT: {
            std::string s = "{";
            for (size_t i = 0; i < e->args.size(); ++i) s += (i ? "," : "") + lvalText(e->args[i]);
            return s + "}";
        }
        default: return exprText(e);
        }
    }
    static std::string exprText(const ExprP& e) {
        if (e->kind == Expr::IDENT) return e->name;
        if (e->kind == Expr::CONST) {
            std::string s;
            for (int i = static_cast<int>(e->bits.size()) - 1; i >= 0; --i) s += e->bits[i];
            return std::to_string(e->bits.size()) + "'b" + s;
        }
        return "<expr>";
    }

    // structural_primitives.sv memories.  The array contents are uninterpreted:
    // each read port's data is a free value named <inst>.rdata<N> (shared by
    // name with the other design), the write/read pin values are compared
    // points, and a synchronous-read port's output register is modelled as a
    // register with next = re ? data : q (so an async memory + dff_en on one
    // side matches a memory_*_sync on the other).  memory_sp's single `addr`
    // is exposed as both waddr and raddr1.
    void recordCell(const Item& it, const Scope& sc, const std::string& inst,
                    const std::function<bool(const std::string&)>& isOut, const Module* defp = nullptr) {
        typename Design::Cell c;
        c.type = it.modName;
        c.name = inst;
        // pins carry their declared width when the module is declared: an
        // input narrower than its port is zero-extended, an output wider than
        // what it drives (`.DOBDO(qb[i])`) gets free bits for the rest
        auto portWidth = [defp](const std::string& n) -> int {
            if (!defp) return -1;
            for (const NetDecl& d : defp->nets) if (d.name == n) return d.width;
            return -1;
        };
        // Parameter values for the emitter, typed by their spelling:
        //   "str"      a string literal, quotes kept
        //   "20.0"     a real, as a quoted string (how yosys writes reals)
        //   bits:0101  a sized literal, MSB first, exactly its width
        //   123        an unsized integer
        for (const auto& kv : it.params) {
            const ExprP& v = kv.second;
            if (!v) continue;
            if (v->kind == Expr::CONST && !v->text.empty() && v->text[0] == '"') {
                c.params.emplace_back(kv.first, v->text);
            } else if (v->kind == Expr::CONST && v->text.find('\'') == std::string::npos
                       && v->text.find('.') != std::string::npos) {
                c.params.emplace_back(kv.first, "\"" + v->text + "\"");
            } else if (v->kind == Expr::CONST && v->sized) {
                std::string s = "bits:";
                for (int i = static_cast<int>(v->bits.size()) - 1; i >= 0; --i) s += v->bits[i] == '1' ? '1' : '0';
                c.params.emplace_back(kv.first, s);
            } else {
                c.params.emplace_back(kv.first, std::to_string(constOf(v, sc)));
            }
        }
        for (const Pin& p : it.pins) {
            if (!p.expr) continue;
            Vec v = eval(p.expr, sc);
            const int pw = portWidth(p.name);
            if (isOut(p.name)) {
                while (pw > 0 && static_cast<int>(v.size()) < pw) v.push_back(m_bl.newVar());
                if (pw > 0 && static_cast<int>(v.size()) > pw) v.resize(pw);
                c.outs.emplace_back(p.name, v);
            } else {
                if (pw > 0) v = m_bl.resize(v, pw, false);
                c.ins.emplace_back(p.name, v);
            }
        }
        m_d->cells2.push_back(c);
    }
    void memoryCell(const Item& it, const Scope& sc, const std::string& inst) {
        const std::string& mn = it.modName;
        recordCell(it, sc, inst, [](const std::string& n) { return n.rfind("rdata", 0) == 0; });
        const bool sync = mn.find("_sync") != std::string::npos;
        auto in = [&](const char* pin, const char* as) {
            const ExprP e = pinExpr(it, pin);
            if (e) m_d->bbIn[inst + "." + as] = eval(e, sc);
        };
        const bool tdp = mn == "memory_tdp_sync";
        if (tdp) {
            for (const char* p : {"clk1", "clk2", "en1", "en2", "we1", "we2", "addr1", "addr2", "wdata1", "wdata2"}) in(p, p);
        } else {
            in("clk", "clk");
        }
        if (tdp) {
        } else if (mn == "memory_sp") {
            in("we", "we");
            in("addr", "waddr");
            in("addr", "raddr1");
            in("wdata", "wdata");
        } else if (mn == "memory_2w2r" || mn == "memory_2w2r_rf") {
            for (const char* p : {"we1", "we2", "addr1", "addr2", "waddr1", "waddr2", "wdata1", "wdata2", "raddr1", "raddr2", "re1", "re2"}) in(p, p);
        } else {
            in("we", "we");
            in("waddr", "waddr");
            in("wdata", "wdata");
            if (pinExpr(it, "raddr")) in("raddr", "raddr1"); else in("raddr1", "raddr1");
            in("raddr2", "raddr2");
        }
        // read ports
        struct RP { const char* data; const char* re; const char* name; };
        const RP ports[] = {{"rdata", "re", "rdata1"}, {"rdata1", "re1", "rdata1"}, {"rdata2", "re2", "rdata2"}};
        for (const RP& rp : ports) {
            const ExprP de = pinExpr(it, rp.data);
            if (!de) continue;
            const std::string key = inst + "." + rp.name;
            const int w = exprWidth(de, sc);
            Vec data(w);
            for (int i = 0; i < w; ++i) data[i] = m_bl.newVar();  // free: uninterpreted contents
            m_d->bbOut[key] = data;
            if (!sync) {
                driveLValue(de, data, sc, "memory read port " + key);
                if (de->kind == Expr::IDENT) m_bbOutNets.insert(sc.prefix + de->name);
                continue;
            }
            // synchronous: the pin net is a register (free Q), next = re ? data : q
            // (a TDP port reads when enabled and not writing)
            const Vec q = m_bl.resize(eval(de, sc), w, false);
            int re = m_bl.T();
            if (tdp) {
                const char* enp = rp.name[5] == '1' ? "en1" : "en2";
                const char* wep = rp.name[5] == '1' ? "we1" : "we2";
                const int en = pinExpr(it, enp) ? m_bl.redOr(eval(pinExpr(it, enp), sc)) : m_bl.T();
                const int we = pinExpr(it, wep) ? m_bl.redOr(eval(pinExpr(it, wep), sc)) : m_bl.F();
                re = m_bl.AND(en, m_bl.NOT(we));
            } else if (pinExpr(it, rp.re)) {
                re = m_bl.redOr(eval(pinExpr(it, rp.re), sc));
                m_d->bbIn[inst + "." + rp.re] = {re};
            }
            const std::string qname = sc.prefix + lvalText(de);
            m_d->regNext[qname] = m_bl.MUXv(re, q, data);
            m_d->regQ[qname] = q;
            if (de->kind == Expr::IDENT) {
                NetBits* nb = findNet(sc.prefix + de->name);
                if (nb) for (int& c : nb->drivers) if (c == 0) c = 1;
            }
        }
    }

    static bool bbOutPin(const std::string& n) {
        return n.rfind("rdata", 0) == 0 || n == "q" || n == "Q" || n.rfind("out", 0) == 0
               || n == "O" || n.rfind("dout", 0) == 0 || n == "cout" || n == "valid"
               || n == "full" || n == "empty" || n == "count" || n == "tc" || n == "pulse"
               || n == "LOCKED" || n.rfind("CLKOUT", 0) == 0 || n == "CLKFBOUT" || n == "ODIV2";
    }
    void blackBox(const Item& it, const Scope& sc, const std::string& inst, const Module* defp = nullptr) {
        // Directions: from a (* blackbox *) declaration when there is one, else
        // the convention of the primitive libraries (pins named rdata*/q*/out*/O/Q
        // are outputs, everything else is input).
        auto isOutPin = [defp](const std::string& n) -> bool {
            if (defp) {
                for (const NetDecl& d : defp->nets) if (d.name == n) return d.dir >= 2;
                return false;
            }
            return bbOutPin(n);
        };
        recordCell(it, sc, inst, isOutPin, defp);
        // Outputs: left free (the nets are already fresh variables); inputs: compared points.
        for (const Pin& p : it.pins) {
            if (!p.expr) continue;
            const std::string& n = p.name;
            const bool isOut = isOutPin(n);
            if (isOut) {
                m_d->bbOut[inst + "." + n] = eval(p.expr, sc);
                if (p.expr->kind == Expr::IDENT) {
                    m_bbOutNets.insert(sc.prefix + p.expr->name);
                    NetBits* nb = findNet(sc.prefix + p.expr->name);
                    if (nb) for (int& c : nb->drivers) if (c == 0) c = 1;
                }
            } else {
                m_d->bbIn[inst + "." + n] = eval(p.expr, sc);
            }
        }
    }
};


}  // namespace svs_netlist
#endif
