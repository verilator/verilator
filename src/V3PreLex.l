/**************************************************************************
 * DESCRIPTION: Verilator: Flex verilog preprocessor
 *
 * Code available from: https://verilator.org
 *
 **************************************************************************
 *
 * Copyright 2003-2024 by Wilson Snyder. This program is free software; you
 * can redistribute it and/or modify it under the terms of either the
 * GNU Lesser General Public License Version 3 or the Perl Artistic License
 * Version 2.0.
 * SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
 *
 **************************************************************************
 * Do not use Flex in C++ mode.  It has bugs with yyunput() which result in
 * lost characters.
 **************************************************************************/
/* clang-format off */

%option noyywrap align interactive
%option stack
%option noc++
%option prefix="V3PreLex"
%{
#ifdef NEVER_JUST_FOR_CLANG_FORMAT
 }
#endif

#include "V3PreProc.h"
#include "V3PreLex.h"
#ifdef _WIN32
# include <io.h> // for isatty
#endif

/* clang-format on */

V3PreLex* V3PreLex::s_currentLexp = nullptr;  // Current lexing point

#define LEXP V3PreLex::s_currentLexp

#define YY_INPUT(buf, result, max_size) \
    do { result = LEXP->inputToLex(buf, max_size); } while (false)

// Accessors, because flex keeps changing the type of yyleng
char* yyourtext() { return yytext; }
size_t yyourleng() { return yyleng; }
void yyourtext(const char* textp, size_t size) {
    yytext = (char*)textp;
    yyleng = size;
}

// FL_FWD only tracks columns; preproc uses linenoInc() to track lines, so
// insertion of a \n does not mess up line count
#define FL_FWDC (LEXP->curFilelinep()->forwardToken(yytext, yyleng, false))
// Use this to break between tokens whereever not return'ing a token (e.g. skipping inside lexer)
#define FL_BRK (LEXP->curFilelinep()->startToken())

static void linenoInc() { LEXP->linenoInc(); }
static bool pedantic() { return LEXP->m_pedantic; }
static void yyerror(char* msg) { LEXP->curFilelinep()->v3error(msg); }
static void yyerrorf(const char* msg) { LEXP->curFilelinep()->v3error(msg); }
static void appendDefValue(const char* t, size_t l) { LEXP->appendDefValue(t, l); }

/* clang-format off */
/**********************************************************************/
%}

%x ARGMODE
%x CMTMODE
%x CMTONEM
%x DEFCMT
%x DEFFORM
%x DEFFPAR
%x DEFVAL
%x ENCBASE64
%x EXPR
%x INCMODE
%x PRAGMA
%x PRAGMAERR
%x PRAGMAPRT
%x PRAGMAPRTERR
%x PRTMODE
%x QQQMODE
%x STRIFY
%x STRMODE

/* drop: Drop Ctrl-Z - can't pass thru or may EOF the output too soon */

ws              [ \t\f\r]
wsn             [ \t\f]
crnl            [\r]*[\n]
quote           [\"]
tickquote       [`][\"]
/* Where we use symb/symbdef, we must also look for a `` join */
/* Note in the preprocessor \ESCaped is *not* always special; mantis1537/bug441 */
symb            ([a-zA-Z_][a-zA-Z0-9_$]*|\\[^ \t\f\r\n]+)
symbdef         ([a-zA-Z_][a-zA-Z0-9_$]*|\\[^ \t\f\r\n`]+)
word            [a-zA-Z0-9_]+
drop            [\032]
bom             [\357\273\277]


        /**************************************************************/
%%

<INITIAL>{bom}          { }
<INITIAL,STRIFY>^{ws}*"`line"{ws}+.*{crnl}      { FL_FWDC; LEXP->lineDirective(yytext);
                                                  return VP_LINE; }

        /* Special directives we recognize */
<INITIAL>"`define"      { FL_FWDC; return VP_DEFINE; }
<INITIAL>"`else"        { FL_FWDC; return VP_ELSE; }
<INITIAL>"`elsif"       { FL_FWDC; return VP_ELSIF; }
<INITIAL>"`endif"       { FL_FWDC; return VP_ENDIF; }
<INITIAL>"`ifdef"       { FL_FWDC; return VP_IFDEF; }
<INITIAL>"`ifndef"      { FL_FWDC; return VP_IFNDEF; }
<INITIAL>"`include"     { FL_FWDC; return VP_INCLUDE; }
<INITIAL>"`undef"       { FL_FWDC; return VP_UNDEF; }
<INITIAL>"`undefineall" { FL_FWDC; return VP_UNDEFINEALL; }
<INITIAL>"`error"       { FL_FWDC; if (!pedantic()) return VP_ERROR; else return VP_DEFREF; }
    /* We wanted this to be next to `protect But it must be before `pramga */
    /* we win only because we both match to the end of the line so the length */
    /* is equal and we are first*/
<PRAGMAPRT>"encoding"{wsn}*[^\n\r]* { FL_FWDC;
                          int res;
                          char enctype[16]; // long enough to hold "quote-printable"
                          if (LEXP->m_protBytes > 0) {
                              LEXP->curFilelinep()->v3warn(BADSTDPRAGMA, "Multiple `pragma protected encoding sections");
                          }
                          res = sscanf(yytext + std::strlen("encoding"), " = (enctype = \"%15[A-Za-z0-9]\", line_length = %d, bytes = %d)", &enctype[0], &LEXP->m_protLength, &LEXP->m_protBytes);
                          if (res == 0)
                              LEXP->curFilelinep()->v3warn(BADSTDPRAGMA, "`pragma protected encoding must have an \"enctype\" field");
                          LEXP->m_encType = !VL_STRCASECMP(enctype, "uuencode") ? Enctype::UUENCODE :
                                            !VL_STRCASECMP(enctype, "base64") ? Enctype::BASE64 :
                                            !VL_STRCASECMP(enctype, "quoted-printable") ? Enctype::QUOTE_PRINTABLE :
                                            !VL_STRCASECMP(enctype, "raw") ? Enctype::RAW : Enctype::ERR;
                          if (LEXP->m_encType == Enctype::ERR)
                              LEXP->curFilelinep()->v3warn(BADSTDPRAGMA, "Illegal encoding type for `pragma protected encoding");
                          if (LEXP->m_encType != Enctype::BASE64)
                              LEXP->curFilelinep()->v3warn(E_UNSUPPORTED, "Unsupported: only BASE64 is recognized for `pragma protected encoding");
                          if (res == 3) {
                              if ((LEXP->m_encType == Enctype::BASE64) && (LEXP->m_protLength & 3))
                                  LEXP->curFilelinep()->v3warn(BADSTDPRAGMA, "line_length must be multiple of 4 for BASE64");
                          } else {
                              // default values
                              LEXP->m_protBytes = 0;
                              LEXP->m_protLength = 76; // ?? default value not mentioned in IEEE spec
                          }
                          BEGIN(INITIAL);
                          return VP_TEXT;
                        }
<PRAGMAPRT>"key_block"{wsn}*[\n\r] {
                          FL_FWDC;
                          linenoInc();
                          BEGIN(ENCBASE64);
                          return VP_TEXT; }
<PRAGMAPRT>"data_block"{wsn}*[\n\r] {
                          FL_FWDC;
                          linenoInc();
                          LEXP->curFilelinep()->v3warn(PROTECTED, "A '`pragma protected data_block' encrypted section was detected and will be skipped.");
                          BEGIN(ENCBASE64);
                          return VP_TEXT; }
<PRAGMAPRT>("begin_protected"|"end_protected"|"end")[\n\r]  { FL_FWDC; linenoInc(); BEGIN(INITIAL); return VP_TEXT; }
<PRAGMAPRT>"version"{wsn}*={wsn}*[^\n\r]*[\n\r] {
                          FL_FWDC;
                          linenoInc();
                          BEGIN(INITIAL);
                          return VP_TEXT; }
<PRAGMAPRT>("encrypt_agent"|"encrypt_agent_info"|"key_keyowner"|"key_keyname"){wsn}*={wsn}*[\"][^\n\r]*[\"][\n\r] {
                          FL_FWDC;
                          linenoInc();
                          BEGIN(INITIAL);
                          return VP_TEXT; }
<PRAGMAPRT>("data_method"|"key_method"){wsn}*={wsn}*[\"][^\n\r]*[\"][\n\r] {
                          FL_FWDC;
                          linenoInc();
                          BEGIN(INITIAL);
                          return VP_TEXT; }
    /* end of `pragma protect */
<PRAGMAPRT>{wsn}+        { FL_FWDC; return VP_TEXT; }
<PRAGMAPRT>[\n\r]        { FL_FWDC; linenoInc(); BEGIN(INITIAL); return VP_TEXT; }

    /* catch-all for unknown '`pragma protect' rules */
<PRAGMAPRT>.            { yyless(0);
                          BEGIN(PRAGMAPRTERR);
                          return VP_TEXT; }
<ENCBASE64>[A-Za-z0-9+/]+[=]{0,2}[\n\r] { FL_FWDC; linenoInc(); FL_BRK;
                          if ((yyourleng()-1) <= size_t(LEXP->m_protLength) && ((yyleng & 3) == 1)) {
                              LEXP->m_protBytes -= (yyleng-1)/4*3;
                          } else {
                              LEXP->curFilelinep()->v3warn(BADSTDPRAGMA, "BASE64 line too long in `pragma protect key_bloock/data_block");
                          }
                          if (yytext[yyleng-3] == '=')
                              LEXP->m_protBytes++;
                          if (yytext[yyleng-2] == '=')
                              LEXP->m_protBytes++;
                          if (LEXP->m_protBytes == 0) {
                              BEGIN(INITIAL);
                          } else if (LEXP->m_protBytes < 0)
                              LEXP->curFilelinep()->v3warn(BADSTDPRAGMA, "BASE64 encoding (too short) in `pragma protect key_bloock/data_block");
                          /*return VP_TEXT;*/ }
<ENCBASE64>{wsn}*[\n\r] { FL_FWDC;
                          if (LEXP->m_protBytes != 0)
                              LEXP->curFilelinep()->v3warn(BADSTDPRAGMA, "BASE64 encoding length mismatch in `pragma protect key_bloock/data_block");
                          linenoInc(); BEGIN(INITIAL);
                          return VP_TEXT; }

    /* Catch only empty `pragma lines */
<INITIAL>"`pragma"{wsn}*[\n\r]  {
                          yyless(yyleng - 1); FL_FWDC;
                          if (v3Global.opt.pedantic()) {
                              LEXP->curFilelinep()->v3warn(BADSTDPRAGMA, "`pragma is missing a pragma_expression.");
                          }
                          return VP_TEXT; }

    /* catch all other nonempty `pragma */
<INITIAL>"`pragma"{wsn}*[^\n\r]  {
                          yyless(yyleng - 1); FL_FWDC;
                          if (!v3Global.opt.preprocOnly())
                              BEGIN(PRAGMA);
                          return VP_TEXT; }
<PRAGMA>"protect"{wsn}* { FL_FWDC; BEGIN(PRAGMAPRT); return VP_TEXT;}
    /* catch-all for unknown `pragma rules */
<PRAGMA>.               { yyless(0);
                          BEGIN(PRAGMAERR);
                          return VP_TEXT; }

    /* the catch-all rule only got 1 char, lets get all line */
<PRAGMAERR>[^\n\r]*     { FL_FWDC;
                          /* Add a warning here for unknown pragmas if desired, at the moment , we don't */
                          /* LEXP->curFilelinep()->v3warn(BADPRAGMA, "Unknown `pragma"); */
                          BEGIN(INITIAL);
                          return VP_TEXT; }
<PRAGMAPRTERR>[^\n\r]*  { FL_FWDC;
                          LEXP->curFilelinep()->v3warn(BADSTDPRAGMA, "Unknown '`pragma protect' error");
                          BEGIN(INITIAL);
                          return VP_TEXT; }
<INITIAL,STRIFY>"`__FILE__"     { FL_FWDC;
                          static string rtnfile;
                          rtnfile = '"'; rtnfile += LEXP->curFilelinep()->filename();
                          rtnfile += '"'; yytext = (char*)rtnfile.c_str(); yyleng = rtnfile.length();
                          return VP_STRING; }
<INITIAL,STRIFY>"`__LINE__"     { FL_FWDC;
                          static char buf[25];
                          VL_SNPRINTF(buf, 25, "%d", LEXP->curFilelinep()->lastLineno());
                          yytext = buf; yyleng = std::strlen(yytext);
                          return VP_TEXT; }

        /* Pass-through strings */
<INITIAL>{quote}        { yy_push_state(STRMODE); yymore(); }
<STRMODE><<EOF>>        { FL_FWDC; linenoInc(); yyerrorf("EOF in unterminated string");
                          yyleng=0; return VP_EOF_ERROR; }
<STRMODE>{crnl}         { FL_FWDC; linenoInc(); yyerrorf("Unterminated string");
                          FL_BRK; BEGIN(INITIAL); }
<STRMODE>{word}         { yymore(); }
<STRMODE>[^\"\\]        { yymore(); }
<STRMODE>[\\]{crnl}     { linenoInc(); yymore(); }
<STRMODE>[\\]{wsn}+{crnl}  { LEXP->warnBackslashSpace(); yyless(1); }
<STRMODE>[\\].          { yymore(); }
<STRMODE>{quote}        { FL_FWDC; yy_pop_state();
                          if (LEXP->m_parenLevel || LEXP->m_defQuote) {
                              LEXP->m_defQuote=false; appendDefValue(yytext, yyleng);
                              yyleng=0; FL_BRK;
                          } else return VP_STRING; }

        /* Pass-through quote-quote-quote */
<INITIAL>{quote}{quote}{quote}        { yy_push_state(QQQMODE); yymore(); }
<QQQMODE><<EOF>>        { FL_FWDC; linenoInc(); yyerrorf("EOF in unterminated \"\"\" string");
                          yyleng=0; return VP_EOF_ERROR; }
<QQQMODE>{crnl}         { FL_FWDC; linenoInc(); yymore(); }
<QQQMODE>{word}         { yymore(); }
<QQQMODE>[^\"\\]        { yymore(); }
<QQQMODE>[\\]{crnl}     { linenoInc(); yymore(); }
<QQQMODE>[\\]{wsn}+{crnl}  { LEXP->warnBackslashSpace(); yyless(1); }
<QQQMODE>[\\].          { yymore(); }
<QQQMODE>.              { yymore(); }
<QQQMODE>{quote}{quote}{quote}        { FL_FWDC; yy_pop_state();
                          if (LEXP->m_parenLevel || LEXP->m_defQuote) {
                              LEXP->m_defQuote=false; appendDefValue(yytext, yyleng);
                              yyleng=0; FL_BRK;
                          } else return VP_STRING; }

        /* Stringification */
<INITIAL>{tickquote}    { FL_FWDC; yy_push_state(STRIFY); return VP_STRIFY; }
<STRIFY><<EOF>>         { FL_FWDC; linenoInc(); yyerrorf("EOF in unterminated '\"");
                          yyleng=0; return VP_EOF_ERROR; }
<STRIFY>"`\\`\""        { FL_FWDC; return VP_BACKQUOTE; }
<STRIFY>{quote}         { yy_push_state(STRMODE); yymore(); }
<STRIFY>{tickquote}     { FL_FWDC; yy_pop_state(); return VP_STRIFY; }
<STRIFY>{symbdef}       { FL_FWDC; return VP_SYMBOL; }
<STRIFY>{symbdef}``     { FL_FWDC; yyleng-=2; return VP_SYMBOL_JOIN; }
<STRIFY>"`"{symbdef}    { FL_FWDC; return VP_DEFREF; }
<STRIFY>"`"{symbdef}``  { FL_FWDC; yyleng-=2; return VP_DEFREF_JOIN; }
<STRIFY>``              { FL_FWDC; yyleng-=2; return VP_JOIN; }
<STRIFY>{crnl}          { FL_FWDC; linenoInc(); yytext = (char*)"\n"; yyleng = 1; return VP_WHITE; }
<STRIFY>{wsn}+          { FL_FWDC; return VP_WHITE; }
<STRIFY>{drop}          { FL_FWDC; FL_BRK; }
<STRIFY>[\r]            { FL_FWDC; FL_BRK; }
<STRIFY>.               { FL_FWDC; return VP_TEXT; }

        /* Protected blocks */
<INITIAL>"`protected"   { yy_push_state(PRTMODE); yymore(); }
<PRTMODE><<EOF>>        { FL_FWDC; linenoInc(); yyerrorf("EOF in `protected");
                          yyleng = 0; return VP_EOF_ERROR; }
<PRTMODE>{crnl}         { FL_FWDC; linenoInc(); return VP_TEXT; }
<PRTMODE>.              { yymore(); }
<PRTMODE>"`endprotected" { FL_FWDC; yy_pop_state(); return VP_TEXT; }

        /* Pass-through include <> filenames */
<INCMODE><<EOF>>        { FL_FWDC; linenoInc(); yyerrorf("EOF in unterminated include filename");
                          yyleng = 0; return VP_EOF_ERROR; }
<INCMODE>{crnl}         { FL_FWDC; linenoInc(); yyerrorf("Unterminated include filename");
                          FL_BRK; BEGIN(INITIAL); }
<INCMODE>[^\>\\]        { yymore(); }
<INCMODE>[\\].          { yymore(); }
<INCMODE>[\>]           { FL_FWDC; yy_pop_state(); return VP_STRING; }

        /* Reading definition formal parenthesis (or not) to begin formal arguments */
        /* Note '(' must IMMEDIATELY follow definition name */
<DEFFPAR>[(]            { FL_FWDC; appendDefValue("(", 1); LEXP->m_formalLevel=1;
                          FL_BRK; BEGIN(DEFFORM); }
<DEFFPAR>{crnl}         { FL_FWDC; yy_pop_state(); unput('\n'); yyleng=0; return VP_DEFFORM; }  /* DEFVAL will later grab the return */
<DEFFPAR><<EOF>>        { FL_FWDC; yy_pop_state(); return VP_DEFFORM; }  /* empty formals */
<DEFFPAR>.              { FL_FWDC; yy_pop_state(); unput(yytext[yyleng-1]); yyleng=0; return VP_DEFFORM; }  /* empty formals */

        /* Reading definition formals (declaration of a define) */
<DEFFORM>[(]            { FL_FWDC; appendDefValue(yytext, yyleng); FL_BRK; yyleng=0; ++LEXP->m_formalLevel; }
<DEFFORM>[)]            { FL_FWDC; appendDefValue(yytext, yyleng); yyleng=0;
                          if ((--LEXP->m_formalLevel)==0) { yy_pop_state(); return VP_DEFFORM; }
                          FL_BRK; }
<DEFFORM>"/*"           { yy_push_state(CMTMODE); yymore(); }
<DEFFORM>"//"[^\n\r]*   { FL_FWDC; return VP_COMMENT;}
<DEFFORM>{drop}         { FL_FWDC; FL_BRK; }
<DEFFORM><<EOF>>        { FL_FWDC; linenoInc(); yy_pop_state(); yyerrorf("Unterminated ( in define formal arguments.");
                          yyleng=0; return VP_DEFFORM; }
<DEFFORM>{crnl}         { FL_FWDC; linenoInc(); appendDefValue((char*)"\n", 1); FL_BRK; }  /* Include return so can maintain output line count */
<DEFFORM>[\\]{wsn}+{crnl}  { LEXP->warnBackslashSpace(); yyless(1); }
<DEFFORM>[\\]{crnl}     { FL_FWDC; linenoInc(); appendDefValue((char*)"\\\n", 2); FL_BRK; }  /* Include return so can maintain output line count */
<DEFFORM>{quote}        { LEXP->m_defQuote=true; yy_push_state(STRMODE); yymore(); }  /* Legal only in default values */
<DEFFORM>{quote}{quote}{quote}   { LEXP->m_defQuote=true; yy_push_state(QQQMODE); yymore(); }  /* Legal only in default values */
<DEFFORM>"`\\`\""       { FL_FWDC; appendDefValue(yytext, yyleng); FL_BRK; }  /* Maybe illegal, otherwise in default value */
<DEFFORM>{tickquote}    { FL_FWDC; appendDefValue(yytext, yyleng); FL_BRK; }  /* Maybe illegal, otherwise in default value */
<DEFFORM>[{\[]          { FL_FWDC; LEXP->m_formalLevel++; appendDefValue(yytext, yyleng); FL_BRK; }
<DEFFORM>[}\]]          { FL_FWDC; LEXP->m_formalLevel--; appendDefValue(yytext, yyleng); FL_BRK; }
<DEFFORM>[^\/\*\n\r\\(){}\[\]\"]+       |
<DEFFORM>[\\][^\n\r]    |
<DEFFORM>.              { FL_FWDC; appendDefValue(yytext, yyleng); FL_BRK; }

        /* Reading definition value (declaration of a define's text) */
<DEFVAL>"/*"            { LEXP->m_defCmtSlash=false; yy_push_state(DEFCMT); yymore(); }  /* Special comment parser */
<DEFVAL>"//"[^\n\r]*[\\]{crnl}  { FL_FWDC; linenoInc(); appendDefValue((char*)"\n", 1); FL_BRK; }  /* Spec says // not part of define value */
<DEFVAL>"//"[^\n\r]*    { FL_FWDC; return VP_COMMENT;}
<DEFVAL>{drop}          { FL_FWDC; FL_BRK; }
<DEFVAL><<EOF>>         { FL_FWDC; linenoInc(); yy_pop_state(); yytext=(char*)"\n"; yyleng=1; return VP_DEFVALUE; }  /* Technically illegal, but people complained */
<DEFVAL>{crnl}          { FL_FWDC; linenoInc(); yy_pop_state(); yytext=(char*)"\n"; yyleng=1; return VP_DEFVALUE; }
<DEFVAL>[\\]{wsn}+{crnl}  { LEXP->warnBackslashSpace(); yyless(1); }
<DEFVAL>[\\]{crnl}      { FL_FWDC; linenoInc(); appendDefValue((char*)"\\\n", 2); FL_BRK; }  /* Return, AND \ is part of define value */
<DEFVAL>{quote}         { LEXP->m_defQuote = true; yy_push_state(STRMODE); yymore(); }
<DEFVAL>{quote}{quote}{quote}   { LEXP->m_defQuote = true; yy_push_state(QQQMODE); yymore(); }
<DEFVAL>[^\/\*\n\r\\\"]+        |
<DEFVAL>[\\][^\n\r]     |
<DEFVAL>.               { FL_FWDC; appendDefValue(yytext, yyleng); FL_BRK; }

        /* Comments inside define values - if embedded get added to define value per spec */
        /* - if no \{crnl} ending then the comment belongs to the next line, as a non-embedded comment */
        /* - if all but (say) 3rd line is missing \ then it's indeterminate */
<DEFCMT>"*/"            { FL_FWDC; yy_pop_state(); appendDefValue(yytext, yyleng); FL_BRK; }
<DEFCMT>[\\]{wsn}+{crnl}  { LEXP->warnBackslashSpace(); yyless(1); }
<DEFCMT>[\\]{crnl}      { FL_FWDC; linenoInc(); LEXP->m_defCmtSlash=true;
                          appendDefValue(yytext, yyleng-2); appendDefValue((char*)"\n", 1);  /* Return but not \ */
                          FL_BRK; }
<DEFCMT>{crnl}          { linenoInc(); yymore(); if (LEXP->m_defCmtSlash) yyerrorf("One line of /* ... */ is missing \\ before newline");
                          BEGIN(CMTMODE); }
<DEFCMT>{word}          { yymore(); }
<DEFCMT>.               { yymore(); }
<DEFCMT><<EOF>>         { FL_FWDC; yyerrorf("EOF in '/* ... */' block comment\n");
                          yyleng=0; return VP_EOF_ERROR; }

        /* Preprocessor expression */
<EXPR><<EOF>>           { FL_FWDC; linenoInc(); yyerrorf("EOF in unterminated preprocessor expression");
                          yyleng = 0; return VP_EOF_ERROR; }
<EXPR>"/*"              { yy_push_state(CMTMODE); yymore(); }
<EXPR>"//"[^\n\r]*      { FL_FWDC; return VP_COMMENT;}
<EXPR>"("               { FL_FWDC; return VP_TEXT; }  /* V3PreProc will push another EXPR state to stack */
<EXPR>")"               { FL_FWDC; yy_pop_state(); return VP_TEXT; }
<EXPR>"!"               { FL_FWDC; return VP_TEXT; }
<EXPR>"&&"              { FL_FWDC; return VP_TEXT; }
<EXPR>"||"              { FL_FWDC; return VP_TEXT; }
<EXPR>"->"              { FL_FWDC; return VP_TEXT; }
<EXPR>"<->"             { FL_FWDC; return VP_TEXT; }
<EXPR>{symb}            { FL_FWDC; return VP_SYMBOL; }
<EXPR>{crnl}            { FL_FWDC; linenoInc(); yytext=(char*)"\n"; yyleng=1; return VP_WHITE; }
<EXPR>{wsn}+            { FL_FWDC; return VP_WHITE; }
<EXPR>.                 { FL_FWDC; return VP_TEXT; }

        /* Define arguments (use of a define) */
<ARGMODE>"/*"           { yy_push_state(CMTMODE); yymore(); }
<ARGMODE>"//"[^\n\r]*   { FL_FWDC; return VP_COMMENT; }
<ARGMODE>{drop}         { FL_FWDC; FL_BRK; }
<ARGMODE><<EOF>>        { FL_FWDC; yyerrorf("EOF in define argument list\n");
                          yyleng = 0; return VP_EOF_ERROR; }
<ARGMODE>{crnl}         { FL_FWDC; linenoInc(); yytext=(char*)"\n"; yyleng=1; return VP_WHITE; }
<ARGMODE>{quote}        { yy_push_state(STRMODE); yymore(); }
<ARGMODE>{quote}{quote}{quote}    { yy_push_state(QQQMODE); yymore(); }
<ARGMODE>"`\\`\""       { FL_FWDC; appendDefValue(yytext, yyleng); FL_BRK; }  /* Literal text */
<ARGMODE>{tickquote}    { FL_FWDC; yy_push_state(STRIFY); return VP_STRIFY; }
<ARGMODE>[{\[]          { FL_FWDC; LEXP->m_parenLevel++; appendDefValue(yytext, yyleng); FL_BRK; }
<ARGMODE>[}\]]          { FL_FWDC; LEXP->m_parenLevel--; appendDefValue(yytext, yyleng); FL_BRK; }
<ARGMODE>[(]            { FL_FWDC; LEXP->m_parenLevel++;
                          // Note paren level 0 means before "(" of starting args
                          // Level 1 means "," between arguments
                          // Level 2+ means one inside the () of an argument
                          if (LEXP->m_parenLevel == 1) {  // Starting (
                              if (!VString::isWhitespace(LEXP->m_defValue)) {
                                  yyerrorf("Illegal text before '(' that starts define arguments");
                              }
                          }
                          if (LEXP->m_parenLevel>1) {
                              appendDefValue(yytext, yyleng); FL_BRK;
                          } else {
                              return VP_TEXT;
                        }}
<ARGMODE>[)]            { FL_FWDC; LEXP->m_parenLevel--;
                          if (LEXP->m_parenLevel>0) {
                              appendDefValue(yytext, yyleng); FL_BRK;
                          } else {
                              yy_pop_state(); return VP_DEFARG;
                        }}
<ARGMODE>[,]            { FL_FWDC; if (LEXP->m_parenLevel>1) {
                              appendDefValue(yytext, yyleng); FL_BRK;
                          } else {
                              yy_pop_state(); return VP_DEFARG;
                        }}
<ARGMODE>"`"{symbdef}   { FL_FWDC; appendDefValue(yytext, yyleng); FL_BRK; }  /* defref in defref - outer macro expands first */
<ARGMODE>"`"{symbdef}`` { FL_FWDC; appendDefValue(yytext, yyleng); FL_BRK; }  /* defref in defref - outer macro expands first */
<ARGMODE>``             { FL_FWDC; appendDefValue(yytext, yyleng); FL_BRK; }  /* defref in defref - outer macro expands first */
<ARGMODE>[^\/\*\n\r\\(,){}\[\]\"`]+     |
<ARGMODE>.              { FL_FWDC; appendDefValue(yytext, yyleng); FL_BRK; }

        /* Pragma comments. */
<INITIAL>"//"{ws}*"verilator lint_off"[^\n\r]*       { FL_FWDC; LEXP->verilatorCmtLint(yytext + 2, true); return VP_COMMENT; }
<INITIAL>"//"{ws}*"verilator lint_on"[^\n\r]*        { FL_FWDC; LEXP->verilatorCmtLint(yytext + 2, false); return VP_COMMENT; }
<INITIAL>"//"{ws}*"verilator lint_restore"[^\n\r]*   { FL_FWDC; LEXP->verilatorCmtLintRestore(); return VP_COMMENT; }
<INITIAL>"//"{ws}*"verilator lint_save"[^\n\r]*      { FL_FWDC; LEXP->verilatorCmtLintSave(); return VP_COMMENT; }
<INITIAL>"/*"{ws}*"verilator lint_off"[^*]*"*/"      { FL_FWDC; LEXP->verilatorCmtLint(yytext + 2, true); return VP_COMMENT; }
<INITIAL>"/*"{ws}*"verilator lint_on"[^*]*"*/"       { FL_FWDC; LEXP->verilatorCmtLint(yytext + 2, false); return VP_COMMENT; }
<INITIAL>"/*"{ws}*"verilator lint_restore"[^*]*"*/"  { FL_FWDC; LEXP->verilatorCmtLintRestore(); return VP_COMMENT; }
<INITIAL>"/*"{ws}*"verilator lint_save"[^*]*"*/"     { FL_FWDC; LEXP->verilatorCmtLintSave(); return VP_COMMENT; }

        /* One line comments. */
<INITIAL>"//"{ws}*{crnl} { FL_FWDC; linenoInc(); yytext=(char*)"\n"; yyleng=1; return VP_WHITE; }
<INITIAL>"//"           { yy_push_state(CMTONEM); yymore(); }
<CMTONEM>[^\n\r]*       { FL_FWDC; yy_pop_state(); return VP_COMMENT; }

        /* C-style comments. */
        /**** See also DEFCMT */
<INITIAL>"/*"           { yy_push_state(CMTMODE); yymore(); }
<CMTMODE>"*/"           { FL_FWDC; yy_pop_state(); return VP_COMMENT; }
<CMTMODE>{crnl}         { linenoInc(); yymore(); }
<CMTMODE><<EOF>>        { FL_FWDC; yyerrorf("EOF in '/* ... */' block comment\n");
                                  yyleng=0; return VP_EOF_ERROR; }
<CMTMODE>{word}         { yymore(); }
<CMTMODE>.              { yymore(); }

        /* Define calls */
        /* symbdef prevents normal lex rules from making `\`"foo a symbol {`"foo} instead of a BACKQUOTE */
<INITIAL>"`"{symbdef}   { FL_FWDC; return VP_DEFREF; }
<INITIAL>"`"{symbdef}`` { FL_FWDC; yyleng-=2; return VP_DEFREF_JOIN; }

        /* Generics */
<INITIAL>{crnl}         { FL_FWDC; linenoInc(); yytext=(char*)"\n"; yyleng=1; return VP_WHITE; }
<INITIAL><<EOF>>        { FL_FWDC; return VP_EOF; }  /* A "normal" EOF */
<INITIAL>{symb}         { FL_FWDC; return VP_SYMBOL; }
<INITIAL>{symb}``       { FL_FWDC; yyleng-=2; return VP_SYMBOL_JOIN; }
<INITIAL>``             { FL_FWDC; yyleng-=2; return VP_JOIN; }
<INITIAL>{wsn}+         { FL_FWDC; return VP_WHITE; }
<INITIAL>{drop}         { FL_FWDC; FL_BRK; }
<INITIAL>[\r]           { FL_FWDC; FL_BRK; }
<INITIAL>.              { FL_FWDC; return VP_TEXT; }
%%
// clang-format on

void V3PreLex::pushStateDefArg(int level) {
    // Enter define substitution argument state
    yy_push_state(ARGMODE);
    m_parenLevel = level;
    m_defValue = "";
}

void V3PreLex::pushStateDefForm() {
    // Enter define formal arguments state
    yy_push_state(DEFFPAR);  // First is an optional ( to begin args
    m_parenLevel = 0;
    m_defValue = "";
}

void V3PreLex::pushStateDefValue() {
    // Enter define value state
    yy_push_state(DEFVAL);
    m_parenLevel = 0;
    m_defValue = "";
}

void V3PreLex::pushStateExpr() {
    // Enter preprocessor expression state
    yy_push_state(EXPR);
}

void V3PreLex::pushStateIncFilename() {
    // Enter include <> filename state
    yy_push_state(INCMODE);
    yymore();
}

void V3PreLex::setYYDebug(bool on) {
    yy_flex_debug = static_cast<int>(on); }

int V3PreLex::lex() {
    V3PreLex::s_currentLexp = this;  // Tell parser where to get/put data
    // Remember token start location, may be updated by the lexer later
    m_tokFilelinep = curFilelinep();
    return yylex();
}

size_t V3PreLex::inputToLex(char* buf, size_t max_size) {
    // We need a custom YY_INPUT because we can't use flex buffers.
    // Flex buffers are limited to 2GB, and we can't chop into 2G pieces
    // because buffers can't end in the middle of tokens.
    // Note if we switched streams here (which we don't) "buf" would be
    // become a stale invalid pointer.
    //
    VPreStream* streamp = curStreamp();
    if (debug() >= 10) {  // LCOV_EXCL_START
        cout << "-  pp:inputToLex ITL s=" << max_size << " bs=" << streamp->m_buffers.size()
             << endl;
        dumpStack();
    }  // LCOV_EXCL_STOP
    // For testing, use really small chunks
    // if (max_size > 13) max_size=13;
again:
    size_t got = 0;
    // Get from this stream
    while (got < max_size  // Haven't got enough
           && !streamp->m_buffers.empty()) {  // And something buffered
        string front = curStreamp()->m_buffers.front();
        streamp->m_buffers.pop_front();
        size_t len = front.length();
        if (len > (max_size - got)) {  // Front string too big
            len = (max_size - got);
            string remainder = front.substr(len);
            front = front.substr(0, len);
            streamp->m_buffers.push_front(remainder);  // Put back remainder for next time
        }
        strncpy(buf + got, front.c_str(), len);
        got += len;
    }
    if (!got) {  // end of stream; try "above" file
        bool again = false;
        string forceOut = endOfStream(again /*ref*/);
        streamp = curStreamp();  // May have been updated
        if (forceOut != "") {
            if (forceOut.length() > max_size) {  // LCOV_EXCL_LINE
                yyerrorf("Output buffer too small for a `line");  // LCOV_EXCL_LINE
            } else {
                got = forceOut.length();
                strncpy(buf, forceOut.c_str(), got);
            }
        } else {
            if (streamp->m_eof) {
                if (yy_flex_debug) cout << "-  EOF\n";
            }
            got = 0;  // 0=EOF/EOS - although got was already 0.
            if (again) goto again;
        }
    }
    if (debug() >= 10) {
        cout << "-  pp::inputToLex  got=" << got << " '" << std::string{buf, got} << "'" << endl;
    }
    return got;
}

string V3PreLex::endOfStream(bool& againr) {
    // Switch to file or next unputString
    againr = false;
    if (yy_flex_debug) {
        cout << "-EOS state=" << curStreamp()->m_termState << " at " << curFilelinep() << endl;
    }
    if (curStreamp()->m_eof) return "";  // Don't delete the final "EOF" stream
    bool exited_file = curStreamp()->m_file;
    if (!exited_file) {
        // Midpoint of stream, just change buffers
        delete curStreamp();
        m_streampStack.pop();  // Must work as size>1; EOF is entry 0
        againr = true;
        return "";
    }
    // Multiple steps because we need FLEX to see ending \n and EOS to end
    // any illegal states, like an unterminated `protected region
    else if (!curStreamp()->m_termState) {
        // First shutdown phase for a file
        // Terminate all files with a newline.  This prevents problems if
        // the user had a define without a terminating newline,
        // otherwise the resumed file's next line would get tacked on.
        // Also makes it likely the `line that changes files comes out
        // immediately.
        curStreamp()->m_termState = 1;
        return "\n";  // Exit old file
    } else if (curStreamp()->m_termState == 1) {
        // Now the EOF - can't be sent with other characters
        curStreamp()->m_termState = 2;
        return "";  // End of file
    } else if (curStreamp()->m_termState == 2) {
        // Now ending `line
        curStreamp()->m_termState = 3;
        return curFilelinep()->lineDirectiveStrg(0);  // THe "2" exit is below
    } else {
        // Final shutdown phase for a stream, we can finally change the
        // current fileline to the new stream
        curStreamp()->m_termState = 0;
        FileLine* const filelinep = curFilelinep();
        delete curStreamp();
        m_streampStack.pop();  // Must work as size>1; EOF is entry 0
        if (curStreamp()->m_eof) {
            // EOF doesn't have a "real" fileline, but a linenumber of 0 from init time
            // Inherit whatever we last parsed so it's more obvious.
            curFilelinep(filelinep);
        }
        // The caller parser remembered the start location for the text we are parsing,
        // but we've discovered there was a file switch along the way, so update it.
        m_tokFilelinep = curFilelinep();
        //
        if (curStreamp()->m_eof) {
            return "";
        } else {
            return curFilelinep()->lineDirectiveStrg(2);  // Reenter resumed file
        }
    }
}

void V3PreLex::initFirstBuffer(FileLine* filelinep) {
    // Called from constructor to make first buffer
    // yy_create_buffer also sets yy_fill_buffer=1 so reads from YY_INPUT
    VPreStream* const streamp = new VPreStream{filelinep, this};
    streamp->m_eof = true;
    m_streampStack.push(streamp);
    //
    m_bufferState = yy_create_buffer(nullptr, YY_BUF_SIZE);
    yy_switch_to_buffer(m_bufferState);
    yyrestart(nullptr);
}

void V3PreLex::scanNewFile(FileLine* filelinep) {
    // Called on new open file.  scanBytesBack will be called next.
    if (streamDepth() > V3PreProc::DEFINE_RECURSION_LEVEL_MAX) {
        // The recursive `include in VPreProcImp should trigger first
        yyerrorf("Recursive `define or other nested inclusion");
        curStreamp()->m_eof = true;  // Fake it to stop recursion
    } else {
        VPreStream* const streamp = new VPreStream{filelinep, this};
        m_tokFilelinep = curFilelinep();
        streamp->m_file = true;
        scanSwitchStream(streamp);
    }
}

void V3PreLex::scanBytes(const string& str) {
    // Note buffers also appended in ::scanBytesBack
    // Not "m_buffers.push_front(std::string{strp,len})" as we need a `define
    // to take effect immediately, in the middle of the current buffer
    // Also we don't use scan_bytes that would set yy_fill_buffer
    // which would force Flex to bypass our YY_INPUT routine.
    if (streamDepth() > V3PreProc::DEFINE_RECURSION_LEVEL_MAX) {
        // More streams if recursive `define with complex insertion
        // More buffers mostly if something internal goes funky
        yyerrorf("Recursive `define or other nested inclusion");
        curStreamp()->m_eof = true;  // Fake it to stop recursion
    } else {
        VPreStream* const streamp = new VPreStream{curFilelinep(), this};
        streamp->m_buffers.push_front(str);
        scanSwitchStream(streamp);
    }
}

void V3PreLex::scanSwitchStream(VPreStream* streamp) {
    curStreamp()->m_buffers.push_front(currentUnreadChars());
    m_streampStack.push(streamp);
    yyrestart(nullptr);
}

void V3PreLex::scanBytesBack(const string& str) {
    // Initial creation, that will pull from YY_INPUT==inputToLex
    // Note buffers also appended in ::scanBytes
    if (VL_UNCOVERABLE(curStreamp()->m_eof)) yyerrorf("scanBytesBack not under scanNewFile");
    curStreamp()->m_buffers.push_back(str);
}

string V3PreLex::currentUnreadChars() {
    // WARNING - Peeking at internals
    ssize_t left = (yy_n_chars - (yy_c_buf_p - currentBuffer()->yy_ch_buf));
    if (left > 0) {  // left may be -1 at EOS
        *(yy_c_buf_p) = (yy_hold_char);
        return std::string(yy_c_buf_p, left);  // () narrowing conversion
    } else {
        return "";
    }
}

YY_BUFFER_STATE V3PreLex::currentBuffer() {
    return YY_CURRENT_BUFFER;
}

int V3PreLex::currentStartState() const {
    return YY_START;
}

void V3PreLex::lineDirective(const char* textp) {
    curFilelinep()->lineDirective(textp, m_enterExit /*ref*/);
    // Make sure we have a dependency on whatever file was specified
    V3File::addSrcDepend(curFilelinep()->filename());
}

void V3PreLex::warnBackslashSpace() {
    // Make fileline highlight the specific backslash and space
    curFilelinep()->v3warn(
        BSSPACE, "Backslash followed by whitespace, perhaps the whitespace is accidental?");
}

void V3PreLex::dumpSummary() {  // LCOV_EXCL_START
    cout << "-  pp::dumpSummary  curBuf=" << cvtToHex(currentBuffer());
#ifdef FLEX_DEBUG  // Else peeking at internals may cause portability issues
    ssize_t left = (yy_n_chars - (yy_c_buf_p - currentBuffer()->yy_ch_buf));
    cout << " left=" << std::dec << left;
#endif
    cout << endl;
}  // LCOV_EXCL_STOP

void V3PreLex::dumpStack() {  // LCOV_EXCL_START
    // For debug use
    dumpSummary();
    std::stack<VPreStream*> tmpstack = LEXP->m_streampStack;
    while (!tmpstack.empty()) {
        const VPreStream* const streamp = tmpstack.top();
        cout << "-    bufferStack[" << cvtToHex(streamp) << "]: "
             << " at=" << streamp->m_curFilelinep << " nBuf=" << streamp->m_buffers.size()
             << " size0=" << (streamp->m_buffers.empty() ? 0 : streamp->m_buffers.front().length())
             << (streamp->m_eof ? " [EOF]" : "") << (streamp->m_file ? " [FILE]" : "") << endl;
        tmpstack.pop();
    }
}  // LCOV_EXCL_STOP

string V3PreLex::cleanDbgStrg(const string& in) {
    string result = in;
    string::size_type pos;
    while ((pos = result.find('\n')) != string::npos) result.replace(pos, 1, "\\n");
    while ((pos = result.find('\r')) != string::npos) result.replace(pos, 1, "\\r");
    return result;
}

void V3PreLex::unused() {
    if (VL_UNCOVERABLE(false)) {  // LCOV_EXCL_START
        // Prevent unused warnings
        yy_top_state();
        yyerror((char*)"");
    }  // LCOV_EXCL_STOP
}

void V3PreLex::verilatorCmtLintSave() {
    m_lexLintState.push_back(*curFilelinep());
}
void V3PreLex::verilatorCmtLintRestore() {
    // No error here on restore without save - the verilog.y parse will report as appropriate
    if (m_lexLintState.empty()) return;
    curFilelinep()->warnStateFrom(m_lexLintState.back());
    m_lexLintState.pop_back();
}
void V3PreLex::verilatorCmtLint(const char* textp, bool warnOff) {
    const char* sp = textp;
    while (*sp && std::isspace(*sp)) ++sp;
    while (*sp && !std::isspace(*sp)) ++sp;  // "verilator"
    while (*sp && std::isspace(*sp)) ++sp;
    while (*sp && !std::isspace(*sp)) ++sp;  // "lint_on/lint_off"
    while (*sp && std::isspace(*sp)) ++sp;
    string msg = sp;
    for (auto pos = msg.begin(); pos != msg.end(); ++pos) {
        if (std::isspace(*pos) || *pos == '*') {
            msg.erase(pos, msg.end());
            break;
        }
    }
    // No warnings on bad warning codes - the verilog.y parse will report as appropriate
    curFilelinep()->warnOff(msg, warnOff);
}

/*###################################################################
 * Local Variables:
 * mode: C++
 * End:
 */
