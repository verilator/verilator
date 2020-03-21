// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilog::Preproc: Internal implementation of default preprocessor
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

#include "config_build.h"
#include "verilatedos.h"

#include "V3Error.h"
#include "V3Global.h"
#include "V3File.h"
#include "V3LanguageWords.h"
#include "V3PreLex.h"
#include "V3PreProc.h"
#include "V3PreShell.h"
#include "V3String.h"

#include <cstdarg>
#include <cstdlib>
#include <fstream>
#include <stack>
#include <vector>

//======================================================================
// Build in LEX script

#define yyFlexLexer V3Lexer
#include "V3PreLex.yy.cpp"
#undef yyFlexLexer

//YYSTYPE yylval;

//*************************************************************************

class VDefine {
    // Define class.  One for each define.
    //string    m_name;         // Name of the define (list is keyed by this)
    FileLine*   m_fileline;     // Where it was declared
    string      m_value;        // Value of define
    string      m_params;       // Parameters
    bool        m_cmdline;      // Set on command line, don't `undefineall
public:
    VDefine(FileLine* fl, const string& value, const string& params, bool cmdline)
        : m_fileline(fl), m_value(value), m_params(params), m_cmdline(cmdline) {}
    FileLine* fileline() const { return m_fileline; }
    string value() const { return m_value; }
    string params() const { return m_params; }
    bool cmdline() const { return m_cmdline; }
};

//*************************************************************************

class VDefineRef {
    // One for each pending define substitution
    string      m_name;         // Define last name being defined
    string      m_params;       // Define parameter list for next expansion
    string      m_nextarg;      // String being built for next argument
    int         m_parenLevel;   // Parenthesis counting inside def args (for PARENT not child)

    std::vector<string> m_args;  // List of define arguments
public:
    string name() const { return m_name; }
    string params() const { return m_params; }
    string nextarg() const { return m_nextarg; }
    void nextarg(const string& value) { m_nextarg = value; }
    int parenLevel() const { return m_parenLevel; }
    void parenLevel(int value) { m_parenLevel = value; }
    std::vector<string>& args() { return m_args; }
    VDefineRef(const string& name, const string& params)
        : m_name(name), m_params(params), m_parenLevel(0) {}
    ~VDefineRef() {}
};

//*************************************************************************
/// Data for parsing on/off

class VPreIfEntry {
    // One for each pending ifdef/ifndef
    bool        m_on;           // Current parse for this ifdef level is "on"
    bool        m_everOn;       // Some if term in elsif tree has been on
public:
    bool on() const { return m_on; }
    bool everOn() const { return m_everOn; }
    VPreIfEntry(bool on, bool everOn)
        : m_on(on), m_everOn(everOn || on) {}  // Note everOn includes new state
    ~VPreIfEntry() {}
};

//*************************************************************************
// Data for a preprocessor instantiation.

class V3PreProcImp : public V3PreProc {
public:
    // TYPES
    typedef std::map<string,VDefine> DefinesMap;
    typedef VInFilter::StrList StrList;

    // debug() -> see V3PreShellImp::debug; use --debugi-V3PreShell

    // Defines list
    DefinesMap m_defines;  ///< Map of defines

    // STATE
    V3PreProc* m_preprocp;  ///< Object we're holding data for
    V3PreLex* m_lexp;  ///< Current lexer state (NULL = closed)
    std::stack<V3PreLex*> m_includeStack;  ///< Stack of includers above current m_lexp
    int m_lastLineno;  // Last line number (stall detection)
    int m_tokensOnLine;  // Number of tokens on line (stall detection)

    enum ProcState { ps_TOP,
                     ps_DEFNAME_UNDEF, ps_DEFNAME_DEFINE,
                     ps_DEFNAME_IFDEF, ps_DEFNAME_IFNDEF, ps_DEFNAME_ELSIF,
                     ps_DEFFORM, ps_DEFVALUE, ps_DEFPAREN, ps_DEFARG,
                     ps_INCNAME, ps_ERRORNAME, ps_JOIN, ps_STRIFY };
    static const char* procStateName(ProcState s) {
        static const char* states[]
            = {"ps_TOP",
               "ps_DEFNAME_UNDEF", "ps_DEFNAME_DEFINE",
               "ps_DEFNAME_IFDEF", "ps_DEFNAME_IFNDEF", "ps_DEFNAME_ELSIF",
               "ps_DEFFORM", "ps_DEFVALUE", "ps_DEFPAREN", "ps_DEFARG",
               "ps_INCNAME", "ps_ERRORNAME", "ps_JOIN", "ps_STRIFY"};
        return states[s];
    }

    std::stack<ProcState> m_states;  ///< Current state of parser
    int         m_off;          ///< If non-zero, ifdef level is turned off, don't dump text
    bool        m_incError;     ///< Include error found
    string      m_lastSym;      ///< Last symbol name found.
    string      m_formals;      ///< Last formals found

    // For getRawToken/ `line insertion
    string      m_lineCmt;      ///< Line comment(s) to be returned
    bool        m_lineCmtNl;    ///< Newline needed before inserting lineCmt
    int         m_lineAdd;      ///< Empty lines to return to maintain line count
    bool        m_rawAtBol;     ///< Last rawToken left us at beginning of line

    // For getFinalToken
    bool        m_finAhead;     ///< Have read a token ahead
    int         m_finToken;     ///< Last token read
    string      m_finBuf;       ///< Last yytext read
    bool        m_finAtBol;     ///< Last getFinalToken left us at beginning of line
    FileLine*   m_finFilelinep; ///< Location of last returned token (internal only)

    // For stringification
    string      m_strify;       ///< Text to be stringified

    // For defines
    std::stack<VDefineRef> m_defRefs;  ///< Pending define substitution
    std::stack<VPreIfEntry> m_ifdefStack;   ///< Stack of true/false emitting evaluations
    unsigned    m_defDepth;     ///< How many `defines deep
    bool        m_defPutJoin;   ///< Insert `` after substitution

    // For `` join
    std::stack<string> m_joinStack;  ///< Text on lhs of join

    // For getline()
    string      m_lineChars;    ///< Characters left for next line

    void v3errorEnd(std::ostringstream& str) {
        fileline()->v3errorEnd(str);
    }

    static const char* tokenName(int tok);
    void debugToken(int tok, const char* cmtp);
    void parseTop();
    void parseUndef();

private:
    // Internal methods
    void endOfOneFile();
    string defineSubst(VDefineRef* refp);

    bool defExists(const string& name);
    string defValue(const string& name);
    string defParams(const string& name);
    FileLine* defFileline(const string& name);

    string commentCleanup(const string& text);
    bool commentTokenMatch(string& cmdr, const char* strg);
    string trimWhitespace(const string& strg, bool trailing);
    void unputString(const string& strg);
    void unputDefrefString(const string& strg);

    void parsingOn() {
        m_off--;
        if (m_off<0) fatalSrc("Underflow of parsing cmds");
        // addLineComment no longer needed; getFinalToken will correct.
    }
    void parsingOff() { m_off++; }

    int getRawToken();
    int getStateToken();
    int getFinalToken(string& buf);

    ProcState state() const { return m_states.top(); }
    bool stateIsDefname() const {
        return state()==ps_DEFNAME_UNDEF
            || state()==ps_DEFNAME_DEFINE
            || state()==ps_DEFNAME_IFDEF
            || state()==ps_DEFNAME_IFNDEF
            || state()==ps_DEFNAME_ELSIF;
    }
    void statePush(ProcState state) {
        m_states.push(state);
    }
    void statePop() {
        m_states.pop();
        if (VL_UNCOVERABLE(m_states.empty())) {
            error("InternalError: Pop of parser state with nothing on stack");  // LCOV_EXCL_LINE
            m_states.push(ps_TOP);  // LCOV_EXCL_LINE
        }
    }
    void stateChange(ProcState state) {
        statePop(); statePush(state);
    }

public:
    // METHODS, called from upper level shell
    void openFile(FileLine* fl, VInFilter* filterp, const string& filename);
    bool isEof() const { return m_lexp->curStreamp()->m_eof; }
    void forceEof() { m_lexp->curStreamp()->m_eof = true; }
    string getline();
    void insertUnreadback(const string& text) { m_lineCmt += text; }
    void insertUnreadbackAtBol(const string& text);
    void addLineComment(int enterExit);
    void dumpDefines(std::ostream& os);
    void candidateDefines(VSpellCheck* spellerp);

    // METHODS, callbacks
    virtual void comment(const string& text);  // Comment detected (if keepComments==2)
    virtual void include(const string& filename);  // Request a include file be processed
    virtual void undef(const string& name);
    virtual void undefineall();
    virtual void define(FileLine* fl, const string& name, const string& value,
                        const string& params, bool cmdline);
    virtual string removeDefines(const string& text);  // Remove defines in a text string

    // CONSTRUCTORS
    V3PreProcImp() {
        m_debug = 0;
        m_states.push(ps_TOP);
        m_off = 0;
        m_incError = false;
        m_lineChars = "";
        m_lastSym = "";
        m_lineAdd = 0;
        m_lineCmtNl = false;
        m_rawAtBol = true;
        m_finAhead = false;
        m_finAtBol = true;
        m_defDepth = 0;
        m_defPutJoin = false;
        m_finToken = 0;
        m_finFilelinep = NULL;
        m_lexp = NULL;
        m_preprocp = NULL;
        m_lastLineno = 0;
        m_tokensOnLine = 0;
    }
    void configure(FileLine* filelinep) {
        // configure() separate from constructor to avoid calling abstract functions
        m_preprocp = this;  // Silly, but to make code more similar to Verilog-Perl
        m_finFilelinep = new FileLine(filelinep->filename());
        m_finFilelinep->lineno(1);
        // Create lexer
        m_lexp = new V3PreLex(this, filelinep);
        m_lexp->m_keepComments = m_preprocp->keepComments();
        m_lexp->m_keepWhitespace = m_preprocp->keepWhitespace();
        m_lexp->m_pedantic = m_preprocp->pedantic();
        m_lexp->debug(debug()>=5 ? debug() : 0);  // See also V3PreProc::debug() method
    }
    ~V3PreProcImp() {
        if (m_lexp) VL_DO_CLEAR(delete m_lexp, m_lexp = NULL);
    }
};

//*************************************************************************
// Creation

V3PreProc* V3PreProc::createPreProc(FileLine* fl) {
    V3PreProcImp* preprocp = new V3PreProcImp();
    preprocp->configure(fl);
    return preprocp;
}

//*************************************************************************
// Defines

void V3PreProcImp::undef(const string& name) {
    m_defines.erase(name);
}
void V3PreProcImp::undefineall() {
    for (DefinesMap::iterator nextit, it = m_defines.begin(); it != m_defines.end(); it=nextit) {
        nextit = it; ++nextit;
        if (!it->second.cmdline()) m_defines.erase(it);
    }
}
bool V3PreProcImp::defExists(const string& name) {
    DefinesMap::iterator iter = m_defines.find(name);
    return (iter != m_defines.end());
}
string V3PreProcImp::defValue(const string& name) {
    DefinesMap::iterator iter = m_defines.find(name);
    if (iter == m_defines.end()) {
        fileline()->v3error("Define or directive not defined: `"+name);
        return "";
    }
    return iter->second.value();
}
string V3PreProcImp::defParams(const string& name) {
    DefinesMap::iterator iter = m_defines.find(name);
    if (iter == m_defines.end()) {
        fileline()->v3error("Define or directive not defined: `"+name);
        return "";
    }
    return iter->second.params();
}
FileLine* V3PreProcImp::defFileline(const string& name) {
    DefinesMap::iterator iter = m_defines.find(name);
    if (iter == m_defines.end()) return NULL;
    return iter->second.fileline();
}
void V3PreProcImp::define(FileLine* fl, const string& name, const string& value,
                          const string& params, bool cmdline) {
    UINFO(4,"DEFINE '"<<name<<"' as '"<<value<<"' params '"<<params<<"'"<<endl);
    if (!V3LanguageWords::isKeyword(string("`") + name).empty()) {
        fl->v3error("Attempting to define built-in directive: '`"
                    << name << "' (IEEE 1800-2017 22.5.1)");
    } else {
        if (defExists(name)) {
            if (!(defValue(name) == value
                  && defParams(name) == params)) {  // Duplicate defs are OK
                fl->v3warn(REDEFMACRO, "Redefining existing define: '"<<name<<"', with different value: "
                           <<value<<(params=="" ? "":" ")<<params);
                defFileline(name)->v3warn(REDEFMACRO, "Previous definition is here, with value: "
                                          << defValue(name)
                                          << (defParams(name).empty() ? "" : " ")
                                          << defParams(name));
            }
            undef(name);
        }
        m_defines.insert(make_pair(name, VDefine(fl, value, params, cmdline)));
    }
}

string V3PreProcImp::removeDefines(const string& text) {
    string val;
    string rtnsym = text;
    for (int loopprevent=0; loopprevent<100; loopprevent++) {
        string xsym = rtnsym;
        if (xsym.substr(0, 1)=="`") xsym.replace(0, 1, "");
        if (defExists(xsym)) {
            val = defValue(xsym);
            if (val != rtnsym) rtnsym = val;  // Prevent infinite loop if have `define X X
            else break;
        } else break;
    }
    return rtnsym;  // NA
}

//**********************************************************************
// Comments

void V3PreProcImp::include(const string& filename) {
    // Include seen.  Ask the preprocessor shell to call back around to us
    V3PreShell::preprocInclude(fileline(), filename);
}

string V3PreProcImp::commentCleanup(const string& text) {
    // Cleanup comment for easier parsing (call before commentTokenMatch)
    string cmd = text;
    string::size_type pos;
    while ((pos = cmd.find("//")) != string::npos) cmd.replace(pos, 2, "");
    while ((pos = cmd.find("/*")) != string::npos) cmd.replace(pos, 2, "");
    while ((pos = cmd.find("*/")) != string::npos) cmd.replace(pos, 2, "");
    while ((pos = cmd.find('\"')) != string::npos) cmd.replace(pos, 1, " ");
    while ((pos = cmd.find('\t')) != string::npos) cmd.replace(pos, 1, " ");
    while ((pos = cmd.find("  ")) != string::npos) cmd.replace(pos, 2, " ");
    while (!cmd.empty() && isspace(cmd[cmd.size()-1])) cmd.erase(cmd.size()-1);
    return cmd;
}

bool V3PreProcImp::commentTokenMatch(string& cmdr, const char* strg) {
    int len = strlen(strg);
    if (0==strncmp(cmdr.c_str(), strg, len)
        && (cmdr[len]=='\0' || isspace(cmdr[len]))) {
        if (isspace(cmdr[len])) len++;
        cmdr = cmdr.substr(len);
        return true;
    } else {
        return false;
    }
}

void V3PreProcImp::comment(const string& text) {
    // Comment detected.  Only keep relevant data.
    bool printed = false;
    if (v3Global.opt.preprocOnly() && v3Global.opt.ppComments()) {
        insertUnreadback(text);
        printed = true;
    }

    const char* cp = text.c_str();
    if (cp[0]=='/' && (cp[1]=='/' || cp[1]=='*')) {
        cp += 2;
    } else return;

    while (isspace(*cp)) cp++;

    bool synth = false;
    bool vlcomment = false;
    if ((cp[0]=='v' || cp[0]=='V')
        && 0==(strncmp(cp+1, "erilator", 8))) {
        cp += strlen("verilator");
        if (*cp == '_') fileline()->v3error("Extra underscore in meta-comment;"
                                            " use /*verilator {...}*/ not /*verilator_{...}*/");
        vlcomment = true;
    } else if (0==(strncmp(cp, "synopsys", strlen("synopsys")))) {
        cp += strlen("synopsys");
        synth = true;
        if (*cp == '_') fileline()->v3error("Extra underscore in meta-comment;"
                                            " use /*synopsys {...}*/ not /*synopsys_{...}*/");
    } else if (0==(strncmp(cp, "cadence", strlen("cadence")))) {
        cp += strlen("cadence");
        synth = true;
    } else if (0==(strncmp(cp, "pragma", strlen("pragma")))) {
        cp += strlen("pragma");
        synth = true;
    } else if (0==(strncmp(cp, "ambit synthesis", strlen("ambit synthesis")))) {
        cp += strlen("ambit synthesis");
        synth = true;
    } else {
        return;
    }

    if (!vlcomment && !synth) return;  // Short-circuit

    while (isspace(*cp)) cp++;
    string cmd = commentCleanup(string(cp));
    // cmd now is comment without extra spaces and "verilator" prefix

    if (synth) {
        if (v3Global.opt.assertOn()) {
            // one_hot, one_cold, (full_case, parallel_case)
            if (commentTokenMatch(cmd/*ref*/, "full_case")) {
                if (!printed) insertUnreadback("/*verilator full_case*/");
            }
            if (commentTokenMatch(cmd/*ref*/, "parallel_case")) {
                if (!printed) insertUnreadback("/*verilator parallel_case*/");
            }
            //if (commentTokenMatch(cmd/*ref*/, "one_hot")) {
            //  insertUnreadback ("/*verilator one_hot*/ "+cmd+";");
            //}
            //if (commentTokenMatch(cmd/*ref*/, "one_cold")) {
            //  insertUnreadback ("/*verilator one_cold*/ "+cmd+";");
            //}
            // else ignore the comment we don't recognize
        }  // else no assertions
    } else if (vlcomment) {
        string::size_type pos;
        if ((pos = cmd.find("public_flat_rw")) != string::npos) {
            // "/*verilator public_flat_rw @(foo) */" -> "/*verilator public_flat_rw*/ @(foo)"
            cmd = cmd.substr(pos+strlen("public_flat_rw"));
            while (isspace(cmd[0])) cmd = cmd.substr(1);
            if (!printed) insertUnreadback("/*verilator public_flat_rw*/ "+cmd+" /**/");
        } else {
            if (!printed) insertUnreadback("/*verilator "+cmd+"*/");
        }
    }
}

//*************************************************************************
// VPreProc Methods.

FileLine* V3PreProc::fileline() {
    V3PreProcImp* idatap = static_cast<V3PreProcImp*>(this);
    return idatap->m_lexp->m_tokFilelinep;
}

//**********************************************************************
// Parser Utilities

const char* V3PreProcImp::tokenName(int tok) {
    switch (tok) {
    case VP_BACKQUOTE   : return("BACKQUOTE");
    case VP_COMMENT     : return("COMMENT");
    case VP_DEFARG      : return("DEFARG");
    case VP_DEFFORM     : return("DEFFORM");
    case VP_DEFINE      : return("DEFINE");
    case VP_DEFREF      : return("DEFREF");
    case VP_DEFREF_JOIN : return("DEFREF_JOIN");
    case VP_DEFVALUE    : return("DEFVALUE");
    case VP_ELSE        : return("ELSE");
    case VP_ELSIF       : return("ELSIF");
    case VP_ENDIF       : return("ENDIF");
    case VP_EOF         : return("EOF");
    case VP_EOF_ERROR   : return("EOF_ERROR");
    case VP_ERROR       : return("ERROR");
    case VP_IFDEF       : return("IFDEF");
    case VP_IFNDEF      : return("IFNDEF");
    case VP_JOIN        : return("JOIN");
    case VP_INCLUDE     : return("INCLUDE");
    case VP_LINE        : return("LINE");
    case VP_STRIFY      : return("STRIFY");
    case VP_STRING      : return("STRING");
    case VP_SYMBOL      : return("SYMBOL");
    case VP_SYMBOL_JOIN : return("SYMBOL_JOIN");
    case VP_TEXT        : return("TEXT");
    case VP_UNDEF       : return("UNDEF");
    case VP_UNDEFINEALL : return("UNDEFINEALL");
    case VP_WHITE       : return("WHITE");
    default: return("?");
    }
}

void V3PreProcImp::unputString(const string& strg) {
    // Note: The preliminary call in ::openFile bypasses this function
    // We used to just m_lexp->unputString(strg.c_str());
    // However this can lead to "flex scanner push-back overflow"
    // so instead we scan from a temporary buffer, then on EOF return.
    // This is also faster than the old scheme, amazingly.
    if (m_lexp->m_bufferState!=m_lexp->currentBuffer()) {
        fatalSrc("bufferStack missing current buffer; will return incorrectly");
        // Hard to debug lost text as won't know till much later
    }
    m_lexp->scanBytes(strg);
}

void V3PreProcImp::unputDefrefString(const string& strg) {
    int multiline = 0;
    for (size_t i=0; i<strg.length(); i++) {
        if (strg[i] == '\n') multiline++;
    }
    unputString(strg);
    // A define that inserts multiple newlines are really attributed to one source line,
    // so temporarily don't increment lineno.
    m_lexp->curStreamp()->m_ignNewlines += multiline;  // Must be after unput - applies to new stream
}

string V3PreProcImp::trimWhitespace(const string& strg, bool trailing) {
    // Remove leading whitespace
    string out = strg;
    string::size_type leadspace = 0;
    while (out.length() > leadspace
           && isspace(out[leadspace])) leadspace++;
    if (leadspace) out.erase(0, leadspace);
    // Remove trailing whitespace
    if (trailing) {
        string::size_type trailspace = 0;
        while (out.length() > trailspace
               && isspace(out[out.length()-1-trailspace])) trailspace++;
        // Don't remove \{space_or_newline}
        if (trailspace && out.length() > trailspace && out[out.length()-1-trailspace]=='\\')
            trailspace--;
        if (trailspace) out.erase(out.length()-trailspace, trailspace);
    }
    return out;
}

string V3PreProcImp::defineSubst(VDefineRef* refp) {
    // Substitute out defines in a define reference.
    // (We also need to call here on non-param defines to handle `")
    // We could push the define text back into the lexer, but that's slow
    // and would make recursive definitions and parameter handling nasty.
    //
    // Note we parse the definition parameters and value here.  If a
    // parameterized define is used many, many times, we could cache the
    // parsed result.
    UINFO(4,"defineSubstIn  `"<<refp->name()<<" "<<refp->params()<<endl);
    for (unsigned i=0; i<refp->args().size(); i++) {
        UINFO(4,"defineArg["<<i<<"] = '"<<refp->args()[i]<<"'"<<endl);
    }
    // Grab value
    string value = defValue(refp->name());
    UINFO(4,"defineValue    '"<<V3PreLex::cleanDbgStrg(value)<<"'"<<endl);

    std::map<string,string> argValueByName;
    {   // Parse argument list into map
        unsigned numArgs = 0;
        string argName;
        int paren = 1;  // (), {} and [] can use same counter, as must be matched pair per spec
        string token;
        bool quote = false;
        bool haveDefault = false;
        // Note there's a leading ( and trailing ), so parens==1 is the base parsing level
        string params = refp->params();  // Must keep str in scope to get pointer
        const char* cp = params.c_str();
        if (*cp == '(') cp++;
        for (; *cp; cp++) {
            //UINFO(4,"   Parse  Paren="<<paren<<"  Arg="<<numArgs<<"  token='"<<token<<"'  Parse="<<cp<<endl);
            if (!quote && paren==1) {
                if (*cp==')' || *cp==',') {
                    string valueDef;
                    if (haveDefault) { valueDef = token; } else { argName = token; }
                    argName = trimWhitespace(argName, true);
                    UINFO(4,"    Got Arg="<<numArgs<<"  argName='"<<argName
                          <<"'  default='"<<valueDef<<"'"<<endl);
                    // Parse it
                    if (argName!="") {
                        if (refp->args().size() > numArgs) {
                            // A call `def( a ) must be equivalent to `def(a ), so trimWhitespace
                            // At one point we didn't trim trailing
                            // whitespace, but this confuses `"
                            string arg = trimWhitespace(refp->args()[numArgs], true);
                            if (arg != "") valueDef = arg;
                        } else if (!haveDefault) {
                            error("Define missing argument '"+argName+"' for: "+refp->name()+"\n");
                            return " `"+refp->name()+" ";
                        }
                        numArgs++;
                    }
                    argValueByName[argName] = valueDef;
                    // Prepare for next
                    argName = "";
                    token = "";
                    haveDefault = false;
                    continue;
                }
                else if (*cp=='=') {
                    haveDefault = true;
                    argName = token;
                    token = "";
                    continue;
                }
            }
            if (cp[0]=='\\' && cp[1]) {
                token += cp[0];  // \{any} Put out literal next character
                token += cp[1];
                cp++;
                continue;
            }
            if (!quote) {
                if (*cp=='(' || *cp=='{' || *cp=='[') paren++;
                else if (*cp==')' || *cp=='}' || *cp==']') paren--;
            }
            if (*cp=='"') quote=!quote;
            if (*cp) token += *cp;
        }
        if (refp->args().size() > numArgs
            // `define X() is ok to call with nothing
            && !(refp->args().size()==1 && numArgs==0
                 && trimWhitespace(refp->args()[0], false)=="")) {
            error("Define passed too many arguments: "+refp->name()+"\n");
            return " `"+refp->name()+" ";
        }
    }

    string out;
    {   // Parse substitution define using arguments
        string argName;
        bool quote = false;
        bool backslashesc = false;  // In \.....{space} block
        // Note we go through the loop once more at the NULL end-of-string
        for (const char* cp=value.c_str(); (*cp) || argName!=""; cp=(*cp?cp+1:cp)) {
            //UINFO(4, "CH "<<*cp<<"  an "<<argName<<endl);
            if (!quote && *cp == '\\') { backslashesc = true; }
            else if (isspace(*cp)) { backslashesc = false; }
            // We don't check for quotes; some simulators expand even inside quotes
            if ( isalpha(*cp) || *cp=='_'
                 || *cp=='$'  // Won't replace system functions, since no $ in argValueByName
                 || (argName!="" && (isdigit(*cp) || *cp=='$'))) {
                argName += *cp;
                continue;
            }
            if (argName != "") {
                // Found a possible variable substitution
                std::map<string,string>::iterator iter = argValueByName.find(argName);
                if (iter != argValueByName.end()) {
                    // Substitute
                    string subst = iter->second;
                    if (subst == "") {
                        // Normally `` is removed later, but with no token after, we're otherwise
                        // stuck, so remove proceeding ``
                        if (out.size()>=2 && out.substr(out.size()-2) == "``") {
                            out = out.substr(0, out.size()-2);
                        }
                    } else {
                        out += subst;
                    }
                } else {
                    out += argName;
                }
                argName = "";
            }
            if (!quote) {
                // Check for `` only after we've detected end-of-argname
                if (cp[0]=='`' && cp[1]=='`') {
                    if (backslashesc) {
                        // Don't put out the ``, we're forming an escape
                        // which will not expand further later
                    } else {
                        out += "``";  // `` must get removed later, as `FOO```BAR must pre-expand FOO and BAR
                        // See also removal in empty substitutes above
                    }
                    cp++;
                    continue;
                }
                else if (cp[0]=='`' && cp[1]=='"') {
                    out += "`\"";  // `" means to put out a " without enabling quote mode (sort of)
                    // however we must expand any macro calls inside it first.
                    // So keep it `", so we don't enter quote mode.
                    cp++;
                    continue;
                }
                else if (cp[0]=='`' && cp[1]=='\\' && cp[2]=='`' && cp[3]=='"') {
                    out += "`\\`\"";   // `\`" means to put out a backslash quote
                    // Leave it literal until we parse the VP_STRIFY string
                    cp += 3;
                    continue;
                }
                else if (cp[0]=='`' && cp[1]=='\\') {
                    out += '\\';  // `\ means to put out a backslash
                    cp++;
                    continue;
                }
                else if (cp[0]=='\\' && cp[1]=='\n') {
                    // We kept the \\n when we lexed because we don't want whitespace
                    // trimming to mis-drop the final \\n
                    // At replacement time we need the standard newline.
                    out += "\n";  // \\n newline
                    cp++;
                    continue;
                }
            }
            if (cp[0]=='\\' && cp[1]=='\"') {
                out += cp[0];  // \{any} Put out literal next character
                out += cp[1];
                cp++;
                continue;
            }
            else if (cp[0]=='\\') {
                // Normally \{any} would put out literal next character
                // Instead we allow "`define A(nm) \nm" to expand, per proposed mantis1537
                out += cp[0];
                continue;
            }
            if (*cp=='"') quote=!quote;
            if (*cp) out += *cp;
        }
    }

    UINFO(4,"defineSubstOut '"<<V3PreLex::cleanDbgStrg(out)<<"'"<<endl);
    return out;
}

//**********************************************************************
// Parser routines

void V3PreProcImp::openFile(FileLine* fl, VInFilter* filterp, const string& filename) {
    // Open a new file, possibly overriding the current one which is active.
    if (m_incError) return;
    V3File::addSrcDepend(filename);

    // Read a list<string> with the whole file.
    StrList wholefile;
    bool ok = filterp->readWholefile(filename, wholefile/*ref*/);
    if (!ok) {
        error("File not found: "+filename+"\n");
        return;
    }

    if (!m_preprocp->isEof()) {  // IE not the first file.
        // We allow the same include file twice, because occasionally it pops
        // up, with guards preventing a real recursion.
        if (m_lexp->m_streampStack.size() > V3PreProc::INCLUDE_DEPTH_MAX) {
            error("Recursive inclusion of file: "+filename);
            // Include might be a tree of includes that is O(n^2) or worse.
            // Once hit this error then, ignore all further includes so can unwind.
            m_incError = true;
            return;
        }
        // There's already a file active.  Push it to work on the new one.
        addLineComment(0);
    }

    // Save file contents for future error reporting
    FileLine* flsp = new FileLine(filename);
    flsp->lineno(1);
    flsp->newContent();
    for (StrList::iterator it=wholefile.begin(); it!=wholefile.end(); ++it) {
        flsp->contentp()->pushText(*it);
    }

    // Create new stream structure
    m_lexp->scanNewFile(flsp);
    addLineComment(1);  // Enter

    // Filter all DOS CR's en-mass.  This avoids bugs with lexing CRs in the wrong places.
    // This will also strip them from strings, but strings aren't supposed
    // to be multi-line without a "\"
    for (StrList::iterator it=wholefile.begin(); it!=wholefile.end(); ++it) {
        // We don't end-loop at \0 as we allow and strip mid-string '\0's (for now).
        bool strip = false;
        const char* sp = it->data();
        const char* ep = sp + it->length();
        // Only process if needed, as saves extra string allocations
        for (const char* cp=sp; cp<ep; cp++) {
            if (VL_UNLIKELY(*cp == '\r' || *cp == '\0')) {
                strip = true; break;
            }
        }
        if (strip) {
            string out;  out.reserve(it->length());
            for (const char* cp=sp; cp<ep; cp++) {
                if (!(*cp == '\r' || *cp == '\0')) {
                    out += *cp;
                }
            }
            *it = out;
        }

        // Push the data to an internal buffer.
        m_lexp->scanBytesBack(*it);
        // Reclaim memory; the push saved the string contents for us
        *it = "";
    }
}

void V3PreProcImp::insertUnreadbackAtBol(const string& text) {
    // Insert insuring we're at the beginning of line, for `line
    // We don't always add a leading newline, as it may result in extra unreadback(newlines).
    if (m_lineCmt == "") { m_lineCmtNl = true; }
    else if (m_lineCmt[m_lineCmt.length()-1]!='\n') {
        insertUnreadback("\n");
    }
    insertUnreadback(text);
}

void V3PreProcImp::addLineComment(int enterExit) {
    if (lineDirectives()) {
        insertUnreadbackAtBol(m_lexp->curFilelinep()->lineDirectiveStrg(enterExit));
    }
}

void V3PreProcImp::dumpDefines(std::ostream& os) {
    for (DefinesMap::const_iterator it = m_defines.begin(); it != m_defines.end(); ++it) {
        os<<"`define "<<it->first;
        // No need to print "()" below as already part of params()
        if (!it->second.params().empty()) os<<it->second.params();
        if (!it->second.value().empty()) os<<" "<<it->second.value();
        os<<endl;
    }
}

void V3PreProcImp::candidateDefines(VSpellCheck* spellerp) {
    for (DefinesMap::const_iterator it = m_defines.begin(); it != m_defines.end(); ++it) {
        spellerp->pushCandidate(string("`") + it->first);
    }
}

int V3PreProcImp::getRawToken() {
    // Get a token from the file, whatever it may be.
    while (1) {
      next_tok:
        if (m_lineAdd) {
            m_lineAdd--;
            m_rawAtBol = true;
            yyourtext("\n", 1);
            if (debug()>=5) debugToken(VP_WHITE, "LNA");
            return VP_WHITE;
        }
        if (m_lineCmt!="") {
            // We have some `line directive or other processed data to return to the user.
            static string rtncmt;  // Keep the c string till next call
            rtncmt = m_lineCmt;
            if (m_lineCmtNl) {
                if (!m_rawAtBol) rtncmt.insert(0, "\n");
                m_lineCmtNl = false;
            }
            yyourtext(rtncmt.c_str(), rtncmt.length());
            m_lineCmt = "";
            if (yyourleng()) m_rawAtBol = (yyourtext()[yyourleng()-1]=='\n');
            if (state()==ps_DEFVALUE) {
                V3PreLex::s_currentLexp->appendDefValue(yyourtext(), yyourleng());
                goto next_tok;
            } else {
                if (debug()>=5) debugToken(VP_TEXT, "LCM");
                return VP_TEXT;
            }
        }
        if (isEof()) return VP_EOF;

        // Snarf next token from the file
        m_lexp->curFilelinep()->startToken();
        int tok = m_lexp->lex();
        if (debug()>=5) debugToken(tok, "RAW");

        if (m_lastLineno != m_lexp->m_tokFilelinep->lineno()) {
            m_lastLineno = m_lexp->m_tokFilelinep->lineno();
            m_tokensOnLine = 0;
        } else if (++m_tokensOnLine > LINE_TOKEN_MAX) {
            error("Too many preprocessor tokens on a line (>"+cvtToStr(LINE_TOKEN_MAX)
                  +"); perhaps recursive `define");
            tok = VP_EOF_ERROR;
        }

        if (tok==VP_EOF || tok==VP_EOF_ERROR) {
            // An error might be in an unexpected point, so stop parsing
            if (tok==VP_EOF_ERROR) forceEof();
            // A EOF on an include, stream will find the EOF, after adding needed `lines
            goto next_tok;
        }

        if (yyourleng()) m_rawAtBol = (yyourtext()[yyourleng()-1]=='\n');
        return tok;
    }
}

void V3PreProcImp::debugToken(int tok, const char* cmtp) {
    static int s_debugFileline = v3Global.opt.debugSrcLevel("fileline");  // --debugi-fileline 9
    if (debug() >= 5) {
        string buf = string(yyourtext(), yyourleng());
        string::size_type pos;
        while ((pos = buf.find('\n')) != string::npos) { buf.replace(pos, 1, "\\n"); }
        while ((pos = buf.find('\r')) != string::npos) { buf.replace(pos, 1, "\\r"); }
        string flcol = m_lexp->m_tokFilelinep->asciiLineCol();
        fprintf(stderr, "%s: %s %s %s(%d) dr%d:  <%d>%-10s: %s\n",
                flcol.c_str(),
                cmtp, (m_off ? "of" : "on"),
                procStateName(state()), static_cast<int>(m_states.size()),
                static_cast<int>(m_defRefs.size()),
                m_lexp->currentStartState(), tokenName(tok), buf.c_str());
        if (s_debugFileline >= 9) {
            std::cerr<<m_lexp->m_tokFilelinep->warnContextSecondary()<<endl;
        }
    }
}

// Sorry, we're not using bison/yacc. It doesn't handle returning white space
// in the middle of parsing other tokens.

int V3PreProcImp::getStateToken() {
    // Return the next state-determined token
    while (1) {
      next_tok:
        if (isEof()) return VP_EOF;
        int tok = getRawToken();

        // Most states emit white space and comments between tokens. (Unless collecting a string)
        if (tok==VP_WHITE && state() !=ps_STRIFY) return tok;
        if (tok==VP_BACKQUOTE && state() !=ps_STRIFY) { tok = VP_TEXT; }
        if (tok==VP_COMMENT) {
            if (!m_off) {
                if (m_lexp->m_keepComments == KEEPCMT_SUB) {
                    string rtn; rtn.assign(yyourtext(), yyourleng());
                    comment(rtn);
                    // Need to ensure "foo/**/bar" becomes two tokens
                    insertUnreadback(" ");
                } else if (m_lexp->m_keepComments) {
                    return tok;
                } else {
                    // Need to ensure "foo/**/bar" becomes two tokens
                    insertUnreadback(" ");
                }
            }
            // We're off or processed the comment specially.  If there are newlines
            // in it, we also return the newlines as TEXT so that the linenumber
            // count is maintained for downstream tools
            for (size_t len=0; len<static_cast<size_t>(yyourleng()); len++) {
                if (yyourtext()[len]=='\n') m_lineAdd++;
            }
            goto next_tok;
        }
        if (tok==VP_LINE) {
            addLineComment(m_lexp->m_enterExit);
            goto next_tok;
        }

        if (tok==VP_DEFREF_JOIN) {
            // Here's something fun and unspecified as yet:
            // The existence of non-existance of a base define changes `` expansion
            //  `define QA_b zzz
            //  `define Q1 `QA``_b
            //   1Q1 -> zzz
            //  `define QA a
            //   `Q1 -> a_b
            // Note parenthesis make this unambiguous
            //  `define Q1 `QA()``_b  // -> a_b
            // This may be a side effect of how `UNDEFINED remains as `UNDEFINED,
            // but it screws up our method here.  So hardcode it.
            string name (yyourtext()+1, yyourleng()-1);
            if (defExists(name)) {  // JOIN(DEFREF)
                // Put back the `` and process the defref
                UINFO(5,"```: define "<<name<<" exists, expand first\n");
                m_defPutJoin = true;  // After define, unputString("``").  Not now as would lose yyourtext()
                UINFO(5,"TOKEN now DEFREF\n");
                tok = VP_DEFREF;
            } else {  // DEFREF(JOIN)
                UINFO(5,"```: define "<<name<<" doesn't exist, join first\n");
                // FALLTHRU, handle as with VP_SYMBOL_JOIN
            }
        }
        if (tok==VP_SYMBOL_JOIN  // not else if, can fallthru from above if()
            || tok==VP_DEFREF_JOIN || tok==VP_JOIN) {
            // a`` -> string doesn't include the ``, so can just grab next and continue
            string out (yyourtext(), yyourleng());
            UINFO(5,"`` LHS:"<<out<<endl);
            // a``b``c can have multiple joins, so we need a stack
            m_joinStack.push(out);
            statePush(ps_JOIN);
            goto next_tok;
        }

        // Deal with some special parser states
        switch (state()) {
        case ps_TOP: {
            break;
        }
        case ps_DEFNAME_UNDEF:   // FALLTHRU
        case ps_DEFNAME_DEFINE:  // FALLTHRU
        case ps_DEFNAME_IFDEF:   // FALLTHRU
        case ps_DEFNAME_IFNDEF:  // FALLTHRU
        case ps_DEFNAME_ELSIF: {
            if (tok==VP_SYMBOL) {
                m_lastSym.assign(yyourtext(), yyourleng());
                if (state()==ps_DEFNAME_IFDEF
                    || state()==ps_DEFNAME_IFNDEF) {
                    bool enable = defExists(m_lastSym);
                    UINFO(4,"Ifdef "<<m_lastSym<<(enable?" ON":" OFF")<<endl);
                    if (state()==ps_DEFNAME_IFNDEF) enable = !enable;
                    m_ifdefStack.push(VPreIfEntry(enable, false));
                    if (!enable) parsingOff();
                    statePop();
                    goto next_tok;
                }
                else if (state()==ps_DEFNAME_ELSIF) {
                    if (m_ifdefStack.empty()) {
                        error("`elsif with no matching `if\n");
                    } else {
                        // Handle `else portion
                        VPreIfEntry lastIf = m_ifdefStack.top(); m_ifdefStack.pop();
                        if (!lastIf.on()) parsingOn();
                        // Handle `if portion
                        bool enable = !lastIf.everOn() && defExists(m_lastSym);
                        UINFO(4,"Elsif "<<m_lastSym<<(enable?" ON":" OFF")<<endl);
                        m_ifdefStack.push(VPreIfEntry(enable, lastIf.everOn()));
                        if (!enable) parsingOff();
                    }
                    statePop();
                    goto next_tok;
                }
                else if (state()==ps_DEFNAME_UNDEF) {
                    if (!m_off) {
                        UINFO(4,"Undef "<<m_lastSym<<endl);
                        undef(m_lastSym);
                    }
                    statePop();
                    goto next_tok;
                }
                else if (state()==ps_DEFNAME_DEFINE) {
                    // m_lastSym already set.
                    stateChange(ps_DEFFORM);
                    m_lexp->pushStateDefForm();
                    goto next_tok;
                }
                else fatalSrc("Bad case\n");
                goto next_tok;
            }
            else if (tok==VP_TEXT) {
                // IE, something like comment between define and symbol
                if (!m_off) return tok;
                else goto next_tok;
            }
            else if (tok==VP_DEFREF) {
                // IE, `ifdef `MACRO(x): Substitute and come back here when state pops.
                break;
            }
            else {
                error(string("Expecting define name. Found: ")+tokenName(tok)+"\n");
                goto next_tok;
            }
        }
        case ps_DEFFORM: {
            if (tok==VP_DEFFORM) {
                m_formals = m_lexp->m_defValue;
                if (debug()>=5) cout<<"DefFormals='"<<V3PreLex::cleanDbgStrg(m_formals)<<"'\n";
                stateChange(ps_DEFVALUE);
                m_lexp->pushStateDefValue();
                goto next_tok;
            } else if (tok==VP_TEXT) {
                // IE, something like comment in formals
                if (!m_off) return tok;
                else goto next_tok;
            } else {
                error(string("Expecting define formal arguments. Found: ")+tokenName(tok)+"\n");
                goto next_tok;
            }
        }
        case ps_DEFVALUE: {
            static string newlines;
            newlines = "\n";  // Always start with trailing return
            if (tok == VP_DEFVALUE) {
                if (debug()>=5) cout<<"DefValue='"<<V3PreLex::cleanDbgStrg(m_lexp->m_defValue)
                                    <<"'  formals='"<<V3PreLex::cleanDbgStrg(m_formals)<<"'\n";
                // Add any formals
                string formals = m_formals;
                string value = m_lexp->m_defValue;
                // Remove returns
                // Not removing returns in values has two problems,
                // 1. we need to correct line numbers with `line after each substitution
                // 2. Substituting in " .... " with embedded returns requires \ escape.
                //    This is very difficult in the presence of `", so we
                //    keep the \ before the newline.
                for (size_t i=0; i<formals.length(); i++) {
                    if (formals[i] == '\n') {
                        newlines += "\n";
                    }
                }
                for (size_t i=0; i<value.length(); i++) {
                    if (value[i] == '\n') {
                        newlines += "\n";
                    }
                }
                if (!m_off) {
                    // Remove leading and trailing whitespace
                    value = trimWhitespace(value, true);
                    // Define it
                    UINFO(4,"Define "<<m_lastSym<<" "<<formals
                          <<" = '"<<V3PreLex::cleanDbgStrg(value)<<"'"<<endl);
                    define(fileline(), m_lastSym, value, formals, false);
                }
            } else {
                string msg = string("Bad define text, unexpected ")+tokenName(tok)+"\n";
                fatalSrc(msg);
            }
            statePop();
            // DEFVALUE is terminated by a return, but lex can't return both tokens.
            // Thus, we emit a return here.
            yyourtext(newlines.c_str(), newlines.length());
            return(VP_WHITE);
        }
        case ps_DEFPAREN: {
            if (tok==VP_TEXT && yyourleng()==1 && yyourtext()[0]=='(') {
                stateChange(ps_DEFARG);
                goto next_tok;
            } else {
                if (m_defRefs.empty()) fatalSrc("Shouldn't be in DEFPAREN w/o active defref");
                VDefineRef* refp = &(m_defRefs.top());
                error(string("Expecting ( to begin argument list for define reference `")+refp->name()+"\n");
                statePop();
                goto next_tok;
            }
        }
        case ps_DEFARG: {
            if (m_defRefs.empty()) fatalSrc("Shouldn't be in DEFARG w/o active defref");
            VDefineRef* refp = &(m_defRefs.top());
            refp->nextarg(refp->nextarg()+m_lexp->m_defValue); m_lexp->m_defValue = "";
            UINFO(4,"defarg++ "<<refp->nextarg()<<endl);
            if (tok==VP_DEFARG && yyourleng()==1 && yyourtext()[0]==',') {
                refp->args().push_back(refp->nextarg());
                stateChange(ps_DEFARG);
                m_lexp->pushStateDefArg(1);
                refp->nextarg("");
                goto next_tok;
            } else if (tok==VP_DEFARG && yyourleng()==1 && yyourtext()[0]==')') {
                // Substitute in and prepare for next action
                // Similar code in non-parenthesized define (Search for END_OF_DEFARG)
                refp->args().push_back(refp->nextarg());
                string out;
                if (!m_off) {
                    out = defineSubst(refp);
                    //NOP: out = m_preprocp->defSubstitute(out);
                }
                VL_DO_DANGLING(m_defRefs.pop(), refp);
                if (m_defRefs.empty()) {
                    statePop();
                    if (state() == ps_JOIN) {  // Handle {left}```FOO(ARG) where `FOO(ARG) might be empty
                        if (m_joinStack.empty()) fatalSrc("`` join stack empty, but in a ``");
                        string lhs = m_joinStack.top(); m_joinStack.pop();
                        out.insert(0, lhs);
                        UINFO(5,"``-end-defarg Out:"<<out<<endl);
                        statePop();
                    }
                    if (!m_off) unputDefrefString(out);
                    // Prevent problem when EMPTY="" in `ifdef NEVER `define `EMPTY
                    else if (stateIsDefname()) unputDefrefString("__IF_OFF_IGNORED_DEFINE");
                    m_lexp->m_parenLevel = 0;
                }
                else {  // Finished a defref inside a upper defref
                    // Can't subst now, or
                    // `define a(ign) x,y
                    // foo(`a(ign),`b)  would break because a contains comma
                    refp = &(m_defRefs.top());  // We popped, so new top
                    refp->nextarg(refp->nextarg()+m_lexp->m_defValue+out); m_lexp->m_defValue = "";
                    m_lexp->m_parenLevel = refp->parenLevel();
                    statePop();  // Will go to ps_DEFARG, as we're under another define
                }
                goto next_tok;
            } else if (tok==VP_DEFREF) {
                // Expand it, then state will come back here
                // Value of building argument is data before the lower defref
                // we'll append it when we push the argument.
                break;
            } else if (tok==VP_SYMBOL || tok==VP_STRING || tok==VP_TEXT || tok==VP_WHITE) {
                string rtn; rtn.assign(yyourtext(), yyourleng());
                refp->nextarg(refp->nextarg()+rtn);
                goto next_tok;
            } else if (tok==VP_STRIFY) {
                // We must expand stringinfication, when done will return to this state
                statePush(ps_STRIFY);
                goto next_tok;
            } else {
                error(string("Expecting ) or , to end argument list for define reference. Found: ")
                      +tokenName(tok));
                statePop();
                goto next_tok;
            }
        }
        case ps_INCNAME: {
            if (tok==VP_STRING) {
                statePop();
                m_lastSym.assign(yyourtext(), yyourleng());
                UINFO(4,"Include "<<m_lastSym<<endl);
                // Drop leading and trailing quotes.
                m_lastSym.erase(0, 1);
                m_lastSym.erase(m_lastSym.length()-1, 1);
                include(m_lastSym);
                goto next_tok;
            }
            else if (tok==VP_TEXT && yyourleng()==1 && yyourtext()[0]=='<') {
                // include <filename>
                stateChange(ps_INCNAME);  // Still
                m_lexp->pushStateIncFilename();
                goto next_tok;
            }
            else if (tok==VP_DEFREF
                     || tok==VP_STRIFY) {
                // Expand it, then state will come back here
                break;
            }
            else {
                statePop();
                error(string("Expecting include filename. Found: ")+tokenName(tok)+"\n");
                goto next_tok;
            }
        }
        case ps_ERRORNAME: {
            if (tok==VP_STRING) {
                if (!m_off) {
                    m_lastSym.assign(yyourtext(), yyourleng());
                    error(m_lastSym);
                }
                statePop();
                goto next_tok;
            }
            else {
                error(string("Expecting `error string. Found: ")+tokenName(tok)+"\n");
                statePop();
                goto next_tok;
            }
        }
        case ps_JOIN: {
            if (tok==VP_SYMBOL || tok==VP_TEXT) {
                if (m_joinStack.empty()) fatalSrc("`` join stack empty, but in a ``");
                string lhs = m_joinStack.top(); m_joinStack.pop();
                UINFO(5,"`` LHS:"<<lhs<<endl);
                string rhs (yyourtext(), yyourleng());
                UINFO(5,"`` RHS:"<<rhs<<endl);
                string out = lhs+rhs;
                UINFO(5,"`` Out:"<<out<<endl);
                unputString(out);
                statePop();
                goto next_tok;
            } else if (tok==VP_EOF || tok==VP_WHITE || tok == VP_COMMENT || tok==VP_STRING) {
                // Other compilers just ignore this, so no warning
                // "Expecting symbol to terminate ``; whitespace etc cannot
                // follow ``. Found: "+tokenName(tok)+"\n"
                string lhs = m_joinStack.top(); m_joinStack.pop();
                unputString(lhs);
                statePop();
                goto next_tok;
            } else {
                // `define, etc, fall through and expand.  Pop back here.
                break;
            }
        }
        case ps_STRIFY: {
            if (tok==VP_STRIFY) {
                // Quote what's in the middle of the stringification
                // Note a `" MACRO_WITH(`") `" doesn't need to be handled (we don't need a stack)
                // That behavior isn't specified, and other simulators vary widely
                string out = m_strify;
                m_strify = "";
                // Convert any newlines to spaces, so we don't get a
                // multiline "..." without \ escapes.
                // The spec is silent about this either way; simulators vary
                string::size_type pos;
                while ((pos = out.find('\n')) != string::npos) {
                    out.replace(pos, 1, " ");
                }
                unputString(string("\"")+out+"\"");
                statePop();
                goto next_tok;
            }
            else if (tok==VP_EOF) {
                error("`\" not terminated at EOF\n");
                break;
            }
            else if (tok==VP_BACKQUOTE) {
                m_strify += "\\\"";
                goto next_tok;
            }
            else if (tok==VP_DEFREF) {
                // Spec says to expand macros inside `"
                // Substitute it into the stream, then return here
                break;
            }
            else {
                // Append token to eventual string
                m_strify.append(yyourtext(), yyourleng());
                goto next_tok;
            }
        }
        default: fatalSrc("Bad case\n");
        }
        // Default is to do top level expansion of some tokens
        switch (tok) {
        case VP_INCLUDE:
            if (!m_off) {
                statePush(ps_INCNAME);
            }  // Else incname looks like normal text, that will be ignored
            goto next_tok;
        case VP_UNDEF:
            statePush(ps_DEFNAME_UNDEF);
            goto next_tok;
        case VP_DEFINE:
            // No m_off check here, as a `ifdef NEVER `define FOO(`endif)  should work
            statePush(ps_DEFNAME_DEFINE);
            goto next_tok;
        case VP_IFDEF:
            statePush(ps_DEFNAME_IFDEF);
            goto next_tok;
        case VP_IFNDEF:
            statePush(ps_DEFNAME_IFNDEF);
            goto next_tok;
        case VP_ELSIF:
            statePush(ps_DEFNAME_ELSIF);
            goto next_tok;
        case VP_ELSE:
            if (m_ifdefStack.empty()) {
                error("`else with no matching `if\n");
            } else {
                VPreIfEntry lastIf = m_ifdefStack.top(); m_ifdefStack.pop();
                bool enable = !lastIf.everOn();
                UINFO(4,"Else "<<(enable?" ON":" OFF")<<endl);
                m_ifdefStack.push(VPreIfEntry(enable, lastIf.everOn()));
                if (!lastIf.on()) parsingOn();
                if (!enable) parsingOff();
            }
            goto next_tok;
        case VP_ENDIF:
            UINFO(4,"Endif "<<endl);
            if (m_ifdefStack.empty()) {
                error("`endif with no matching `if\n");
            } else {
                VPreIfEntry lastIf = m_ifdefStack.top(); m_ifdefStack.pop();
                if (!lastIf.on()) parsingOn();
                // parsingOn() really only enables parsing if
                // all ifdef's above this want it on
            }
            goto next_tok;

        case VP_DEFREF: {
            // m_off not right here, but inside substitution, to make this work:
            // `ifdef NEVER `DEFUN(`endif)
            string name (yyourtext()+1, yyourleng()-1);
            UINFO(4,"DefRef "<<name<<endl);
            if (m_defPutJoin) { m_defPutJoin = false; unputString("``"); }
            if (m_defDepth++ > V3PreProc::DEFINE_RECURSION_LEVEL_MAX) {
                error("Recursive `define substitution: `"+name);
                goto next_tok;
            }
            // Substitute
            if (!defExists(name)) {  // Not found, return original string as-is
                m_defDepth = 0;
                UINFO(4,"Defref `"<<name<<" => not_defined"<<endl);
                if (m_off) {
                    goto next_tok;
                } else {
                    return VP_TEXT;
                }
            }
            else {
                string params = defParams(name);
                if (params=="0" || params=="") {  // Found, as simple substitution
                    string out;
                    if (!m_off) {
                        VDefineRef tempref(name, "");
                        out = defineSubst(&tempref);
                    }
                    // Similar code in parenthesized define (Search for END_OF_DEFARG)
                    //NOP: out = m_preprocp->defSubstitute(out);
                    if (m_defRefs.empty()) {
                        // Just output the substitution
                        if (state() == ps_JOIN) {  // Handle {left}```FOO where `FOO might be empty
                            if (m_joinStack.empty()) fatalSrc("`` join stack empty, but in a ``");
                            string lhs = m_joinStack.top(); m_joinStack.pop();
                            out.insert(0, lhs);
                            UINFO(5,"``-end-defref Out:"<<out<<endl);
                            statePop();
                        }
                        if (!m_off) unputDefrefString(out);
                        // Prevent problem when EMPTY="" in `ifdef NEVER `define `EMPTY
                        else if (stateIsDefname()) unputDefrefString("__IF_OFF_IGNORED_DEFINE");
                    } else {
                        // Inside another define.
                        // Can't subst now, or
                        // `define a x,y
                        // foo(`a,`b)  would break because a contains comma
                        VDefineRef* refp = &(m_defRefs.top());
                        refp->nextarg(refp->nextarg()+m_lexp->m_defValue+out);
                        m_lexp->m_defValue = "";
                    }
                    goto next_tok;
                }
                else {  // Found, with parameters
                    UINFO(4,"Defref `"<<name<<" => parameterized"<<endl);
                    // The CURRENT macro needs the paren saved, it's not a
                    // property of the child macro
                    if (!m_defRefs.empty()) m_defRefs.top().parenLevel(m_lexp->m_parenLevel);
                    m_defRefs.push(VDefineRef(name, params));
                    statePush(ps_DEFPAREN);
                    m_lexp->pushStateDefArg(0);
                    goto next_tok;
                }
            }
            fatalSrc("Bad case\n");  // FALLTHRU
            goto next_tok;  // above fatal means unreachable, but fixes static analysis warning
        }
        case VP_ERROR: {
            statePush(ps_ERRORNAME);
            goto next_tok;
        }
        case VP_EOF:
            if (!m_ifdefStack.empty()) {
                error("`ifdef not terminated at EOF\n");
            }
            return tok;
        case VP_UNDEFINEALL:
            if (!m_off) {
                UINFO(4,"Undefineall "<<endl);
                undefineall();
            }
            goto next_tok;
        case VP_STRIFY:
            // We must expand macros in the body of the stringification
            // Then, when done, form a final string to return
            // (it could be used as a include filename, for example, so need the string token)
            statePush(ps_STRIFY);
            goto next_tok;
        case VP_SYMBOL:
        case VP_STRING:
        case VP_TEXT: {
            m_defDepth = 0;
            if (!m_off) return tok;
            else goto next_tok;
        }
        case VP_WHITE:     // Handled at top of loop
        case VP_COMMENT:   // Handled at top of loop
        case VP_DEFFORM:   // Handled by state=ps_DEFFORM;
        case VP_DEFVALUE:  // Handled by state=ps_DEFVALUE;
        default:
            fatalSrc(string("Internal error: Unexpected token ")+tokenName(tok)+"\n");
            break;
        }
        return tok;
    }
}

int V3PreProcImp::getFinalToken(string& buf) {
    // Return the next user-visible token in the input stream.
    // Includes and such are handled here, and are never seen by the caller.
    if (!m_finAhead) {
        m_finAhead = true;
        m_finToken = getStateToken();
        m_finBuf = string(yyourtext(), yyourleng());
    }
    int tok = m_finToken;
    buf = m_finBuf;
    if (0 && debug()>=5) {
        string bufcln = V3PreLex::cleanDbgStrg(buf);
        string flcol = m_lexp->m_tokFilelinep->asciiLineCol();
        fprintf(stderr, "%s: FIN:      %-10s: %s\n",
                flcol.c_str(),
                tokenName(tok), bufcln.c_str());
    }
    // Track `line
    const char* bufp = buf.c_str();
    while (*bufp == '\n') bufp++;
    if ((tok == VP_TEXT || tok == VP_LINE) && 0==strncmp(bufp, "`line ", 6)) {
        int enter;
        m_finFilelinep->lineDirective(bufp, enter/*ref*/);
    }
    else {
        if (m_finAtBol && !(tok==VP_TEXT && buf=="\n")
            && m_preprocp->lineDirectives()) {
            if (int outBehind = (m_lexp->m_tokFilelinep->lastLineno()
                                 - m_finFilelinep->lastLineno())) {
                if (debug()>=5) {
                    string flcol = m_lexp->m_tokFilelinep->asciiLineCol();
                    fprintf(stderr, "%s: FIN: readjust, fin at %d  request at %d\n",
                            flcol.c_str(),
                            m_finFilelinep->lastLineno(),
                            m_lexp->m_tokFilelinep->lastLineno());
                }
                m_finFilelinep->filename(m_lexp->m_tokFilelinep->filename());
                m_finFilelinep->lineno(m_lexp->m_tokFilelinep->lastLineno());
                if (outBehind > 0
                    && (outBehind <= static_cast<int>(V3PreProc::NEWLINES_VS_TICKLINE))) {
                    // Output stream is behind, send newlines to get back in sync
                    // (Most likely because we're completing a disabled `endif)
                    if (m_preprocp->keepWhitespace()) {
                        buf = string(outBehind,'\n');
                        return VP_TEXT;
                    }
                } else {
                    // Need to backup, use `line
                    buf = m_finFilelinep->lineDirectiveStrg(0);
                    return VP_LINE;
                }
            }
        }
        // Track newlines in prep for next token
        for (string::iterator cp=buf.begin(); cp!=buf.end(); ++cp) {
            if (*cp == '\n') {
                m_finAtBol = true;
                m_finFilelinep->linenoInc();
            } else {
                m_finAtBol = false;
            }
        }
    }
    m_finAhead = false;  // Consumed the token
    return tok;
}

string V3PreProcImp::getline() {
    // Get a single line from the parse stream.  Buffer unreturned text until the newline.
    if (isEof()) return "";
    const char* rtnp;
    bool gotEof = false;
    while (NULL == (rtnp = strchr(m_lineChars.c_str(), '\n')) && !gotEof) {
        string buf;
        int tok = getFinalToken(buf/*ref*/);
        if (debug()>=5) {
            string bufcln = V3PreLex::cleanDbgStrg(buf);
            string flcol = m_lexp->m_tokFilelinep->asciiLineCol();
            fprintf(stderr, "%s: GETFETC:  %-10s: %s\n",
                    flcol.c_str(),
                    tokenName(tok), bufcln.c_str());
        }
        if (tok==VP_EOF) {
            // Add a final newline, if the user forgot the final \n.
            if (m_lineChars != "" && m_lineChars[m_lineChars.length()-1] != '\n') {
                m_lineChars.append("\n");
            }
            gotEof = true;
        }
        else {
            m_lineChars.append(buf);
        }
    }

    // Make new string with data up to the newline.
    int len = rtnp-m_lineChars.c_str()+1;
    string theLine(m_lineChars, 0, len);
    m_lineChars = m_lineChars.erase(0, len);  // Remove returned characters
    if (debug()>=4) {
        string lncln = V3PreLex::cleanDbgStrg(theLine);
        string flcol = m_lexp->m_tokFilelinep->asciiLineCol();
        fprintf(stderr, "%s: GETLINE:  %s\n",
                flcol.c_str(),
                lncln.c_str());
    }
    return theLine;
}
