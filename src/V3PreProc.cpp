// $Id$  -*- C++ -*-
//*************************************************************************
// DESCRIPTION: Verilog::Preproc: Internal implementation of default preprocessor
//
// Code available from: http://www.veripool.com/verilog-perl
//
// Authors: Wilson Snyder
//
//*************************************************************************
//
// Copyright 2000-2006 by Wilson Snyder.  This program is free software;
// you can redistribute it and/or modify it under the terms of either the GNU
// General Public License or the Perl Artistic License.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
//*************************************************************************

#include "config.h"
#include <stdio.h>
#include <stdarg.h>
#include <unistd.h>
#include <fstream>
#include <stack>
#include <vector>
#include <map>

#include "V3Error.h"
#include "V3Global.h"
#include "V3File.h"
#include "V3PreLex.h"
#include "V3PreProc.h"
#include "V3PreShell.h"

//======================================================================
// Build in LEX script

#define yyFlexLexer V3Lexer
#include "V3PreLex.yy.cpp"
#undef yyFlexLexer

//YYSTYPE yylval;

//*************************************************************************

class V3Define {
    // Define class.  One for each define.
    //string	m_name;		// Name of the define (list is keyed by this)
    FileLine*	m_fileline;	// Where it was declared
    string	m_value;	// Value of define
    string	m_params;	// Parameters
public:
    V3Define(FileLine* fl, const string& value, const string& params)
	: m_fileline(fl), m_value(value), m_params(params) {}
    FileLine* fileline() const { return m_fileline; }
    string value() const { return m_value; }
    string params() const { return m_params; }
};

//*************************************************************************
// Data for a preprocessor instantiation.

struct V3PreProcImp : public V3PreProc {
    // TYPES
    typedef std::map<string,V3Define> DefinesMap;

    // debug() -> see V3PreShellImp::debug

    // STATE
    V3PreLex* m_lexp;	// Current lexer state (NULL = closed)
    stack<V3PreLex*> m_includeStack;	// Stack of includers above current m_lexp

    enum ProcState { ps_TOP, ps_DEFNAME, ps_DEFVALUE, ps_DEFPAREN, ps_DEFARG,
		     ps_INCNAME, ps_ERRORNAME };
    ProcState	m_state;	// Current state of parser
    int		m_stateFor;	// Token state is parsing for
    int		m_off;		// If non-zero, ifdef level is turned off, don't dump text
    string	m_lastSym;	// Last symbol name found.

    // For getRawToken/ `line insertion
    string	m_lineCmt;	// Line comment(s) to be returned
    int		m_lineAdd;	// Empty lines to return to maintain line count

    // For defines
    string	m_defName;	// Define last name being defined
    string	m_defParams;	// Define parameter list for next expansion
    stack<bool> m_ifdefStack;	// Stack of true/false emitting evaluations
    vector<string> m_defArgs;	// List of define arguments
    unsigned	m_defDepth;	// How many `defines deep

    // Defines list
    DefinesMap	m_defines;		// Map of defines

    // For getline()
    string	m_lineChars;	// Characters left for next line

    void v3errorEnd(ostringstream& str) {
	fileline()->v3errorEnd(str);
    }

    const char* tokenName(int tok);
    int getRawToken();
    int getToken();
    void parseTop();
    void parseUndef();

private:
    // Internal methods
    void eof();
    string defineSubst();
    void addLineComment(int enter_exit_level);

    bool defExists(const string& name);
    string defValue(const string& name);
    string defParams(const string& name);
    FileLine* defFileline(const string& name);

    bool commentTokenMatch(string& cmdr, const char* strg);

    void parsingOn() {
	m_off--;
	if (m_off<0) fileline()->v3fatalSrc("Underflow of parsing cmds");
	if (!m_off) addLineComment(0);
    }
    void parsingOff() { m_off++; }

public:
    // METHODS, called from upper level shell
    virtual void openFile(FileLine* fl, const string& filename);
    virtual bool isEof() const { return (m_lexp==NULL); }
    virtual string getline();
    virtual void insertUnreadback(const string& text) { m_lineCmt += text; }

    // METHODS, callbacks
    virtual void comment(const string& cmt);		// Comment detected (if keepComments==2)
    virtual void include(const string& filename);	// Request a include file be processed
    virtual void undef (const string& name);
    virtual void define (FileLine* fl, const string& name, const string& value, const string& params);
    virtual string removeDefines(const string& text);	// Remove defines in a text string

    // CONSTRUCTORS
    V3PreProcImp(FileLine* fl) : V3PreProc(fl) {
	m_lexp = NULL;	 // Closed.
	m_state = ps_TOP;
	m_defName = "";
	m_off = 0;
	m_lineChars = "";
	m_lastSym = "";
	m_lineAdd = 0;
	m_defDepth = 0;
    }
};

//*************************************************************************
// Creation

V3PreProc* V3PreProc::createPreProc(FileLine* fl) {
    return new V3PreProcImp(fl);
}

bool V3PreProc::optPsl() {
    return v3Global.opt.psl();
}

//*************************************************************************
// Defines

void V3PreProcImp::undef(const string& name) {
    m_defines.erase(name);
}
bool V3PreProcImp::defExists(const string& name) {
    DefinesMap::iterator iter = m_defines.find(name);
    if (iter == m_defines.end()) return false;
    return true;
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
    if (iter == m_defines.end()) return false;
    return iter->second.fileline();
}
void V3PreProcImp::define(FileLine* fl, const string& name, const string& value, const string& params) {
    UINFO(4,"DEFINE '"<<name<<"' as '"<<value<<"' params '"<<params<<"'"<<endl);
    if (defExists(name)) {
	if (!(defValue(name)==value && defParams(name)==params)) {  // Duplicate defs are OK
	    fl->v3error("Define already exists: "<<name);
	    defFileline(name)->v3error("Previous definition is here.");
	}
	undef(name);
    }
    m_defines.insert(make_pair(name, V3Define(fl, value, params)));
}

string V3PreProcImp::removeDefines(const string& sym) {
    string val = "0_never_match";
    string rtnsym = sym;
    for (int loopprevent=0; loopprevent<100; loopprevent++) {
	string xsym = rtnsym;
	if (xsym.substr(0,1)=="`") xsym.replace(0,1,"");
        if (defExists(xsym)) {
	    val = defValue(xsym);
	    if (val != rtnsym) rtnsym=val;  // Prevent infinite loop if have `define X X
	    else break;
        } else break;
    }
    return rtnsym;  // NA
}

//**********************************************************************
// Comments

void V3PreProcImp::include(const string& filename) {
    // Include seen.  Ask the preprocessor shell to call back around to us
    V3PreShell::preprocInclude (fileline(), filename);
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
    // if (text =~ m!^\/[\*\/]\s*[vV]erilator\s*(.*$)!) {
    //	  string cmd = $1;
    //	  cmd =~ s!\s*(\*\/)\s*$!!;
    //	  cmd =~ s!\s+! !g;
    //	  cmd =~ s!\s+$!!g;
    const char* cp = text.c_str();
    if (cp[0]=='/' && (cp[1]=='/' || cp[1]=='*')) {
	cp+=2;
    } else return;

    while (isspace(*cp)) cp++;

    bool synth = false;
    if ((cp[0]=='v' || cp[0]=='V')
	&& 0==(strncmp(cp+1,"erilator",8))) {
	cp+=strlen("verilator");
    } else if (0==(strncmp(cp,"synopsys",strlen("synopsys")))) {
	cp+=strlen("synopsys");
	synth = true;
    } else if (0==(strncmp(cp,"cadence",strlen("cadence")))) {
	cp+=strlen("cadence");
	synth = true;
    } else if (0==(strncmp(cp,"ambit synthesis",strlen("ambit synthesis")))) {
	cp+=strlen("ambit synthesis");
	synth = true;
    } else {
	return;
    }
    if (*cp && !isspace(*cp)) return;

    while (isspace(*cp)) cp++;

    const char* ep = cp+strlen(cp);
    if (ep>cp && (ep[-1]=='/' || cp[-2]=='*')) ep-=2;
    while (ep>cp && (isspace(ep[-1]))) ep--;

    string cmd (cp, ep-cp);
    string::size_type pos;
    while ((pos=cmd.find("\"")) != string::npos)
	cmd.replace(pos, 1, " ");
    while ((pos=cmd.find("\t")) != string::npos)
	cmd.replace(pos, 1, " ");
    while ((pos=cmd.find("  ")) != string::npos)
	cmd.replace(pos, 2, " ");

    if (synth) {
	if (v3Global.opt.assertOn()) {
	    // one_hot, one_cold, (full_case, parallel_case)
	    if (commentTokenMatch(cmd/*ref*/, "full_case")) {
		insertUnreadback ("/*verilator full_case*/");
	    }
	    if (commentTokenMatch(cmd/*ref*/, "parallel_case")) {
		insertUnreadback ("/*verilator parallel_case*/");
	    }
	    if (commentTokenMatch(cmd/*ref*/, "one_hot")) {
		insertUnreadback ("/*verilator one_hot*/ "+cmd+";");
	    }
	    if (commentTokenMatch(cmd/*ref*/, "one_cold")) {
		insertUnreadback ("/*verilator one_cold*/ "+cmd+";");
	    }
	    // else ignore the comment we don't recognize
	} // else no assertions
    } else {
	insertUnreadback ("/*verilator "+cmd+"*/");
    }
}

//**********************************************************************
// Parser Utilities

const char* V3PreProcImp::tokenName(int tok) {
    switch (tok) {
    case VP_EOF		: return("EOF");
    case VP_INCLUDE	: return("INCLUDE");
    case VP_IFDEF	: return("IFDEF");
    case VP_IFNDEF	: return("IFNDEF");
    case VP_ENDIF	: return("ENDIF");
    case VP_UNDEF	: return("UNDEF");
    case VP_DEFINE	: return("DEFINE");
    case VP_ELSE	: return("ELSE");	
    case VP_ELSIF	: return("ELSIF");	
    case VP_SYMBOL	: return("SYMBOL");
    case VP_STRING	: return("STRING");
    case VP_DEFVALUE	: return("DEFVALUE");
    case VP_COMMENT	: return("COMMENT");
    case VP_TEXT	: return("TEXT");	
    case VP_WHITE	: return("WHITE");	
    case VP_DEFREF	: return("DEFREF");
    case VP_DEFARG	: return("DEFARG");
    case VP_ERROR	: return("ERROR");
    case VP_PSL		: return("PSL");
    default: return("?");
    } 
}

string V3PreProcImp::defineSubst() {
    // Substitute out defines in a argumented define reference.
    // We could push the define text back into the lexer, but that's slow
    // and would make recursive definitions and parameter handling nasty.
    //
    // Note we parse the definition parameters and value here.  If a
    // parameterized define is used many, many times, we could cache the
    // parsed result.
    UINFO(4,"defineSubstIn  `"<<m_defName<<" "<<m_defParams<<endl);
    for (unsigned i=0; i<m_defArgs.size(); i++) {
	UINFO(4,"defineArg["<<i<<"] = "<<m_defArgs[i]<<endl);
    }
    // Grab value
    string value = defValue(m_defName);
    UINFO(4,"defineValue    `"<<value<<endl);

    map<string,string> argValueByName;
    {   // Parse argument list into map
	unsigned numArgs=0;
	string argName;
	for (const char* cp=m_defParams.c_str(); *cp; cp++) {
	    if (*cp=='(') {
	    } else if (argName=="" && isspace(*cp)) {
	    } else if (isspace(*cp) || *cp==')' || *cp==',') {
		if (argName!="") {
		    if (m_defArgs.size() >= numArgs) {
			argValueByName[argName] = m_defArgs[numArgs];
		    }
		    numArgs++;
		    //cout << "  arg "<<argName<<endl;
		}
		argName = "";
	    } else if ( isalpha(*cp) || *cp=='_'
			|| (argName!="" && (isdigit(*cp) || *cp=='$'))) {
		argName += *cp;
	    }
	}
	if (m_defArgs.size() != numArgs) {
	    fileline()->v3error("Define passed wrong number of arguments: "+m_defName+"\n");
	    return " `"+m_defName+" ";
	}
    }

    string out = " ";
    {   // Parse substitution define using arguments
	string argName;
	string prev;
	bool quote = false;
	// Note we go through the loop once more at the NULL end-of-string
	for (const char* cp=value.c_str(); (*cp) || argName!=""; cp=(*cp?cp+1:cp)) {
	    //cout << "CH "<<*cp<<"  an "<<argName<<"\n";
	    if (!quote) {
		if ( isalpha(*cp) || *cp=='_'
		     || (argName!="" && (isdigit(*cp) || *cp=='$'))) {
		    argName += *cp;
		    continue;
		}
	    }
	    if (argName != "") {
		// Found a possible variable substitution
		map<string,string>::iterator iter = argValueByName.find(argName);
		if (iter != argValueByName.end()) {
		    // Substitute
		    string subst = iter->second;
		    out += subst;
		} else {
		    out += argName;
		}
		argName = "";
	    }
	    if (!quote) {
		// Check for `` only after we've detected end-of-argname
		if (cp[0]=='`' && cp[1]=='`') {
		    //out += "";   // `` means to suppress the ``
		    cp++;
		    continue;
		}
		else if (cp[0]=='`' && cp[1]=='"') {
		    out += '"';   // `" means to put out a " without enabling quote mode (sort of)
		    cp++;
		    continue;
		}
		else if (cp[0]=='`' && cp[1]=='\\') {
		    out += '\\';   // `\ means to put out a backslash
		    cp++;
		    continue;
		}
	    }
	    if (cp[0]=='\\' && cp[1]) {
		out += cp[0]; // \{any} Put out literal next character
		out += cp[1];
		cp++;
		continue;
	    }
	    if (*cp=='"') quote=!quote;
	    if (*cp) out += *cp;
	}
    }

    out += " ";
    UINFO(4,"defineSubstOut "<<out<<endl);
    return out;
}

//**********************************************************************
// Parser routines

void V3PreProcImp::openFile(FileLine* fl, const string& filename) {
    // Open a new file, possibly overriding the current one which is active.
    if (fl) {
	m_fileline = new FileLine(fl);
    }

    V3File::addSrcDepend(filename);
    FILE* fp = fopen (filename.c_str(), "r");
    if (!fp) {
	fileline()->v3error("File not found: "+filename+"\n");
	return;
    }

    if (m_lexp) {
	// We allow the same include file twice, because occasionally it pops
	// up, with guards preventing a real recursion.
	if (m_includeStack.size()>V3PreProc::INCLUDE_DEPTH_MAX) {
	    fileline()->v3error("Recursive inclusion of file: "+filename);
	    return;
	}
	// There's already a file active.  Push it to work on the new one.
	m_includeStack.push(m_lexp);
	addLineComment(0);
    }

    m_lexp = new V3PreLex (fp);
    m_lexp->m_keepComments = keepComments();
    m_lexp->m_pedantic = pedantic();
    m_lexp->m_curFilelinep = new FileLine(filename, 1);
    m_fileline = m_lexp->m_curFilelinep;  // Remember token start location
    addLineComment(1); // Enter

    yy_flex_debug = (debug()>4)?1:0;
    yy_switch_to_buffer(m_lexp->m_yyState);
}

void V3PreProcImp::addLineComment(int enter_exit_level) {
    if (lineDirectives()) {
	char numbuf[20]; sprintf(numbuf, "%d", m_lexp->m_curFilelinep->lineno());
	char levelbuf[20]; sprintf(levelbuf, "%d", enter_exit_level);
	string cmt = ((string)"\n`line "+numbuf
		      +" \""+m_lexp->m_curFilelinep->filename()+"\" "
		      +levelbuf+"\n");
	insertUnreadback(cmt);
    }
}

void V3PreProcImp::eof() {
    // Remove current lexer
    UINFO(4,fileline()<<"EOF!\n");
    addLineComment(2);	// Exit
    delete m_lexp;  m_lexp=NULL;
    // Perhaps there's a parent file including us?
    if (!m_includeStack.empty()) {
	// Back to parent.
	m_lexp = m_includeStack.top(); m_includeStack.pop();
	addLineComment(0);
	yy_switch_to_buffer(m_lexp->m_yyState);
    }
}

int V3PreProcImp::getRawToken() {
    // Get a token from the file, whatever it may be.
    while (1) {
      next_tok:
	if (m_lineAdd) {
	    m_lineAdd--;
	    yytext="\n"; yyleng=1;
	    return (VP_TEXT);
	}
	if (m_lineCmt!="") {
	    // We have some `line directive to return to the user.  Do it.
	    static string rtncmt;  // Keep the c string till next call
	    rtncmt = m_lineCmt;
	    yytext=(char*)rtncmt.c_str(); yyleng=rtncmt.length();
	    m_lineCmt = "";
	    if (m_state!=ps_DEFVALUE) return (VP_TEXT);
	    else {
		V3PreLex::s_currentLexp->appendDefValue(yytext,yyleng); 
		goto next_tok;
	    }
	}
	if (isEof()) return (VP_EOF);
	// Snarf next token from the file
	m_fileline = m_lexp->m_curFilelinep;  // Remember token start location
	V3PreLex::s_currentLexp = m_lexp;   // Tell parser where to get/put data
	int tok = yylex();

	if (debug()>4) {
	    char buf[10000]; strncpy(buf, yytext, yyleng);  buf[yyleng] = '\0';
	    for (char* cp=buf; *cp; cp++) if (*cp=='\n') *cp='$';
	    fprintf (stderr, "%d: RAW %d %d:  %-10s: %s\n",
		     fileline()->lineno(), m_off, m_state, tokenName(tok), buf);
	}
    
	// On EOF, try to pop to upper level includes, as needed.
	if (tok==VP_EOF) {
	    eof();
	    goto next_tok;  // Parse parent, or find the EOF.
	}

	return tok;
    }
}

// Sorry, we're not using bison/yacc. It doesn't handle returning white space
// in the middle of parsing other tokens.

int V3PreProcImp::getToken() {
    // Return the next user-visible token in the input stream.
    // Includes and such are handled here, and are never seen by the caller.
    while (1) {
      next_tok:
	if (isEof()) return VP_EOF;
	int tok = getRawToken();
	// Always emit white space and comments between tokens.
	if (tok==VP_WHITE) return (tok);
	if (tok==VP_COMMENT) {
	    if (!m_off) {
		if (m_lexp->m_keepComments == KEEPCMT_SUB) {
		    string rtn; rtn.assign(yytext,yyleng);
		    comment(rtn);
		} else {
		    return (tok);
		}
	    }
	    // We're off or processed the comment specially.  If there are newlines
	    // in it, we also return the newlines as TEXT so that the linenumber
	    // count is maintained for downstream tools
	    for (int len=0; len<yyleng; len++) { if (yytext[len]=='\n') m_lineAdd++; }
	    goto next_tok;
	}
	// Deal with some special parser states
	switch (m_state) {
	case ps_TOP: {
	    break;
	}
	case ps_DEFNAME: {
	    if (tok==VP_SYMBOL) {
		m_state = ps_TOP;
		m_lastSym.assign(yytext,yyleng);
		if (m_stateFor==VP_IFDEF
		    || m_stateFor==VP_IFNDEF) {
		    bool enable = defExists(m_lastSym);
		    UINFO(4,"Ifdef "<<m_lastSym<<(enable?" ON":" OFF")<<endl);
		    if (m_stateFor==VP_IFNDEF) enable = !enable;
		    m_ifdefStack.push(enable);
		    if (!enable) parsingOff();
		}
		else if (m_stateFor==VP_ELSIF) {
		    if (m_ifdefStack.empty()) {
			fileline()->v3error("`elsif with no matching `if\n");
		    } else {
			// Handle `else portion
			bool lastEnable = m_ifdefStack.top(); m_ifdefStack.pop();
			if (!lastEnable) parsingOn();
			// Handle `if portion
			bool enable = !lastEnable && defExists(m_lastSym);
			UINFO(4,"Elsif "<<m_lastSym<<(enable?" ON":" OFF")<<endl);
			m_ifdefStack.push(enable);
			if (!enable) parsingOff();
		    }
		}
		else if (m_stateFor==VP_UNDEF) {
		    if (!m_off) {
			UINFO(4,"Undef "<<m_lastSym<<endl);
			undef(m_lastSym);
		    }
		}
		else if (m_stateFor==VP_DEFINE) {
		    // m_lastSym already set.
		    m_state = ps_DEFVALUE;
		    m_lexp->setStateDefValue();
		}
		else fileline()->v3fatalSrc("Bad case\n");
		goto next_tok;
	    }
	    else {
		fileline()->v3error("Expecting define name. Found: "<<tokenName(tok));
		goto next_tok;
	    }
	}
	case ps_DEFVALUE: {
 	    static string newlines;
	    newlines = "\n";  // Always start with trailing return
	    if (tok == VP_DEFVALUE) {
		// Remove returns
		for (unsigned i=0; i<m_lexp->m_defValue.length(); i++) {
		    if (m_lexp->m_defValue[i] == '\n') {
			m_lexp->m_defValue[i] = ' ';
			newlines += "\n";
		    }
		}
		if (!m_off) {
		    string params;
		    if (m_lexp->m_defValue=="" || isspace(m_lexp->m_defValue[0])) {
			// Define without parameters
		    } else if (m_lexp->m_defValue[0] == '(') {
			string::size_type paren = m_lexp->m_defValue.find(")");
			if (paren == string::npos) {
			    fileline()->v3error("Missing ) to end define arguments.");
			} else {
			    params = m_lexp->m_defValue.substr(0, paren+1);
			    m_lexp->m_defValue.replace(0, paren+1, "");
			}
		    } else {
			fileline()->v3error("Missing space or paren to start define value.");
		    }
		    // Remove leading whitespace
		    unsigned leadspace = 0;
		    while (m_lexp->m_defValue.length() > leadspace
		    	   && isspace(m_lexp->m_defValue[leadspace])) leadspace++;
		    if (leadspace) m_lexp->m_defValue.erase(0,leadspace);
		    // Remove trailing whitespace
		    unsigned trailspace = 0;
		    while (m_lexp->m_defValue.length() > trailspace
			   && isspace(m_lexp->m_defValue[m_lexp->m_defValue.length()-1-trailspace])) trailspace++;
		    if (trailspace) m_lexp->m_defValue.erase(m_lexp->m_defValue.length()-trailspace,trailspace);
		    // Define it
		    UINFO(4,"Define "<<m_lastSym<<" = "<<m_lexp->m_defValue<<endl);
		    define(fileline(), m_lastSym, m_lexp->m_defValue, params);
		}
	    } else {
		fileline()->v3fatalSrc("Bad define text\n");
	    }
	    m_state = ps_TOP;
	    // DEFVALUE is terminated by a return, but lex can't return both tokens.
	    // Thus, we emit a return here.
	    yytext=(char*)(newlines.c_str()); yyleng=newlines.length();
	    return(VP_WHITE); 
	}
	case ps_DEFPAREN: {
	    if (tok==VP_TEXT && yyleng==1 && yytext[0]=='(') {
		m_defArgs.clear();
		m_state = ps_DEFARG;
		m_lexp->setStateDefArg();
		goto next_tok;
	    } else {
		m_state = ps_TOP;
		fileline()->v3error("Expecting ( to begin argument list for define reference `"<<m_defName);
		goto next_tok;
	    }
	}
	case ps_DEFARG: {
	    if (tok==VP_DEFARG) {
		UINFO(4,"   Defarg "<<m_defName<<" arg="<<m_lexp->m_defValue<<endl);
		goto next_tok;  // Next is a , or )
	    } else if (tok==VP_TEXT && yyleng==1 && yytext[0]==',') {
		m_defArgs.push_back(m_lexp->m_defValue);
		m_state = ps_DEFARG;
		m_lexp->setStateDefArg();
		goto next_tok;
	    } else if (tok==VP_TEXT && yyleng==1 && yytext[0]==')') {
		m_defArgs.push_back(m_lexp->m_defValue);
		string out = defineSubst();
		m_lexp->m_parenLevel = 0;
		m_lexp->unputString(out.c_str());
		// Prepare for next action
		m_defArgs.clear();
		m_state = ps_TOP;
		goto next_tok;
	    } else {
		fileline()->v3error("Expecting ) or , to end argument list for define reference. Found: "<<tokenName(tok));
		m_state = ps_TOP;
		goto next_tok;
	    }
	    goto next_tok;
	}
	case ps_INCNAME: {
	    if (tok==VP_STRING) {
		m_state = ps_TOP;
		if (!m_off) {
		    m_lastSym.assign(yytext,yyleng);
		    UINFO(4,"Include "<<m_lastSym<<endl);
		    // Drop leading and trailing quotes.
		    m_lastSym.erase(0,1);
		    m_lastSym.erase(m_lastSym.length()-1,1);
		    include(m_lastSym);
		}
		goto next_tok;
	    }
	    else if (tok==VP_TEXT && yyleng==1 && yytext[0]=='<') {
		// include <filename>
		m_state = ps_INCNAME;  // Still
		m_lexp->setStateIncFilename();
		goto next_tok;
	    }
	    else if (tok==VP_DEFREF) {
		// Expand it, then state will come back here
		break;
	    }
	    else {
		m_state = ps_TOP;
		fileline()->v3error("Expecting include filename. Found: "<<tokenName(tok));
		goto next_tok;
	    }
	}
	case ps_ERRORNAME: {
	    if (tok==VP_STRING) {
		m_state = ps_TOP;
		if (!m_off) {
		    m_lastSym.assign(yytext,yyleng);
		    fileline()->v3error(m_lastSym);
		}
		goto next_tok;
	    }
	    else {
		m_state = ps_TOP;
		fileline()->v3error("Expecting `error string. Found: "<<tokenName(tok));
		goto next_tok;
	    }
	}
	default: fileline()->v3fatalSrc("Bad case\n");
	}
	// Default is to do top level expansion of some tokens
	switch (tok) {
	case VP_INCLUDE:
	    m_state = ps_INCNAME;  m_stateFor = tok;
	    goto next_tok;
	case VP_UNDEF:
	case VP_DEFINE:
	case VP_IFDEF:
	case VP_IFNDEF:
	case VP_ELSIF:
	    m_state = ps_DEFNAME;  m_stateFor = tok;
	    goto next_tok;
	case VP_ELSE:
	    if (m_ifdefStack.empty()) {
		fileline()->v3error("`else with no matching `if\n");
	    } else {
		bool lastEnable = m_ifdefStack.top(); m_ifdefStack.pop();
		bool enable = !lastEnable;
		UINFO(4,"Else "<<(enable?" ON":" OFF")<<endl);
		m_ifdefStack.push(enable);
		if (!lastEnable) parsingOn();
		if (!enable) parsingOff();
	    }
	    goto next_tok;
	case VP_ENDIF:
	    if (m_ifdefStack.empty()) {
		fileline()->v3error("`endif with no matching `if\n");
	    } else {
		bool lastEnable = m_ifdefStack.top(); m_ifdefStack.pop();
		UINFO(4,"Endif "<<endl);
		if (!lastEnable) parsingOn();
	    }
	    goto next_tok;

	case VP_DEFREF: {
	    if (!m_off) {
		string name; name.append(yytext+1,yyleng-1);
		UINFO(4,"DefRef "<<name<<endl);
		if (m_defDepth++ > V3PreProc::DEFINE_RECURSION_LEVEL_MAX) {
		    fileline()->v3error("Recursive `define substitution: `"+name);
		    goto next_tok;
		}
		// Substitute
		if (!defExists(name)) {   // Not found, return original string as-is
		    m_defDepth = 0;
		    UINFO(4,"Defref `"<<name<<" => not_defined"<<endl);
		    return (VP_TEXT);
		}
		else {
		    string params = defParams(name);
		    if (params=="0" || params=="") {  // Found, as simple substitution
			// Pack spaces around the define value, as there must be token boundaries around it.
			// It also makes it more obvious where defines got substituted.
			string out = " "+defValue(name)+" ";
			UINFO(4,"Defref `"<<name<<" => "<<out<<endl);
			m_lexp->unputString(out.c_str());
			goto next_tok;
		    }
		    else {  // Found, with parameters
			UINFO(4,"Defref `"<<name<<" => parameterized"<<endl);
			m_defName = name;
			m_defParams = params;
			m_state = ps_DEFPAREN;  m_stateFor = tok;
			goto next_tok;
		    }
		}
		fileline()->v3fatalSrc("Bad case\n");
	    }
	    else goto next_tok;
	}
	case VP_ERROR: {
	    m_state = ps_ERRORNAME;  m_stateFor = tok;
	    goto next_tok;
	}
	case VP_EOF:
	    if (!m_ifdefStack.empty()) {
		fileline()->v3error("`ifdef not terminated at EOF\n");
	    }
	    return tok;
	case VP_SYMBOL:
	case VP_STRING:
	case VP_PSL:
	case VP_TEXT: {
	    m_defDepth = 0;
	    if (!m_off) return tok;
	    else goto next_tok;
	}
	case VP_WHITE:		// Handled at top of loop
	case VP_COMMENT:	// Handled at top of loop
	case VP_DEFVALUE:	// Handled by m_state=ps_DEFVALUE;
	default:
	    fileline()->v3fatalSrc("Internal error: Unexpected token.\n");
	    break;
	}
	return tok;
    }
}

string V3PreProcImp::getline() {
    // Get a single line from the parse stream.  Buffer unreturned text until the newline.
    if (isEof()) return "";
    char* rtnp;
    while (NULL==(rtnp=strchr(m_lineChars.c_str(),'\n'))) {
	int tok = getToken();
	if (debug()>4) {
	    char buf[100000];
	    strncpy(buf, yytext, yyleng);
	    buf[yyleng] = '\0';
	    for (char* cp=buf; *cp; cp++) if (*cp=='\n') *cp='$';
	    fprintf (stderr,"%d: GETFETC:  %-10s: %s\n",
		     fileline()->lineno(), tokenName(tok), buf);
	}
	if (tok==VP_EOF) {
	    // Add a final newline, in case the user forgot the final \n.
	    m_lineChars.append("\n");
	}
	else if (tok==VP_PSL) {
	    m_lineChars.append(" psl ");
	}
	else {
	    m_lineChars.append(yytext,0,yyleng);
	}
    }

    // Make new string with data up to the newline.
    int len = rtnp-m_lineChars.c_str()+1;
    string theLine(m_lineChars, 0, len);
    m_lineChars = m_lineChars.erase(0,len);	// Remove returned characters
    UINFO(4, fileline()->lineno()<<": GETLINE: "<<theLine.c_str()<<endl);
    return theLine;
}
