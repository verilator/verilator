// -*- C++ -*-
//*************************************************************************
// DESCRIPTION: Verilog::Preproc: Internal implementation of default preprocessor
//
// Code available from: http://www.veripool.org/verilator
//
// Authors: Wilson Snyder
//
//*************************************************************************
//
// Copyright 2000-2010 by Wilson Snyder.  This program is free software;
// you can redistribute it and/or modify it under the terms of either the
// GNU Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"
#include <cstdio>
#include <cstdarg>
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
    bool	m_cmdline;	// Set on command line, don't `undefineall
public:
    V3Define(FileLine* fl, const string& value, const string& params, bool cmdline)
	: m_fileline(fl), m_value(value), m_params(params), m_cmdline(cmdline) {}
    FileLine* fileline() const { return m_fileline; }
    string value() const { return m_value; }
    string params() const { return m_params; }
    bool cmdline() const { return m_cmdline; }
};

//*************************************************************************

class V3DefineRef {
    // One for each pending define substitution
    string	m_name;		// Define last name being defined
    string	m_params;	// Define parameter list for next expansion
    string	m_nextarg;	// String being built for next argument
    int		m_parenLevel;	// Parenthesis counting inside def args (for PARENT not child)

    vector<string> m_args;	// List of define arguments
public:
    string name() const { return m_name; }
    string params() const { return m_params; }
    string nextarg() const { return m_nextarg; }
    void nextarg(const string& value) { m_nextarg = value; }
    int parenLevel() const { return m_parenLevel; }
    void parenLevel(int value) { m_parenLevel = value; }
    vector<string>& args() { return m_args; }
    V3DefineRef(const string& name, const string& params)
	: m_name(name), m_params(params), m_parenLevel(0) {}
    ~V3DefineRef() {}
};

//*************************************************************************
/// Data for parsing on/off

class VPreIfEntry {
    // One for each pending ifdef/ifndef
    bool	m_on;		// Current parse for this ifdef level is "on"
    bool	m_everOn;	// Some if term in elsif tree has been on
public:
    bool on() const { return m_on; }
    bool everOn() const { return m_everOn; }
    VPreIfEntry(bool on, bool everOn)
	: m_on(on), m_everOn(everOn || on) {}  // Note everOn includes new state
    ~VPreIfEntry() {}
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

    enum ProcState { ps_TOP,
		     ps_DEFNAME, ps_DEFFORM, ps_DEFVALUE, ps_DEFPAREN, ps_DEFARG,
		     ps_INCNAME, ps_ERRORNAME };
    ProcState	m_state;	// Current state of parser
    int		m_stateFor;	// Token state is parsing for
    int		m_off;		// If non-zero, ifdef level is turned off, don't dump text
    string	m_lastSym;	// Last symbol name found.
    string	m_formals;	///< Last formals found

    // For getRawToken/ `line insertion
    string	m_lineCmt;	// Line comment(s) to be returned
    bool	m_lineCmtNl;	///< Newline needed before inserting lineCmt
    int		m_lineAdd;	///< Empty lines to return to maintain line count
    bool	m_rawAtBol;	///< Last rawToken left us at beginning of line

    // For defines
    stack<V3DefineRef> m_defRefs; // Pending definine substitution
    stack<VPreIfEntry> m_ifdefStack;	///< Stack of true/false emitting evaluations
    unsigned	m_defDepth;	// How many `defines deep

    // Defines list
    DefinesMap	m_defines;	// Map of defines

    // For getline()
    string	m_lineChars;	// Characters left for next line

    void v3errorEnd(ostringstream& str) {
	fileline()->v3errorEnd(str);
    }

    const char* tokenName(int tok);
    int getRawToken();
    int getToken();
    void debugToken(int tok, const char* cmtp);
    void parseTop();
    void parseUndef();

private:
    // Internal methods
    void eof();
    string defineSubst(V3DefineRef* refp);
    void addLineComment(int enter_exit_level);

    bool defExists(const string& name);
    string defValue(const string& name);
    string defParams(const string& name);
    FileLine* defFileline(const string& name);

    bool commentTokenMatch(string& cmdr, const char* strg);
    string trimWhitespace(const string& strg, bool trailing);
    void unputString(const string& strg, bool first=false);

    void parsingOn() {
	m_off--;
	if (m_off<0) fileline()->v3fatalSrc("Underflow of parsing cmds");
	if (!m_off) addLineComment(0);
    }
    void parsingOff() { m_off++; }

public:
    // METHODS, called from upper level shell
    virtual void openFile(FileLine* fl, V3InFilter* filterp, const string& filename);
    virtual bool isEof() const { return (m_lexp==NULL); }
    virtual string getline();
    virtual void insertUnreadback(const string& text) { m_lineCmt += text; }
    void insertUnreadbackAtBol(const string& text);

    // METHODS, callbacks
    virtual void comment(const string& cmt);		// Comment detected (if keepComments==2)
    virtual void include(const string& filename);	// Request a include file be processed
    virtual void undef (const string& name);
    virtual void undefineall();
    virtual void define (FileLine* fl, const string& name, const string& value,
			 const string& params, bool cmdline);
    virtual string removeDefines(const string& text);	// Remove defines in a text string

    // CONSTRUCTORS
    V3PreProcImp(FileLine* fl) : V3PreProc(fl) {
	m_lexp = NULL;	 // Closed.
	m_state = ps_TOP;
	m_off = 0;
	m_lineChars = "";
	m_lastSym = "";
	m_lineAdd = 0;
	m_lineCmtNl = false;
	m_rawAtBol = true;
	m_defDepth = 0;
    }
    ~V3PreProcImp() {
	if (m_lexp) { delete m_lexp; m_lexp = NULL; }
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
void V3PreProcImp::undefineall() {
    for (DefinesMap::iterator nextit, it = m_defines.begin(); it != m_defines.end(); it=nextit) {
	nextit = it; ++nextit;
	if (!it->second.cmdline()) m_defines.erase(it);
    }
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
void V3PreProcImp::define(FileLine* fl, const string& name, const string& value,
			  const string& params, bool cmdline) {
    UINFO(4,"DEFINE '"<<name<<"' as '"<<value<<"' params '"<<params<<"'"<<endl);
    if (defExists(name)) {
	if (!(defValue(name)==value && defParams(name)==params)) {  // Duplicate defs are OK
	    fl->v3warn(REDEFMACRO,"Redefining existing define: "<<name<<", with different value: "<<value<<" "<<params);
	    defFileline(name)->v3warn(REDEFMACRO,"Previous definition is here, with value: "<<defValue(name)<<" "<<defParams(name));
	}
	undef(name);
    }
    m_defines.insert(make_pair(name, V3Define(fl, value, params, cmdline)));
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
	    //if (commentTokenMatch(cmd/*ref*/, "one_hot")) {
	    //	insertUnreadback ("/*verilator one_hot*/ "+cmd+";");
	    //}
	    //if (commentTokenMatch(cmd/*ref*/, "one_cold")) {
	    //	insertUnreadback ("/*verilator one_cold*/ "+cmd+";");
	    //}
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
    case VP_LINE	: return("LINE");
    case VP_SYMBOL	: return("SYMBOL");
    case VP_STRING	: return("STRING");
    case VP_DEFFORM	: return("DEFFORM");
    case VP_DEFVALUE	: return("DEFVALUE");
    case VP_COMMENT	: return("COMMENT");
    case VP_TEXT	: return("TEXT");
    case VP_WHITE	: return("WHITE");
    case VP_DEFREF	: return("DEFREF");
    case VP_DEFARG	: return("DEFARG");
    case VP_ERROR	: return("ERROR");
    case VP_UNDEFINEALL	: return("UNDEFINEALL");
    case VP_PSL		: return("PSL");
    default: return("?");
    }
}

void V3PreProcImp::unputString(const string& strg, bool first) {
    // We used to just m_lexp->unputString(strg.c_str());
    // However this can lead to "flex scanner push-back overflow"
    // so instead we scan from a temporary buffer, then on EOF return.
    // This is also faster than the old scheme, amazingly.
    if (!first) {  // Else the initial creation
	if (m_lexp->m_bufferStack.empty() || m_lexp->m_bufferStack.top()!=m_lexp->currentBuffer()) {
	    fileline()->v3fatalSrc("bufferStack missing current buffer; will return incorrectly");
	    // Hard to debug lost text as won't know till much later
	}
    }
    m_lexp->scanBytes(strg);
}

string V3PreProcImp::trimWhitespace(const string& strg, bool trailing) {
    // Remove leading whitespace
    string out = strg;
    string::size_type leadspace = 0;
    while (out.length() > leadspace
	   && isspace(out[leadspace])) leadspace++;
    if (leadspace) out.erase(0,leadspace);
    // Remove trailing whitespace
    if (trailing) {
	string::size_type trailspace = 0;
	while (out.length() > trailspace
	       && isspace(out[out.length()-1-trailspace])) trailspace++;
	if (trailspace) out.erase(out.length()-trailspace,trailspace);
    }
    return out;
}

string V3PreProcImp::defineSubst(V3DefineRef* refp) {
    // Substitute out defines in a argumented define reference.
    // We could push the define text back into the lexer, but that's slow
    // and would make recursive definitions and parameter handling nasty.
    //
    // Note we parse the definition parameters and value here.  If a
    // parametrized define is used many, many times, we could cache the
    // parsed result.
    UINFO(4,"defineSubstIn  `"<<refp->name()<<" "<<refp->params()<<endl);
    for (unsigned i=0; i<refp->args().size(); i++) {
	UINFO(4,"defineArg["<<i<<"] = '"<<refp->args()[i]<<"'"<<endl);
    }
    // Grab value
    string value = defValue(refp->name());
    UINFO(4,"defineValue    '"<<value<<"'"<<endl);

    map<string,string> argValueByName;
    {   // Parse argument list into map
	unsigned numArgs=0;
	string argName;
	int paren = 1;  // (), {} and [] can use same counter, as must be matched pair per spec
	string token;
	bool quote = false;
	bool haveDefault = false;
	// Note there's a leading ( and trailing ), so parens==1 is the base parsing level
	const char* cp=refp->params().c_str();
	if (*cp == '(') cp++;
	for (; *cp; cp++) {
	    //UINFO(4,"   Parse  Paren="<<paren<<"  Arg="<<numArgs<<"  token='"<<token<<"'  Parse="<<cp<<endl);
	    if (!quote && paren==1) {
		if (*cp==')' || *cp==',') {
		    string value;
		    if (haveDefault) { value=token; } else { argName=token; }
		    argName = trimWhitespace(argName,true);
		    UINFO(4,"    Got Arg="<<numArgs<<"  argName='"<<argName<<"'  default='"<<value<<"'"<<endl);
		    // Parse it
		    if (argName!="") {
			if (refp->args().size() > numArgs) {
			    // A call `def( a ) must be equivelent to `def(a ), so trimWhitespace
			    // Note other sims don't trim trailing whitespace, so we don't either.
			    string arg = trimWhitespace(refp->args()[numArgs], false);
			    if (arg != "") value = arg;
			} else if (!haveDefault) {
			    fileline()->v3error("Define missing argument '"+argName+"' for: "+refp->name()+"\n");
			    return " `"+refp->name()+" ";
			}
			numArgs++;
		    }
		    argValueByName[argName] = value;
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
		token += cp[0]; // \{any} Put out literal next character
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
	    && !(refp->args().size()==1 && numArgs==0 && trimWhitespace(refp->args()[0],false)=="")) {
	    fileline()->v3error("Define passed too many arguments: "+refp->name()+"\n");
	    return " `"+refp->name()+" ";
	}
    }

    string out = "";
    {   // Parse substitution define using arguments
	string argName;
	string prev;
	bool quote = false;
	// Note we go through the loop once more at the NULL end-of-string
	for (const char* cp=value.c_str(); (*cp) || argName!=""; cp=(*cp?cp+1:cp)) {
	    //cout << "CH "<<*cp<<"  an "<<argName<<"\n";
	    if (!quote) {
		if ( isalpha(*cp) || *cp=='_'
		     || *cp=='$' // Won't replace system functions, since no $ in argValueByName
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

    UINFO(4,"defineSubstOut '"<<out<<"'"<<endl);
    return out;
}

//**********************************************************************
// Parser routines

void V3PreProcImp::openFile(FileLine* fl, V3InFilter* filterp, const string& filename) {
    // Open a new file, possibly overriding the current one which is active.
    if (fl) {
	m_fileline = new FileLine(fl);
    }

    V3File::addSrcDepend(filename);

    string wholefile;
    bool ok = filterp->readWholefile(filename, wholefile/*ref*/);
    if (!ok) {
	fileline()->v3error("File not found: "+filename+"\n");
	return;
    }

    // Filter all DOS CR's en-mass.  This avoids bugs with lexing CRs in the wrong places.
    // This will also strip them from strings, but strings aren't supposed to be multi-line without a "\"
    string wholefilecr;
    size_t wholesize = wholefile.length();
    for (size_t i=0; i<wholesize; i++) {  // Not a c_str(), as we keep '\0's for now.
	if (wholefile[i] != '\r' && wholefile[i] != '\0') wholefilecr += wholefile[i];
    }
    wholefile.resize(0); // free memory

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

    m_lexp = new V3PreLex();
    m_lexp->m_keepComments = keepComments();
    m_lexp->m_pedantic = pedantic();
    m_lexp->m_curFilelinep = new FileLine(filename, 1);
    m_fileline = m_lexp->m_curFilelinep;  // Remember token start location
    addLineComment(1); // Enter

    yy_flex_debug = (debug()>4)?1:0;
    unputString(wholefilecr,true);
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

void V3PreProcImp::addLineComment(int enter_exit_level) {
    if (lineDirectives()) {
	char numbuf[20]; sprintf(numbuf, "%d", m_lexp->m_curFilelinep->lineno());
	char levelbuf[20]; sprintf(levelbuf, "%d", enter_exit_level);
	string cmt = ((string)"`line "+numbuf
		      +" \""+m_lexp->m_curFilelinep->filename()+"\" "
		      +levelbuf+"\n");
	insertUnreadbackAtBol(cmt);
    }
}

void V3PreProcImp::eof() {
    // Perhaps we're completing unputString
    if (m_lexp->m_bufferStack.size()>1) {
	UINFO(4,fileline()<<"EOS\n");
	// Switch to file or next unputString, but not a eof so don't delete lexer
	yy_delete_buffer(m_lexp->currentBuffer());
	m_lexp->m_bufferStack.pop();  // Must work as size>1
	yy_switch_to_buffer(m_lexp->m_bufferStack.top());
    } else {
	// Remove current lexer
	UINFO(4,fileline()<<"EOF!\n");
	addLineComment(2);	// Exit
	// Destructor will call yy_delete_buffer
	delete m_lexp;  m_lexp=NULL;
	// Perhaps there's a parent file including us?
	if (!m_includeStack.empty()) {
	    // Back to parent.
	    m_lexp = m_includeStack.top(); m_includeStack.pop();
	    addLineComment(0);
	    if (m_lexp->m_bufferStack.empty()) fileline()->v3fatalSrc("No include buffer to return to");
	    yy_switch_to_buffer(m_lexp->m_bufferStack.top());  // newest buffer in older lexer
	}
    }
}

int V3PreProcImp::getRawToken() {
    // Get a token from the file, whatever it may be.
    while (1) {
      next_tok:
	if (m_lineAdd) {
	    m_lineAdd--;
	    m_rawAtBol = true;
	    yyourtext("\n",1);
	    if (debug()) debugToken(VP_WHITE, "LNA");
	    return (VP_WHITE);
	}
	if (m_lineCmt!="") {
	    // We have some `line directive or other processed data to return to the user.
	    static string rtncmt;  // Keep the c string till next call
	    rtncmt = m_lineCmt;
	    if (m_lineCmtNl) {
		if (!m_rawAtBol) rtncmt = "\n"+rtncmt;
		m_lineCmtNl = false;
	    }
	    yyourtext(rtncmt.c_str(), rtncmt.length());
	    m_lineCmt = "";
	    if (yyourleng()) m_rawAtBol = (yyourtext()[yyourleng()-1]=='\n');
	    if (m_state==ps_DEFVALUE) {
		V3PreLex::s_currentLexp->appendDefValue(yyourtext(),yyourleng());
		goto next_tok;
	    } else {
		if (debug()) debugToken(VP_TEXT, "LCM");
		return (VP_TEXT);
	    }
	}
	if (isEof()) return (VP_EOF);

	// Snarf next token from the file
	m_fileline = m_lexp->m_curFilelinep;  // Remember token start location
	V3PreLex::s_currentLexp = m_lexp;   // Tell parser where to get/put data
	int tok = yylex();

	if (debug()) debugToken(tok, "RAW");

	// On EOF, try to pop to upper level includes, as needed.
	if (tok==VP_EOF) {
	    eof();
	    goto next_tok;  // Parse parent, or find the EOF.
	}

	if (yyourleng()) m_rawAtBol = (yyourtext()[yyourleng()-1]=='\n');
	return tok;
    }
}

void V3PreProcImp::debugToken(int tok, const char* cmtp) {
    if (debug()>4) {
	string buf = string (yyourtext(), yyourleng());
	string::size_type pos;
	while ((pos=buf.find("\n")) != string::npos) { buf.replace(pos, 1, "\\n"); }
	while ((pos=buf.find("\r")) != string::npos) { buf.replace(pos, 1, "\\r"); }
	fprintf (stderr, "%d: %s %s s%d dr%d:  <%d>%-10s: %s\n",
		 fileline()->lineno(), cmtp, m_off?"of":"on", m_state, (int)m_defRefs.size(),
		 m_lexp->currentStartState(), tokenName(tok), buf.c_str());
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
		    string rtn; rtn.assign(yyourtext(),yyourleng());
		    comment(rtn);
		} else {
		    return (tok);
		}
	    }
	    // We're off or processed the comment specially.  If there are newlines
	    // in it, we also return the newlines as TEXT so that the linenumber
	    // count is maintained for downstream tools
	    for (int len=0; len<yyourleng(); len++) { if (yyourtext()[len]=='\n') m_lineAdd++; }
	    goto next_tok;
	}
	if (tok==VP_LINE) {
	    addLineComment(0);
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
		m_lastSym.assign(yyourtext(),yyourleng());
		if (m_stateFor==VP_IFDEF
		    || m_stateFor==VP_IFNDEF) {
		    bool enable = defExists(m_lastSym);
		    UINFO(4,"Ifdef "<<m_lastSym<<(enable?" ON":" OFF")<<endl);
		    if (m_stateFor==VP_IFNDEF) enable = !enable;
		    m_ifdefStack.push(VPreIfEntry(enable,false));
		    if (!enable) parsingOff();
		}
		else if (m_stateFor==VP_ELSIF) {
		    if (m_ifdefStack.empty()) {
			fileline()->v3error("`elsif with no matching `if\n");
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
		}
		else if (m_stateFor==VP_UNDEF) {
		    if (!m_off) {
			UINFO(4,"Undef "<<m_lastSym<<endl);
			undef(m_lastSym);
		    }
		}
		else if (m_stateFor==VP_DEFINE) {
		    // m_lastSym already set.
		    m_state = ps_DEFFORM;
		    m_lexp->pushStateDefForm();
		}
		else fileline()->v3fatalSrc("Bad case\n");
		goto next_tok;
	    }
	    else if (tok==VP_TEXT) {
		// IE, something like comment between define and symbol
		if (!m_off) return tok;
		else goto next_tok;
	    }
	    else {
		fileline()->v3error("Expecting define name. Found: "<<tokenName(tok));
		goto next_tok;
	    }
	}
	case ps_DEFFORM: {
	    if (tok==VP_DEFFORM) {
		m_formals = m_lexp->m_defValue;
		m_state = ps_DEFVALUE;
		if (debug()) cout<<"DefFormals='"<<m_formals<<"'\n";
		m_lexp->pushStateDefValue();
		goto next_tok;
	    } else if (tok==VP_TEXT) {
		// IE, something like comment in formals
		if (!m_off) return tok;
		else goto next_tok;
	    } else {
		fileline()->v3error("Expecting define formal arguments. Found: "<<tokenName(tok));
		goto next_tok;
	    }
	}
	case ps_DEFVALUE: {
	    static string newlines;
	    newlines = "\n";  // Always start with trailing return
	    if (tok == VP_DEFVALUE) {
		if (debug()) cout<<"DefValue='"<<m_lexp->m_defValue<<"'  formals='"<<m_formals<<"'\n";
		// Add any formals
		string formals = m_formals;
		string value = m_lexp->m_defValue;
		// Remove returns
		// Not removing returns in values has two problems,
		// 1. we need to correct line numbers with `line after each substitution
		// 2. Substituting in " .... " with embedded returns requires \ escape.
		//    This is very difficult in the presence of `".
		for (size_t i=0; i<formals.length(); i++) {
		    if (formals[i] == '\n') {
			formals[i] = ' ';
			newlines += "\n";
		    }
		}
		for (size_t i=0; i<value.length(); i++) {
		    if (value[i] == '\n') {
			value[i] = ' ';
			newlines += "\n";
		    }
		}
		if (!m_off) {
		    // Remove leading and trailing whitespace
		    value = trimWhitespace(value, true);
		    // Define it
		    UINFO(4,"Define "<<m_lastSym<<" "<<formals<<" = '"<<value<<"'"<<endl);
		    define(fileline(), m_lastSym, value, formals, false);
		}
	    } else {
		string msg = string("Bad define text, unexpected ")+tokenName(tok)+"\n";
		fileline()->v3fatalSrc(msg);
	    }
	    m_state = ps_TOP;
	    // DEFVALUE is terminated by a return, but lex can't return both tokens.
	    // Thus, we emit a return here.
	    yyourtext(newlines.c_str(), newlines.length());
	    return(VP_WHITE);
	}
	case ps_DEFPAREN: {
	    if (tok==VP_TEXT && yyourleng()==1 && yyourtext()[0]=='(') {
		m_state = ps_DEFARG;
		goto next_tok;
	    } else {
		m_state = ps_TOP;
		if (m_defRefs.empty()) v3fatalSrc("Shouldn't be in DEFPAREN w/o active defref");
		V3DefineRef* refp = &(m_defRefs.top());
		fileline()->v3error("Expecting ( to begin argument list for define reference `"<<refp->name());
		goto next_tok;
	    }
	}
	case ps_DEFARG: {
	    if (m_defRefs.empty()) v3fatalSrc("Shouldn't be in DEFARG w/o active defref");
	    V3DefineRef* refp = &(m_defRefs.top());
	    refp->nextarg(refp->nextarg()+m_lexp->m_defValue); m_lexp->m_defValue="";
	    UINFO(4,"defarg++ "<<refp->nextarg()<<endl);
	    if (tok==VP_DEFARG && yyourleng()==1 && yyourtext()[0]==',') {
		refp->args().push_back(refp->nextarg());
		m_state = ps_DEFARG;
		m_lexp->pushStateDefArg(1);
		refp->nextarg("");
		goto next_tok;
	    } else if (tok==VP_DEFARG && yyourleng()==1 && yyourtext()[0]==')') {
		refp->args().push_back(refp->nextarg());
		string out = defineSubst(refp);
		// Substitute in and prepare for next action
		// Similar code in non-parenthesized define (Search for END_OF_DEFARG)
		m_defRefs.pop();
		if (m_defRefs.empty()) {
		    unputString(out.c_str());
		    m_state = ps_TOP;
		    m_lexp->m_parenLevel = 0;
		}
		else {  // Finished a defref inside a upper defref
		    // Can't subst now, or
		    // `define a(ign) x,y
		    // foo(`a(ign),`b)  would break because a contains comma
		    refp = &(m_defRefs.top());  // We popped, so new top
		    refp->nextarg(refp->nextarg()+m_lexp->m_defValue+out); m_lexp->m_defValue="";
		    m_lexp->m_parenLevel = refp->parenLevel();
		    m_state = ps_DEFARG;
		}
		goto next_tok;
	    } else if (tok==VP_DEFREF) {
		// Expand it, then state will come back here
		// Value of building argument is data before the lower defref
		// we'll append it when we push the argument.
		break;
	    } else if (tok==VP_SYMBOL || tok==VP_STRING || VP_TEXT || VP_WHITE || VP_PSL) {
		string rtn; rtn.assign(yyourtext(),yyourleng());
		refp->nextarg(refp->nextarg()+rtn);
		goto next_tok;
	    } else {
		fileline()->v3error("Expecting ) or , to end argument list for define reference. Found: "<<tokenName(tok));
		m_state = ps_TOP;
		goto next_tok;
	    }
	}
	case ps_INCNAME: {
	    if (tok==VP_STRING) {
		m_state = ps_TOP;
		m_lastSym.assign(yyourtext(),yyourleng());
		UINFO(4,"Include "<<m_lastSym<<endl);
		// Drop leading and trailing quotes.
		m_lastSym.erase(0,1);
		m_lastSym.erase(m_lastSym.length()-1,1);
		include(m_lastSym);
		goto next_tok;
	    }
	    else if (tok==VP_TEXT && yyourleng()==1 && yyourtext()[0]=='<') {
		// include <filename>
		m_state = ps_INCNAME;  // Still
		m_lexp->pushStateIncFilename();
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
		    m_lastSym.assign(yyourtext(),yyourleng());
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
	    if (!m_off) {
		m_state = ps_INCNAME;  m_stateFor = tok;
	    }
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
		fileline()->v3error("`endif with no matching `if\n");
	    } else {
		VPreIfEntry lastIf = m_ifdefStack.top(); m_ifdefStack.pop();
		if (!lastIf.on()) parsingOn();
		// parsingOn() really only enables parsing if
		// all ifdef's above this want it on
	    }
	    goto next_tok;

	case VP_DEFREF: {
	    if (!m_off) {
		string name; name.append(yyourtext()+1,yyourleng()-1);
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
			string out = defValue(name);
			UINFO(4,"Defref `"<<name<<" => '"<<out<<"'"<<endl);
			// Similar code in parenthesized define (Search for END_OF_DEFARG)
			if (m_defRefs.empty()) {
			    // Just output the substitution
			    unputString(out.c_str());
			} else {
			    // Inside another define.  Can't subst now, or
			    // `define a x,y
			    // foo(`a,`b)  would break because a contains comma
			    V3DefineRef* refp = &(m_defRefs.top());
			    refp->nextarg(refp->nextarg()+m_lexp->m_defValue+out); m_lexp->m_defValue="";
			}
			goto next_tok;
		    }
		    else {  // Found, with parameters
			UINFO(4,"Defref `"<<name<<" => parameterized"<<endl);
			// The CURRENT macro needs the paren saved, it's not a property of the child macro
			if (!m_defRefs.empty()) m_defRefs.top().parenLevel(m_lexp->m_parenLevel);
			m_defRefs.push(V3DefineRef(name, params));
			m_state = ps_DEFPAREN;  m_stateFor = tok;
			m_lexp->pushStateDefArg(0);
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
	case VP_UNDEFINEALL:
	    if (!m_off) {
		UINFO(4,"Undefineall "<<endl);
		undefineall();
	    }
	    goto next_tok;
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
	case VP_DEFFORM:	// Handled by m_state=ps_DEFFORM;
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
    const char* rtnp;
    bool gotEof = false;
    while (NULL==(rtnp=strchr(m_lineChars.c_str(),'\n')) && !gotEof) {
	int tok = getToken();
	if (debug()>4) {
	    string buf = string (yyourtext(), yyourleng());
	    string::size_type pos;
	    while ((pos=buf.find("\n")) != string::npos) { buf.replace(pos, 1, "\\n"); }
	    while ((pos=buf.find("\r")) != string::npos) { buf.replace(pos, 1, "\\r"); }
	    fprintf (stderr,"%d: GETFETC:  %-10s: %s\n",
		     fileline()->lineno(), tokenName(tok), buf.c_str());
	}
	if (tok==VP_EOF) {
	    // Add a final newline, if the user forgot the final \n.
	    // Note tok==VP_EOF isn't always seen by us, as isEof() may be set earlier
	    if (m_lineChars != "" && m_lineChars[m_lineChars.length()-1] != '\n') {
		m_lineChars.append("\n");
	    }
	    gotEof = true;
	}
	else if (tok==VP_PSL) {
	    m_lineChars.append(" psl ");
	}
	else {
	    m_lineChars.append(yyourtext(),0,yyourleng());
	}
    }

    // Make new string with data up to the newline.
    int len = rtnp-m_lineChars.c_str()+1;
    string theLine(m_lineChars, 0, len);
    m_lineChars = m_lineChars.erase(0,len);	// Remove returned characters
    UINFO(4, fileline()->lineno()<<": GETLINE: "<<theLine.c_str()<<endl);
    return theLine;
}
