%option noyywrap align interactive
%option stack
%option noc++
%option prefix="V3PreLex"
%{
/**************************************************************************
 * DESCRIPTION: Verilator: Flex verilog preprocessor
 *
 * Code available from: http://www.veripool.org/verilator
 *
 **************************************************************************
 *
 * Copyright 2003-2015 by Wilson Snyder.  This program is free software;
 * you can redistribute it and/or modify it under the terms of either the
 * GNU Lesser General Public License Version 3 or the Perl Artistic License
 * Version 2.0.
 *
 * Verilator is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 **************************************************************************
 * Do not use Flex in C++ mode.  It has bugs with yyunput() which result in
 * lost characters.
 **************************************************************************/

#include "V3PreProc.h"
#include "V3PreLex.h"

V3PreLex* V3PreLex::s_currentLexp = NULL;	// Current lexing point

#define LEXP V3PreLex::s_currentLexp

#define YY_INPUT(buf,result,max_size) \
    result = LEXP->inputToLex(buf,max_size);

// Accessors, because flex keeps changing the type of yyleng
char* yyourtext() { return yytext; }
size_t yyourleng() { return yyleng; }
void yyourtext(const char* textp, size_t size) { yytext=(char*)textp; yyleng=size; }

// Prevent conflicts from perl version
static void linenoInc()  {LEXP->linenoInc();}
static bool pedantic() { return LEXP->m_pedantic; }
static void yyerror(char* msg) { LEXP->curFilelinep()->v3error(msg); }
static void yyerrorf(const char* msg) { LEXP->curFilelinep()->v3error(msg); }
static void appendDefValue(const char* t, size_t l) { LEXP->appendDefValue(t,l); }

/**********************************************************************/
%}

%x CMTONEM
%x CMTBEGM
%x CMTMODE
%x STRMODE
%x DEFFPAR
%x DEFFORM
%x DEFVAL
%x DEFCMT
%x STRIFY
%x ARGMODE
%x INCMODE
%x PRTMODE

/* drop: Drop Ctrl-Z - can't pass thru or may EOF the output too soon */

ws		[ \t\f\r]
wsn		[ \t\f]
crnl		[\r]*[\n]
quote		[\"]
tickquote	[`][\"]
backslash	[\\]
/* Where we use symb/symbdef, we must also look for a `` join */
/* Note in the preprocessor \ESCaped is *not* always special; mantis1537/bug441 */
symb		([a-zA-Z_][a-zA-Z0-9_$]*|\\[^ \t\f\r\n]+)
symbdef		([a-zA-Z_][a-zA-Z0-9_$]*|\\[^ \t\f\r\n`]+)
word		[a-zA-Z0-9_]+
drop		[\032]

	/**************************************************************/
%%

<INITIAL,STRIFY>^{ws}*"`line"{ws}+.*{crnl}	{ LEXP->lineDirective(yytext);
						  return(VP_LINE); }

	/* Special directives we recognize */
<INITIAL>"`define"	{ return(VP_DEFINE); }
<INITIAL>"`else"	{ return(VP_ELSE); }
<INITIAL>"`elsif"	{ return(VP_ELSIF); }
<INITIAL>"`endif"	{ return(VP_ENDIF); }
<INITIAL>"`ifdef"	{ return(VP_IFDEF); }
<INITIAL>"`ifndef"	{ return(VP_IFNDEF); }
<INITIAL>"`include"	{ return(VP_INCLUDE); }
<INITIAL>"`undef"	{ return(VP_UNDEF); }
<INITIAL>"`undefineall"	{ return(VP_UNDEFINEALL); }
<INITIAL>"`error"	{ if (!pedantic()) return (VP_ERROR); else return(VP_DEFREF); }
<INITIAL,STRIFY>"`__FILE__"	{ static string rtnfile;
			  rtnfile = '"'; rtnfile += LEXP->curFilelinep()->filename();
			  rtnfile += '"'; yytext=(char*)rtnfile.c_str(); yyleng = rtnfile.length();
			  return (VP_STRING); }
<INITIAL,STRIFY>"`__LINE__"	{ static char buf[10];
			  sprintf(buf, "%d",LEXP->curFilelinep()->lineno());
	                  yytext = buf; yyleng = strlen(yytext);
			  return (VP_TEXT); }

	/* Pass-through strings */
<INITIAL>{quote}	{ yy_push_state(STRMODE); yymore(); }
<STRMODE><<EOF>>	{ linenoInc(); yyerrorf("EOF in unterminated string"); yyleng=0; yyterminate(); }
<STRMODE>{crnl}		{ linenoInc(); yyerrorf("Unterminated string"); BEGIN(INITIAL); }
<STRMODE>{word}		{ yymore(); }
<STRMODE>[^\"\\]	{ yymore(); }
<STRMODE>{backslash}{crnl}	{ linenoInc(); yymore(); }
<STRMODE>{backslash}.	{ yymore(); }
<STRMODE>{quote} 	{ yy_pop_state();
			  if (LEXP->m_parenLevel || LEXP->m_defQuote) { LEXP->m_defQuote=false; appendDefValue(yytext,yyleng); yyleng=0; }
			  else return (VP_STRING); }

	/* Stringification */
<INITIAL>{tickquote}	{ yy_push_state(STRIFY); return VP_STRIFY; }
<STRIFY><<EOF>>		{ linenoInc(); yyerrorf("EOF in unterminated '\""); yyleng=0; yyterminate(); }
<STRIFY>"`\\`\""	{ return VP_BACKQUOTE; }
<STRIFY>{quote}		{ yy_push_state(STRMODE); yymore(); }
<STRIFY>{tickquote}	{ yy_pop_state(); return VP_STRIFY; }
<STRIFY>{symbdef}	{ return (VP_SYMBOL); }
<STRIFY>{symbdef}``	{ yyleng-=2; return (VP_SYMBOL_JOIN); }
<STRIFY>"`"{symbdef}	{ return (VP_DEFREF); }
<STRIFY>"`"{symbdef}``	{ yyleng-=2; return (VP_DEFREF_JOIN); }
<STRIFY>{crnl}		{ linenoInc(); yytext=(char*)"\n"; yyleng=1; return(VP_WHITE); }
<STRIFY>{wsn}+		{ return (VP_WHITE); }
<STRIFY>{drop}		{ }
<STRIFY>[\r]		{ }
<STRIFY>.		{ return (VP_TEXT); }

	/* Protected blocks */
<INITIAL>"`protected"	{ yy_push_state(PRTMODE); yymore(); }
<PRTMODE><<EOF>>	{ linenoInc(); yyerrorf("EOF in `protected"); yyleng=0; yyterminate(); }
<PRTMODE>{crnl}		{ linenoInc(); return VP_TEXT; }
<PRTMODE>.	 	{ yymore(); }
<PRTMODE>"`endprotected" { yy_pop_state(); return VP_TEXT; }

	/* Pass-through include <> filenames */
<INCMODE><<EOF>>	{ linenoInc(); yyerrorf("EOF in unterminated include filename"); yyleng=0; yyterminate(); }
<INCMODE>{crnl}		{ linenoInc(); yyerrorf("Unterminated include filename"); BEGIN(INITIAL); }
<INCMODE>[^\>\\]	{ yymore(); }
<INCMODE>{backslash}.	{ yymore(); }
<INCMODE>[\>]	 	{ yy_pop_state(); return VP_STRING; }

	/* Reading definition formal parenthesis (or not) to begin formal arguments */
	/* Note '(' must IMMEDIATELY follow definition name */
<DEFFPAR>[(]		{ appendDefValue("(",1); LEXP->m_formalLevel=1; BEGIN(DEFFORM); }
<DEFFPAR>{crnl}		{ yy_pop_state(); unput('\n'); yyleng=0; return VP_DEFFORM; } /* DEFVAL will later grab the return */
<DEFFPAR><<EOF>>	{ yy_pop_state(); return VP_DEFFORM; }  /* empty formals */
<DEFFPAR>.		{ yy_pop_state(); unput(yytext[yyleng-1]); yyleng=0; return VP_DEFFORM; }  /* empty formals */

	/* Reading definition formals (declaration of a define) */
<DEFFORM>[(]		{ appendDefValue(yytext,yyleng); yyleng=0; ++LEXP->m_formalLevel; }
<DEFFORM>[)]		{ appendDefValue(yytext,yyleng); yyleng=0; if ((--LEXP->m_formalLevel)==0) { yy_pop_state(); return VP_DEFFORM; } }
<DEFFORM>"/*"		{ yy_push_state(CMTMODE); yymore(); }
<DEFFORM>"//"[^\n\r]*	{ return (VP_COMMENT);}
<DEFFORM>{drop}		{ }
<DEFFORM><<EOF>>	{ linenoInc(); yy_pop_state(); yyerrorf("Unterminated ( in define formal arguments."); yyleng=0; return VP_DEFFORM; }
<DEFFORM>{crnl}		{ linenoInc(); appendDefValue((char*)"\n",1); } /* Include return so can maintain output line count */
<DEFFORM>[\\]{crnl}	{ linenoInc(); appendDefValue((char*)"\\\n",2); } /* Include return so can maintain output line count */
<DEFFORM>{quote}	{ LEXP->m_defQuote=true; yy_push_state(STRMODE); yymore(); }  /* Legal only in default values */
<DEFFORM>"`\\`\""	{ appendDefValue(yytext,yyleng); }  /* Maybe illegal, otherwise in default value */
<DEFFORM>{tickquote}	{ appendDefValue(yytext,yyleng); }  /* Maybe illegal, otherwise in default value */
<DEFFORM>[{\[]		{ LEXP->m_formalLevel++; appendDefValue(yytext,yyleng); }
<DEFFORM>[}\]]		{ LEXP->m_formalLevel--; appendDefValue(yytext,yyleng); }
<DEFFORM>[^\/\*\n\r\\(){}\[\]\"]+	|
<DEFFORM>[\\][^\n\r]	|
<DEFFORM>.		{ appendDefValue(yytext,yyleng); }

	/* Reading definition value (declaration of a define's text) */
<DEFVAL>"/*"		{ LEXP->m_defCmtSlash=false; yy_push_state(DEFCMT); yymore(); }  /* Special comment parser */
<DEFVAL>"//"[^\n\r]*[\\]{crnl}	{ linenoInc(); appendDefValue((char*)"\n",1); }  /* Spec says // not part of define value */
<DEFVAL>"//"[^\n\r]*	{ return (VP_COMMENT);}
<DEFVAL>{drop}		{ }
<DEFVAL><<EOF>>		{ linenoInc(); yy_pop_state(); yytext=(char*)"\n"; yyleng=1; return (VP_DEFVALUE); } /* Technically illegal, but people complained */
<DEFVAL>{crnl}		{ linenoInc(); yy_pop_state(); yytext=(char*)"\n"; yyleng=1; return (VP_DEFVALUE); }
<DEFVAL>[\\]{crnl}	{ linenoInc(); appendDefValue((char*)"\\\n",2); } /* Return, AND \ is part of define value */
<DEFVAL>{quote}		{ LEXP->m_defQuote=true; yy_push_state(STRMODE); yymore(); }
<DEFVAL>[^\/\*\n\r\\\"]+	|
<DEFVAL>[\\][^\n\r]	|
<DEFVAL>.		{ appendDefValue(yytext,yyleng); }

	/* Comments inside define values - if embedded get added to define value per spec */
	/* - if no \{crnl} ending then the comment belongs to the next line, as a non-embedded comment */
	/* - if all but (say) 3rd line is missing \ then it's indeterminate */
<DEFCMT>"*/"		{ yy_pop_state(); appendDefValue(yytext,yyleng); }
<DEFCMT>[\\]{crnl}	{ linenoInc(); LEXP->m_defCmtSlash=true;
	 		  appendDefValue(yytext,yyleng-2); appendDefValue((char*)"\n",1); }  /* Return but not \ */
<DEFCMT>{crnl}		{ linenoInc(); yymore(); if (LEXP->m_defCmtSlash) yyerrorf("One line of /* ... */ is missing \\ before newline");
			  BEGIN(CMTMODE); }
<DEFCMT>{word}		{ yymore(); }
<DEFCMT>.		{ yymore(); }
<DEFCMT><<EOF>>		{ yyerrorf("EOF in '/* ... */' block comment\n"); yyleng=0; yyterminate(); }

	/* Define arguments (use of a define) */
<ARGMODE>"/*"		{ yy_push_state(CMTMODE); yymore(); }
<ARGMODE>"//"[^\n\r]*	{ return (VP_COMMENT);}
<ARGMODE>{drop}		{ }
<ARGMODE><<EOF>>	{ yyerrorf("EOF in define argument list\n"); yyleng = 0; yyterminate(); }
<ARGMODE>{crnl}		{ linenoInc(); yytext=(char*)"\n"; yyleng=1; return(VP_WHITE); }
<ARGMODE>{quote}	{ yy_push_state(STRMODE); yymore(); }
<ARGMODE>"`\\`\""	{ appendDefValue(yytext,yyleng); }  /* Literal text */
<ARGMODE>{tickquote}	{ return(VP_STRIFY); }
<ARGMODE>[{\[]		{ LEXP->m_parenLevel++; appendDefValue(yytext,yyleng); }
<ARGMODE>[}\]]		{ LEXP->m_parenLevel--; appendDefValue(yytext,yyleng); }
<ARGMODE>[(]		{ LEXP->m_parenLevel++;
			  // Note paren level 0 means before "(" of starting args
			  // Level 1 means "," between arguments
			  // Level 2+ means one argument's internal ()
			  if (LEXP->m_parenLevel>1) {
			      appendDefValue(yytext,yyleng);
			  } else {
			      return (VP_TEXT);
			}}
<ARGMODE>[)]		{ LEXP->m_parenLevel--;
			  if (LEXP->m_parenLevel>0) {
			      appendDefValue(yytext,yyleng);
			  } else {
			      yy_pop_state(); return (VP_DEFARG);
			}}
<ARGMODE>[,]		{ if (LEXP->m_parenLevel>1) {
			      appendDefValue(yytext,yyleng);
			  } else {
			      yy_pop_state(); return (VP_DEFARG);
			}}
<ARGMODE>"`"{symbdef}	{ appendDefValue(yytext,yyleng); }  /* defref in defref - outer macro expands first */
<ARGMODE>"`"{symbdef}`` { appendDefValue(yytext,yyleng); }  /* defref in defref - outer macro expands first */
<ARGMODE>[^\/\*\n\r\\(,){}\[\]\"`]+	|
<ARGMODE>.		{ appendDefValue(yytext,yyleng); }

	/* One line comments. */
<INITIAL>"//"{ws}*{crnl} { linenoInc(); yytext=(char*)"\n"; yyleng=1; return (VP_WHITE); }
<INITIAL>"//" 		{ yy_push_state(CMTONEM); yymore(); }
<CMTONEM>[^\n\r]* 	{ yy_pop_state(); return (VP_COMMENT); }

	/* C-style comments. */
	/**** See also DEFCMT */
	/* We distinguish between the start of a comment, and later, to look for prefix comments (deprecated) */
<INITIAL>"/*"		{ yy_push_state(CMTMODE); yymore(); }
<CMTBEGM>{ws}+		{ yymore(); }
<CMTBEGM,CMTMODE>"*/"		{ yy_pop_state(); return(VP_COMMENT); }
<CMTBEGM,CMTMODE>{crnl}		{ linenoInc(); yymore(); }
<CMTBEGM,CMTMODE><<EOF>>	{ yyerrorf("EOF in '/* ... */' block comment\n"); yyleng=0; yyterminate(); }
<CMTMODE>{word}			{ yymore(); }
<CMTBEGM>.			{ BEGIN CMTMODE; yymore(); }	/* beginning in comment */
<CMTMODE>.			{ yymore(); }

	/* Define calls */
	/* symbdef prevents normal lex rules from making `\`"foo a symbol {`"foo} instead of a BACKQUOTE */
<INITIAL>"`"{symbdef}	{ return (VP_DEFREF); }
<INITIAL>"`"{symbdef}`` { yyleng-=2; return (VP_DEFREF_JOIN); }

	/* Generics */
<INITIAL>{crnl}		{ linenoInc(); yytext=(char*)"\n"; yyleng=1; return(VP_WHITE); }
<INITIAL><<EOF>>	{ yyterminate(); }  /* A "normal" EOF */
<INITIAL>{symb} 	{ return (VP_SYMBOL); }
<INITIAL>{symb}``	{ yyleng-=2; return (VP_SYMBOL_JOIN); }
<INITIAL>{wsn}+		{ return (VP_WHITE); }
<INITIAL>{drop}		{ }
<INITIAL>[\r]		{ }
<INITIAL>.		{ return (VP_TEXT); }
%%

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

void V3PreLex::pushStateIncFilename() {
    // Enter include <> filename state
    yy_push_state(INCMODE);
    yymore();
}

void V3PreLex::debug(int level) { yy_flex_debug=level; }
int V3PreLex::debug() { return yy_flex_debug; }

int V3PreLex::lex() {
    V3PreLex::s_currentLexp = this;  // Tell parser where to get/put data
    m_tokFilelinep = curFilelinep();  // Remember token start location, may be updated by the lexer later
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
    if (debug()>=10) { cout<<"-  pp:inputToLex ITL s="<<max_size<<" bs="<<streamp->m_buffers.size()<<endl;  dumpStack(); }
    // For testing, use really small chunks
    //if (max_size > 13) max_size=13;
  again:
    size_t got = 0;
    // Get from this stream
    while (got < max_size	// Haven't got enough
	   && !streamp->m_buffers.empty()) {	// And something buffered
	string front = curStreamp()->m_buffers.front(); streamp->m_buffers.pop_front();
	size_t len = front.length();
	if (len > (max_size-got)) {  // Front string too big
	    len = (max_size-got);
	    string remainder = front.substr(len);
	    front = front.substr(0, len);
	    streamp->m_buffers.push_front(remainder);  // Put back remainder for next time
	}
	strncpy(buf+got, front.c_str(), len);
	got += len;
    }
    if (!got) { // end of stream; try "above" file
	bool again=false;
	string forceOut = endOfStream(again/*ref*/);
	streamp = curStreamp();  // May have been updated
	if (forceOut != "") {
	    if (forceOut.length() > max_size) {
		yyerrorf("Output buffer too small for a `line");
	    } else {
		got = forceOut.length();
		strncpy(buf, forceOut.c_str(), got);
	    }
	} else {
	    if (streamp->m_eof) {
		if (yy_flex_debug) cout<<"-  EOF\n";
	    }
	    got = 0;  // 0=EOF/EOS - although got was already 0.
	    if (again) goto again;
	}
    }
    if (debug()>=10) { cout<<"-  pp::inputToLex  got="<<got<<" '"<<string(buf,got)<<"'"<<endl; }
    return got;
}

string V3PreLex::endOfStream(bool& againr) {
    // Switch to file or next unputString
    againr = false;
    if (yy_flex_debug) cout<<"-EOS state="<<curStreamp()->m_termState<<" at "<<curFilelinep()<<endl;
    if (curStreamp()->m_eof) return "";   // Don't delete the final "EOF" stream
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
    }
    else if (curStreamp()->m_termState == 1) {
	// Now the EOF - can't be sent with other characters
	curStreamp()->m_termState = 2;
	return "";  // End of file
    }
    else if (curStreamp()->m_termState == 2) {
	// Now ending `line
	curStreamp()->m_termState = 3;
	return curFilelinep()->lineDirectiveStrg(2);  // Exit old file
    }
    else {
	// Final shutdown phase for a stream, we can finally change the
	// current fileline to the new stream
	curStreamp()->m_termState = 0;
	FileLine* filelinep = curFilelinep();
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
	    return curFilelinep()->lineDirectiveStrg(0);  // Reenter resumed file
	}
    }
}

void V3PreLex::initFirstBuffer(FileLine* filelinep) {
    // Called from constructor to make first buffer
    // yy_create_buffer also sets yy_fill_buffer=1 so reads from YY_INPUT
    VPreStream* streamp = new VPreStream(filelinep, this);
    streamp->m_eof = true;
    m_streampStack.push(streamp);
    //
    m_bufferState = yy_create_buffer(NULL, YY_BUF_SIZE);
    yy_switch_to_buffer(m_bufferState);
    yyrestart(NULL);
}

void V3PreLex::scanNewFile(FileLine* filelinep) {
    // Called on new open file.  scanBytesBack will be called next.
    if (streamDepth() > V3PreProc::DEFINE_RECURSION_LEVEL_MAX) {
	// The recursive `include in VPreProcImp should trigger first
	yyerrorf("Recursive `define or other nested inclusion");
	curStreamp()->m_eof = true;  // Fake it to stop recursion
    } else {
	VPreStream* streamp = new VPreStream(filelinep, this);
	m_tokFilelinep = curFilelinep();
	streamp->m_file = true;
	scanSwitchStream(streamp);
    }
}

void V3PreLex::scanBytes(const string& str) {
    // Note buffers also appended in ::scanBytesBack
    // Not "m_buffers.push_front(string(strp,len))" as we need a `define
    // to take effect immediately, in the middle of the current buffer
    // Also we don't use scan_bytes that would set yy_fill_buffer
    // which would force Flex to bypass our YY_INPUT routine.
    if (streamDepth() > V3PreProc::DEFINE_RECURSION_LEVEL_MAX) {
	// More streams if recursive `define with complex insertion
	// More buffers mostly if something internal goes funky
	yyerrorf("Recursive `define or other nested inclusion");
	curStreamp()->m_eof = true;  // Fake it to stop recursion
    } else {
	VPreStream* streamp = new VPreStream(curFilelinep(), this);
	streamp->m_buffers.push_front(str);
	scanSwitchStream(streamp);
    }
}

void V3PreLex::scanSwitchStream(VPreStream* streamp) {
    curStreamp()->m_buffers.push_front(currentUnreadChars());
    m_streampStack.push(streamp);
    yyrestart(NULL);
}

void V3PreLex::scanBytesBack(const string& str) {
    // Initial creation, that will pull from YY_INPUT==inputToLex
    // Note buffers also appended in ::scanBytes
    if (curStreamp()->m_eof) yyerrorf("scanBytesBack without being under scanNewFile");
    curStreamp()->m_buffers.push_back(str);
}

string V3PreLex::currentUnreadChars() {
    // WARNING - Peeking at internals
    ssize_t left = (yy_n_chars - (yy_c_buf_p -currentBuffer()->yy_ch_buf));
    if (left > 0) {  // left may be -1 at EOS
	*(yy_c_buf_p) = (yy_hold_char);
	return string(yy_c_buf_p, left);
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
    curFilelinep()->lineDirective(textp, m_enterExit/*ref*/);
    // Make sure we have a dependency on whatever file was specified
    V3File::addSrcDepend(curFilelinep()->filename());
}

void V3PreLex::dumpSummary() {
    cout<<"-  pp::dumpSummary  curBuf="<<(void*)(currentBuffer());
#ifdef FLEX_DEBUG  // Else peeking at internals may cause portability issues
    ssize_t left = (yy_n_chars
		    - (yy_c_buf_p
		       -currentBuffer()->yy_ch_buf));
    cout<<" left="<<dec<<left;
#endif
    cout<<endl;
}

void V3PreLex::dumpStack() {
    // For debug use
    dumpSummary();
    stack<VPreStream*> tmpstack = LEXP->m_streampStack;
    while (!tmpstack.empty()) {
	VPreStream* streamp = tmpstack.top();
	cout<<"-    bufferStack["<<(void*)(streamp)<<"]: "
	    <<" at="<<streamp->m_curFilelinep
	    <<" nBuf="<<streamp->m_buffers.size()
	    <<" size0="<<(streamp->m_buffers.empty() ? 0 : streamp->m_buffers.front().length())
	    <<(streamp->m_eof?" [EOF]":"")
	    <<(streamp->m_file?" [FILE]":"");
	cout<<endl;
	tmpstack.pop();
    }
}

string V3PreLex::cleanDbgStrg(const string& in) {
    string out = in;
    string::size_type pos;
    while ((pos=out.find("\n")) != string::npos) { out.replace(pos, 1, "\\n"); }
    while ((pos=out.find("\r")) != string::npos) { out.replace(pos, 1, "\\r"); }
    return out;
}

void V3PreLex::unused() {
    if (0) {
	// Prevent unused warnings
	yy_top_state();
	yyerror((char*)"");
    }
}

/*###################################################################
 * Local Variables:
 * mode: C++
 * End:
 */
