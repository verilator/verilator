//*************************************************************************
// DESCRIPTION: Verilator: Error handling
//
// Code available from: http://www.veripool.org/verilator
//
// AUTHORS: Wilson Snyder with Paul Wasson, Duane Gabli
//
//*************************************************************************
//
// Copyright 2003-2012 by Wilson Snyder.  This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
//
// Verilator is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
//*************************************************************************

#include <cstdio>
#include <cstdarg>
#include <cstring>
#include <set>
#include "V3Error.h"
#ifndef _V3ERROR_NO_GLOBAL_
# include "V3Ast.h"
# include "V3Global.h"
# include "V3Stats.h"
# include "V3Config.h"
#endif

//======================================================================
// Statics

int V3Error::s_errCount = 0;
int V3Error::s_warnCount = 0;
int V3Error::s_debugDefault = 0;
int V3Error::s_tellManual = 0;
ostringstream V3Error::s_errorStr;		// Error string being formed
V3ErrorCode V3Error::s_errorCode = V3ErrorCode::EC_FATAL;
bool V3Error::s_errorSuppressed = false;
bool V3Error::s_describedEachWarn[V3ErrorCode::_ENUM_MAX];
bool V3Error::s_describedWarnings = false;
bool V3Error::s_pretendError[V3ErrorCode::_ENUM_MAX];

struct v3errorIniter {
    v3errorIniter() {  V3Error::init(); }
};
v3errorIniter v3errorInit;

//######################################################################
// ErrorCode class functions

V3ErrorCode::V3ErrorCode(const char* msgp) {
    // Return error encoding for given string, or ERROR, which is a bad code
    for (int codei=V3ErrorCode::EC_MIN; codei<V3ErrorCode::_ENUM_MAX; codei++) {
	V3ErrorCode code = (V3ErrorCode)codei;
	if (0==strcasecmp(msgp,code.ascii())) {
	    m_e = code; return;
	}
    }
    m_e = V3ErrorCode::EC_ERROR;
}

//######################################################################
// FileLineSingleton class functions

int FileLineSingleton::nameToNumber(const string& filename) {
    // Convert filenames to a filenameno
    // This lets us assign a nice small identifier for debug messages, but more
    // importantly lets us use a 4 byte int instead of 8 byte pointer in every FileLine.
    map<string,int>::const_iterator iter = m_namemap.find(filename);
    if (VL_LIKELY(iter != m_namemap.end())) return iter->second;
    int num = m_names.size();
    m_names.push_back(filename);
    m_namemap.insert(make_pair(filename,num));
    return num;
}

//######################################################################
// FileLine class functions

FileLine::FileLine(FileLine::EmptySecret) {
    // Sort of a singleton
    m_lineno=0;
    m_filenameno=singleton().nameToNumber("AstRoot");

    m_warnOn=0;
    for (int codei=V3ErrorCode::EC_MIN; codei<V3ErrorCode::_ENUM_MAX; codei++) {
	V3ErrorCode code = (V3ErrorCode)codei;
	warnOff(code, code.defaultsOff());
    }
}

const string FileLine::filenameLetters() const {
    const int size = 1 + (64 / 4);  // Each letter retires more than 4 bits of a > 64 bit number
    char out[size];
    char* op = out+size-1;
    *--op = '\0';  // We build backwards
    int num = m_filenameno;
    do {
	*--op = 'a'+num%26;
	num /= 26;
    } while (num);
    return op;
}

string FileLine::lineDirectiveStrg(int enterExit) const {
    char numbuf[20]; sprintf(numbuf, "%d", lineno());
    char levelbuf[20]; sprintf(levelbuf, "%d", enterExit);
    return ((string)"`line "+numbuf+" \""+filename()+"\" "+levelbuf+"\n");
}

void FileLine::lineDirective(const char* textp, int& enterExitRef) {
    // Handle `line directive
    // Skip `line
    while (*textp && isspace(*textp)) textp++;
    while (*textp && !isspace(*textp)) textp++;
    while (*textp && (isspace(*textp) || *textp=='"')) textp++;

    // Grab linenumber
    const char *ln = textp;
    while (*textp && !isspace(*textp)) textp++;
    if (isdigit(*ln)) {
	this->lineno(atoi(ln));
    }
    while (*textp && (isspace(*textp) || *textp=='"')) textp++;

    // Grab filename
    const char *fn = textp;
    while (*textp && !(isspace(*textp) || *textp=='"')) textp++;
    if (textp != fn) {
	string strfn = fn;
	strfn = strfn.substr(0, textp-fn);
	this->filename(strfn);
    }

    // Grab level
    while (*textp && (isspace(*textp) || *textp=='"')) textp++;
    if (isdigit(*textp)) enterExitRef = atoi(textp);
    else enterExitRef = 0;

    //printf ("PPLINE %d '%s'\n", s_lineno, s_filename.c_str());
}

FileLine* FileLine::copyOrSameFileLine() {
    // When a fileline is "used" to produce a node, calls this function.
    // Return this, or a copy of this
    // There are often more than one token per line, thus we use the
    // same pointer as long as we're on the same line, file & warn state.
#ifndef _V3ERROR_NO_GLOBAL_
    V3Config::applyIgnores(this);  // Toggle warnings based on global config file
#endif
    static FileLine* lastNewp = NULL;
    if (lastNewp && *lastNewp == *this) {  // Compares lineno, filename, etc
	return lastNewp;
    }
    FileLine* newp = new FileLine(this);
    lastNewp = newp;
    return newp;
}

const string FileLine::filebasename() const {
    string name = filename();
    string::size_type pos;
    if ((pos = name.rfind("/")) != string::npos) {
	name.erase(0,pos+1);
    }
    return name;
}

const string FileLine::filebasenameNoExt() const {
    string name = filebasename();
    string::size_type pos;
    if ((pos = name.find(".")) != string::npos) {
	name = name.substr(0,pos);
    }
    return name;
}

const string FileLine::profileFuncname() const {
    // Return string that is OK as a function name - for profiling
    string name  = filebasenameNoExt();
    string::size_type pos;
    while ((pos = name.find_first_not_of("abcdefghijlkmnopqrstuvwxyzABCDEFGHIJLKMNOPQRSTUVWXYZ0123456789_"))
	   != string::npos) {
	name.replace(pos, 1, "_");
    }
    name += "__l"+cvtToStr(lineno());
    return name;
}

string FileLine::ascii() const {
    return filename()+":"+cvtToStr(lineno());
}
ostream& operator<<(ostream& os, FileLine* fileline) {
    os <<fileline->ascii()<<": "<<hex;
    return(os);
}

bool FileLine::warnOff(const string& msg, bool flag) {
    V3ErrorCode code (msg.c_str());
    if (code < V3ErrorCode::EC_FIRST_WARN) {
	return false;
    } else if (v3Global.opt.lintOnly()   // Lint mode is allowed to suppress some errors
	       && code < V3ErrorCode::EC_MIN) {
	return false;
    } else {
	warnOff(code, flag);
	return true;
    }
}

void FileLine::warnLintOff(bool flag) {
    for (int codei=V3ErrorCode::EC_MIN; codei<V3ErrorCode::_ENUM_MAX; codei++) {
	V3ErrorCode code = (V3ErrorCode)codei;
	if (code.lintError()) warnOff(code, flag);
    }
}

void FileLine::warnStyleOff(bool flag) {
    for (int codei=V3ErrorCode::EC_MIN; codei<V3ErrorCode::_ENUM_MAX; codei++) {
	V3ErrorCode code = (V3ErrorCode)codei;
	if (code.styleError()) warnOff(code, flag);
    }
}

bool FileLine::warnIsOff(V3ErrorCode code) const {
    if (!m_warnOn.test(code)) return true;
    // UNOPTFLAT implies UNOPT
    if (code==V3ErrorCode::UNOPT && !m_warnOn.test(V3ErrorCode::UNOPTFLAT)) return true;
    if ((code.lintError() || code.styleError()) && !m_warnOn.test(V3ErrorCode::I_LINT)) return true;
    return false;
}

void FileLine::modifyStateInherit(const FileLine* fromp) {
    // Any warnings that are off in "from", become off in "this".
    for (int codei=V3ErrorCode::EC_MIN; codei<V3ErrorCode::_ENUM_MAX; codei++) {
	V3ErrorCode code = (V3ErrorCode)codei;
	if (fromp->warnIsOff(code)) {
	    this->warnOff(code, true);
	}
    }
}

void FileLine::v3errorEnd(ostringstream& str) {
    if (this && m_lineno) {
	ostringstream nsstr;
	nsstr<<this<<str.str();
	if (warnIsOff(V3Error::errorCode())) V3Error::suppressThisWarning();
	V3Error::v3errorEnd(nsstr);
    } else {
	V3Error::v3errorEnd(str);
    }
}

#ifdef VL_LEAK_CHECKS
typedef set<FileLine*> FileLineCheckSet;
FileLineCheckSet fileLineLeakChecks;

void* FileLine::operator new(size_t size) {
    FileLine* objp = static_cast<FileLine*>(::operator new(size));
    fileLineLeakChecks.insert(objp);
    return objp;
}

void FileLine::operator delete(void* objp, size_t size) {
    if (!objp) return;
    FileLine* flp = static_cast<FileLine*>(objp);
    FileLineCheckSet::iterator it = fileLineLeakChecks.find(flp);
    if (it != fileLineLeakChecks.end()) {
	fileLineLeakChecks.erase(it);
    } else {
	flp->v3fatalSrc("Deleting FileLine object that was never tracked\n");
    }
    ::operator delete(objp);
}
#endif

void FileLine::deleteAllRemaining() {
#ifdef VL_LEAK_CHECKS
    // FileLines are allocated, but never nicely freed, as it's much faster
    // that way.  Unfortunately this makes our leak checking a big mess, so
    // only when leak checking we'll track them all and cleanup.
    while (1) {
	FileLineCheckSet::iterator it=fileLineLeakChecks.begin();
	if (it==fileLineLeakChecks.end()) break;
	delete *it;
	// Operator delete will remove the iterated object from the list.
	// Eventually the list will be empty and terminate the loop.
    }
    fileLineLeakChecks.clear();
    FileLineSingleton::clear();
#endif
}

//######################################################################
// V3Error class functions

void V3Error::init() {
    for (int i=0; i<V3ErrorCode::_ENUM_MAX; i++) {
	s_describedEachWarn[i] = false;
	s_pretendError[i] = V3ErrorCode(i).pretendError();
    }

    if (string(V3ErrorCode(V3ErrorCode::_ENUM_MAX).ascii()) != " MAX") {
	v3fatalSrc("Enum table in V3ErrorCode::EC_ascii() is munged");
    }
}

string V3Error::lineStr (const char* filename, int lineno) {
    ostringstream out;
    const char* fnslashp = strrchr (filename, '/');
    if (fnslashp) filename = fnslashp+1;
    out<<filename<<":"<<dec<<lineno<<":";
    const char* spaces = "                    ";
    size_t numsp = out.str().length(); if (numsp>20) numsp = 20;
    out<<(spaces + numsp);
    return out.str();
}

void V3Error::incWarnings() {
    s_warnCount++;
    // We don't exit on a lot of warnings.
}

void V3Error::incErrors() {
    s_errCount++;
    if (errorCount() == v3Global.opt.errorLimit()) {  // Not >= as would otherwise recurse
	v3fatal ("Exiting due to too many errors encountered; --error-limit="<<errorCount()<<endl);
    }
}

void V3Error::abortIfErrors() {
    if (errorCount()) {
	abortIfWarnings();
    }
}

void V3Error::abortIfWarnings() {
    bool exwarn = v3Global.opt.warnFatal() && warnCount();
    if (errorCount() && exwarn) {
	v3fatal ("Exiting due to "<<dec<<errorCount()<<" error(s), "<<warnCount()<<" warning(s)\n");
    } else if (errorCount()) {
	v3fatal ("Exiting due to "<<dec<<errorCount()<<" error(s)\n");
    } else if (exwarn) {
	v3fatal ("Exiting due to "<<dec<<warnCount()<<" warning(s)\n");
    }
}

bool V3Error::isError(V3ErrorCode code, bool supp) {
    if (supp) return false;
    else if (code==V3ErrorCode::EC_INFO) return false;
    else if (code==V3ErrorCode::EC_FATAL) return true;
    else if (code==V3ErrorCode::EC_FATALSRC) return true;
    else if (code==V3ErrorCode::EC_ERROR) return true;
    else if (code<V3ErrorCode::EC_FIRST_WARN
	     || s_pretendError[code]) return true;
    else return false;
}

string V3Error::msgPrefix(V3ErrorCode code, bool supp) {
    if (supp) return "-arning-suppressed: ";
    else if (code==V3ErrorCode::EC_INFO) return "-Info: ";
    else if (code==V3ErrorCode::EC_FATAL) return "%Error: ";
    else if (code==V3ErrorCode::EC_FATALSRC) return "%Error: Internal Error: ";
    else if (code==V3ErrorCode::EC_ERROR) return "%Error: ";
    else if (isError(code, supp)) return "%Error-"+(string)code.ascii()+": ";
    else return "%Warning-"+(string)code.ascii()+": ";
}

//======================================================================
// Abort/exit

void V3Error::vlAbort () {
    if (V3Error::debugDefault()) {
	cerr<<msgPrefix()<<"Aborting since under --debug"<<endl;
	abort();
    } else {
	exit(10);
    }
}

//======================================================================
// Global Functions

string V3Error::v3sform (const char* format, ...) {
    static char msg[1000] = "";

    va_list ap;
    va_start(ap,format);
    vsprintf(msg,format,ap);
    va_end(ap);

    string out = msg;
    return out;
}

void V3Error::suppressThisWarning() {
    if (s_errorCode>=V3ErrorCode::EC_MIN) {
	V3Stats::addStatSum(string("Warnings, Suppressed ")+s_errorCode.ascii(), 1);
	s_errorSuppressed = true;
    }
}

void V3Error::v3errorEnd (ostringstream& sstr) {
#if defined(__COVERITY__) || defined(__cppcheck__)
    if (s_errorCode==V3ErrorCode::EC_FATAL) __coverity_panic__(x);
#endif
    if (!s_errorSuppressed
	// On debug, show only non default-off warning to prevent pages of warnings
	|| (debug() && !s_errorCode.defaultsOff())) {
	cerr<<msgPrefix()<<sstr.str();
	if (sstr.str()[sstr.str().length()-1] != '\n') {
	    cerr<<endl;
	}
	if (!s_errorSuppressed && s_errorCode!=V3ErrorCode::EC_INFO) {
	    if (!s_describedEachWarn[s_errorCode]
		&& !s_pretendError[s_errorCode]) {
		s_describedEachWarn[s_errorCode] = true;
		if (s_errorCode>=V3ErrorCode::EC_FIRST_WARN && !s_describedWarnings) {
		    cerr<<msgPrefix()<<"Use \"/* verilator lint_off "<<s_errorCode.ascii()
			<<" */\" and lint_on around source to disable this message."<<endl;
		    s_describedWarnings = true;
		}
		if (s_errorCode.dangerous()) {
		    cerr<<msgPrefix()<<"*** See the manual before disabling this,"<<endl;
		    cerr<<msgPrefix()<<"else you may end up with different sim results."<<endl;
		}
	    }
	    // If first warning is not the user's fault (internal/unsupported) then give the website
	    // Not later warnings, as a internal may be caused by an earlier problem
	    if (s_tellManual == 0) {
		if (s_errorCode.mentionManual()
		    || sstr.str().find("Unsupported") != string::npos) {
		    s_tellManual = 1;
		} else {
		    s_tellManual = 2;
		}
	    }
	    if (isError(s_errorCode, s_errorSuppressed)) incErrors();
	    else incWarnings();
	    if (s_errorCode==V3ErrorCode::EC_FATAL
		|| s_errorCode==V3ErrorCode::EC_FATALSRC) {
		static bool inFatal = false;
		if (!inFatal) {
		    inFatal = true;
		    if (s_tellManual==1) {
			cerr<<msgPrefix()<<"See the manual and http://www.veripool.org/verilator for more assistance."<<endl;
			s_tellManual = 2;
		    }
#ifndef _V3ERROR_NO_GLOBAL_
		    if (debug()) {
			v3Global.rootp()->dumpTreeFile(v3Global.debugFilename("final.tree",99));
			V3Stats::statsFinalAll(v3Global.rootp());
			V3Stats::statsReport();
		    }
#endif
		}

		vlAbort();
	    }
	}
    }
}
