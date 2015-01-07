// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Error handling
//
// Code available from: http://www.veripool.org/verilator
//
//*************************************************************************
//
// Copyright 2003-2015 by Wilson Snyder.  This program is free software; you can
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
#endif

//======================================================================
// Statics

int V3Error::s_errCount = 0;
int V3Error::s_warnCount = 0;
int V3Error::s_debugDefault = 0;
int V3Error::s_errorLimit = V3Error::MAX_ERRORS;
bool V3Error::s_warnFatal = true;
int V3Error::s_tellManual = 0;
ostringstream V3Error::s_errorStr;		// Error string being formed
V3ErrorCode V3Error::s_errorCode = V3ErrorCode::EC_FATAL;
bool V3Error::s_errorSuppressed = false;
bool V3Error::s_describedEachWarn[V3ErrorCode::_ENUM_MAX];
bool V3Error::s_describedWarnings = false;
bool V3Error::s_pretendError[V3ErrorCode::_ENUM_MAX];
V3Error::MessagesSet V3Error::s_messages;
V3Error::ErrorExitCb V3Error::s_errorExitCb = NULL;

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

void V3Error::incErrors() {
    s_errCount++;
    if (errorCount() == errorLimit()) {  // Not >= as would otherwise recurse
	v3fatal ("Exiting due to too many errors encountered; --error-limit="<<errorCount()<<endl);
    }
}

void V3Error::abortIfWarnings() {
    bool exwarn = warnFatal() && warnCount();
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

string V3Error::msgPrefix() {
    V3ErrorCode code=s_errorCode;
    bool supp=s_errorSuppressed;
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

void V3Error::suppressThisWarning() {
    if (s_errorCode>=V3ErrorCode::EC_MIN) {
#ifndef _V3ERROR_NO_GLOBAL_
	V3Stats::addStatSum(string("Warnings, Suppressed ")+s_errorCode.ascii(), 1);
#endif
	s_errorSuppressed = true;
    }
}

string V3Error::warnMore() {
    return msgPrefix();
}

void V3Error::v3errorEnd (ostringstream& sstr) {
#if defined(__COVERITY__) || defined(__cppcheck__)
    if (s_errorCode==V3ErrorCode::EC_FATAL) __coverity_panic__(x);
#endif
    // Skip suppressed messages
    if (s_errorSuppressed
	// On debug, show only non default-off warning to prevent pages of warnings
	&& (!debug() || s_errorCode.defaultsOff())) return;
    string msg = msgPrefix()+sstr.str();
    if (msg[msg.length()-1] != '\n') msg += '\n';
    // Suppress duplicates
    if (s_messages.find(msg) != s_messages.end()) return;
    s_messages.insert(msg);
    // Output
    cerr<<msg;
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
		    v3Global.rootp()->dumpTreeFile(v3Global.debugFilename("final.tree",990));
		    if (s_errorExitCb) s_errorExitCb();
		    V3Stats::statsFinalAll(v3Global.rootp());
		    V3Stats::statsReport();
		}
#endif
	    }

	    vlAbort();
	}
	else if (isError(s_errorCode, s_errorSuppressed)) {
	    // We don't dump tree on any error because a Visitor may be in middle of
	    // a tree cleanup and cause a false broken problem.
	    if (s_errorExitCb) s_errorExitCb();
	}
    }
}
