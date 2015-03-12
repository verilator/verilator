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

#ifndef _V3ERROR_H_
#define _V3ERROR_H_ 1
#include "config_build.h"
#include "verilatedos.h"
#include <string>
#include <iostream>
#include <sstream>
#include <bitset>
#include <map>
#include <set>
#include <deque>

//######################################################################

class V3ErrorCode {
public:
    enum en {
	EC_MIN=0,	// Keep first
	//
	EC_INFO,	// General information out
	EC_FATAL,	// Kill the program
	EC_FATALSRC,	// Kill the program, for internal source errors
	EC_ERROR,	// General error out, can't suppress
	// Boolean information we track per-line, but aren't errors
	I_COVERAGE,	// Coverage is on/off from /*verilator coverage_on/off*/
	I_TRACING,	// Tracing is on/off from /*verilator tracing_on/off*/
	I_LINT,		// All lint messages
	I_DEF_NETTYPE_WIRE,  // `default_nettype is WIRE (false=NONE)
	// Error codes:
	E_BLKLOOPINIT,	// Error: Delayed assignment to array inside for loops
	E_DETECTARRAY,	// Error: Unsupported: Can't detect changes on arrayed variable
	E_MULTITOP,	// Error: Multiple top level modules
	E_TASKNSVAR,	// Error: Task I/O not simple
	//
	// Warning codes:
	EC_FIRST_WARN,	// Just a code so the program knows where to start warnings
	//
	ALWCOMBORDER,	// Always_comb with unordered statements
	ASSIGNDLY,	// Assignment delays
	ASSIGNIN,	// Assigning to input
	BLKANDNBLK,	// Blocked and non-blocking assignments to same variable
	BLKSEQ,		// Blocking assignments in sequential block
	CASEINCOMPLETE,	// Case statement has missing values
	CASEOVERLAP,	// Case statements overlap
	CASEWITHX,	// Case with X values
	CASEX,		// Casex
	CDCRSTLOGIC,	// Logic in async reset path
	CLKDATA,        // Clock used as data
	CMPCONST,	// Comparison is constant due to limited range
	COMBDLY,	// Combinatorial delayed assignment
	DEFPARAM,	// Style: Defparam
	DECLFILENAME,	// Declaration doesn't match filename
	ENDLABEL,	// End lable name mismatch
	GENCLK,		// Generated Clock
	IFDEPTH,	// If statements too deep
	IMPERFECTSCH,	// Imperfect schedule (disabled by default)
	IMPLICIT,	// Implicit wire
	IMPURE,		// Impure function not being inlined
	INCABSPATH,	// Include has absolute path
	INITIALDLY,	// Initial delayed statement
	LITENDIAN,	// Little bit endian vector
	MODDUP,		// Duplicate module
	MULTIDRIVEN,	// Driven from multiple blocks
	PINMISSING,	// Cell pin not specified
	PINNOCONNECT,	// Cell pin not connected
	PINCONNECTEMPTY,// Cell pin connected by name with empty reference: ".name()" (can be used to mark unused pins)
	REALCVT,	// Real conversion
	REDEFMACRO,	// Redefining existing define macro
	SELRANGE,	// Selection index out of range
	STMTDLY,	// Delayed statement
	SYMRSVDWORD,	// Symbol is Reserved Word
	SYNCASYNCNET,	// Mixed sync + async reset
	UNDRIVEN,	// No drivers
	UNOPT,		// Unoptimizable block
	UNOPTFLAT,	// Unoptimizable block after flattening
	UNPACKED,	// Unsupported unpacked
	UNSIGNED,	// Comparison is constant due to unsigned arithmetic
	UNUSED,		// No receivers
	VARHIDDEN,	// Hiding variable
	WIDTH,		// Width mismatch
	WIDTHCONCAT,	// Unsized numbers/parameters in concatenations
	_ENUM_MAX
	// ***Add new elements below also***
    };
    enum en m_e;
    inline V3ErrorCode () : m_e(EC_MIN) {}
    inline V3ErrorCode (en _e) : m_e(_e) {}
    V3ErrorCode (const char* msgp);	// Matching code or ERROR
    explicit inline V3ErrorCode (int _e) : m_e(static_cast<en>(_e)) {}
    operator en () const { return m_e; }
    const char* ascii() const {
	const char* names[] = {
	    // Leading spaces indicate it can't be disabled.
	    " MIN", " INFO", " FATAL", " FATALSRC", " ERROR",
	    // Boolean
	    " I_COVERAGE", " I_TRACING", " I_LINT", " I_DEF_NETTYPE_WIRE",
	    // Errors
	    "BLKLOOPINIT", "DETECTARRAY", "MULTITOP", "TASKNSVAR",
	    // Warnings
	    " EC_FIRST_WARN",
	    "ALWCOMBORDER", "ASSIGNDLY", "ASSIGNIN",
	    "BLKANDNBLK", "BLKSEQ",
	    "CASEINCOMPLETE", "CASEOVERLAP", "CASEWITHX", "CASEX", "CDCRSTLOGIC", "CLKDATA",
	    "CMPCONST", "COMBDLY", "DEFPARAM", "DECLFILENAME",
	    "ENDLABEL", "GENCLK",
	    "IFDEPTH", "IMPERFECTSCH", "IMPLICIT", "IMPURE",
	    "INCABSPATH", "INITIALDLY",
	    "LITENDIAN", "MODDUP",
	    "MULTIDRIVEN",
	    "PINMISSING", "PINNOCONNECT", "PINCONNECTEMPTY",
	    "REALCVT", "REDEFMACRO",
	    "SELRANGE", "STMTDLY", "SYMRSVDWORD", "SYNCASYNCNET",
	    "UNDRIVEN", "UNOPT", "UNOPTFLAT", "UNPACKED", "UNSIGNED", "UNUSED",
	    "VARHIDDEN", "WIDTH", "WIDTHCONCAT",
	    " MAX"
	};
	return names[m_e];
    }
    // Warnings that default to off
    bool defaultsOff() const { return ( m_e==IMPERFECTSCH || styleError()); }
    // Warnings that warn about nasty side effects
    bool dangerous() const { return ( m_e==COMBDLY ); }
    // Warnings we'll present to the user as errors
    // Later -Werror- options may make more of these.
    bool pretendError() const { return ( m_e==ASSIGNIN || m_e==BLKANDNBLK
					 || m_e==IMPURE || m_e==MODDUP); }
    // Warnings to mention manual
    bool mentionManual() const { return ( m_e==EC_FATALSRC || m_e==SYMRSVDWORD
					  || pretendError() ); }

    // Warnings that are lint only
    bool lintError() const { return ( m_e==ALWCOMBORDER
				      || m_e==CASEINCOMPLETE || m_e==CASEOVERLAP
				      || m_e==CASEWITHX || m_e==CASEX
				      || m_e==CMPCONST
				      || m_e==ENDLABEL
				      || m_e==IMPLICIT
				      || m_e==LITENDIAN
				      || m_e==PINMISSING
				      || m_e==REALCVT
				      || m_e==UNSIGNED
				      || m_e==WIDTH); }
    // Warnings that are style only
    bool styleError() const { return ( m_e==ASSIGNDLY  // More than style, but for backward compatibility
				       || m_e==BLKSEQ
				       || m_e==DEFPARAM
				       || m_e==DECLFILENAME
				       || m_e==INCABSPATH
				       || m_e==PINCONNECTEMPTY
				       || m_e==PINNOCONNECT
				       || m_e==SYNCASYNCNET
				       || m_e==UNDRIVEN
				       || m_e==UNUSED
				       || m_e==VARHIDDEN ); }
  };
  inline bool operator== (V3ErrorCode lhs, V3ErrorCode rhs) { return (lhs.m_e == rhs.m_e); }
  inline bool operator== (V3ErrorCode lhs, V3ErrorCode::en rhs) { return (lhs.m_e == rhs); }
  inline bool operator== (V3ErrorCode::en lhs, V3ErrorCode rhs) { return (lhs == rhs.m_e); }
  inline ostream& operator<<(ostream& os, V3ErrorCode rhs) { return os<<rhs.ascii(); }

//######################################################################

class V3Error {
    // Base class for any object that wants debugging and error reporting

    typedef set<string> MessagesSet;
    typedef void (*ErrorExitCb)(void);

  private:
    static bool 	s_describedWarnings;	// Told user how to disable warns
    static bool 	s_describedEachWarn[V3ErrorCode::_ENUM_MAX]; // Told user specifics about this warning
    static bool 	s_pretendError[V3ErrorCode::_ENUM_MAX]; // Pretend this warning is an error
    static int		s_debugDefault;		// Option: --debugi Default debugging level
    static int		s_errorLimit;		// Option: --error-limit Number of errors before exit
    static bool		s_warnFatal;		// Option: --warnFatal Warnings are fatal
    static int		s_errCount;		// Error count
    static int		s_warnCount;		// Warning count
    static int 		s_tellManual;		// Tell user to see manual, 0=not yet, 1=doit, 2=disable
    static ostringstream s_errorStr;		// Error string being formed
    static V3ErrorCode	s_errorCode;		// Error string being formed will abort
    static bool		s_errorSuppressed;	// Error being formed should be suppressed
    static MessagesSet	s_messages;		// What errors we've outputted
    static ErrorExitCb	s_errorExitCb;		// Callback when error occurs for dumping

    enum MaxErrors { 	MAX_ERRORS = 50 };	// Fatal after this may errors

    V3Error() { cerr<<("Static class"); abort(); }

  public:
    // CREATORS
    // ACCESSORS
    static void		debugDefault(int level) { s_debugDefault = level; }
    static int		debugDefault() { return s_debugDefault; }
    static void		errorLimit(int level) { s_errorLimit = level; }
    static int		errorLimit() { return s_errorLimit; }
    static void		warnFatal(bool flag) { s_warnFatal = flag; }
    static bool		warnFatal() { return s_warnFatal; }
    static string	msgPrefix();	// returns %Error/%Warn
    static int		errorCount() { return s_errCount; }
    static int		warnCount() { return s_warnCount; }
    static int		errorOrWarnCount() { return errorCount()+warnCount(); }
    // METHODS
    static void		incErrors();
    static void		incWarnings() { s_warnCount++; }
    static void		init();
    static void		abortIfErrors() { if (errorCount()) abortIfWarnings(); }
    static void		abortIfWarnings();
    static void		suppressThisWarning();	// Suppress next %Warn if user has it off
    static void		pretendError(V3ErrorCode code, bool flag) { s_pretendError[code]=flag; }
    static bool		isError(V3ErrorCode code, bool supp);
    static string	lineStr (const char* filename, int lineno);
    static V3ErrorCode	errorCode() { return s_errorCode; }
    static void		errorExitCb(ErrorExitCb cb) { s_errorExitCb = cb; }

    // When printing an error/warning, print prefix for multiline message
    static string warnMore();

    // Internals for v3error()/v3fatal() macros only
    // Error end takes the string stream to output, be careful to seek() as needed
    static void v3errorPrep(V3ErrorCode code) {
	s_errorStr.str(""); s_errorCode=code; s_errorSuppressed=false; }
    static ostringstream& v3errorStr() { return s_errorStr; }
    static void	vlAbort();
    static void	v3errorEnd(ostringstream& sstr);	// static, but often overridden in classes.
};

// Global versions, so that if the class doesn't define a operator, we get the functions anyways.
inline int debug() { return V3Error::debugDefault(); }
inline void v3errorEnd(ostringstream& sstr) { V3Error::v3errorEnd(sstr); }

// Theses allow errors using << operators: v3error("foo"<<"bar");
// Careful, you can't put () around msg, as you would in most macro definitions
// Note the commas are the comma operator, not separating arguments. These are needed to insure
// evaluation order as otherwise we couldn't insure v3errorPrep is called first.
#define v3warnCode(code,msg) v3errorEnd((V3Error::v3errorPrep(code), (V3Error::v3errorStr()<<msg), V3Error::v3errorStr()));
#define v3warn(code,msg) v3warnCode(V3ErrorCode::code,msg)
#define v3info(msg)  v3warn(EC_INFO,msg)
#define v3fatal(msg) v3warn(EC_FATAL,msg)
#define v3error(msg) v3warn(EC_ERROR,msg)
// Use this instead of fatal() to mention the source code line.
#define v3fatalSrc(msg) v3warn(EC_FATALSRC,__FILE__<<":"<<dec<<__LINE__<<": "<<msg)

#define UINFO(level,stmsg) {if(VL_UNLIKELY(debug()>=(level))) { cout<<"- "<<V3Error::lineStr(__FILE__,__LINE__)<<stmsg; }}
#define UINFONL(level,stmsg) {if(VL_UNLIKELY(debug()>=(level))) { cout<<stmsg; } }

#define UDEBUGONLY(stmts) {stmts}
#define UASSERT(condition,stmsg) { if (VL_UNLIKELY(!(condition))) { v3fatalSrc(stmsg); }}
// For use in V3Ast static functions only
#define UASSERT_STATIC(condition,stmsg) { if (VL_UNLIKELY(!(condition))) { cerr<<"Internal Error: "<<__FILE__<<":"<<dec<<__LINE__<<":"<<(stmsg)<<endl; abort(); } }

#define V3ERROR_NA { v3error("Internal: Unexpected Call"); v3fatalSrc("Unexpected Call"); }

//----------------------------------------------------------------------

template< class T> std::string cvtToStr (const T& t) {
    ostringstream os; os<<t; return os.str();
}

inline uint32_t cvtToHash(const void* vp) {
    // We can shove a 64 bit pointer into a 32 bit bucket
    // On 32-bit systems, lower is always 0, but who cares?
    union { const void* up; struct {uint32_t upper; uint32_t lower;} l;} u;
    u.l.upper=0; u.l.lower=0; u.up=vp;
    return u.l.upper^u.l.lower;
}

inline string ucfirst(const string& text) {
    string out = text;
    out[0] = toupper(out[0]);
    return out;
}

#endif // Guard
