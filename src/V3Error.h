// -*- C++ -*-
//*************************************************************************
// DESCRIPTION: Verilator: Error handling
//
// Code available from: http://www.veripool.org/verilator
//
// AUTHORS: Wilson Snyder with Paul Wasson, Duane Gabli
//
//*************************************************************************
//
// Copyright 2003-2010 by Wilson Snyder.  This program is free software; you can
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

//######################################################################

class V3ErrorCode {
public:
    enum en {
	EC_MIN=0,	// Keep first
	//
	EC_SUPPRESS,	// Warning suppressed by user
	EC_INFO,	// General information out
	EC_FATAL,	// Kill the program
	EC_FATALSRC,	// Kill the program, for internal source errors
	EC_ERROR,	// General error out, can't suppress
	// Boolean information we track per-line, but aren't errors
	I_COVERAGE,	// Coverage is on/off from /*verilator coverage_on/off*/
	I_TRACING,	// Tracing is on/off from /*verilator tracing_on/off*/
	I_DEF_NETTYPE_WIRE,  // `default_nettype is WIRE (false=NONE)
	// Error codes:
	E_MULTITOP,	// Error: Multiple top level modules
	E_TASKNSVAR,	// Error: Task I/O not simple
	E_BLKLOOPINIT,	// Error: Delayed assignment to array inside for loops
	// Warning codes:
	EC_FIRST_WARN,	// Just a code so the program knows where to start warnings
	//
	BLKANDNBLK,	// Blocked and non-blocking assignments to same variable
	CASEINCOMPLETE,	// Case statement has missing values
	CASEOVERLAP,	// Case statements overlap
	CASEWITHX,	// Case with X values
	CASEX,		// Casex
	CDCRSTLOGIC,	// Logic in async reset path
	CMPCONST,	// Comparison is constant due to limited range
	COMBDLY,	// Combinatorial delayed assignment
	STMTDLY,	// Delayed statement
	SYMRSVDWORD,	// Symbol is Reserved Word
	GENCLK,		// Generated Clock
	IMPERFECTSCH,	// Imperfect schedule (disabled by default)
	IMPLICIT,	// Implicit wire
	IMPURE,		// Impure function not being inlined
	LITENDIAN,	// Little bit endian vector
	MODDUP,		// Duplicate module
	MULTIDRIVEN,	// Driven from multiple blocks
	REDEFMACRO,	// Redefining existing define macro
	UNDRIVEN,	// No drivers
	UNOPT,		// Unoptimizable block
	UNOPTFLAT,	// Unoptimizable block after flattening
	UNSIGNED,	// Comparison is constant due to unsigned arithmetic
	UNUSED,		// No receivers
	VARHIDDEN,	// Hiding variable
	WIDTH,		// Width mismatch
	WIDTHCONCAT,	// Unsized numbers/parameters in concatenations
	_ENUM_MAX
	// ***Add new elements below also***
    };
    enum en m_e;
    inline V3ErrorCode () {}
    inline V3ErrorCode (en _e) : m_e(_e) {}
    V3ErrorCode (const char* msgp);	// Matching code or ERROR
    explicit inline V3ErrorCode (int _e) : m_e(static_cast<en>(_e)) {}
    operator en () const { return m_e; }
    const char* ascii() const {
	const char* names[] = {
	    // Leading spaces indicate it can't be disabled.
	    " MIN", " SUPPRESS", " INFO", " FATAL", " FATALSRC", " ERROR",
	    // Boolean
	    " I_COVERAGE", " I_TRACING", " I_DEF_NETTYPE_WIRE",
	    // Errors
	    "MULTITOP", "TASKNSVAR", "BLKLOOPINIT",
	    // Warnings
	    " FIRST_WARN",
	    "BLKANDNBLK",
	    "CASEINCOMPLETE", "CASEOVERLAP", "CASEWITHX", "CASEX", "CDCRSTLOGIC", "CMPCONST",
	    "COMBDLY", "STMTDLY", "SYMRSVDWORD", "GENCLK", "IMPERFECTSCH", "IMPLICIT", "IMPURE",
	    "LITENDIAN", "MODDUP",
	    "MULTIDRIVEN", "REDEFMACRO",
	    "UNDRIVEN", "UNOPT", "UNOPTFLAT", "UNSIGNED", "UNUSED",
	    "VARHIDDEN", "WIDTH", "WIDTHCONCAT",
	    " MAX"
	};
	return names[m_e];
    }
    // Warnings that default to off
    bool defaultsOff() const { return ( m_e==IMPERFECTSCH ); }
    // Warnings that warn about nasty side effects
    bool dangerous() const { return ( m_e==COMBDLY ); }
    // Warnings we'll present to the user as errors
    // Later -Werror- options may make more of these.
    bool pretendError() const { return ( m_e==BLKANDNBLK || m_e==IMPURE || m_e==MODDUP || m_e==SYMRSVDWORD); }
    // Warnings to mention manual
    bool mentionManual() const { return ( m_e==EC_FATALSRC || pretendError() ); }

    // Warnings that are lint only
    bool lintError() const { return ( m_e==CASEINCOMPLETE || m_e==CASEOVERLAP
				      || m_e==CASEWITHX || m_e==CASEX
				      || m_e==CMPCONST
				      || m_e==IMPLICIT
				      || m_e==LITENDIAN
				      || m_e==UNDRIVEN || m_e==UNSIGNED
				      || m_e==UNUSED || m_e==VARHIDDEN
				      || m_e==WIDTH); }
  };
  inline bool operator== (V3ErrorCode lhs, V3ErrorCode rhs) { return (lhs.m_e == rhs.m_e); }
  inline bool operator== (V3ErrorCode lhs, V3ErrorCode::en rhs) { return (lhs.m_e == rhs); }
  inline bool operator== (V3ErrorCode::en lhs, V3ErrorCode rhs) { return (lhs == rhs.m_e); }
  inline ostream& operator<<(ostream& os, V3ErrorCode rhs) { return os<<rhs.ascii(); }

//######################################################################

class V3Error {
    // Base class for any object that wants debugging and error reporting
  private:
    static bool 	s_describedWarnings;	// Told user how to disable warns
    static bool 	s_describedEachWarn[V3ErrorCode::_ENUM_MAX]; // Told user specifics about this warning
    static bool 	s_pretendError[V3ErrorCode::_ENUM_MAX]; // Pretend this warning is an error
    static int		s_debugDefault;		// Default debugging level
    static int		s_errCount;		// Error count
    static int		s_warnCount;		// Error count
    static int 		s_tellManual;		// Tell user to see manual, 0=not yet, 1=doit, 2=disable
    static ostringstream s_errorStr;		// Error string being formed
    static V3ErrorCode	s_errorCode;		// Error string being formed will abort
    enum MaxErrors { 	MAX_ERRORS = 50 };	// Fatal after this may errors

    V3Error() { cerr<<("Static class"); abort(); }

  public:
    // CREATORS
    // ACCESSORS
    static void		debugDefault(int level) { s_debugDefault = level; }
    static int		debugDefault() { return s_debugDefault; }
    static string	msgPrefix(V3ErrorCode code=s_errorCode);	// returns %Error/%Warn
    static int		errorCount() { return s_errCount; }
    static int		warnCount() { return s_warnCount; }
    static int		errorOrWarnCount() { return errorCount()+warnCount(); }
    // METHODS
    static void		incErrors();
    static void		incWarnings();
    static void		init();
    static void		abortIfErrors();
    static void		abortIfWarnings();
    static void		suppressThisWarning();	// Suppress next %Warn if user has it off
    static void		pretendError(V3ErrorCode code, bool flag) { s_pretendError[code]=flag; }
    static bool		isError(V3ErrorCode code);
    static string 	v3sform (const char* format, ...);
    static string	lineStr (const char* filename, int lineno);
    static V3ErrorCode	errorCode() { return s_errorCode; }

    // Internals for v3error()/v3fatal() macros only
    // Error end takes the string stream to output, be careful to seek() as needed
    static ostringstream& v3errorPrep (V3ErrorCode code) {
	s_errorStr.str(""); s_errorCode=code; return s_errorStr; }
    static ostringstream& v3errorStr () { return s_errorStr; }
    static void	vlAbort();
    static void	v3errorEnd(ostringstream& sstr);	// static, but often overridden in classes.
};

// Global versions, so that if the class doesn't define a operator, we get the functions anyways.
inline int debug() { return V3Error::debugDefault(); }
inline void v3errorEnd(ostringstream& sstr) { V3Error::v3errorEnd(sstr); }

// These allow errors using << operators: v3error("foo"<<"bar");
// Careful, you can't put () around msg, as you would in most macro definitions
#define v3warnCode(code,msg) v3errorEnd(((V3Error::v3errorPrep(code)<<msg),V3Error::v3errorStr()));
#define v3warn(code,msg) v3warnCode(V3ErrorCode::code,msg)
#define v3info(msg)  v3warn(EC_INFO,msg)
#define v3fatal(msg) v3warn(EC_FATAL,msg)
#define v3error(msg) v3warn(EC_ERROR,msg)
// Use this instead of fatal() to mention the source code line.
#define v3fatalSrc(msg) v3warn(EC_FATALSRC,__FILE__<<":"<<dec<<__LINE__<<": "<<msg)

#define UINFO(level,stmsg) {if(debug()>=(level)) { cout<<"- "<<V3Error::lineStr(__FILE__,__LINE__)<<stmsg; }}
#define UINFONL(level,stmsg) {if(debug()>=(level)) { cout<<stmsg; } }

#define UDEBUGONLY(stmts) {stmts}
#define UASSERT(condition,stmsg) { if (!(condition)) { v3fatalSrc(stmsg); }}
// For use in V3Ast static functions only
#define UASSERT_STATIC(condition,stmsg) { if (!(condition)) { cerr<<"Internal Error: "<<__FILE__<<":"<<dec<<__LINE__<<":"<<(stmsg)<<endl; abort(); } }

#define V3ERROR_NA { v3error("Internal: Unexpected Call"); v3fatalSrc("Unexpected Call"); }

//----------------------------------------------------------------------

template< class T> std::string cvtToStr (const T& t) {
    ostringstream os; os<<t; return os.str();
}

inline uint32_t cvtToHash(void* vp) {
    // We can shove a 64 bit pointer into a 32 bit bucket
    // On 32 bit systems, lower is always 0, but who cares?
    union { void* up; struct {uint32_t upper; uint32_t lower;} l;} u;
    u.l.upper=0; u.l.lower=0; u.up=vp;
    return u.l.upper^u.l.lower;
}

//######################################################################

class FileLine {
    // File and line number of an object, mostly for error reporting
    int		m_lineno;
    string	m_filename;
    bitset<V3ErrorCode::_ENUM_MAX>	m_warnOn;
    static FileLine s_defaultFileLine;
    struct EmptySecret {};
protected:
    // User routines should never need to change line numbers
    // We are storing pointers, so we CAN'T change them after initial reading.
    friend class V3ParseImp;
    friend class V3PreLex;
    void lineno(int num) { m_lineno = num; }
    void filename(const string& name) { m_filename = name; }
    void lineDirective(const char* textp);
    void incLineno() { m_lineno++; }
    FileLine* copyOrSameFileLine();
public:
    FileLine (const string& filename, int lineno) { m_lineno=lineno; m_filename = filename; m_warnOn=s_defaultFileLine.m_warnOn; }
    FileLine (FileLine* fromp) { m_lineno=fromp->lineno(); m_filename = fromp->filename(); m_warnOn=fromp->m_warnOn; }
    FileLine (EmptySecret);
    ~FileLine() { }
    static void deleteAllRemaining();
#ifdef VL_LEAK_CHECKS
    static void* operator new(size_t size);
    static void operator delete(void* obj, size_t size);
#endif
    int lineno () const { return m_lineno; }
    string ascii() const;
    const string filename () const { return m_filename; }
    const string filebasename () const;
    const string profileFuncname() const;
    void warnOn(V3ErrorCode code, bool flag) { m_warnOn.set(code,flag); }	// Turn on/off warning messages on this line.
    void warnOff(V3ErrorCode code, bool flag) { warnOn(code,!flag); }
    bool warnOff(const string& code, bool flag);  // Returns 1 if ok
    bool warnIsOff(V3ErrorCode code) const;
    void warnLintOff(bool flag);
    void warnStateFrom(const FileLine& from) { m_warnOn=from.m_warnOn; }
    void warnResetDefault() { warnStateFrom(s_defaultFileLine); }

    // Specific flag ACCESSORS/METHODS
    bool coverageOn() const { return m_warnOn.test(V3ErrorCode::I_COVERAGE); }
    void coverageOn(bool flag) { warnOn(V3ErrorCode::I_COVERAGE,flag); }
    bool tracingOn() const { return m_warnOn.test(V3ErrorCode::I_TRACING); }
    void tracingOn(bool flag) { warnOn(V3ErrorCode::I_TRACING,flag); }

    // METHODS - Global
    static void globalWarnLintOff(bool flag) { s_defaultFileLine.warnLintOff(flag); }
    static void globalWarnOff(V3ErrorCode code, bool flag) { s_defaultFileLine.warnOff(code, flag); }
    static bool globalWarnOff(const string& code, bool flag) { return s_defaultFileLine.warnOff(code, flag); }

    // METHODS - Called from netlist
    // Merge warning disables from another fileline
    void modifyStateInherit(const FileLine* fromp);
    // Change the current fileline due to actions discovered after parsing
    // and may have side effects on other nodes sharing this FileLine.
    // Use only when this is intended 
    void modifyWarnOff(V3ErrorCode code, bool flag) { warnOff(code,flag); }

    // OPERATORS
    void v3errorEnd(ostringstream& str);
    inline bool operator==(FileLine rhs) {
	return (m_lineno==rhs.m_lineno && m_filename==rhs.m_filename && m_warnOn==rhs.m_warnOn);
    }
};
ostream& operator<<(ostream& os, FileLine* fileline);

#endif // Guard
