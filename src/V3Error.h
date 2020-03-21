// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Error handling
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2020 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#ifndef _V3ERROR_H_
#define _V3ERROR_H_ 1

#include "config_build.h"
#include "verilatedos.h"

// Limited V3 headers here - this is a base class for Vlc etc
#include "V3String.h"

#include <bitset>
#include <cassert>
#include <deque>
#include <map>
#include <set>
#include <sstream>

//######################################################################

class V3ErrorCode {
public:
    enum en {
        EC_MIN=0,       // Keep first
        //
        EC_INFO,        // General information out
        EC_FATAL,       // Kill the program
        EC_FATALEXIT,   // Kill the program, suppress with --quiet-exit
        EC_FATALSRC,    // Kill the program, for internal source errors
        EC_ERROR,       // General error out, can't suppress
        // Boolean information we track per-line, but aren't errors
        I_COVERAGE,     // Coverage is on/off from /*verilator coverage_on/off*/
        I_TRACING,      // Tracing is on/off from /*verilator tracing_on/off*/
        I_LINT,         // All lint messages
        I_DEF_NETTYPE_WIRE,  // `default_nettype is WIRE (false=NONE)
        // Error codes:
        E_DETECTARRAY,  // Error: Unsupported: Can't detect changes on arrayed variable
        E_PORTSHORT,    // Error: Output port is connected to a constant, electrical short
        E_TASKNSVAR,    // Error: Task I/O not simple
        //
        // Warning codes:
        EC_FIRST_WARN,  // Just a code so the program knows where to start warnings
        //
        ALWCOMBORDER,   // Always_comb with unordered statements
        ASSIGNDLY,      // Assignment delays
        ASSIGNIN,       // Assigning to input
        BLKANDNBLK,     // Blocked and non-blocking assignments to same variable
        BLKLOOPINIT,    // Delayed assignment to array inside for loops
        BLKSEQ,         // Blocking assignments in sequential block
        BSSPACE,        // Backslash space
        CASEINCOMPLETE, // Case statement has missing values
        CASEOVERLAP,    // Case statements overlap
        CASEWITHX,      // Case with X values
        CASEX,          // Casex
        CDCRSTLOGIC,    // Logic in async reset path
        CLKDATA,        // Clock used as data
        CMPCONST,       // Comparison is constant due to limited range
        COLONPLUS,      // :+ instead of +:
        COMBDLY,        // Combinatorial delayed assignment
        CONTASSREG,     // Continuous assignment on reg
        DEFPARAM,       // Style: Defparam
        DECLFILENAME,   // Declaration doesn't match filename
        DEPRECATED,     // Feature will be deprecated
        ENDLABEL,       // End lable name mismatch
        GENCLK,         // Generated Clock
        IFDEPTH,        // If statements too deep
        IGNOREDRETURN,  // Ignoring return value (function as task)
        IMPERFECTSCH,   // Imperfect schedule (disabled by default)
        IMPLICIT,       // Implicit wire
        IMPORTSTAR,     // Import::* in $unit
        IMPURE,         // Impure function not being inlined
        INCABSPATH,     // Include has absolute path
        INFINITELOOP,   // Infinite loop
        INITIALDLY,     // Initial delayed statement
        INSECURE,       // Insecure options
        LITENDIAN,      // Little bit endian vector
        MODDUP,         // Duplicate module
        MULTIDRIVEN,    // Driven from multiple blocks
        MULTITOP,       // Multiple top level modules
        PINMISSING,     // Cell pin not specified
        PINNOCONNECT,   // Cell pin not connected
        PINCONNECTEMPTY,// Cell pin connected by name with empty reference
        PROCASSWIRE,    // Procedural assignment on wire
        REALCVT,        // Real conversion
        REDEFMACRO,     // Redefining existing define macro
        SELRANGE,       // Selection index out of range
        SHORTREAL,      // Shortreal not supported
        SPLITVAR,       // Cannot split the variable
        STMTDLY,        // Delayed statement
        SYMRSVDWORD,    // Symbol is Reserved Word
        SYNCASYNCNET,   // Mixed sync + async reset
        TICKCOUNT,      // Too large tick count
        UNDRIVEN,       // No drivers
        UNOPT,          // Unoptimizable block
        UNOPTFLAT,      // Unoptimizable block after flattening
        UNOPTTHREADS,   // Thread partitioner unable to fill all requested threads
        UNPACKED,       // Unsupported unpacked
        UNSIGNED,       // Comparison is constant due to unsigned arithmetic
        UNUSED,         // No receivers
        USERERROR,      // Elaboration time $error
        USERFATAL,      // Elaboration time $fatal
        USERINFO,       // Elaboration time $info
        USERWARN,       // Elaboration time $warning
        VARHIDDEN,      // Hiding variable
        WIDTH,          // Width mismatch
        WIDTHCONCAT,    // Unsized numbers/parameters in concatenations
        _ENUM_MAX
        // ***Add new elements below also***
    };
    enum en m_e;
    inline V3ErrorCode() : m_e(EC_MIN) {}
    // cppcheck-suppress noExplicitConstructor
    inline V3ErrorCode(en _e) : m_e(_e) {}
    explicit V3ErrorCode(const char* msgp);  // Matching code or ERROR
    explicit inline V3ErrorCode(int _e) : m_e(static_cast<en>(_e)) {}
    operator en() const { return m_e; }
    const char* ascii() const {
        const char* names[] = {
            // Leading spaces indicate it can't be disabled.
            " MIN", " INFO", " FATAL", " FATALEXIT", " FATALSRC", " ERROR",
            // Boolean
            " I_COVERAGE", " I_TRACING", " I_LINT", " I_DEF_NETTYPE_WIRE",
            // Errors
            "DETECTARRAY", "PORTSHORT", "TASKNSVAR",
            // Warnings
            " EC_FIRST_WARN",
            "ALWCOMBORDER", "ASSIGNDLY", "ASSIGNIN",
            "BLKANDNBLK", "BLKLOOPINIT", "BLKSEQ", "BSSPACE",
            "CASEINCOMPLETE", "CASEOVERLAP", "CASEWITHX", "CASEX", "CDCRSTLOGIC", "CLKDATA",
            "CMPCONST", "COLONPLUS", "COMBDLY", "CONTASSREG",
            "DEFPARAM", "DECLFILENAME", "DEPRECATED",
            "ENDLABEL", "GENCLK",
            "IFDEPTH", "IGNOREDRETURN",
            "IMPERFECTSCH", "IMPLICIT", "IMPORTSTAR", "IMPURE",
            "INCABSPATH", "INFINITELOOP", "INITIALDLY", "INSECURE",
            "LITENDIAN", "MODDUP",
            "MULTIDRIVEN", "MULTITOP",
            "PINMISSING", "PINNOCONNECT", "PINCONNECTEMPTY", "PROCASSWIRE",
            "REALCVT", "REDEFMACRO",
            "SELRANGE", "SHORTREAL", "SPLITVAR", "STMTDLY", "SYMRSVDWORD", "SYNCASYNCNET",
            "TICKCOUNT",
            "UNDRIVEN", "UNOPT", "UNOPTFLAT", "UNOPTTHREADS",
            "UNPACKED", "UNSIGNED", "UNUSED",
            "USERERROR", "USERFATAL", "USERINFO", "USERWARN",
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
                                         || m_e==BLKLOOPINIT
                                         || m_e==CONTASSREG
                                         || m_e==IMPURE
                                         || m_e==PROCASSWIRE); }
    // Warnings to mention manual
    bool mentionManual() const { return ( m_e==EC_FATALSRC || m_e==SYMRSVDWORD
                                          || pretendError() ); }

    // Warnings that are lint only
    bool lintError() const { return ( m_e==ALWCOMBORDER
                                      || m_e==BSSPACE
                                      || m_e==CASEINCOMPLETE || m_e==CASEOVERLAP
                                      || m_e==CASEWITHX || m_e==CASEX
                                      || m_e==CMPCONST
                                      || m_e==COLONPLUS
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
                                       || m_e==IMPORTSTAR
                                       || m_e==INCABSPATH
                                       || m_e==PINCONNECTEMPTY
                                       || m_e==PINNOCONNECT
                                       || m_e==SYNCASYNCNET
                                       || m_e==UNDRIVEN
                                       || m_e==UNUSED
                                       || m_e==VARHIDDEN ); }
};
inline bool operator==(const V3ErrorCode& lhs, const V3ErrorCode& rhs) {
    return lhs.m_e == rhs.m_e;
}
inline bool operator==(const V3ErrorCode& lhs, V3ErrorCode::en rhs) { return lhs.m_e == rhs; }
inline bool operator==(V3ErrorCode::en lhs, const V3ErrorCode& rhs) { return lhs == rhs.m_e; }
inline std::ostream& operator<<(std::ostream& os, const V3ErrorCode& rhs) {
    return os << rhs.ascii();
}

//######################################################################

class V3Error {
    // Base class for any object that wants debugging and error reporting

    typedef std::set<string> MessagesSet;
    typedef void (*ErrorExitCb)(void);

  private:
    static bool         s_describedWarnings;    // Told user how to disable warns
    static bool         s_describedEachWarn[V3ErrorCode::_ENUM_MAX]; // Told user specifics about this warning
    static bool         s_pretendError[V3ErrorCode::_ENUM_MAX]; // Pretend this warning is an error
    static int          s_debugDefault;         // Option: --debugi Default debugging level
    static int          s_errorLimit;           // Option: --error-limit Number of errors before exit
    static bool         s_warnFatal;            // Option: --warnFatal Warnings are fatal
    static int          s_errCount;             // Error count
    static int          s_warnCount;            // Warning count
    static int          s_tellManual;           // Tell user to see manual, 0=not yet, 1=doit, 2=disable
    static std::ostringstream s_errorStr;       // Error string being formed
    static V3ErrorCode  s_errorCode;            // Error string being formed will abort
    static bool         s_errorContexted;       // Error being formed got context
    static bool         s_errorSuppressed;      // Error being formed should be suppressed
    static MessagesSet  s_messages;             // What errors we've outputted
    static ErrorExitCb  s_errorExitCb;          // Callback when error occurs for dumping

    enum MaxErrors {    MAX_ERRORS = 50 };      // Fatal after this may errors

    V3Error() { std::cerr<<("Static class"); abort(); }

  public:
    // CONSTRUCTORS
    // ACCESSORS
    static void debugDefault(int level) { s_debugDefault = level; }
    static int debugDefault() { return s_debugDefault; }
    static void errorLimit(int level) { s_errorLimit = level; }
    static int errorLimit() { return s_errorLimit; }
    static void warnFatal(bool flag) { s_warnFatal = flag; }
    static bool warnFatal() { return s_warnFatal; }
    static string msgPrefix();  // returns %Error/%Warn
    static int errorCount() { return s_errCount; }
    static int warnCount() { return s_warnCount; }
    static int errorOrWarnCount() { return errorCount()+warnCount(); }
    static bool errorContexted() { return s_errorContexted; }
    static void errorContexted(bool flag) { s_errorContexted = flag; }
    // METHODS
    static void incErrors();
    static void incWarnings() { s_warnCount++; }
    static void init();
    static void abortIfErrors() { if (errorCount()) abortIfWarnings(); }
    static void abortIfWarnings();
    static void suppressThisWarning();  // Suppress next %Warn if user has it off
    static void pretendError(V3ErrorCode code, bool flag) { s_pretendError[code] = flag; }
    static bool isError(V3ErrorCode code, bool supp);
    static string lineStr(const char* filename, int lineno);
    static V3ErrorCode errorCode() { return s_errorCode; }
    static void errorExitCb(ErrorExitCb cb) { s_errorExitCb = cb; }

    // When printing an error/warning, print prefix for multiline message
    static string warnMore();
    /// When building an error, don't show context info
    static string warnContextNone() { V3Error::errorContexted(true); return ""; }

    // Internals for v3error()/v3fatal() macros only
    // Error end takes the string stream to output, be careful to seek() as needed
    static void v3errorPrep(V3ErrorCode code) {
        s_errorStr.str(""); s_errorCode = code;
        s_errorContexted = false; s_errorSuppressed = false; }
    static std::ostringstream& v3errorStr() { return s_errorStr; }
    static void vlAbort();
    static void v3errorEnd(std::ostringstream& sstr, const string& locationStr = "");  // static, but often overridden in classes.
};

// Global versions, so that if the class doesn't define a operator, we get the functions anyways.
inline int debug() { return V3Error::debugDefault(); }
inline void v3errorEnd(std::ostringstream& sstr) { V3Error::v3errorEnd(sstr); }
inline void v3errorEndFatal(std::ostringstream& sstr) {
    V3Error::v3errorEnd(sstr); assert(0); VL_UNREACHABLE }

// Theses allow errors using << operators: v3error("foo"<<"bar");
// Careful, you can't put () around msg, as you would in most macro definitions
// Note the commas are the comma operator, not separating arguments. These are needed to ensure
// evaluation order as otherwise we couldn't ensure v3errorPrep is called first.
#define v3warnCode(code,msg) \
    v3errorEnd((V3Error::v3errorPrep(code), (V3Error::v3errorStr()<<msg), V3Error::v3errorStr()));
#define v3warnCodeFatal(code,msg) \
    v3errorEndFatal((V3Error::v3errorPrep(code), (V3Error::v3errorStr()<<msg), \
                     V3Error::v3errorStr()));
#define v3warn(code,msg) v3warnCode(V3ErrorCode::code, msg)
#define v3info(msg)  v3warnCode(V3ErrorCode::EC_INFO, msg)
#define v3error(msg) v3warnCode(V3ErrorCode::EC_ERROR, msg)
#define v3fatal(msg) v3warnCodeFatal(V3ErrorCode::EC_FATAL, msg)
// Use this instead of fatal() if message gets suppressed with --quiet-exit
#define v3fatalExit(msg) v3warnCodeFatal(V3ErrorCode::EC_FATALEXIT, msg)
// Use this instead of fatal() to mention the source code line.
#define v3fatalSrc(msg) v3warnCodeFatal(V3ErrorCode::EC_FATALSRC, __FILE__<<":"<<std::dec<<__LINE__<<": "<<msg)
// Use this when normal v3fatal is called in static method that overrides fileline.
#define v3fatalStatic(msg) \
    ::v3errorEndFatal((V3Error::v3errorPrep(V3ErrorCode::EC_FATAL), \
                       (V3Error::v3errorStr()<<msg), V3Error::v3errorStr()));

#define UINFO(level, stmsg) \
    { if (VL_UNCOVERABLE(debug() >= (level))) { \
            cout << "- " << V3Error::lineStr(__FILE__, __LINE__) << stmsg; } }
#define UINFONL(level, stmsg) \
    { if (VL_UNCOVERABLE(debug() >= (level))) { cout << stmsg; } }

#ifdef VL_DEBUG
# define UDEBUGONLY(stmts) {stmts}
#else
# define UDEBUGONLY(stmts) {if (0) {stmts}}
#endif

// Assertion without object, generally UOBJASSERT preferred
#define UASSERT(condition,stmsg) \
    do { if (VL_UNCOVERABLE(!(condition))) { v3fatalSrc(stmsg); }} while(0)
// Assertion with object
#define UASSERT_OBJ(condition,obj,stmsg) \
    do { if (VL_UNCOVERABLE(!(condition))) { (obj)->v3fatalSrc(stmsg); }} while(0)
// For use in V3Ast static functions only
#define UASSERT_STATIC(condition,stmsg) \
    do { if (VL_UNCOVERABLE(!(condition))) { \
            std::cerr<<"Internal Error: "<<__FILE__<<":"<<std::dec<<__LINE__ \
                     <<":"<<(stmsg)<<std::endl; abort(); } } while(0)
// Check self test values for expected value.  Safe from side-effects.
// Type argument can be removed when go to C++11 (use auto).
#define UASSERT_SELFTEST(Type,got,exp) \
    do { Type g = (got); Type e = (exp); \
         UASSERT(g==e, "Self-test failed '" #got "==" #exp "'"" got=" \
                 <<g<<" expected="<<e); } while(0)

#define V3ERROR_NA \
    do { v3error("Internal: Unexpected Call"); v3fatalSrc("Unexpected Call"); } while(0)

/// Declare a convenience debug() routine that may be added to any class in
/// Verilator so that --debugi-<srcfile> will work to control UINFOs in
/// that class:
#define VL_DEBUG_FUNC \
    static int debug() {       \
        static int level = -1; \
        if (VL_UNLIKELY(level < 0)) level = v3Global.opt.debugSrcLevel(__FILE__); \
        return level; \
    }

//----------------------------------------------------------------------

#endif  // Guard
