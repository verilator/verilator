// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Error handling
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2023 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#ifndef VERILATOR_V3ERROR_H_
#define VERILATOR_V3ERROR_H_

#include "config_build.h"
#include "verilatedos.h"

#include "V3Mutex.h"

// Limited V3 headers here - this is a base class for Vlc etc
#include "V3String.h"
#ifndef V3ERROR_NO_GLOBAL_
#include "V3ThreadPool.h"
#endif

#include <array>
#include <bitset>
#include <cassert>
#include <cctype>
#include <deque>
#include <map>
#include <set>
#include <sstream>

//######################################################################

class V3ErrorCode final {
public:
    // clang-format off
    enum en: uint8_t  {
        EC_MIN=0,       // Keep first
        //
        EC_INFO,        // General information out
        EC_FATAL,       // Kill the program
        EC_FATALEXIT,   // Kill the program, suppress with --quiet-exit
        EC_FATALSRC,    // Kill the program, for internal source errors
        EC_ERROR,       // General error out, can't suppress
        EC_FIRST_NAMED,  // Just a code so the program knows where to start info/errors
        // Boolean information we track per-line, but aren't errors
        I_CELLDEFINE,   // Inside cell define from `celldefine/`endcelldefine
        I_COVERAGE,     // Coverage is on/off from /*verilator coverage_on/off*/
        I_DEF_NETTYPE_WIRE,  // `default_nettype is WIRE (false=NONE)
        I_LINT,         // All lint messages
        I_TIMING,       // Enable timing from /*verilator timing_on/off*/
        I_TRACING,      // Tracing is on/off from /*verilator tracing_on/off*/
        I_UNUSED,       // Unused genvar, parameter or signal message (Backward Compatibility)
        // Error codes:
        E_LIFETIME,     // Error: Reference to a variable might outlive the variable.
        E_NEEDTIMINGOPT,  // Error: --timing/--no-timing option not specified
        E_NOTIMING,     // Timing control encountered with --no-timing
        E_PORTSHORT,    // Error: Output port is connected to a constant, electrical short
        E_TASKNSVAR,    // Error: Task I/O not simple
        E_UNSUPPORTED,  // Error: Unsupported (generally)
        //
        // Warning codes:
        EC_FIRST_WARN,  // Just a code so the program knows where to start warnings
        //
        ALWCOMBORDER,   // Always_comb with unordered statements
        ASCRANGE,       // Ascending bit range vector
        ASSIGNDLY,      // Assignment delays
        ASSIGNIN,       // Assigning to input
        BADSTDPRAGMA,   // Any error related to pragmas
        BLKANDNBLK,     // Blocked and non-blocking assignments to same variable
        BLKLOOPINIT,    // Delayed assignment to array inside for loops
        BLKSEQ,         // Blocking assignments in sequential block
        BSSPACE,        // Backslash space
        CASEINCOMPLETE, // Case statement has missing values
        CASEOVERLAP,    // Case statements overlap
        CASEWITHX,      // Case with X values
        CASEX,          // Casex
        CASTCONST,      // Cast is constant
        CDCRSTLOGIC,    // Logic in async reset path. Historical, never issued.
        CLKDATA,        // Clock used as data. Historical, never issued.
        CMPCONST,       // Comparison is constant due to limited range
        COLONPLUS,      // :+ instead of +:
        COMBDLY,        // Combinatorial delayed assignment
        CONSTRAINTIGN,  // Constraint ignored
        CONTASSREG,     // Continuous assignment on reg
        DECLFILENAME,   // Declaration doesn't match filename
        DEFPARAM,       // Style: Defparam
        DEPRECATED,     // Feature will be deprecated
        ENCAPSULATED,   // Error: local/protected violation
        ENDLABEL,       // End lable name mismatch
        ENUMVALUE,      // Error: enum type needs explicit cast
        EOFNEWLINE,     // End-of-file missing newline
        GENCLK,         // Generated Clock. Historical, never issued.
        GENUNNAMED,     // Generate unnamed, without label
        HIERBLOCK,      // Ignored hierarchical block setting
        IFDEPTH,        // If statements too deep
        IGNOREDRETURN,  // Ignoring return value (function as task)
        IMPERFECTSCH,   // Imperfect schedule (disabled by default). Historical, never issued.
        IMPLICIT,       // Implicit wire
        IMPLICITSTATIC, // Implicit static function
        IMPORTSTAR,     // Import::* in $unit
        IMPURE,         // Impure function not being inlined
        INCABSPATH,     // Include has absolute path
        INFINITELOOP,   // Infinite loop
        INITIALDLY,     // Initial delayed statement
        INSECURE,       // Insecure options
        LATCH,          // Latch detected outside of always_latch block
        LITENDIAN,      // Little endian, renamed to ASCRANGE
        MINTYPMAXDLY,   // Unsupported: min/typ/max delay expressions
        MISINDENT,      // Misleading indentation
        MODDUP,         // Duplicate module
        MULTIDRIVEN,    // Driven from multiple blocks
        MULTITOP,       // Multiple top level modules
        NEWERSTD,       // Newer language standard required
        NOLATCH,        // No latch detected in always_latch block
        NULLPORT,       // Null port detected in module definition
        PINCONNECTEMPTY,// Cell pin connected by name with empty reference
        PINMISSING,     // Cell pin not specified
        PINNOCONNECT,   // Cell pin not connected
        PINNOTFOUND,    // instance port name not found in it's module
        PKGNODECL,      // Error: Package/class needs to be predeclared
        PROCASSWIRE,    // Procedural assignment on wire
        PROFOUTOFDATE,  // Profile data out of date
        PROTECTED,      // detected `pragma protected
        RANDC,          // Unsupported: 'randc' converted to 'rand'
        REALCVT,        // Real conversion
        REDEFMACRO,     // Redefining existing define macro
        RISEFALLDLY,    // Unsupported: rise/fall/turn-off delays
        SELRANGE,       // Selection index out of range
        SHORTREAL,      // Shortreal not supported
        SPLITVAR,       // Cannot split the variable
        STATICVAR,      // Static variable declared in a loop with a declaration assignment
        STMTDLY,        // Delayed statement
        SYMRSVDWORD,    // Symbol is Reserved Word
        SYNCASYNCNET,   // Mixed sync + async reset
        TICKCOUNT,      // Too large tick count
        TIMESCALEMOD,   // Need timescale for module
        UNDRIVEN,       // No drivers
        UNOPT,          // Unoptimizable block. Historical, never issued.
        UNOPTFLAT,      // Unoptimizable block after flattening
        UNOPTTHREADS,   // Thread partitioner unable to fill all requested threads
        UNPACKED,       // Unsupported unpacked
        UNSIGNED,       // Comparison is constant due to unsigned arithmetic
        UNUSEDGENVAR,   // No receivers for genvar
        UNUSEDPARAM,    // No receivers for parameters
        UNUSEDSIGNAL,   // No receivers for signals
        USERERROR,      // Elaboration time $error
        USERFATAL,      // Elaboration time $fatal
        USERINFO,       // Elaboration time $info
        USERWARN,       // Elaboration time $warning
        VARHIDDEN,      // Hiding variable
        WAITCONST,      // Wait condition is constant
        WIDTH,          // Width mismatch
        WIDTHCONCAT,    // Unsized numbers/parameters in concatenations
        WIDTHEXPAND,    // Width mismatch- lhs > rhs
        WIDTHTRUNC,     // Width mismatch- lhs < rhs
        WIDTHXZEXPAND,  // Width mismatch- lhs > rhs xz filled
        ZERODLY,        // #0 delay
        _ENUM_MAX
        // ***Add new elements below also***
    };
    // clang-format on
    enum en m_e;
    V3ErrorCode()
        : m_e{EC_MIN} {}
    // cppcheck-suppress noExplicitConstructor
    constexpr V3ErrorCode(en _e)
        : m_e{_e} {}
    explicit V3ErrorCode(const char* msgp);  // Matching code or ERROR
    explicit V3ErrorCode(int _e)
        : m_e(static_cast<en>(_e)) {}  // Need () or GCC 4.8 false warning
    constexpr operator en() const VL_MT_SAFE { return m_e; }
    const char* ascii() const VL_MT_SAFE {
        // clang-format off
        static const char* const names[] = {
            // Leading spaces indicate it can't be disabled.
            " MIN", " INFO", " FATAL", " FATALEXIT", " FATALSRC", " ERROR", " FIRST_NAMED",
            // Boolean
            " I_CELLDEFINE", " I_COVERAGE",  " I_DEF_NETTYPE_WIRE", " I_LINT", " I_TIMING", " I_TRACING", " I_UNUSED",
            // Errors
            "LIFETIME", "NEEDTIMINGOPT", "NOTIMING", "PORTSHORT", "TASKNSVAR", "UNSUPPORTED",
            // Warnings
            " EC_FIRST_WARN",
            "ALWCOMBORDER", "ASCRANGE", "ASSIGNDLY", "ASSIGNIN", "BADSTDPRAGMA",
            "BLKANDNBLK", "BLKLOOPINIT", "BLKSEQ", "BSSPACE",
            "CASEINCOMPLETE", "CASEOVERLAP", "CASEWITHX", "CASEX", "CASTCONST", "CDCRSTLOGIC", "CLKDATA",
            "CMPCONST", "COLONPLUS", "COMBDLY", "CONSTRAINTIGN", "CONTASSREG",
            "DECLFILENAME", "DEFPARAM", "DEPRECATED",
            "ENCAPSULATED", "ENDLABEL", "ENUMVALUE", "EOFNEWLINE", "GENCLK", "GENUNNAMED",
            "HIERBLOCK",
            "IFDEPTH", "IGNOREDRETURN",
            "IMPERFECTSCH", "IMPLICIT", "IMPLICITSTATIC", "IMPORTSTAR", "IMPURE",
            "INCABSPATH", "INFINITELOOP", "INITIALDLY", "INSECURE",
            "LATCH", "LITENDIAN", "MINTYPMAXDLY", "MISINDENT", "MODDUP",
            "MULTIDRIVEN", "MULTITOP", "NEWERSTD", "NOLATCH", "NULLPORT", "PINCONNECTEMPTY",
            "PINMISSING", "PINNOCONNECT",  "PINNOTFOUND", "PKGNODECL", "PROCASSWIRE",
            "PROFOUTOFDATE", "PROTECTED", "RANDC", "REALCVT", "REDEFMACRO", "RISEFALLDLY",
            "SELRANGE", "SHORTREAL", "SPLITVAR", "STATICVAR", "STMTDLY", "SYMRSVDWORD", "SYNCASYNCNET",
            "TICKCOUNT", "TIMESCALEMOD",
            "UNDRIVEN", "UNOPT", "UNOPTFLAT", "UNOPTTHREADS",
            "UNPACKED", "UNSIGNED", "UNUSEDGENVAR", "UNUSEDPARAM", "UNUSEDSIGNAL",
            "USERERROR", "USERFATAL", "USERINFO", "USERWARN",
            "VARHIDDEN", "WAITCONST", "WIDTH", "WIDTHCONCAT",  "WIDTHEXPAND", "WIDTHTRUNC", "WIDTHXZEXPAND", "ZERODLY",
            " MAX"
        };
        // clang-format on
        return names[m_e];
    }
    // Warnings that default to off
    bool defaultsOff() const VL_MT_SAFE {
        return (m_e == IMPERFECTSCH || m_e == I_CELLDEFINE || styleError());
    }
    // Warnings that warn about nasty side effects
    bool dangerous() const VL_MT_SAFE { return (m_e == COMBDLY); }
    // Warnings we'll present to the user as errors
    // Later -Werror- options may make more of these.
    bool pretendError() const VL_MT_SAFE {
        return (m_e == ASSIGNIN || m_e == BADSTDPRAGMA || m_e == BLKANDNBLK || m_e == BLKLOOPINIT
                || m_e == CONTASSREG || m_e == ENCAPSULATED || m_e == ENDLABEL || m_e == ENUMVALUE
                || m_e == IMPURE || m_e == PINNOTFOUND || m_e == PKGNODECL
                || m_e == PROCASSWIRE  // Says IEEE
        );
    }
    // Warnings to mention manual
    bool mentionManual() const VL_MT_SAFE {
        return (m_e == EC_FATALSRC || m_e == SYMRSVDWORD || m_e == ZERODLY || pretendError());
    }
    // Warnings that are lint only
    bool lintError() const VL_MT_SAFE {
        return (m_e == ALWCOMBORDER || m_e == ASCRANGE || m_e == BSSPACE || m_e == CASEINCOMPLETE
                || m_e == CASEOVERLAP || m_e == CASEWITHX || m_e == CASEX || m_e == CASTCONST
                || m_e == CMPCONST || m_e == COLONPLUS || m_e == IMPLICIT || m_e == IMPLICITSTATIC
                || m_e == LATCH || m_e == MISINDENT || m_e == NEWERSTD || m_e == PINMISSING
                || m_e == REALCVT || m_e == STATICVAR || m_e == UNSIGNED || m_e == WIDTH
                || m_e == WIDTHTRUNC || m_e == WIDTHEXPAND || m_e == WIDTHXZEXPAND);
    }
    // Warnings that are style only
    bool styleError() const VL_MT_SAFE {
        return (m_e == ASSIGNDLY  // More than style, but for backward compatibility
                || m_e == BLKSEQ || m_e == DEFPARAM || m_e == DECLFILENAME || m_e == EOFNEWLINE
                || m_e == GENUNNAMED || m_e == IMPORTSTAR || m_e == INCABSPATH
                || m_e == PINCONNECTEMPTY || m_e == PINNOCONNECT || m_e == SYNCASYNCNET
                || m_e == UNDRIVEN || m_e == UNUSEDGENVAR || m_e == UNUSEDPARAM
                || m_e == UNUSEDSIGNAL || m_e == VARHIDDEN);
    }
    // Warnings that are unused only
    bool unusedError() const VL_MT_SAFE {
        return (m_e == UNUSEDGENVAR || m_e == UNUSEDPARAM || m_e == UNUSEDSIGNAL);
    }

    V3ErrorCode renamedTo() const {
        // Return a new error this error has been renamed to
        if (m_e == LITENDIAN) return V3ErrorCode{ASCRANGE};
        return V3ErrorCode{EC_MIN};  // Not renamed; see isRenamed()
    }
    bool isRenamed() const { return renamedTo() != V3ErrorCode{EC_MIN}; }
    bool isUnder(V3ErrorCode other) {
        // backwards compatibility inheritance-like warnings
        if (m_e == other) { return true; }
        if (other == V3ErrorCode::WIDTH) {
            return (m_e == WIDTHEXPAND || m_e == WIDTHTRUNC || m_e == WIDTHXZEXPAND);
        }
        if (other == V3ErrorCode::I_UNUSED) {
            return (m_e == UNUSEDGENVAR || m_e == UNUSEDPARAM || m_e == UNUSEDSIGNAL);
        }
        return false;
    }

    static bool unusedMsg(const char* msgp) { return 0 == VL_STRCASECMP(msgp, "UNUSED"); }
};
constexpr bool operator==(const V3ErrorCode& lhs, const V3ErrorCode& rhs) {
    return lhs.m_e == rhs.m_e;
}
constexpr bool operator==(const V3ErrorCode& lhs, V3ErrorCode::en rhs) { return lhs.m_e == rhs; }
constexpr bool operator==(V3ErrorCode::en lhs, const V3ErrorCode& rhs) { return lhs == rhs.m_e; }
inline std::ostream& operator<<(std::ostream& os, const V3ErrorCode& rhs) {
    return os << rhs.ascii();
}

// ######################################################################
class V3Error;

class V3ErrorGuarded final {
    // Should only be used by V3ErrorGuarded::m_mutex is already locked
    // contains guarded members
    friend class V3Error;

public:
    using MessagesSet = std::set<std::string>;
    using ErrorExitCb = void (*)(void);

private:
    static constexpr unsigned MAX_ERRORS = 50;  // Fatal after this may errors

    bool m_describedWarnings VL_GUARDED_BY(m_mutex) = false;  // Told user how to disable warns
    // Tell user to see manual, 0=not yet, 1=doit, 2=disable
    int m_tellManual VL_GUARDED_BY(m_mutex) = 0;
    V3ErrorCode m_errorCode VL_GUARDED_BY(m_mutex)
        = V3ErrorCode::EC_FATAL;  // Error string being formed will abort
    bool m_errorSuppressed VL_GUARDED_BY(m_mutex)
        = false;  // Error being formed should be suppressed
    MessagesSet m_messages VL_GUARDED_BY(m_mutex);  // What errors we've outputted
    ErrorExitCb m_errorExitCb VL_GUARDED_BY(m_mutex)
        = nullptr;  // Callback when error occurs for dumping
    bool m_errorContexted VL_GUARDED_BY(m_mutex) = false;  // Error being formed got context
    int m_warnCount VL_GUARDED_BY(m_mutex) = 0;  // Warning count
    int m_errCount VL_GUARDED_BY(m_mutex) = 0;  // Error count
    // Pretend this warning is an error
    std::array<bool, V3ErrorCode::_ENUM_MAX> m_pretendError VL_GUARDED_BY(m_mutex);
    bool m_describedWeb VL_GUARDED_BY(m_mutex) = false;  // Told user to see web
    // Told user specifics about this warning
    std::array<bool, V3ErrorCode::_ENUM_MAX> m_describedEachWarn VL_GUARDED_BY(m_mutex);
    int m_debugDefault = 0;  // Option: --debugi Default debugging level
    int m_errorLimit VL_GUARDED_BY(m_mutex)
        = MAX_ERRORS;  // Option: --error-limit Number of errors before exit
    bool m_warnFatal VL_GUARDED_BY(m_mutex) = true;  // Option: --warnFatal Warnings are fatal
    std::ostringstream m_errorStr VL_GUARDED_BY(m_mutex);  // Error string being formed

    void v3errorPrep(V3ErrorCode code) VL_REQUIRES(m_mutex) {
        m_errorStr.str("");
        m_errorCode = code;
        m_errorContexted = false;
        m_errorSuppressed = false;
    }
    std::ostringstream& v3errorStr() VL_REQUIRES(m_mutex) { return m_errorStr; }
    void v3errorEnd(std::ostringstream& sstr, const string& extra = "") VL_REQUIRES(m_mutex);

public:
    V3RecursiveMutex m_mutex;  // Make sure only single thread is in class

    string msgPrefix() VL_REQUIRES(m_mutex);  // returns %Error/%Warn
    string warnMore() VL_REQUIRES(m_mutex);
    void execErrorExitCb() VL_REQUIRES(m_mutex) {
        if (m_errorExitCb) m_errorExitCb();
    }
    void errorExitCb(ErrorExitCb cb) VL_REQUIRES(m_mutex) { m_errorExitCb = cb; }
    ErrorExitCb errorExitCb() VL_REQUIRES(m_mutex) { return m_errorExitCb; }
    bool isError(V3ErrorCode code, bool supp) VL_REQUIRES(m_mutex);
    void vlAbortOrExit() VL_REQUIRES(m_mutex);
    void errorContexted(bool flag) VL_REQUIRES(m_mutex) { m_errorContexted = flag; }
    void incWarnings() VL_REQUIRES(m_mutex) { m_warnCount++; }
    void incErrors() VL_REQUIRES(m_mutex) {
        m_errCount++;
        if (errorCount() == errorLimit()) {  // Not >= as would otherwise recurse
            v3errorEnd(
                (v3errorPrep(V3ErrorCode::EC_FATALEXIT),
                 (v3errorStr() << "Exiting due to too many errors encountered; --error-limit="
                               << errorCount() << std::endl),
                 v3errorStr()));
            assert(0);  // LCOV_EXCL_LINE
            VL_UNREACHABLE;
        }
    }
    int errorCount() VL_REQUIRES(m_mutex) { return m_errCount; }
    bool pretendError(int errorCode) VL_REQUIRES(m_mutex) { return m_pretendError[errorCode]; }
    void pretendError(V3ErrorCode code, bool flag) VL_REQUIRES(m_mutex) {
        if (code == V3ErrorCode::WIDTH) {
            m_pretendError[V3ErrorCode::WIDTHTRUNC] = flag;
            m_pretendError[V3ErrorCode::WIDTHEXPAND] = flag;
            m_pretendError[V3ErrorCode::WIDTHXZEXPAND] = flag;
        }
        m_pretendError[code] = flag;
    }
    void debugDefault(int level) VL_MT_UNSAFE { m_debugDefault = level; }
    int debugDefault() VL_MT_SAFE { return m_debugDefault; }
    void errorLimit(int level) VL_REQUIRES(m_mutex) { m_errorLimit = level; }
    int errorLimit() VL_REQUIRES(m_mutex) { return m_errorLimit; }
    void warnFatal(bool flag) VL_REQUIRES(m_mutex) { m_warnFatal = flag; }
    bool warnFatal() VL_REQUIRES(m_mutex) { return m_warnFatal; }
    V3ErrorCode errorCode() VL_REQUIRES(m_mutex) { return m_errorCode; }
    bool errorContexted() VL_REQUIRES(m_mutex) { return m_errorContexted; }
    int warnCount() VL_REQUIRES(m_mutex) { return m_warnCount; }
    bool errorSuppressed() VL_REQUIRES(m_mutex) { return m_errorSuppressed; }
    void errorSuppressed(bool flag) VL_REQUIRES(m_mutex) { m_errorSuppressed = flag; }
    bool describedWeb() VL_REQUIRES(m_mutex) { return m_describedWeb; }
    void describedWeb(bool flag) VL_REQUIRES(m_mutex) { m_describedWeb = flag; }
    bool describedEachWarn(V3ErrorCode code) VL_REQUIRES(m_mutex) {
        return m_describedEachWarn[code];
    }
    void describedEachWarn(V3ErrorCode code, bool flag) VL_REQUIRES(m_mutex) {
        m_describedEachWarn[code] = flag;
    }
    bool describedWarnings() VL_REQUIRES(m_mutex) { return m_describedWarnings; }
    void describedWarnings(bool flag) VL_REQUIRES(m_mutex) { m_describedWarnings = flag; }
    int tellManual() VL_REQUIRES(m_mutex) { return m_tellManual; }
    void tellManual(int level) VL_REQUIRES(m_mutex) { m_tellManual = level; }
    void suppressThisWarning() VL_REQUIRES(m_mutex);
    string warnContextNone() VL_REQUIRES(m_mutex) {
        errorContexted(true);
        return "";
    }
};

// ######################################################################
class V3Error final {
    // Base class for any object that wants debugging and error reporting
private:
    // CONSTRUCTORS
    V3Error() {
        std::cerr << ("Static class");
        V3Error::vlAbort();
    }

public:
    static V3ErrorGuarded& s() VL_MT_SAFE {  // Singleton
        static V3ErrorGuarded s_s;
        return s_s;
    }

    // ACCESSORS
    static void debugDefault(int level) VL_MT_UNSAFE { s().debugDefault(level); }
    static int debugDefault() VL_MT_SAFE { return s().debugDefault(); }
    static void errorLimit(int level) VL_MT_SAFE_EXCLUDES(s().m_mutex) {
        const V3RecursiveLockGuard guard{s().m_mutex};
        s().errorLimit(level);
    }
    static int errorLimit() VL_MT_SAFE_EXCLUDES(s().m_mutex) {
        const V3RecursiveLockGuard guard{s().m_mutex};
        return s().errorLimit();
    }
    static void warnFatal(bool flag) VL_MT_SAFE_EXCLUDES(s().m_mutex) {
        const V3RecursiveLockGuard guard{s().m_mutex};
        s().warnFatal(flag);
    }
    static bool warnFatal() VL_MT_SAFE_EXCLUDES(s().m_mutex) {
        const V3RecursiveLockGuard guard{s().m_mutex};
        return s().warnFatal();
    }
    // returns %Error/%Warn
    static string msgPrefix() VL_MT_SAFE_EXCLUDES(s().m_mutex) {
        const V3RecursiveLockGuard guard{s().m_mutex};
        return s().msgPrefix();
    }
    static int errorCount() VL_MT_SAFE_EXCLUDES(s().m_mutex) {
        const V3RecursiveLockGuard guard{s().m_mutex};
        return s().errorCount();
    }
    static bool pretendError(int errorCode) VL_MT_SAFE_EXCLUDES(s().m_mutex) {
        const V3RecursiveLockGuard guard{s().m_mutex};
        return s().pretendError(errorCode);
    }
    static int warnCount() VL_MT_SAFE_EXCLUDES(s().m_mutex) {
        const V3RecursiveLockGuard guard{s().m_mutex};
        return s().warnCount();
    }
    static bool errorContexted() VL_MT_SAFE_EXCLUDES(s().m_mutex) {
        const V3RecursiveLockGuard guard{s().m_mutex};
        return s().errorContexted();
    }
    static void errorContexted(bool flag) VL_MT_SAFE_EXCLUDES(s().m_mutex) {
        const V3RecursiveLockGuard guard{s().m_mutex};
        s().errorContexted(flag);
    }
    static void describedEachWarn(V3ErrorCode code, bool flag) VL_MT_SAFE_EXCLUDES(s().m_mutex) {
        const V3RecursiveLockGuard guard{s().m_mutex};
        s().describedEachWarn(code, flag);
    }
    // METHODS
    static void incErrors() VL_MT_SAFE_EXCLUDES(s().m_mutex) {
        const V3RecursiveLockGuard guard{s().m_mutex};
        s().incErrors();
    }
    static void incWarnings() VL_MT_SAFE_EXCLUDES(s().m_mutex) {
        const V3RecursiveLockGuard guard{s().m_mutex};
        s().incWarnings();
    }
    static void init();
    static void abortIfErrors() {
        if (errorCount()) abortIfWarnings();
    }
    static void abortIfWarnings();
    // Suppress next %Warn if user has it off
    static void suppressThisWarning() VL_MT_SAFE_EXCLUDES(s().m_mutex) {
        const V3RecursiveLockGuard guard{s().m_mutex};
        s().suppressThisWarning();
    }
    static void pretendError(V3ErrorCode code, bool flag) VL_MT_SAFE_EXCLUDES(s().m_mutex) {
        const V3RecursiveLockGuard guard{s().m_mutex};
        s().pretendError(code, flag);
    }
    static string lineStr(const char* filename, int lineno) VL_PURE;
    static V3ErrorCode errorCode() VL_MT_SAFE_EXCLUDES(s().m_mutex) {
        const V3RecursiveLockGuard guard{s().m_mutex};
        return s().errorCode();
    }
    static void errorExitCb(V3ErrorGuarded::ErrorExitCb cb) VL_MT_SAFE_EXCLUDES(s().m_mutex) {
        const V3RecursiveLockGuard guard{s().m_mutex};
        s().errorExitCb(cb);
    }

    // When printing an error/warning, print prefix for multiline message
    static string warnMore() VL_REQUIRES(s().m_mutex) { return s().warnMore(); }
    // This function should only be used when it is impossible to
    // generate whole error message inside v3warn macros and it needs to be
    // streamed directly to cerr.
    // Use with caution as this function isn't MT_SAFE.
    static string warnMoreStandalone() VL_EXCLUDES(s().m_mutex) VL_MT_UNSAFE {
        const V3RecursiveLockGuard guard{s().m_mutex};
        return s().warnMore();
    }
    // This function marks place in error message from which point message
    // should be printed after information on the error code.
    // The post-processing is done in v3errorEnd function.
    static string warnAdditionalInfo() VL_MT_SAFE { return "__WARNADDITIONALINFO__"; }
    /// When building an error, don't show context info
    static string warnContextNone() {
        V3Error::errorContexted(true);
        return "";
    }

    // Internals for v3error()/v3fatal() macros only
    // Error end takes the string stream to output, be careful to seek() as needed
    static void v3errorAcquireLock() VL_ACQUIRE(s().m_mutex);
    static std::ostringstream& v3errorPrep(V3ErrorCode code) VL_ACQUIRE(s().m_mutex);
    static std::ostringstream& v3errorPrepFileLine(V3ErrorCode code, const char* file, int line)
        VL_ACQUIRE(s().m_mutex);
    static std::ostringstream& v3errorStr() VL_REQUIRES(s().m_mutex);
    // static, but often overridden in classes.
    static void v3errorEnd(std::ostringstream& sstr, const string& extra = "")
        VL_RELEASE(s().m_mutex);
    static void vlAbort();
};

// Global versions, so that if the class doesn't define an operator, we get the functions anyway.
void v3errorEnd(std::ostringstream& sstr) VL_RELEASE(V3Error::s().m_mutex);
void v3errorEndFatal(std::ostringstream& sstr) VL_RELEASE(V3Error::s().m_mutex);

// Theses allow errors using << operators: v3error("foo"<<"bar");
// Careful, you can't put () around msg, as you would in most macro definitions.
// 'V3Error::v3errorPrep(code) << msg' could be more efficient but the order of function calls in a
// single statement can be arbitrary until C++17, thus make it possible to execute
// V3Error::v3errorPrep that acquires the lock after functions in the msg may require it. So we use
// the comma operator (,) to guarantee the execution order here.
#define v3errorBuildMessage(prep, msg) \
    (prep, static_cast<std::ostringstream&>(V3Error::v3errorStr() << msg))
#define v3warnCode(code, msg) v3errorEnd(v3errorBuildMessage(V3Error::v3errorPrep(code), msg))
#define v3warnCodeFatal(code, msg) \
    v3errorEndFatal(v3errorBuildMessage(V3Error::v3errorPrep(code), msg))
#define v3warn(code, msg) v3warnCode(V3ErrorCode::code, msg)
#define v3info(msg) v3warnCode(V3ErrorCode::EC_INFO, msg)
#define v3error(msg) v3warnCode(V3ErrorCode::EC_ERROR, msg)
#define v3fatal(msg) v3warnCodeFatal(V3ErrorCode::EC_FATAL, msg)
// Use this instead of fatal() if message gets suppressed with --quiet-exit
#define v3fatalExit(msg) v3warnCodeFatal(V3ErrorCode::EC_FATALEXIT, msg)
// Use this instead of fatal() to mention the source code line.
#define v3fatalSrc(msg) \
    v3errorEndFatal(v3errorBuildMessage( \
        V3Error::v3errorPrepFileLine(V3ErrorCode::EC_FATALSRC, __FILE__, __LINE__), msg))
// Use this when normal v3fatal is called in static method that overrides fileline.
#define v3fatalStatic(msg) \
    ::v3errorEndFatal(v3errorBuildMessage(V3Error::v3errorPrep(V3ErrorCode::EC_FATAL), msg))

#define UINFO(level, stmsg) \
    do { \
        if (VL_UNCOVERABLE(debug() >= (level))) { \
            std::cout << "- " << V3Error::lineStr(__FILE__, __LINE__) << stmsg; \
        } \
    } while (false)
#define UINFONL(level, stmsg) \
    do { \
        if (VL_UNCOVERABLE(debug() >= (level))) { std::cout << stmsg; } \
    } while (false)

#ifdef VL_DEBUG
#define UDEBUGONLY(stmts) \
    do { stmts } while (false)
#else
#define UDEBUGONLY(stmts) \
    do { \
        if (false) { stmts } \
    } while (false)
#endif

// Assertion without object, generally UOBJASSERT preferred
#define UASSERT(condition, stmsg) \
    do { \
        if (VL_UNCOVERABLE(!(condition))) v3fatalSrc(stmsg); \
    } while (false)
// Assertion with object
#define UASSERT_OBJ(condition, obj, stmsg) \
    do { \
        if (VL_UNCOVERABLE(!(condition))) (obj)->v3fatalSrc(stmsg); \
    } while (false)
// For use in V3Ast static functions only
#define UASSERT_STATIC(condition, stmsg) \
    do { \
        if (VL_UNCOVERABLE(!(condition))) { \
            std::cerr << "Internal Error: " << __FILE__ << ":" << std::dec << __LINE__ << ":" \
                      << (stmsg) << std::endl; \
            V3Error::vlAbort(); \
        } \
    } while (false)
// Check self test values for expected value.  Safe from side-effects.
// Type argument can be removed when go to C++11 (use auto).
#define UASSERT_SELFTEST(Type, got, exp) \
    do { \
        Type g = (got); \
        Type e = (exp); \
        UASSERT(g == e, "Self-test failed '" #got "==" #exp "'" \
                        " got=" \
                            << g << " expected=" << e); \
    } while (false)

#define V3ERROR_NA \
    do { \
        v3error("Internal: Unexpected Call"); \
        v3fatalSrc("Unexpected Call"); \
    } while (false)

/// Throw fatal and return a value. The return value will never really be
/// needed, but required to avoid compiler error.
#define V3ERROR_NA_RETURN(value) \
    V3ERROR_NA; \
    return value

// Helper macros for VL_DEFINE_DEBUG_FUNCTIONS
// Takes an optional "name" (as __VA_ARGS__)
#define VL_DEFINE_DEBUG(...) \
    VL_ATTR_UNUSED static int debug##__VA_ARGS__() VL_MT_SAFE { \
        static int level = -1; \
        if (VL_UNLIKELY(level < 0)) { \
            std::string tag{VL_STRINGIFY(__VA_ARGS__)}; \
            tag[0] = std::tolower(tag[0]); \
            const unsigned debugTag = v3Global.opt.debugLevel(tag); \
            const unsigned debugSrc = v3Global.opt.debugSrcLevel(__FILE__); \
            const unsigned debugLevel = debugTag >= debugSrc ? debugTag : debugSrc; \
            if (!v3Global.opt.available()) return static_cast<int>(debugLevel); \
            level = static_cast<int>(debugLevel); \
        } \
        return level; \
    } \
    static_assert(true, "")

// Takes an optional "name" (as __VA_ARGS__)
#define VL_DEFINE_DUMP(func, tag) \
    VL_ATTR_UNUSED static int dump##func() { \
        static int level = -1; \
        if (VL_UNLIKELY(level < 0)) { \
            const unsigned dumpTag = v3Global.opt.dumpLevel(tag); \
            const unsigned dumpSrc = v3Global.opt.dumpSrcLevel(__FILE__); \
            const unsigned dumpLevel = dumpTag >= dumpSrc ? dumpTag : dumpSrc; \
            if (!v3Global.opt.available()) return static_cast<int>(dumpLevel); \
            level = static_cast<int>(dumpLevel); \
        } \
        return level; \
    } \
    static_assert(true, "")

// Define debug*() and dump*() routines. This needs to be added to every compilation unit so that
// --debugi-<tag/srcfile> and --dumpi-<tag/srcfile> can be used to control debug prints and dumping
#define VL_DEFINE_DEBUG_FUNCTIONS \
    VL_DEFINE_DEBUG(); /* Define 'int debug()' for --debugi */ \
    VL_DEFINE_DUMP(Level, ""); /* Define 'int dumpLevel()' for --dumpi */ \
    VL_DEFINE_DUMP(DfgLevel, "dfg"); /* Define 'int dumpDfgLevel()' for --dumpi-level */ \
    VL_DEFINE_DUMP(GraphLevel, "graph"); /* Define 'int dumpGraphLevel()' for dumpi-graph */ \
    VL_DEFINE_DUMP(TreeLevel, "tree"); /* Define 'int dumpTreeLevel()' for dumpi-tree */ \
    static_assert(true, "")

//----------------------------------------------------------------------

#endif  // Guard
