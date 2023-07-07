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

// clang-format off
#include "V3Error.h"
#ifndef V3ERROR_NO_GLOBAL_
# include "V3Ast.h"
# include "V3Global.h"
# include "V3Stats.h"
VL_DEFINE_DEBUG_FUNCTIONS;
#endif
// clang-format on

//======================================================================

struct v3errorIniter {
    v3errorIniter() { V3Error::init(); }
};
v3errorIniter v3errorInit;

//######################################################################
// ErrorCode class functions

V3ErrorCode::V3ErrorCode(const char* msgp) {
    // Return error encoding for given string, or ERROR, which is a bad code
    for (int codei = V3ErrorCode::EC_MIN; codei < V3ErrorCode::_ENUM_MAX; codei++) {
        const V3ErrorCode code{codei};
        if (0 == VL_STRCASECMP(msgp, code.ascii())) {
            m_e = code;
            if (isRenamed()) m_e = renamedTo().m_e;
            return;
        }
    }
    m_e = V3ErrorCode::EC_ERROR;
}

//######################################################################
// V3ErrorGuarded class functions
//

bool V3ErrorGuarded::isError(V3ErrorCode code, bool supp) VL_REQUIRES(m_mutex) {
    if (supp) {
        return false;
    } else if (code == V3ErrorCode::USERINFO) {
        return false;
    } else if (code == V3ErrorCode::EC_INFO) {
        return false;
    } else if (code == V3ErrorCode::EC_FATAL) {
        return true;
    } else if (code == V3ErrorCode::EC_FATALEXIT) {
        return true;
    } else if (code == V3ErrorCode::EC_FATALSRC) {
        return true;
    } else if (code == V3ErrorCode::EC_ERROR) {
        return true;
    } else if (code < V3ErrorCode::EC_FIRST_WARN || pretendError(code)) {
        return true;
    } else {
        return false;
    }
}

string V3ErrorGuarded::msgPrefix() VL_REQUIRES(m_mutex) {
    const V3ErrorCode code = m_errorCode;
    const bool supp = m_errorSuppressed;
    if (supp) {
        return "-arning-suppressed: ";
    } else if (code == V3ErrorCode::USERINFO) {
        return "-Info: ";
    } else if (code == V3ErrorCode::EC_INFO) {
        return "-Info: ";
    } else if (code == V3ErrorCode::EC_FATAL) {
        return "%Error: ";
    } else if (code == V3ErrorCode::EC_FATALEXIT) {
        return "%Error: ";
    } else if (code == V3ErrorCode::EC_FATALSRC) {
        return "%Error: Internal Error: ";
    } else if (code == V3ErrorCode::EC_ERROR) {
        return "%Error: ";
    } else if (isError(code, supp)) {
        return "%Error-" + std::string{code.ascii()} + ": ";
    } else {
        return "%Warning-" + std::string{code.ascii()} + ": ";
    }
}

void V3ErrorGuarded::vlAbortOrExit() VL_REQUIRES(m_mutex) {
    if (V3Error::debugDefault()) {
        std::cerr << msgPrefix() << "Aborting since under --debug" << endl;
        V3Error::vlAbort();
    } else {
        std::exit(1);
    }
}

string V3ErrorGuarded::warnMore() VL_REQUIRES(m_mutex) { return string(msgPrefix().size(), ' '); }

void V3ErrorGuarded::suppressThisWarning() VL_REQUIRES(m_mutex) {
#ifndef V3ERROR_NO_GLOBAL_
    V3Stats::addStatSum(std::string{"Warnings, Suppressed "} + errorCode().ascii(), 1);
#endif
    errorSuppressed(true);
}

// cppcheck-has-bug-suppress constParameter
void V3ErrorGuarded::v3errorEnd(std::ostringstream& sstr, const string& extra)
    VL_REQUIRES(m_mutex) {
#if defined(__COVERITY__) || defined(__cppcheck__)
    if (m_errorCode == V3ErrorCode::EC_FATAL) __coverity_panic__(x);
#endif
    // Skip suppressed messages
    if (m_errorSuppressed
        // On debug, show only non default-off warning to prevent pages of warnings
        && (!debug() || m_errorCode.defaultsOff()))
        return;
    string msg = msgPrefix() + sstr.str();
    // If suppressed print only first line to reduce verbosity
    if (m_errorSuppressed) {
        string::size_type pos;
        if ((pos = msg.find('\n')) != string::npos) {
            msg.erase(pos, msg.length() - pos);
            msg += "...";
        }
    }
    string msg_additional;
    {
        string::size_type pos;
        if ((pos = msg.find(V3Error::warnAdditionalInfo())) != string::npos) {
            msg_additional = msg.substr(pos + V3Error::warnAdditionalInfo().size());
            msg.erase(pos);
        }
    }
    // Trailing newline (generally not on messages) & remove dup newlines
    {
        msg += '\n';  // Trailing newlines generally not put on messages so add
        string::size_type pos;
        while ((pos = msg.find("\n\n")) != string::npos) msg.erase(pos + 1, 1);
        while ((pos = msg_additional.find("\n\n")) != string::npos)
            msg_additional.erase(pos + 1, 1);
    }
    // Suppress duplicate messages
    if (!m_messages.insert(msg).second) return;
    if (!extra.empty()) {
        const string extraMsg = warnMore() + extra + "\n";
        const size_t pos = msg.find('\n');
        msg.insert(pos + 1, extraMsg);
    }
    // Output
    if (
#ifndef V3ERROR_NO_GLOBAL_
        !(v3Global.opt.quietExit() && m_errorCode == V3ErrorCode::EC_FATALEXIT)
#else
        true
#endif
    ) {
        std::cerr << msg;
    }
    if (!m_errorSuppressed
        && !(m_errorCode == V3ErrorCode::EC_INFO || m_errorCode == V3ErrorCode::USERINFO)) {
        const bool anError = isError(m_errorCode, m_errorSuppressed);
        if (m_errorCode >= V3ErrorCode::EC_FIRST_NAMED && !m_describedWeb) {
            m_describedWeb = true;
            std::cerr << warnMore() << "... For " << (anError ? "error" : "warning")
                      << " description see https://verilator.org/warn/" << m_errorCode.ascii()
                      << "?v=" << PACKAGE_VERSION_NUMBER_STRING << endl;
        }
        if (!m_describedEachWarn[m_errorCode] && !m_pretendError[m_errorCode]) {
            m_describedEachWarn[m_errorCode] = true;
            if (m_errorCode >= V3ErrorCode::EC_FIRST_WARN && !m_describedWarnings) {
                m_describedWarnings = true;
                std::cerr << warnMore() << "... Use \"/* verilator lint_off "
                          << m_errorCode.ascii()
                          << " */\" and lint_on around source to disable this message." << endl;
            }
            if (m_errorCode.dangerous()) {
                std::cerr << warnMore() << "*** See https://verilator.org/warn/"
                          << m_errorCode.ascii() << " before disabling this,\n";
                std::cerr << warnMore() << "else you may end up with different sim results."
                          << endl;
            }
        }
        if (!msg_additional.empty()) { std::cerr << msg_additional; }
        // If first warning is not the user's fault (internal/unsupported) then give the website
        // Not later warnings, as a internal may be caused by an earlier problem
        if (tellManual() == 0) {
            if (m_errorCode.mentionManual() || sstr.str().find("Unsupported") != string::npos) {
                tellManual(1);
            } else {
                tellManual(2);
            }
        }
        if (anError) {
            incErrors();
        } else {
            incWarnings();
        }
        if (m_errorCode == V3ErrorCode::EC_FATAL || m_errorCode == V3ErrorCode::EC_FATALEXIT
            || m_errorCode == V3ErrorCode::EC_FATALSRC) {
            static bool inFatal = false;
            if (!inFatal) {
                inFatal = true;
                if (tellManual() == 1) {
                    std::cerr << warnMore()
                              << "... See the manual at https://verilator.org/verilator_doc.html "
                                 "for more assistance."
                              << endl;
                    tellManual(2);
                }
#ifndef V3ERROR_NO_GLOBAL_
                if (dumpTreeLevel() || debug()) {
                    V3Broken::allowMidvisitorCheck(true);
                    const V3ThreadPool::ScopedExclusiveAccess exclusiveAccess;
                    if (dumpTreeLevel()) {
                        v3Global.rootp()->dumpTreeFile(v3Global.debugFilename("final.tree", 990));
                    }
                    if (debug()) {
                        execErrorExitCb();
                        V3Stats::statsFinalAll(v3Global.rootp());
                        V3Stats::statsReport();
                    }
                    // Abort in exclusive access to make sure other threads
                    // don't change error code
                    vlAbortOrExit();
                }
#endif
            }

            vlAbortOrExit();
        } else if (anError) {
            // We don't dump tree on any error because a Visitor may be in middle of
            // a tree cleanup and cause a false broken problem.
            execErrorExitCb();
        }
    }
}

//######################################################################
// V3Error class functions

void V3Error::init() {
    for (int i = 0; i < V3ErrorCode::_ENUM_MAX; i++) {
        describedEachWarn(static_cast<V3ErrorCode>(i), false);
        pretendError(static_cast<V3ErrorCode>(i), V3ErrorCode{i}.pretendError());
    }
    if (VL_UNCOVERABLE(string{V3ErrorCode{V3ErrorCode::_ENUM_MAX}.ascii()} != " MAX")) {
        v3fatalSrc("Enum table in V3ErrorCode::EC_ascii() is munged");
    }
}

string V3Error::lineStr(const char* filename, int lineno) VL_PURE {
    std::ostringstream out;
    const char* const fnslashp = std::strrchr(filename, '/');
    if (fnslashp) filename = fnslashp + 1;
    out << filename << ":" << std::dec << lineno << ":";
    const char* const spaces = "                    ";
    size_t numsp = out.str().length();
    if (numsp > 20) numsp = 20;
    out << (spaces + numsp);
    return out.str();
}

void V3Error::abortIfWarnings() {
    const bool exwarn = warnFatal() && warnCount();
    if (errorCount() && exwarn) {
        v3fatalExit("Exiting due to " << std::dec << V3Error::s().errorCount() << " error(s), "  //
                                      << V3Error::s().warnCount() << " warning(s)\n");
    } else if (errorCount()) {
        v3fatalExit("Exiting due to " << std::dec << V3Error::s().errorCount() << " error(s)\n");
    } else if (exwarn) {
        v3fatalExit("Exiting due to " << std::dec << V3Error::s().warnCount() << " warning(s)\n");
    }
}

//======================================================================
// Abort/exit

void V3Error::vlAbort() {
    VL_GCOV_DUMP();
    std::abort();
}
void V3Error::v3errorAcquireLock(bool mtDisabledCodeUnit) VL_ACQUIRE(s().m_mutex) {
#if !defined(V3ERROR_NO_GLOBAL_)
    if (!mtDisabledCodeUnit) {
        V3Error::s().m_mutex.lockCheckStopRequest(
            []() -> void { V3ThreadPool::s().waitIfStopRequested(); });
    } else {
        V3Error::s().m_mutex.lock();
    }
#else
    V3Error::s().m_mutex.lock();
#endif
}
std::ostringstream& V3Error::v3errorPrep(V3ErrorCode code, bool mtDisabledCodeUnit)
    VL_ACQUIRE(s().m_mutex) {
    v3errorAcquireLock(mtDisabledCodeUnit);
    s().v3errorPrep(code);
    return v3errorStr();
}
std::ostringstream& V3Error::v3errorPrepFileLine(V3ErrorCode code, const char* file, int line,
                                                 bool mtDisabledCodeUnit) VL_ACQUIRE(s().m_mutex) {
    v3errorPrep(code, mtDisabledCodeUnit) << file << ":" << std::dec << line << ": ";
    return v3errorStr();
}
std::ostringstream& V3Error::v3errorStr() VL_REQUIRES(s().m_mutex) { return s().v3errorStr(); }
void V3Error::v3errorEnd(std::ostringstream& sstr, const string& extra) VL_RELEASE(s().m_mutex) {
    s().v3errorEnd(sstr, extra);
    V3Error::s().m_mutex.unlock();
}

void v3errorEnd(std::ostringstream& sstr) VL_RELEASE(V3Error::s().m_mutex) {
    V3Error::v3errorEnd(sstr);
}
void v3errorEndFatal(std::ostringstream& sstr) VL_RELEASE(V3Error::s().m_mutex) {
    V3Error::v3errorEnd(sstr);
    assert(0);  // LCOV_EXCL_LINE
    VL_UNREACHABLE;
}
