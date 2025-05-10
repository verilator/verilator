// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Error handling
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2025 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

// clang-format off
#include "V3Error.h"
#include "V3Os.h"
#ifndef V3ERROR_NO_GLOBAL_
# include "V3Ast.h"
# include "V3Global.h"
# include "V3Stats.h"
VL_DEFINE_DEBUG_FUNCTIONS;
#endif
#include <thread>
// clang-format on

//======================================================================

struct v3errorIniter final {
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

string V3ErrorCode::url() const {
    if (m_e < V3ErrorCode::EC_FIRST_NAMED) {
        return "https://verilator.org/verilator_doc.html"s + "?v=" + PACKAGE_VERSION_NUMBER_STRING;
    } else {
        return "https://verilator.org/warn/"s + ascii() + "?v=" + PACKAGE_VERSION_NUMBER_STRING;
    }
}

//######################################################################
// V3ErrorGuarded class functions
//

bool V3ErrorGuarded::isError(V3ErrorCode code, bool supp) VL_REQUIRES(m_mutex) {
    if (code.hardError()) return true;
    if (supp) return false;
    if (code == V3ErrorCode::USERINFO || code == V3ErrorCode::EC_INFO) return false;
    if (pretendError(code)) return true;
    return false;
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
    } else if (code == V3ErrorCode::EC_FATALMANY) {
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
    }
#ifndef V3ERROR_NO_GLOBAL_
    else if (v3Global.opt.verilateJobs() > 1
             && v3Global.mainThreadId() != std::this_thread::get_id()) {
        VL_GCOV_DUMP();  // No static destructors are called, thus must be called manually.

        // Exit without triggering any global destructors.
        // Used to prevent detached V3ThreadPool jobs accessing destroyed static objects.
        ::_exit(1);
    }
#endif
    else {
        std::exit(1);
    }
}

string V3ErrorGuarded::warnMore() VL_REQUIRES(m_mutex) { return string(msgPrefix().size(), ' '); }

void V3ErrorGuarded::suppressThisWarning() VL_REQUIRES(m_mutex) {
#ifndef V3ERROR_NO_GLOBAL_
    V3Stats::addStatSum("Warnings, Suppressed "s + errorCode().ascii(), 1);
#endif
    errorSuppressed(true);
}

void V3ErrorGuarded::v3errorPrep(V3ErrorCode code) VL_REQUIRES(m_mutex) {
    m_errorStr.str("");
    m_errorCode = code;
    m_errorContexted = false;
    m_errorSuppressed = false;
}

// cppcheck-has-bug-suppress constParameter
void V3ErrorGuarded::v3errorEnd(std::ostringstream& sstr, const string& extra)
    VL_REQUIRES(m_mutex) {
    // 'extra' is appended to the message, and is is excluded in check for
    // duplicate messages. Currently used for reporting instance name.
#if defined(__COVERITY__) || defined(__cppcheck__)
    if (m_errorCode == V3ErrorCode::EC_FATAL) __coverity_panic__(x);
#endif
    // Skip suppressed messages
    if (m_errorSuppressed
        // On debug, show only non default-off warning to prevent pages of warnings
        && (!debug() || debug() < 3 || m_errorCode.defaultsOff()))
        return;
    string msg = msgPrefix() + sstr.str();

    // If suppressed print only first line to reduce verbosity
    string firstLine = msg;
    string::size_type pos;
    if ((pos = firstLine.find('\n')) != string::npos) {
        firstLine.erase(pos, firstLine.length() - pos);
        firstLine += "...";
    }
    if (m_errorSuppressed) msg = firstLine;
    // Suppress duplicate messages
    if (!m_messages.insert(firstLine).second) return;

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
    if (!extra.empty() && !m_errorSuppressed) {
        const string extraMsg = warnMore() + extra + "\n";
        const size_t pos = msg.find('\n');
        msg.insert(pos + 1, extraMsg);
    }
    // Output
    if (
#ifndef V3ERROR_NO_GLOBAL_
        !(v3Global.opt.quietExit() && m_errorCode == V3ErrorCode::EC_FATALMANY)
#else
        true
#endif
    ) {
        std::cerr << msg;
    }
    if (!m_errorSuppressed
        && !(m_errorCode == V3ErrorCode::EC_INFO || m_errorCode == V3ErrorCode::USERINFO)) {
        const bool anError = isError(m_errorCode, m_errorSuppressed);
        if (m_errorCode != V3ErrorCode::EC_FATALMANY  // Not verbose on final too-many-errors error
            && !m_describedEachWarn[m_errorCode]) {
            m_describedEachWarn[m_errorCode] = true;
            if (m_errorCode >= V3ErrorCode::EC_FIRST_NAMED) {
                std::cerr << warnMore() << "... For " << (anError ? "error" : "warning")
                          << " description see " << m_errorCode.url() << endl;
            } else if (m_errCount >= 1
                       && (m_errorCode == V3ErrorCode::EC_FATAL
                           || m_errorCode == V3ErrorCode::EC_FATALMANY
                           || m_errorCode == V3ErrorCode::EC_FATALSRC)
                       && !m_tellInternal) {
                m_tellInternal = true;
                std::cerr << warnMore()
                          << "... This fatal error may be caused by the earlier error(s);"
                             " resolve those first."
                          << endl;
            } else if (!m_tellManual) {
                m_tellManual = true;
                std::cerr << warnMore() << "... See the manual at " << m_errorCode.url()
                          << " for more assistance." << endl;
            }
            if (!m_pretendError[m_errorCode] && !m_errorCode.hardError()) {
                std::cerr << warnMore() << "... Use \"/* verilator lint_off "
                          << m_errorCode.ascii()
                          << " */\" and lint_on around source to disable this message." << endl;
                if (m_errorCode.dangerous()) {
                    std::cerr << warnMore() << "*** See " << m_errorCode.url()
                              << " before disabling this,\n";
                    std::cerr << warnMore() << "else you may end up with different sim results."
                              << endl;
                }
            }
        }
        if (!msg_additional.empty()) std::cerr << msg_additional;
        if (anError) {
            incErrors();
        } else {
            incWarnings();
        }
        if (m_errorCode == V3ErrorCode::EC_FATAL || m_errorCode == V3ErrorCode::EC_FATALMANY
            || m_errorCode == V3ErrorCode::EC_FATALSRC) {
            static bool inFatal = false;
            if (!inFatal) {
                inFatal = true;
#ifndef V3ERROR_NO_GLOBAL_
                if (dumpTreeLevel() || dumpTreeJsonLevel() || debug()) {
                    V3Broken::allowMidvisitorCheck(true);
                    if (dumpTreeLevel()) {
                        v3Global.rootp()->dumpTreeFile(v3Global.debugFilename("final.tree", 990));
                    }
                    if (dumpTreeJsonLevel()) {
                        v3Global.rootp()->dumpTreeJsonFile(
                            v3Global.debugFilename("final.tree.json", 990));
                    }
                    if (debug()) {
                        execErrorExitCb();
                        V3Stats::statsFinalAll(v3Global.rootp());
                        V3Stats::statsReport();
                    }
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
    UASSERT(std::string{V3ErrorCode{V3ErrorCode::_ENUM_MAX}.ascii()} == " MAX",
            "Enum table in V3ErrorCode::EC_ascii() is munged");
}

string V3Error::lineStr(const char* filename, int lineno) VL_PURE {
    std::ostringstream out;
    out << V3Os::filenameNonDir(filename) << ":" << std::dec << lineno << ":";
    out << std::string(std::max<int>(0, 20 - static_cast<int>(out.str().length())), ' ');
    return out.str();
}

void V3Error::abortIfWarnings() {
    const bool exwarn = warnFatal() && warnCount();
    if (errorCount() && exwarn) {
        v3fatalMany("Exiting due to " << std::dec << V3Error::s().errorCount() << " error(s), "  //
                                      << V3Error::s().warnCount() << " warning(s)\n");
    } else if (errorCount()) {
        v3fatalMany("Exiting due to " << std::dec << V3Error::s().errorCount() << " error(s)\n");
    } else if (exwarn) {
        v3fatalMany("Exiting due to " << std::dec << V3Error::s().warnCount() << " warning(s)\n");
    }
}

//======================================================================
// Abort/exit

void V3Error::vlAbort() {
    VL_GCOV_DUMP();
    std::abort();
}
std::ostringstream& V3Error::v3errorPrep(V3ErrorCode code) VL_ACQUIRE(s().m_mutex) {
    V3Error::s().m_mutex.lock();
    s().v3errorPrep(code);
    return v3errorStr();
}
std::ostringstream& V3Error::v3errorPrepFileLine(V3ErrorCode code, const char* file, int line)
    VL_ACQUIRE(s().m_mutex) {
    v3errorPrep(code) << file << ":" << std::dec << line << ": ";
    return v3errorStr();
}
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
