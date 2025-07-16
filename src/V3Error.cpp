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
# include "V3DiagSarif.h"
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
    if (!isNamed()) {
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
    if (code.severityInfo()) return false;
    if (pretendError(code)) return true;
    return false;
}

string V3ErrorGuarded::msgPrefix() VL_REQUIRES(m_mutex) {
    const V3ErrorCode code = m_message.code();
    const bool supp = m_errorSuppressed;
    if (supp) {
        return "-arning-suppressed: ";
    } else if (code.severityInfo()) {
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

string V3ErrorGuarded::warnMoreSpaces() VL_REQUIRES(m_mutex) {
    UASSERT_STATIC(!m_message.isClear(), "warnMore() outside of v3errorPrep...v3errorEnd");
    return string(msgPrefix().size(), ' ');
}

void V3ErrorGuarded::suppressThisWarning() VL_REQUIRES(m_mutex) {
#ifndef V3ERROR_NO_GLOBAL_
    V3Stats::addStatSum("Warnings, Suppressed "s + errorCode().ascii(), 1);
#endif
    errorSuppressed(true);
}

void V3ErrorGuarded::v3errorPrep(V3ErrorCode code) VL_REQUIRES(m_mutex) {
    m_errorStr.str("");
    UASSERT_STATIC(m_message.isClear(), "Attempted v3errorPrep inside v3errorPrep...v3errorEnd");
    m_message.init(code);
    m_errorContexted = false;
    m_errorSuppressed = false;
}

void V3ErrorGuarded::v3errorEnd(std::ostringstream& sstr, const string& extra, FileLine* fileline)
    VL_REQUIRES(m_mutex) {
    static bool s_firedTooMany = false;
    v3errorEndGuts(sstr, extra, fileline);
    m_message.clear();
    if (errorLimit() && errorCount() >= errorLimit() && !s_firedTooMany) {
        s_firedTooMany = true;
        // Recurses here
        v3errorEnd((v3errorPrep(V3ErrorCode::EC_FATALMANY),
                    (v3errorStr() << "Exiting due to too many errors encountered; --error-limit="
                                  << errorCount() << std::endl),
                    v3errorStr()),
                   "", nullptr);
        assert(0);  // LCOV_EXCL_LINE
        VL_UNREACHABLE;
    }
}

// cppcheck-has-bug-suppress constParameter
void V3ErrorGuarded::v3errorEndGuts(std::ostringstream& sstr, const string& extra,
                                    FileLine* fileline) VL_REQUIRES(m_mutex) {
    // 'extra' is appended to the message, and is is excluded in check for
    // duplicate messages. Currently used for reporting instance name.
#if defined(__COVERITY__) || defined(__cppcheck__)
    if (m_errorCode == V3ErrorCode::EC_FATAL) __coverity_panic__(x);
#endif

    UASSERT_STATIC(!m_message.isClear(), "v3errorEnd() outside of v3errorPrep...v3errorEnd");
    m_message.fileline(fileline);

    // Skip suppressed messages
    if (m_errorSuppressed
        // On debug, show only non default-off warning to prevent pages of warnings
        && (!debug() || debug() < 3 || m_message.code().defaultsOff()))
        return;
    string msg
        = V3Error::warnContextBegin() + msgPrefix() + V3Error::warnContextEnd() + sstr.str();

    // If suppressed print only first line to reduce verbosity
    string firstLine = msg;
    {
        string::size_type pos;
        if ((pos = firstLine.find('\n')) != string::npos) {
            firstLine.erase(pos, firstLine.length() - pos);
            firstLine += "...";
        }
    }
    if (m_errorSuppressed) msg = firstLine;
    // Suppress duplicate messages
    if (!m_messages.insert(firstLine).second) return;

    msg = VString::replaceSubstr(msg, V3Error::warnMore(), warnMoreSpaces());

    string msg_additional;
    {
        string::size_type pos;
        if ((pos = msg.find(V3Error::warnAdditionalInfo())) != string::npos) {
            msg_additional = msg.substr(pos + V3Error::warnAdditionalInfo().size());
            msg.erase(pos);
        }
    }
    msg += '\n';  // Trailing newlines generally not put on messages so add
    if (!extra.empty() && !m_errorSuppressed) {
        string extraMsg = VString::replaceSubstr(extra, V3Error::warnMore(), warnMoreSpaces());
        extraMsg = warnMoreSpaces() + extraMsg + "\n";
        const size_t pos = msg.find('\n');
        msg.insert(pos + 1, extraMsg);
    }
    // Output
    string text;
    if (
#ifndef V3ERROR_NO_GLOBAL_
        !(v3Global.opt.quietExit() && m_message.code() == V3ErrorCode::EC_FATALMANY)
#else
        true
#endif
    )
        text += msg;
    if (m_errorSuppressed || m_message.code().severityInfo()) {
        std::cerr << V3Error::stripMetaText(text, false);
        m_message.text(text);
#ifndef V3ERROR_NO_GLOBAL_
        V3DiagSarif::pushMessage(m_message);
#endif
    } else {
        const bool anError = isError(m_message.code(), m_errorSuppressed);
        if (m_message.code()
                != V3ErrorCode::EC_FATALMANY  // Not verbose on final too-many-errors error
            && !m_describedEachWarn[m_message.code()]) {
            m_describedEachWarn[m_message.code()] = true;
            if (m_message.code() >= V3ErrorCode::EC_FIRST_NAMED) {
                text += warnMoreSpaces() + "... For " + (anError ? "error" : "warning")
                        + " description see " + m_message.code().url() + '\n';
            } else if (m_errCount >= 1 && m_message.code().severityFatal() && !m_tellInternal) {
                m_tellInternal = true;
                text += warnMoreSpaces()
                        + "... This fatal error may be caused by the earlier error(s);"
                          " resolve those first.\n";
            } else if (!m_tellManual) {
                m_tellManual = true;
                text += warnMoreSpaces() + "... See the manual at " + m_message.code().url()
                        + " for more assistance.\n";
            }
            if (!m_pretendError[m_message.code()] && !m_message.code().hardError()) {
                text += warnMoreSpaces() + "... Use \"/* verilator lint_off "
                        + m_message.code().ascii()
                        + " */\" and lint_on around source to disable this message.\n";
                if (m_message.code().dangerous()) {
                    text += warnMoreSpaces() + "*** See " + m_message.code().url()
                            + " before disabling this,\n";
                    text += warnMoreSpaces() + "else you may end up with different sim results.\n";
                }
            }
        }
        if (!msg_additional.empty()) text += msg_additional;
        std::cerr << V3Error::stripMetaText(text, false);
        m_message.text(text);
#ifndef V3ERROR_NO_GLOBAL_
        V3DiagSarif::pushMessage(m_message);
#endif

        if (anError) {
            incErrors();
        } else {
            incWarnings();
        }
        if (m_message.code().severityFatal()) {
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
                V3DiagSarif::output(false);
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

string V3Error::stripMetaText(const string& text, bool stripContext) VL_PURE {
    string result;
    result.reserve(text.size());
    int inBegins = 0;
    for (string::size_type pos = 0; pos < text.size();) {
        // string::starts_with is C++20
        if (0 == text.compare(pos, std::strlen("__WARN"), "__WARN")) {
            if (0 == text.compare(pos, std::strlen("__WARNRELATED("), "__WARNRELATED(")) {
                while (pos < text.size() && text[pos] != ')') ++pos;
                if (pos < text.size() && text[pos] == ')') ++pos;
                continue;
            }
            if (0
                == text.compare(pos, std::strlen(V3Error::WARN_CONTEXT_BEGIN),
                                V3Error::WARN_CONTEXT_BEGIN)) {
                pos += std::strlen(V3Error::WARN_CONTEXT_BEGIN);
                ++inBegins;
                continue;
            }
            if (0
                == text.compare(pos, std::strlen(V3Error::WARN_CONTEXT_END),
                                V3Error::WARN_CONTEXT_END)) {
                pos += std::strlen(V3Error::WARN_CONTEXT_END);
                // No assert, is not VL_PURE
                // UASSERT_STATIC(inBegins, "warnContextEnd() outside of warnContextBegin()");
                --inBegins;
                continue;
            }
        }
        if (!stripContext || inBegins == 0) {
            // Remove double newlines
            if (!(text[pos] == '\n' && !result.empty() && result[result.size() - 1] == '\n'))
                result += text[pos];
        }
        ++pos;
    }
    return result;
}

void V3Error::abortIfWarnings() {
    if (!isErrorOrWarn()) return;
    const bool exwarn = warnFatal() && warnCount();
    if (errorCount() && exwarn) {
        v3fatalMany("Exiting due to " << std::dec << V3Error::s().errorCount() << " error(s), "  //
                                      << V3Error::s().warnCount() << " warning(s)\n");
    } else if (errorCount()) {
        v3fatalMany("Exiting due to " << std::dec << V3Error::s().errorCount() << " error(s)\n");
    } else {
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
void V3Error::v3errorEnd(std::ostringstream& sstr, const string& extra, FileLine* fileline)
    VL_RELEASE(s().m_mutex) {
    s().v3errorEnd(sstr, extra, fileline);
    V3Error::s().m_mutex.unlock();
}

void v3errorEnd(std::ostringstream& sstr) VL_RELEASE(V3Error::s().m_mutex) {
    V3Error::v3errorEnd(sstr, "", nullptr);
}
void v3errorEndFatal(std::ostringstream& sstr) VL_RELEASE(V3Error::s().m_mutex) {
    V3Error::v3errorEnd(sstr, "", nullptr);
    assert(0);  // LCOV_EXCL_LINE
    VL_UNREACHABLE;
}
