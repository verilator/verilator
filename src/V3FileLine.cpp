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

#include "config_build.h"
#include "verilatedos.h"

// clang-format off
#include "V3Error.h"
#include "V3FileLine.h"
#include "V3Os.h"
#include "V3String.h"
#ifndef V3ERROR_NO_GLOBAL_
# include "V3Global.h"
# include "V3Config.h"
# include "V3File.h"
#endif
#include "V3Waiver.h"
// clang-format on

#include <algorithm>
#include <iomanip>
#include <limits>
#include <unordered_set>

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// FileLineSingleton class functions

string FileLineSingleton::filenameLetters(fileNameIdx_t fileno) VL_PURE {
    constexpr int size
        = 1 + (64 / 4);  // Each letter retires more than 4 bits of a > 64 bit number
    char out[size];
    char* op = out + size - 1;
    *--op = '\0';  // We build backwards
    int num = fileno;
    do {
        *--op = 'a' + num % 26;
        num /= 26;
    } while (num);
    return op;
}

//! Convert filenames to a filenameno

//! This lets us assign a nice small identifier for debug messages, but more
//! importantly lets us use a 4 byte int instead of 8 byte pointer in every
//! FileLine.

//! We associate a language with each source file, so we also set the default
//! for this.
FileLineSingleton::fileNameIdx_t FileLineSingleton::nameToNumber(const string& filename) {
    const auto pair = m_namemap.emplace(filename, 0);
    fileNameIdx_t& idx = pair.first->second;
    if (pair.second) {
        const size_t nextIdx = m_names.size();
        UASSERT(nextIdx <= std::numeric_limits<fileNameIdx_t>::max(),
                "Too many input files (" + cvtToStr(nextIdx) + "+).");
        idx = static_cast<fileNameIdx_t>(nextIdx);
        m_names.push_back(filename);
        m_languages.push_back(V3LangCode::mostRecent());
    }
    return idx;
}

//! Support XML output
//! Experimental. Updated to also put out the language.
void FileLineSingleton::fileNameNumMapDumpXml(std::ostream& os) {
    os << "<files>\n";
    for (const auto& itr : m_namemap) {
        os << "<file id=\"" << filenameLetters(itr.second) << "\" filename=\""
           << V3OutFormatter::quoteNameControls(itr.first, V3OutFormatter::LA_XML)
           << "\" language=\"" << numberToLang(itr.second).ascii() << "\"/>\n";
    }
    os << "</files>\n";
}

FileLineSingleton::msgEnSetIdx_t FileLineSingleton::addMsgEnBitSet(const MsgEnBitSet& bitSet)
    VL_MT_SAFE_EXCLUDES(m_mutex) {
    V3LockGuard lock{m_mutex};
    const auto pair = m_internedMsgEnIdxs.emplace(bitSet, 0);
    msgEnSetIdx_t& idx = pair.first->second;
    if (pair.second) {
        const size_t nextIdx = m_internedMsgEns.size();
        UASSERT(nextIdx <= std::numeric_limits<msgEnSetIdx_t>::max(),
                "Too many unique message enable sets (" + cvtToStr(nextIdx) + "+).");
        idx = static_cast<msgEnSetIdx_t>(nextIdx);
        m_internedMsgEns.push_back(bitSet);
    }
    return idx;
}

FileLineSingleton::msgEnSetIdx_t FileLineSingleton::defaultMsgEnIndex() VL_MT_SAFE {
    MsgEnBitSet msgEnBitSet;
    for (int i = V3ErrorCode::EC_MIN; i < V3ErrorCode::_ENUM_MAX; ++i) {
        msgEnBitSet.set(i, !V3ErrorCode{i}.defaultsOff());
    }
    return addMsgEnBitSet(msgEnBitSet);
}

FileLineSingleton::msgEnSetIdx_t FileLineSingleton::msgEnSetBit(msgEnSetIdx_t setIdx,
                                                                size_t bitIdx, bool value) {
    if (msgEn(setIdx).test(bitIdx) == value) return setIdx;
    MsgEnBitSet msgEnBitSet{msgEn(setIdx)};
    msgEnBitSet.set(bitIdx, value);
    return addMsgEnBitSet(msgEnBitSet);
}

FileLineSingleton::msgEnSetIdx_t FileLineSingleton::msgEnAnd(msgEnSetIdx_t lhsIdx,
                                                             msgEnSetIdx_t rhsIdx) {
    MsgEnBitSet msgEnBitSet{msgEn(lhsIdx)};
    msgEnBitSet &= msgEn(rhsIdx);
    if (msgEnBitSet == msgEn(lhsIdx)) return lhsIdx;
    if (msgEnBitSet == msgEn(rhsIdx)) return rhsIdx;
    return addMsgEnBitSet(msgEnBitSet);
}

// ######################################################################
//  VFileContents class functions

void VFileContent::pushText(const string& text) {
    if (m_lines.size() == 0) {
        m_lines.emplace_back("");  // no such thing as line [0]
        m_lines.emplace_back("");  // start with no leftover
    }

    // Any leftover text is stored on largest line (might be "")
    const string leftover = m_lines.back() + text;
    m_lines.pop_back();

    // Insert line-by-line
    string::size_type line_start = 0;
    while (true) {
        const string::size_type line_end = leftover.find('\n', line_start);
        if (line_end != string::npos) {
            const string oneline(leftover, line_start, line_end - line_start + 1);
            m_lines.push_back(oneline);  // Keeps newline
            UINFO(9, "PushStream[ct" << m_id << "+" << (m_lines.size() - 1) << "]: " << oneline);
            line_start = line_end + 1;
        } else {
            break;
        }
    }
    // Keep leftover for next time
    m_lines.emplace_back(string(leftover, line_start));  // Might be ""
}

string VFileContent::getLine(int lineno) const VL_MT_SAFE {
    // Return error text rather than asserting so the user isn't left without a message
    // cppcheck-suppress negativeContainerIndex
    if (VL_UNCOVERABLE(lineno < 0 || lineno >= (int)m_lines.size())) {
        if (debug() || v3Global.opt.debugCheck()) {
            return ("%Error-internal-contents-bad-ct" + cvtToStr(m_id) + "-ln" + cvtToStr(lineno));
        } else {
            return "";
        }
    }
    string text = m_lines[lineno];
    UINFO(9, "Get Stream[ct" << m_id << "+" << lineno << "]: " << text);
    return text;
}

std::ostream& operator<<(std::ostream& os, VFileContent* contentp) {
    if (!contentp) {
        os << "ct0";
    } else {
        os << contentp->ascii();
    }
    return os;
}

// ######################################################################
//  FileLine class functions

FileLine::~FileLine() {
    if (m_contentp) VL_DO_DANGLING(m_contentp->refDec(), m_contentp);
}

void FileLine::newContent() {
    if (m_contentp) VL_DO_DANGLING(m_contentp->refDec(), m_contentp);
    m_contentp = new VFileContent;
    m_contentp->refInc();
    m_contentLineno = 1;
}

string FileLine::xmlDetailedLocation() const {
    return "loc=\"" + cvtToStr(filenameLetters()) + "," + cvtToStr(firstLineno()) + ","
           + cvtToStr(firstColumn()) + "," + cvtToStr(lastLineno()) + "," + cvtToStr(lastColumn())
           + "\"";
}

string FileLine::lineDirectiveStrg(int enterExit) const {
    return std::string{"`line "} + cvtToStr(lastLineno()) + " \""
           + V3OutFormatter::quoteNameControls(filename()) + "\" " + cvtToStr(enterExit) + "\n";
}

void FileLine::lineDirective(const char* textp, int& enterExitRef) {
    // Handle `line directive
    // Does not parse streamNumber/streamLineno as the next input token
    // will come from the same stream as the previous line.
    do {
        int lineNo;
        // Skip `line
        while (*textp && std::isspace(*textp)) ++textp;
        while (*textp && !std::isspace(*textp)) ++textp;
        while (*textp && std::isspace(*textp)) ++textp;

        // Grab linenumber
        const char* const ln = textp;
        while (*textp && !std::isspace(*textp)) ++textp;
        if (0 == strncmp(ln, "`__LINE__", textp - ln)) {
            // Special case - see docs - don't change other than accounting for `line itself
            lineNo = lineno() + 1;
        } else if (std::isdigit(*ln)) {
            lineNo = std::atoi(ln);
        } else {
            break;  // Fail
        }
        lineno(lineNo);
        while (*textp && (std::isspace(*textp))) ++textp;

        // Grab filename
        if (*textp != '"') break;  // Fail
        const char* const fn = ++textp;
        while (*textp && *textp != '"') ++textp;
        if (*textp != '"') break;  // Fail
        string errMsg;
        const string& parsedFilename = VString::unquoteSVString(string{fn, textp}, errMsg);
        if (!errMsg.empty()) this->v3error(errMsg.c_str());
        filename(parsedFilename);
        ++textp;
        while (*textp && std::isspace(*textp)) ++textp;

        // Grab level
        if (!std::isdigit(*textp)) break;  // Fail
        const int level = std::atoi(textp);
        if (level < 0 || level >= 3) break;  // Fail
        /// TODO: store lineno/filename only when the `line directive is valid
        /// lineno(lineNo);
        /// filename(filenameNew);
        enterExitRef = level;
        return;
    } while (false);

    // Fail
    // TODO: show correct place of the code
    v3error("`line was not properly formed with '`line number \"filename\" level'\n");
    enterExitRef = 0;
}

void FileLine::forwardToken(const char* textp, size_t size, bool trackLines) {
    for (const char* sp = textp; size && *sp; ++sp, --size) {
        if (*sp == '\n') {
            if (trackLines) linenoInc();
            m_lastColumn = 1;
        } else if (VL_UNCOVERABLE(*sp == '\r')) {  // Generally stripped by preproc
        } else {  // Tabs are considered one column; hence column means number of chars
            ++m_lastColumn;
        }
    }
}

FileLine* FileLine::copyOrSameFileLine() {
    // When a fileline is "used" to produce a node, calls this function.
    // Return this, or a copy of this
    // There are often more than one token per line, thus we use the
    // same pointer as long as we're on the same line, file & warn state.
#ifndef V3ERROR_NO_GLOBAL_
    V3Config::applyIgnores(this);  // Toggle warnings based on global config file
#endif
    static FileLine* lastNewp = nullptr;
    if (lastNewp && *lastNewp == *this) {  // Compares lineno, filename, etc
        return lastNewp;
    }
    FileLine* const newp = new FileLine{this};
    lastNewp = newp;
    return newp;
}

string FileLine::filebasename() const VL_MT_SAFE { return V3Os::filenameNonDir(filename()); }

string FileLine::filebasenameNoExt() const { return V3Os::filenameNonDirExt(filename()); }

string FileLine::firstColumnLetters() const VL_MT_SAFE {
    const char a = ((firstColumn() / 26) % 26) + 'a';
    const char b = (firstColumn() % 26) + 'a';
    return string(1, a) + string(1, b);
}

string FileLine::profileFuncname() const {
    // Return string that is OK as a function name - for profiling
    string name = filebasenameNoExt();
    string::size_type pos;
    while ((pos = name.find_first_not_of(
                "abcdefghijlkmnopqrstuvwxyzABCDEFGHIJLKMNOPQRSTUVWXYZ0123456789_"))
           != string::npos) {
        name.replace(pos, 1, "_");
    }
    name += "__l" + cvtToStr(lastLineno());
    return name;
}

string FileLine::asciiLineCol() const {
    return (cvtToStr(firstLineno()) + "-" + cvtToStr(lastLineno()) + ":" + cvtToStr(firstColumn())
            + "-" + cvtToStr(lastColumn()) + "[" + (m_contentp ? m_contentp->ascii() : "ct0") + "+"
            + cvtToStr(m_contentLineno) + "]");
}
string FileLine::ascii() const {
    // For most errors especially in the parser the lastLineno is more accurate than firstLineno
    return filename() + ":" + cvtToStr(lastLineno()) + ":" + cvtToStr(firstColumn());
}
std::ostream& operator<<(std::ostream& os, FileLine* fileline) {
    os << fileline->ascii() << ": " << std::hex;
    return (os);
}

bool FileLine::warnOff(const string& msg, bool flag) {
    const char* cmsg = msg.c_str();
    // Backward compatibility with msg="UNUSED"
    if (V3ErrorCode::unusedMsg(cmsg)) {
        warnOff(V3ErrorCode::UNUSEDGENVAR, flag);
        warnOff(V3ErrorCode::UNUSEDPARAM, flag);
        warnOff(V3ErrorCode::UNUSEDSIGNAL, flag);
        return true;
    }
    const V3ErrorCode code{cmsg};
    if (code < V3ErrorCode::EC_FIRST_WARN) {
        return false;
    } else {
        warnOff(code, flag);
        return true;
    }
}

void FileLine::warnLintOff(bool flag) {
    for (int codei = V3ErrorCode::EC_MIN; codei < V3ErrorCode::_ENUM_MAX; codei++) {
        const V3ErrorCode code{codei};
        if (code.lintError()) warnOff(code, flag);
    }
}

void FileLine::warnStyleOff(bool flag) {
    for (int codei = V3ErrorCode::EC_MIN; codei < V3ErrorCode::_ENUM_MAX; codei++) {
        const V3ErrorCode code{codei};
        if (code.styleError()) warnOff(code, flag);
    }
}

void FileLine::warnUnusedOff(bool flag) {
    warnOff(V3ErrorCode::UNUSEDGENVAR, flag);
    warnOff(V3ErrorCode::UNUSEDPARAM, flag);
    warnOff(V3ErrorCode::UNUSEDSIGNAL, flag);
}

bool FileLine::warnIsOff(V3ErrorCode code) const {
    if (!msgEn().test(code)) return true;
    if (!defaultFileLine().msgEn().test(code)) return true;  // Global overrides local
    if ((code.lintError() || code.styleError()) && !msgEn().test(V3ErrorCode::I_LINT)) {
        return true;
    }
    if ((code.unusedError()) && !msgEn().test(V3ErrorCode::I_UNUSED)) { return true; }
    return false;
}

// cppverilator-suppress constParameter
void FileLine::v3errorEnd(std::ostringstream& sstr, const string& extra)
    VL_RELEASE(V3Error::s().m_mutex) {
    std::ostringstream nsstr;
    if (lastLineno()) nsstr << this;
    nsstr << sstr.str();
    nsstr << endl;
    std::ostringstream lstr;
    if (!extra.empty()) {
        lstr << std::setw(ascii().length()) << " "
             << ": " << extra;
    }
    m_waive = V3Config::waive(this, V3Error::s().errorCode(), sstr.str());
    if (warnIsOff(V3Error::s().errorCode()) || m_waive) {
        V3Error::s().suppressThisWarning();
    } else if (!V3Error::s().errorContexted()) {
        nsstr << warnContextPrimary();
    }
    if (!m_waive) V3Waiver::addEntry(V3Error::s().errorCode(), filename(), sstr.str());
    V3Error::v3errorEnd(nsstr, lstr.str());
}

string FileLine::warnMore() const VL_REQUIRES(V3Error::s().m_mutex) {
    if (lastLineno()) {
        return V3Error::s().warnMore() + string(ascii().size(), ' ') + ": ";
    } else {
        return V3Error::s().warnMore();
    }
}
string FileLine::warnOther() const VL_REQUIRES(V3Error::s().m_mutex) {
    if (lastLineno()) {
        return V3Error::s().warnMore() + ascii() + ": ";
    } else {
        return V3Error::s().warnMore();
    }
};
string FileLine::warnOtherStandalone() const VL_EXCLUDES(V3Error::s().m_mutex) VL_MT_UNSAFE {
    const V3RecursiveLockGuard guard{V3Error::s().m_mutex};
    return warnOther();
}

string FileLine::source() const VL_MT_SAFE {
    if (VL_UNCOVERABLE(!m_contentp)) {  // LCOV_EXCL_START
        if (debug() || v3Global.opt.debugCheck()) {
            // The newline here is to work around the " <line#> | "
            return "\n%Error: internal tracking of file contents failed";
        } else {
            return "";
        }
    }  // LCOV_EXCL_STOP
    return m_contentp->getLine(m_contentLineno);
}
string FileLine::sourcePrefix(int toColumn) const VL_MT_SAFE {
    const std::string src = source();
    if (toColumn > static_cast<int>(src.length())) toColumn = static_cast<int>(src.length());
    if (toColumn < 1) return "";
    return src.substr(0, toColumn - 1);
}
string FileLine::prettySource() const VL_MT_SAFE {
    string out = source();
    // Drop ignore trailing newline
    const string::size_type pos = out.find('\n');
    if (pos != string::npos) out = string(out, 0, pos);
    // Column tracking counts tabs = 1, so match that when print source
    return VString::spaceUnprintable(out);
}

string FileLine::warnContext() const {
    if (!v3Global.opt.context()) return "";
    string out;
    if (firstLineno() == lastLineno() && firstColumn()) {
        const string sourceLine = prettySource();
        // Don't show super-long lines as can fill screen and unlikely to help user
        if (!sourceLine.empty() && sourceLine.length() < SHOW_SOURCE_MAX_LENGTH
            && sourceLine.length() >= static_cast<size_t>(lastColumn() - 1)) {
            string linestr = cvtToStr(firstLineno());
            while (linestr.size() < 5) linestr = ' ' + linestr;
            out += linestr + " | " + sourceLine + "\n";
            out += std::string(linestr.size(), ' ') + " | ";
            out += string((firstColumn() - 1), ' ') + '^';
            // Can't use UASSERT_OBJ used in warnings already inside the error end handler
            if (lastColumn() > firstColumn()) {
                // Note lastColumn() can be <= firstColumn() in some weird preproc expansions
                out += string((lastColumn() - firstColumn() - 1), '~');
            }
            out += "\n";
        }
    }
    return out;
}

string FileLine::warnContextParent() const VL_REQUIRES(V3Error::s().m_mutex) {
    string result;
    for (FileLine* parentFl = parent(); parentFl; parentFl = parentFl->parent()) {
        if (parentFl->filenameIsGlobal()) break;
        result += parentFl->warnOther() + "... note: In file included from '"
                  + parentFl->filebasename() + "'\n";
    }
    return result;
}
#ifdef VL_LEAK_CHECKS
std::unordered_set<FileLine*> fileLineLeakChecks;

void* FileLine::operator new(size_t size) {
    FileLine* const objp = static_cast<FileLine*>(::operator new(size));
    fileLineLeakChecks.insert(objp);
    return objp;
}

void FileLine::operator delete(void* objp, size_t size) {
    if (!objp) return;
    FileLine* const flp = static_cast<FileLine*>(objp);
    const auto it = fileLineLeakChecks.find(flp);
    if (it != fileLineLeakChecks.end()) {
        fileLineLeakChecks.erase(it);
    } else {
        flp->v3fatalSrc("Deleting FileLine object that was never tracked");
    }
    ::operator delete(objp);
}
#endif

void FileLine::deleteAllRemaining() {
#ifdef VL_LEAK_CHECKS
    // FileLines are allocated, but never nicely freed, as it's much faster
    // that way.  Unfortunately this makes our leak checking a big mess, so
    // only when leak checking we'll track them all and cleanup.
    while (true) {
        const auto it = fileLineLeakChecks.begin();
        if (it == fileLineLeakChecks.end()) break;
        delete *it;
        // Operator delete will remove the iterated object from the list.
        // Eventually the list will be empty and terminate the loop.
    }
    fileLineLeakChecks.clear();
    singleton().clear();
#endif
}
