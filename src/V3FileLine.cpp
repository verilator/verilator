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

#include "config_build.h"
#include "verilatedos.h"

#include "V3Error.h"
#include "V3FileLine.h"
#include "V3String.h"
#ifndef _V3ERROR_NO_GLOBAL_
# include "V3Ast.h"
# include "V3Global.h"
# include "V3Stats.h"
# include "V3Config.h"
# include "V3File.h"
#endif

#include <algorithm>
#include <cstdarg>
#include <iomanip>
#include VL_INCLUDE_UNORDERED_SET

//######################################################################
// FileLineSingleton class functions

const string FileLineSingleton::filenameLetters(int fileno) {
    const int size = 1 + (64 / 4);  // Each letter retires more than 4 bits of a > 64 bit number
    char out[size];
    char* op = out+size-1;
    *--op = '\0';  // We build backwards
    int num = fileno;
    do {
        *--op = 'a'+num%26;
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
int FileLineSingleton::nameToNumber(const string& filename) {
    FileNameNumMap::const_iterator it = m_namemap.find(filename);
    if (VL_LIKELY(it != m_namemap.end())) return it->second;
    int num = m_names.size();
    m_names.push_back(filename);
    m_languages.push_back(V3LangCode::mostRecent());
    m_namemap.insert(make_pair(filename, num));
    return num;
}

//! Support XML output
//! Experimental. Updated to also put out the language.
void FileLineSingleton::fileNameNumMapDumpXml(std::ostream& os) {
    os<<"<files>\n";
    for (FileNameNumMap::const_iterator it = m_namemap.begin(); it != m_namemap.end(); ++it) {
        os<<"<file id=\""<<filenameLetters(it->second)
          <<"\" filename=\""<<V3OutFormatter::quoteNameControls(it->first, V3OutFormatter::LA_XML)
          <<"\" language=\""<<numberToLang(it->second).ascii()<<"\"/>\n";
    }
    os<<"</files>\n";
}

//######################################################################
// VFileContents class functions

int VFileContent::debug() {
    static int level = -1;
    if (VL_UNLIKELY(level < 0)) level = v3Global.opt.debugSrcLevel(__FILE__);
    return level;
}

void VFileContent::pushText(const string& text) {
    if (m_lines.size() == 0) {
        m_lines.push_back("");  // no such thing as line [0]
        m_lines.push_back("");  // start with no leftover
    }

    // Any leftover text is stored on largest line (might be "")
    string leftover = m_lines.back() + text; m_lines.pop_back();

    // Insert line-by-line
    string::size_type line_start = 0;
    while (1) {
        string::size_type line_end = leftover.find("\n", line_start);
        if (line_end != string::npos) {
            string oneline (leftover, line_start, line_end-line_start+1);
            m_lines.push_back(oneline);  // Keeps newline
            UINFO(9, "PushStream[ct"<<m_id<<"+"<<(m_lines.size()-1)<<"]: "<<oneline);
            line_start = line_end+1;
        } else {
            break;
        }
    }
    // Keep leftover for next time
    m_lines.push_back(string(leftover, line_start));  // Might be ""
}

string VFileContent::getLine(int lineno) const {
    // Return error text rather than asserting so the user isn't left without a message
    // cppcheck-suppress negativeContainerIndex
    if (VL_UNCOVERABLE(lineno < 0 || lineno >= (int)m_lines.size())) {
        if (debug() || v3Global.opt.debugCheck()) {
            return ("%Error-internal-contents-bad-ct"+cvtToStr(m_id)
                    +"-ln"+cvtToStr(lineno));
        } else return "";
    }
    string text = m_lines[lineno];
    UINFO(9, "Get Stream[ct"<<m_id<<"+"<<lineno<<"]: "<<text);
    return text;
}

std::ostream& operator<<(std::ostream& os, VFileContent* contentp) {
    if (!contentp) os <<"ct0";
    else os <<contentp->ascii();
    return os;
}

//######################################################################
// FileLine class functions

FileLine::FileLine(FileLine::EmptySecret) {
    // Sort of a singleton
    m_firstLineno = 0;
    m_lastLineno = 0;
    m_firstColumn = 0;
    m_lastColumn = 0;
    m_filenameno = singleton().nameToNumber(FileLine::builtInFilename());
    m_contentp = NULL;
    m_contentLineno = 0;
    m_parent = NULL;

    m_warnOn = 0;
    for (int codei=V3ErrorCode::EC_MIN; codei<V3ErrorCode::_ENUM_MAX; codei++) {
        V3ErrorCode code = V3ErrorCode(codei);
        warnOff(code, code.defaultsOff());
    }
}

const string FileLine::xmlDetailedLocation() const {
    return "loc=\"" +
        cvtToStr(filenameLetters()) + "," +
        cvtToStr(firstLineno()) + "," +
        cvtToStr(firstColumn()) + "," +
        cvtToStr(lastLineno()) + "," +
        cvtToStr(lastColumn()) + "\"";
}

string FileLine::lineDirectiveStrg(int enterExit) const {
    char numbuf[20]; sprintf(numbuf, "%d", lastLineno());
    char levelbuf[20]; sprintf(levelbuf, "%d", enterExit);
    return (string("`line ")+numbuf+" \""+filename()+"\" "+levelbuf+"\n");
}

void FileLine::lineDirective(const char* textp, int& enterExitRef) {
    // Handle `line directive
    // Does not parse streamNumber/streamLineno as the next input token
    // will come from the same stream as the previous line.

    // Skip `line
    while (*textp && isspace(*textp)) textp++;
    while (*textp && !isspace(*textp)) textp++;
    while (*textp && (isspace(*textp) || *textp=='"')) textp++;

    // Grab linenumber
    bool fail = false;
    const char* ln = textp;
    while (*textp && !isspace(*textp)) textp++;
    if (isdigit(*ln)) {
        lineno(atoi(ln));
    } else fail = true;
    while (*textp && (isspace(*textp))) textp++;
    if (*textp != '"') fail = true;
    while (*textp && (isspace(*textp) || *textp == '"')) textp++;

    // Grab filename
    const char* fn = textp;
    while (*textp && !(isspace(*textp) || *textp=='"')) textp++;
    if (textp != fn) {
        string strfn = fn;
        strfn = strfn.substr(0, textp-fn);
        filename(strfn);
    } else fail = true;

    // Grab level
    while (*textp && (isspace(*textp) || *textp=='"')) textp++;
    if (isdigit(*textp)) {
        enterExitRef = atoi(textp);
        if (enterExitRef >= 3) fail = true;
    } else {
        enterExitRef = 0;
        fail = true;
    }

    if (fail && v3Global.opt.pedantic()) {
        v3error("`line was not properly formed with '`line number \"filename\" level'\n");
    }

    //printf ("PPLINE %d '%s'\n", s_lineno, s_filename.c_str());
}

void FileLine::forwardToken(const char* textp, size_t size, bool trackLines) {
    for (const char* sp = textp; size && *sp; ++sp, --size) {
        if (*sp == '\n') {
            if (trackLines) linenoInc();
            m_lastColumn = 1;
        } else if (*sp == '\r') {
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
    if ((pos = name.rfind('/')) != string::npos) {
        name.erase(0, pos+1);
    }
    return name;
}

const string FileLine::filebasenameNoExt() const {
    string name = filebasename();
    string::size_type pos;
    if ((pos = name.find('.')) != string::npos) {
        name = name.substr(0, pos);
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
    name += "__l"+cvtToStr(lastLineno());
    return name;
}

string FileLine::asciiLineCol() const {
    return (cvtToStr(firstLineno())+"-"+cvtToStr(lastLineno())
            +":"+cvtToStr(firstColumn())+"-"+cvtToStr(lastColumn())
            +"["+(m_contentp ? m_contentp->ascii() : "ct0")
            +"+"+cvtToStr(m_contentLineno)+"]");
}
string FileLine::ascii() const {
    // For most errors especially in the parser the lastLineno is more accurate than firstLineno
    return filename() + ":" + cvtToStr(lastLineno()) + ":" + cvtToStr(firstColumn());
}
std::ostream& operator<<(std::ostream& os, FileLine* fileline) {
    os <<fileline->ascii()<<": "<<std::hex;
    return(os);
}

bool FileLine::warnOff(const string& msg, bool flag) {
    V3ErrorCode code (msg.c_str());
    if (code < V3ErrorCode::EC_FIRST_WARN) {
        return false;
#ifndef _V3ERROR_NO_GLOBAL_
    } else if (v3Global.opt.lintOnly()  // Lint mode is allowed to suppress some errors
               && code < V3ErrorCode::EC_MIN) {
        return false;
#endif
    } else {
        warnOff(code, flag);
        return true;
    }
}

void FileLine::warnLintOff(bool flag) {
    for (int codei=V3ErrorCode::EC_MIN; codei<V3ErrorCode::_ENUM_MAX; codei++) {
        V3ErrorCode code = V3ErrorCode(codei);
        if (code.lintError()) warnOff(code, flag);
    }
}

void FileLine::warnStyleOff(bool flag) {
    for (int codei=V3ErrorCode::EC_MIN; codei<V3ErrorCode::_ENUM_MAX; codei++) {
        V3ErrorCode code = V3ErrorCode(codei);
        if (code.styleError()) warnOff(code, flag);
    }
}

bool FileLine::warnIsOff(V3ErrorCode code) const {
    if (!m_warnOn.test(code)) return true;
    if (!defaultFileLine().m_warnOn.test(code)) return true;  // Global overrides local
    // UNOPTFLAT implies UNOPT
    if (code==V3ErrorCode::UNOPT && !m_warnOn.test(V3ErrorCode::UNOPTFLAT)) return true;
    if ((code.lintError() || code.styleError())
        && !m_warnOn.test(V3ErrorCode::I_LINT)) return true;
    return false;
}

void FileLine::modifyStateInherit(const FileLine* fromp) {
    // Any warnings that are off in "from", become off in "this".
    for (int codei=V3ErrorCode::EC_MIN; codei<V3ErrorCode::_ENUM_MAX; codei++) {
        V3ErrorCode code = V3ErrorCode(codei);
        if (fromp->warnIsOff(code)) { warnOff(code, true); }
    }
}

void FileLine::v3errorEnd(std::ostringstream& str, const string& locationStr) {
    std::ostringstream nsstr;
    if (lastLineno()) nsstr<<this;
    nsstr<<str.str();
    nsstr<<endl;
    std::ostringstream lstr;
    if (!locationStr.empty()) {
        lstr<<std::setw(ascii().length())<<" "<<": "<<locationStr;
    }
    if (warnIsOff(V3Error::errorCode())
        || V3Config::waive(this, V3Error::errorCode(), str.str())) {
        V3Error::suppressThisWarning();
    }
    else if (!V3Error::errorContexted()) nsstr<<warnContextPrimary();
    V3Error::v3errorEnd(nsstr, lstr.str());
}

string FileLine::warnMore() const {
    if (lastLineno()) {
        return V3Error::warnMore()+string(ascii().size(), ' ')+": ";
    } else {
        return V3Error::warnMore();
    }
}
string FileLine::warnOther() const {
    if (lastLineno()) {
        return V3Error::warnMore()+ascii()+": ";
    } else {
        return V3Error::warnMore();
    }
}

string FileLine::source() const {
    if (VL_UNCOVERABLE(!m_contentp)) {
        if (debug() || v3Global.opt.debugCheck()) {
            return "%Error: internal tracking of file contents failed";
        } else {
            return "";
        }
    }
    return m_contentp->getLine(m_contentLineno);
}
string FileLine::prettySource() const {
    string out = source();
    // Drop ignore trailing newline
    string::size_type pos = out.find('\n');
    if (pos != string::npos) out = string(out, 0, pos);
    // Column tracking counts tabs = 1, so match that when print source
    return VString::spaceUnprintable(out);
}

string FileLine::warnContext(bool secondary) const {
    V3Error::errorContexted(true);
    if (!v3Global.opt.context()) return "";
    string out = "";
    if (firstLineno()==lastLineno() && firstColumn()) {
        string sourceLine = prettySource();
        // Don't show super-long lines as can fill screen and unlikely to help user
        if (!sourceLine.empty()
            && sourceLine.length() < SHOW_SOURCE_MAX_LENGTH
            && sourceLine.length() >= (size_t)(lastColumn()-1)) {
            out += sourceLine+"\n";
            out += string((firstColumn()-1), ' ')+'^';
            // Can't use UASSERT_OBJ used in warnings already inside the error end handler
            if (lastColumn() > firstColumn()) {
                // Note lastColumn() can be <= firstColumn() in some weird preproc expansions
                out += string((lastColumn()-firstColumn()-1), '~');
            }
            out += "\n";
        }
    }
    if (!secondary) {  // Avoid printing long paths on informational part of error
        for (FileLine* parentFl = parent(); parentFl; parentFl = parentFl->parent()) {
            if (parentFl->filenameIsGlobal()) break;
            out += parentFl->warnOther()+"... note: In file included from "
                +parentFl->filebasename()+"\n";
        }
    }
    return out;
}

#ifdef VL_LEAK_CHECKS
typedef vl_unordered_set<FileLine*> FileLineCheckSet;
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
    while (1) {
        FileLineCheckSet::iterator it = fileLineLeakChecks.begin();
        if (it==fileLineLeakChecks.end()) break;
        delete *it;
        // Operator delete will remove the iterated object from the list.
        // Eventually the list will be empty and terminate the loop.
    }
    fileLineLeakChecks.clear();
    singleton().clear();
#endif
}
