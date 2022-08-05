// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Error handling
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2022 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#ifndef VERILATOR_V3FILELINE_H_
#define VERILATOR_V3FILELINE_H_

#include "config_build.h"
#include "verilatedos.h"

#include "V3Error.h"
#include "V3LangCode.h"

#include <bitset>
#include <deque>
#include <map>
#include <memory>
#include <set>
#include <sstream>

//######################################################################

class FileLine;

//! Singleton class with tables of per-file data.

//! This singleton class contains tables of data that are unchanging in each
//! source file (each with its own unique filename number).
class FileLineSingleton final {
    // MEMBERS
    std::map<const std::string, int> m_namemap;  // filenameno for each filename
    std::deque<string> m_names;  // filename text for each filenameno
    std::deque<V3LangCode> m_languages;  // language for each filenameno
    // CONSTRUCTORS
    FileLineSingleton() = default;
    ~FileLineSingleton() = default;

protected:
    friend class FileLine;
    int nameToNumber(const string& filename);
    string numberToName(int filenameno) const { return m_names[filenameno]; }
    V3LangCode numberToLang(int filenameno) const { return m_languages[filenameno]; }
    void numberToLang(int filenameno, const V3LangCode& l) { m_languages[filenameno] = l; }
    void clear() {
        m_namemap.clear();
        m_names.clear();
        m_languages.clear();
    }
    void fileNameNumMapDumpXml(std::ostream& os);
    static string filenameLetters(int fileno);
};

//! All source lines from a file/stream, to enable errors to show sources
class VFileContent final {
    // MEMBERS
    int m_id;  // Content ID number
    std::deque<string> m_lines;  // Source text lines
public:
    VFileContent() {
        static int s_id = 0;
        m_id = ++s_id;
    }
    ~VFileContent() = default;
    // METHODS
    void pushText(const string& text);  // Add arbitrary text (need not be line-by-line)
    string getLine(int lineno) const;
    string ascii() const { return "ct" + cvtToStr(m_id); }
    static int debug();
};
std::ostream& operator<<(std::ostream& os, VFileContent* contentp);

//! File and line number of an object, mostly for error reporting

//! This class is instantiated for every source code line (potentially
//! millions). To save space, per-file information (e.g. filename, source
//! language is held in tables in the FileLineSingleton class.
class FileLine final {
    // CONSTANTS
    static constexpr unsigned SHOW_SOURCE_MAX_LENGTH = 400;  // Don't show source lines > this long

    // MEMBERS
    // Columns here means number of chars from beginning (i.e. tabs count as one)
    int m_firstLineno = 0;  // `line corrected token's first line number
    int m_firstColumn = 0;  // `line corrected token's first column number
    int m_lastLineno = 0;  // `line corrected token's last line number
    int m_lastColumn = 0;  // `line corrected token's last column number
    int m_filenameno;  // `line corrected filename number
    int m_contentLineno = 0;  // Line number within source stream
    std::shared_ptr<VFileContent> m_contentp = nullptr;  // Source text contents line is within
    FileLine* m_parent = nullptr;  // Parent line that included this line
    std::bitset<V3ErrorCode::_ENUM_MAX> m_warnOn;
    bool m_waive = false;  // Waive warning

protected:
    // User routines should never need to change line numbers
    // We are storing pointers, so we CAN'T change them after initial reading.
    friend class FileLineSingleton;
    friend class V3ParseImp;
    friend class V3PreLex;
    friend class V3PreProcImp;
    friend class V3PreShellImp;

private:
    // CONSTRUCTORS
    static FileLineSingleton& singleton() {
        static FileLineSingleton s;
        return s;
    }
    static FileLine& defaultFileLine() {
        static FileLine* defFilelinep = new FileLine(FileLine::EmptySecret());
        return *defFilelinep;
    }

public:
    explicit FileLine(const string& filename)
        : m_filenameno{singleton().nameToNumber(filename)}
        , m_warnOn{defaultFileLine().m_warnOn} {}
    explicit FileLine(FileLine* fromp)
        : m_firstLineno{fromp->m_firstLineno}
        , m_firstColumn{fromp->m_firstColumn}
        , m_lastLineno{fromp->m_lastLineno}
        , m_lastColumn{fromp->m_lastColumn}
        , m_filenameno{fromp->m_filenameno}
        , m_contentLineno{fromp->m_contentLineno}
        , m_contentp{fromp->m_contentp}
        , m_parent{fromp->m_parent}
        , m_warnOn{fromp->m_warnOn}
        , m_waive{fromp->m_waive} {}
    struct EmptySecret {};  // Constructor selection
    explicit FileLine(EmptySecret);
    FileLine* copyOrSameFileLine();
    static void deleteAllRemaining();
    ~FileLine() = default;
#ifdef VL_LEAK_CHECKS
    static void* operator new(size_t size);
    static void operator delete(void* obj, size_t size);
#endif
    // METHODS
    void newContent();
    void contentLineno(int num) {
        lineno(num);
        m_contentLineno = num;
    }
    void lineno(int num) {
        m_firstLineno = num;
        m_lastLineno = num;
        m_firstColumn = m_lastColumn = 1;
    }
    void column(int firstColumn, int lastColumn) {
        m_firstColumn = firstColumn;
        m_lastColumn = lastColumn;
    }
    void language(V3LangCode lang) const { singleton().numberToLang(filenameno(), lang); }
    void filename(const string& name) { m_filenameno = singleton().nameToNumber(name); }
    void parent(FileLine* fileline) { m_parent = fileline; }
    void lineDirective(const char* textp, int& enterExitRef);
    void linenoInc() {
        m_lastLineno++;
        m_lastColumn = 1;
        m_contentLineno++;
    }
    void startToken() {
        m_firstLineno = m_lastLineno;
        m_firstColumn = m_lastColumn;
    }
    // Advance last line/column based on given text
    void forwardToken(const char* textp, size_t size, bool trackLines = true);
    int firstLineno() const { return m_firstLineno; }
    int firstColumn() const { return m_firstColumn; }
    int lastLineno() const { return m_lastLineno; }
    int lastColumn() const { return m_lastColumn; }
    std::shared_ptr<VFileContent> contentp() const { return m_contentp; }
    // If not otherwise more specific, use last lineno for errors etc,
    // as the parser errors etc generally make more sense pointing at the last parse point
    int lineno() const { return m_lastLineno; }
    string source() const;
    string prettySource() const;  // Source, w/stripped unprintables and newlines
    FileLine* parent() const { return m_parent; }
    V3LangCode language() const { return singleton().numberToLang(filenameno()); }
    string ascii() const;
    string asciiLineCol() const;
    int filenameno() const { return m_filenameno; }
    string filename() const { return singleton().numberToName(filenameno()); }
    bool filenameIsGlobal() const {
        return (filename() == commandLineFilename() || filename() == builtInFilename());
    }
    string filenameLetters() const { return FileLineSingleton::filenameLetters(filenameno()); }
    string filebasename() const;
    string filebasenameNoExt() const;
    string firstColumnLetters() const;
    string profileFuncname() const;
    string xmlDetailedLocation() const;
    string lineDirectiveStrg(int enterExit) const;

    // Turn on/off warning messages on this line.
    void warnOn(V3ErrorCode code, bool flag) { m_warnOn.set(code, flag); }
    void warnOff(V3ErrorCode code, bool flag) { warnOn(code, !flag); }
    bool warnOff(const string& msg, bool flag);  // Returns 1 if ok
    bool warnIsOff(V3ErrorCode code) const;
    void warnLintOff(bool flag);
    void warnStyleOff(bool flag);
    void warnStateFrom(const FileLine& from) { m_warnOn = from.m_warnOn; }
    void warnResetDefault() { warnStateFrom(defaultFileLine()); }
    bool lastWarnWaived() const { return m_waive; }

    // Specific flag ACCESSORS/METHODS
    bool celldefineOn() const { return m_warnOn.test(V3ErrorCode::I_CELLDEFINE); }
    void celldefineOn(bool flag) { warnOn(V3ErrorCode::I_CELLDEFINE, flag); }
    bool coverageOn() const { return m_warnOn.test(V3ErrorCode::I_COVERAGE); }
    void coverageOn(bool flag) { warnOn(V3ErrorCode::I_COVERAGE, flag); }
    bool tracingOn() const { return m_warnOn.test(V3ErrorCode::I_TRACING); }
    void tracingOn(bool flag) { warnOn(V3ErrorCode::I_TRACING, flag); }

    // METHODS - Global
    // <command-line> and <built-in> match what GCC outputs
    static string commandLineFilename() { return "<command-line>"; }
    static string builtInFilename() { return "<built-in>"; }
    static void globalWarnLintOff(bool flag) { defaultFileLine().warnLintOff(flag); }
    static void globalWarnStyleOff(bool flag) { defaultFileLine().warnStyleOff(flag); }
    static void globalWarnOff(V3ErrorCode code, bool flag) {
        defaultFileLine().warnOff(code, flag);
    }
    static bool globalWarnOff(const string& code, bool flag) {
        return defaultFileLine().warnOff(code, flag);
    }
    static void fileNameNumMapDumpXml(std::ostream& os) { singleton().fileNameNumMapDumpXml(os); }

    // METHODS - Called from netlist
    // Merge warning disables from another fileline
    void modifyStateInherit(const FileLine* fromp);
    // Change the current fileline due to actions discovered after parsing
    // and may have side effects on other nodes sharing this FileLine.
    // Use only when this is intended
    void modifyWarnOff(V3ErrorCode code, bool flag) { warnOff(code, flag); }

    // OPERATORS
    void v3errorEnd(std::ostringstream& str, const string& extra = "");
    void v3errorEndFatal(std::ostringstream& str) VL_ATTR_NORETURN;
    /// When building an error, prefix for printing continuation lines
    /// e.g. information referring to the same FileLine as before
    string warnMore() const;
    /// When building an error, prefix for printing secondary information
    /// from a different FileLine than the original error
    string warnOther() const;
    /// When building an error, current location in include etc
    /// If not used in a given error, automatically pasted at end of error
    string warnContextPrimary() const { return warnContext(false); }
    /// When building an error, additional location for additional references
    /// Simplified information vs warnContextPrimary() to make dump clearer
    string warnContextSecondary() const { return warnContext(true); }
    bool operator==(const FileLine& rhs) const {
        return (m_firstLineno == rhs.m_firstLineno && m_firstColumn == rhs.m_firstColumn
                && m_lastLineno == rhs.m_lastLineno && m_lastColumn == rhs.m_lastColumn
                && m_filenameno == rhs.m_filenameno && m_warnOn == rhs.m_warnOn);
    }
    // Returns -1 if (*this) should come before rhs after sorted. 1 for the opposite case. 0 for
    // equivalent.
    int operatorCompare(const FileLine& rhs) const {
        if (m_filenameno != rhs.m_filenameno) return (m_filenameno < rhs.m_filenameno) ? -1 : 1;
        if (m_firstLineno != rhs.m_firstLineno)
            return (m_firstLineno < rhs.m_firstLineno) ? -1 : 1;
        if (m_firstColumn != rhs.m_firstColumn)
            return (m_firstColumn < rhs.m_firstColumn) ? -1 : 1;
        if (m_lastLineno != rhs.m_lastLineno) return (m_lastLineno < rhs.m_lastLineno) ? -1 : 1;
        if (m_lastColumn != rhs.m_lastColumn) return (m_lastColumn < rhs.m_lastColumn) ? -1 : 1;
        for (size_t i = 0; i < m_warnOn.size(); ++i) {
            if (m_warnOn[i] != rhs.m_warnOn[i]) return (m_warnOn[i] < rhs.m_warnOn[i]) ? -1 : 1;
        }
        return 0;  // (*this) and rhs are equivalent
    }

private:
    string warnContext(bool secondary) const;
};
std::ostream& operator<<(std::ostream& os, FileLine* fileline);

inline void FileLine::v3errorEndFatal(std::ostringstream& str) {
    v3errorEnd(str);
    assert(0);  // LCOV_EXCL_LINE
    VL_UNREACHABLE
}

#endif  // Guard
