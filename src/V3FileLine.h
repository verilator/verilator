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

#ifndef VERILATOR_V3FILELINE_H_
#define VERILATOR_V3FILELINE_H_

#include "config_build.h"
#include "verilatedos.h"

#include "V3Error.h"
#include "V3LangCode.h"

#include <atomic>
#include <bitset>
#include <deque>
#include <map>
#include <memory>
#include <set>
#include <sstream>
#include <unordered_map>
#include <vector>

// ######################################################################

class FileLine;

//! Singleton class with tables of per-file data.

//! This singleton class contains tables of data that are unchanging in each
//! source file (each with its own unique filename number).
class FileLineSingleton final {
    friend class FileLine;

    // TYPES
    using fileNameIdx_t = uint16_t;  // Increase width if 64K input files are not enough
    using msgEnSetIdx_t = uint16_t;  // Increase width if 64K unique message sets are not enough
    using MsgEnBitSet = std::bitset<V3ErrorCode::_ENUM_MAX>;

    // MEMBERS
    std::map<const std::string, fileNameIdx_t> m_namemap;  // filenameno for each filename
    std::deque<string> m_names;  // filename text for each filenameno
    std::deque<V3LangCode> m_languages;  // language for each filenameno

    // Map from flag set to the index in m_internedMsgEns for interning
    std::unordered_map<MsgEnBitSet, msgEnSetIdx_t> m_internedMsgEnIdxs;
    // Interned message enablement flag sets
    std::vector<MsgEnBitSet> m_internedMsgEns;

    // CONSTRUCTORS
    FileLineSingleton() = default;
    ~FileLineSingleton() = default;

    fileNameIdx_t nameToNumber(const string& filename);
    string numberToName(fileNameIdx_t filenameno) const { return m_names[filenameno]; }
    V3LangCode numberToLang(fileNameIdx_t filenameno) const { return m_languages[filenameno]; }
    void numberToLang(fileNameIdx_t filenameno, const V3LangCode& l) {
        m_languages[filenameno] = l;
    }
    void clear() {
        m_namemap.clear();
        m_names.clear();
        m_languages.clear();
    }
    void fileNameNumMapDumpXml(std::ostream& os);
    static string filenameLetters(fileNameIdx_t fileno);

    // Add given bitset to the interned bitsets, return interned index
    msgEnSetIdx_t addMsgEnBitSet(const MsgEnBitSet& bitSet);
    // Add index of default bitset
    msgEnSetIdx_t defaultMsgEnIndex();
    // Set bitIdx to value in bitset at interned index setIdx, return interned index of result
    msgEnSetIdx_t msgEnSetBit(msgEnSetIdx_t setIdx, size_t bitIdx, bool value);
    // Return index to intersection set
    msgEnSetIdx_t msgEnAnd(msgEnSetIdx_t lhsIdx, msgEnSetIdx_t rhsIdx);
    // Retrieve interned bitset at given interned index. The returned reference is not persistent.
    const MsgEnBitSet& msgEn(msgEnSetIdx_t idx) const VL_MT_SAFE {
        return m_internedMsgEns.at(idx);
    }
};

// All source lines from a file/stream, to enable errors to show sources
class VFileContent final {
    friend class FileLine;
    // MEMBERS
    int m_id;  // Content ID number
    // Reference count for sharing (shared_ptr has size overhead that we don't want)
    std::atomic<size_t> m_refCount{0};
    std::deque<string> m_lines;  // Source text lines
    VFileContent() {
        static int s_id = 0;
        m_id = ++s_id;
    }
    ~VFileContent() = default;
    // METHODS
    void refInc() { ++m_refCount; }
    void refDec() {
        if (!--m_refCount) delete this;
    }

public:
    void pushText(const string& text);  // Add arbitrary text (need not be line-by-line)
    string getLine(int lineno) const VL_MT_SAFE;
    string ascii() const { return "ct" + cvtToStr(m_id); }
};
std::ostream& operator<<(std::ostream& os, VFileContent* contentp);

// File and line number of an object, mostly for error reporting

// This class is instantiated for every source code line (potentially millions), and  instances
// created at any point usually persist until the end of the program. To save space, per-file
// information (e.g. filename, source language) is held in tables in the FileLineSingleton class.
// Similarly, message enablement flags are interned in FileLineSingleton.

// WARNING: Avoid increasing the size of this class as much as possible.
class FileLine final {

    // CONSTANTS
    static constexpr unsigned SHOW_SOURCE_MAX_LENGTH = 400;  // Don't show source lines > this long

    // TYPES
    using fileNameIdx_t = FileLineSingleton::fileNameIdx_t;
    using msgEnSetIdx_t = FileLineSingleton::msgEnSetIdx_t;
    using MsgEnBitSet = FileLineSingleton::MsgEnBitSet;

    // MEMBERS
    // Columns here means number of chars from beginning (i.e. tabs count as one)
    msgEnSetIdx_t m_msgEnIdx = 0;  // Message enable bit set (index into interned array)
    fileNameIdx_t m_filenameno = 0;  // `line corrected filename number
    bool m_waive : 1;  // Waive warning - pack next to the line number to save 8 bytes of storage
    unsigned m_contentLineno : 31;  // Line number within source stream
    int m_firstLineno = 0;  // `line corrected token's first line number
    int m_firstColumn = 0;  // `line corrected token's first column number
    int m_lastLineno = 0;  // `line corrected token's last line number
    int m_lastColumn = 0;  // `line corrected token's last column number
    VFileContent* m_contentp = nullptr;  // Source text contents line is within
    FileLine* m_parent = nullptr;  // Parent line that included this line

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
        static FileLine s;
        return s;
    }

    FileLine()  // Only used for defaultFileLine above
        : m_msgEnIdx{singleton().defaultMsgEnIndex()}
        , m_filenameno{singleton().nameToNumber(FileLine::builtInFilename())}
        , m_waive{false}
        , m_contentLineno{0} {}

public:
    explicit FileLine(const string& filename)
        : m_msgEnIdx{defaultFileLine().m_msgEnIdx}
        , m_filenameno{singleton().nameToNumber(filename)}
        , m_waive{false}
        , m_contentLineno{0} {}
    explicit FileLine(FileLine* fromp)
        : m_msgEnIdx{fromp->m_msgEnIdx}
        , m_filenameno{fromp->m_filenameno}
        , m_waive{fromp->m_waive}
        , m_contentLineno{fromp->m_contentLineno}
        , m_firstLineno{fromp->m_firstLineno}
        , m_firstColumn{fromp->m_firstColumn}
        , m_lastLineno{fromp->m_lastLineno}
        , m_lastColumn{fromp->m_lastColumn}
        , m_contentp{fromp->m_contentp}
        , m_parent{fromp->m_parent} {
        if (m_contentp) m_contentp->refInc();
    }
    FileLine* copyOrSameFileLine();
    static void deleteAllRemaining();
    ~FileLine();
#ifdef VL_LEAK_CHECKS
    static void* operator new(size_t size);
    static void operator delete(void* obj, size_t size);
#endif
    // METHODS
    void newContent();
    void contentLineno(int num) {
        lineno(num);
        m_contentLineno = static_cast<unsigned>(num);
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
    int firstLineno() const VL_MT_SAFE { return m_firstLineno; }
    int firstColumn() const VL_MT_SAFE { return m_firstColumn; }
    int lastLineno() const VL_MT_SAFE { return m_lastLineno; }
    int lastColumn() const VL_MT_SAFE { return m_lastColumn; }
    VFileContent* contentp() const { return m_contentp; }
    // If not otherwise more specific, use last lineno for errors etc,
    // as the parser errors etc generally make more sense pointing at the last parse point
    int lineno() const VL_MT_SAFE { return m_lastLineno; }
    string source() const VL_MT_SAFE;
    string prettySource() const VL_MT_SAFE;  // Source, w/stripped unprintables and newlines
    FileLine* parent() const VL_MT_SAFE { return m_parent; }
    V3LangCode language() const { return singleton().numberToLang(filenameno()); }
    string ascii() const;
    string asciiLineCol() const;
    int filenameno() const VL_MT_SAFE { return m_filenameno; }
    string filename() const VL_MT_SAFE { return singleton().numberToName(filenameno()); }
    bool filenameIsGlobal() const VL_MT_SAFE {
        return (filename() == commandLineFilename() || filename() == builtInFilename());
    }
    string filenameLetters() const VL_MT_SAFE {
        return FileLineSingleton::filenameLetters(filenameno());
    }
    string filebasename() const VL_MT_SAFE;
    string filebasenameNoExt() const;
    string firstColumnLetters() const VL_MT_SAFE;
    string profileFuncname() const;
    string xmlDetailedLocation() const;
    string lineDirectiveStrg(int enterExit) const;

    // Turn on/off warning messages on this line.
    void warnOn(V3ErrorCode code, bool flag) {
        if (code == V3ErrorCode::WIDTH) {
            warnOn(V3ErrorCode::WIDTHTRUNC, flag);
            warnOn(V3ErrorCode::WIDTHEXPAND, flag);
            warnOn(V3ErrorCode::WIDTHXZEXPAND, flag);
        }
        m_msgEnIdx = singleton().msgEnSetBit(m_msgEnIdx, code, flag);
    }
    void warnOff(V3ErrorCode code, bool flag) { warnOn(code, !flag); }
    bool warnOff(const string& msg, bool flag);  // Returns 1 if ok
    bool warnIsOff(V3ErrorCode code) const;
    void warnLintOff(bool flag);
    void warnStyleOff(bool flag);
    void warnUnusedOff(bool flag);
    void warnStateFrom(const FileLine& from) { m_msgEnIdx = from.m_msgEnIdx; }
    void warnResetDefault() { warnStateFrom(defaultFileLine()); }
    bool lastWarnWaived() const { return m_waive; }

    // Specific flag ACCESSORS/METHODS
    bool celldefineOn() const { return msgEn().test(V3ErrorCode::I_CELLDEFINE); }
    void celldefineOn(bool flag) { warnOn(V3ErrorCode::I_CELLDEFINE, flag); }
    bool coverageOn() const { return msgEn().test(V3ErrorCode::I_COVERAGE); }
    void coverageOn(bool flag) { warnOn(V3ErrorCode::I_COVERAGE, flag); }
    bool tracingOn() const { return msgEn().test(V3ErrorCode::I_TRACING); }
    void tracingOn(bool flag) { warnOn(V3ErrorCode::I_TRACING, flag); }
    bool timingOn() const { return msgEn().test(V3ErrorCode::I_TIMING); }
    void timingOn(bool flag) { warnOn(V3ErrorCode::I_TIMING, flag); }

    // METHODS - Global
    // <command-line> and <built-in> match what GCC outputs
    static string commandLineFilename() VL_MT_SAFE { return "<command-line>"; }
    static string builtInFilename() VL_MT_SAFE { return "<built-in>"; }
    static void globalWarnLintOff(bool flag) { defaultFileLine().warnLintOff(flag); }
    static void globalWarnStyleOff(bool flag) { defaultFileLine().warnStyleOff(flag); }
    static void globalWarnUnusedOff(bool flag) { defaultFileLine().warnUnusedOff(flag); }
    static void globalWarnOff(V3ErrorCode code, bool flag) {
        defaultFileLine().warnOff(code, flag);
    }
    static bool globalWarnOff(const string& code, bool flag) {
        return defaultFileLine().warnOff(code, flag);
    }
    static void fileNameNumMapDumpXml(std::ostream& os) { singleton().fileNameNumMapDumpXml(os); }

    // METHODS - Called from netlist
    // Merge warning disables from another fileline
    void modifyStateInherit(const FileLine* fromp) {
        m_msgEnIdx = singleton().msgEnAnd(m_msgEnIdx, fromp->m_msgEnIdx);
    }
    // Change the current fileline due to actions discovered after parsing
    // and may have side effects on other nodes sharing this FileLine.
    // Use only when this is intended
    void modifyWarnOff(V3ErrorCode code, bool flag) { warnOff(code, flag); }

    // OPERATORS
    void v3errorEnd(std::ostringstream& str, const string& extra = "")
        VL_REQUIRES(V3Error::s().m_mutex);
    void v3errorEndFatal(std::ostringstream& str) VL_ATTR_NORETURN
        VL_REQUIRES(V3Error::s().m_mutex) {
        v3errorEnd(str);
        assert(0);  // LCOV_EXCL_LINE
        VL_UNREACHABLE;
    }
    /// When building an error, prefix for printing continuation lines
    /// e.g. information referring to the same FileLine as before
    string warnMore() const VL_REQUIRES(V3Error::s().m_mutex);
    /// When building an error, prefix for printing secondary information
    /// from a different FileLine than the original error
    string warnOther() const VL_REQUIRES(V3Error::s().m_mutex);
    string warnOtherStandalone() const VL_EXCLUDES(V3Error::s().m_mutex) VL_MT_UNSAFE;
    /// When building an error, current location in include etc
    /// If not used in a given error, automatically pasted at end of error
    string warnContextPrimary() const VL_REQUIRES(V3Error::s().m_mutex) {
        V3Error::s().errorContexted(true);
        return warnContext() + warnContextParent();
    }
    /// When building an error, additional location for additional references
    /// Simplified information vs warnContextPrimary() to make dump clearer
    string warnContextSecondary() const { return warnContext(); }
    bool operator==(const FileLine& rhs) const {
        return (m_firstLineno == rhs.m_firstLineno && m_firstColumn == rhs.m_firstColumn
                && m_lastLineno == rhs.m_lastLineno && m_lastColumn == rhs.m_lastColumn
                && m_filenameno == rhs.m_filenameno && m_msgEnIdx == rhs.m_msgEnIdx);
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
        for (size_t i = 0; i < msgEn().size(); ++i) {
            if (msgEn().test(i) != rhs.msgEn().test(i)) return rhs.msgEn().test(i) ? -1 : 1;
        }
        return 0;  // (*this) and rhs are equivalent
    }

private:
    string warnContext() const;
    string warnContextParent() const VL_REQUIRES(V3Error::s().m_mutex);
    const MsgEnBitSet& msgEn() const VL_MT_SAFE { return singleton().msgEn(m_msgEnIdx); }
};
std::ostream& operator<<(std::ostream& os, FileLine* fileline);

#endif  // Guard
