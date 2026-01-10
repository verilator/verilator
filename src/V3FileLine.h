// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Error handling
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2026 by Wilson Snyder. This program is free software; you
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
#include "V3Hash.h"
#include "V3LangCode.h"
#include "V3Mutex.h"

#include <atomic>
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
    class MsgEnBitSet final {
        VErrorBitSet m_codeEn;  // Enabled by code directives/metacomments
        VErrorBitSet m_ctrlEn;  // Enabled by control file

    public:
        enum class Subset {
            CODE = 0,  // Selects m_codeEn, the enable bits used by in-code directives/metacomments
            CTRL = 1,  // Selects m_ctrlEn, the enable bits used by control files
        };

        // Create empty set
        MsgEnBitSet() = default;
        // Create intersection set
        MsgEnBitSet(const MsgEnBitSet& a, const MsgEnBitSet& b)
            : m_codeEn{a.m_codeEn & b.m_codeEn}
            , m_ctrlEn{a.m_ctrlEn & b.m_ctrlEn} {}

        struct Hash final {
            size_t operator()(const MsgEnBitSet& item) const {
                V3Hash hash{item.m_codeEn.hash()};
                hash += item.m_ctrlEn.hash();
                return hash.value();
            }
        };

        struct Equal final {
            bool operator()(const MsgEnBitSet& a, const MsgEnBitSet& b) const { return a == b; }
        };

        bool operator==(const MsgEnBitSet& other) const {
            return m_codeEn == other.m_codeEn && m_ctrlEn == other.m_ctrlEn;
        }

        const VErrorBitSet& getAll(Subset subset) const {
            return subset == Subset::CODE ? m_codeEn : m_ctrlEn;
        }
        bool test(Subset subset, V3ErrorCode code) const {
            return subset == Subset::CODE ? m_codeEn.test(code) : m_ctrlEn.test(code);
        }
        void setAll(Subset subset, const VErrorBitSet& bitset) {
            if (subset == Subset::CODE) {  // LCOV_EXCL_BR_LINE
                m_codeEn = bitset;  // LCOV_EXCL_LINE
            } else {
                m_ctrlEn = bitset;
            }
        }
        void set(Subset subset, V3ErrorCode code, bool value) {
            if (subset == Subset::CODE) {
                m_codeEn.set(code, value);
            } else {
                m_ctrlEn.set(code, value);
            }
        }

        // Enabled iff enabled by both in-code dierctives/metacomments and control file
        bool enabled(V3ErrorCode code) const { return m_codeEn.test(code) && m_ctrlEn.test(code); }
    };

    // MEMBERS
    V3Mutex m_mutex;  // protects members
    std::map<const std::string, fileNameIdx_t> m_namemap;  // filenameno for each filename
    std::deque<string> m_names;  // filename text for each filenameno
    std::deque<V3LangCode> m_languages;  // language for each filenameno

    // Map from flag set to the index in m_internedMsgEns for interning
    std::unordered_map<MsgEnBitSet, msgEnSetIdx_t, MsgEnBitSet::Hash, MsgEnBitSet::Equal>
        m_internedMsgEnIdxs VL_GUARDED_BY(m_mutex);
    // Interned message enablement flag sets
    std::vector<MsgEnBitSet> m_internedMsgEns;

    // CONSTRUCTORS
    FileLineSingleton() = default;
    ~FileLineSingleton() = default;

    fileNameIdx_t nameToNumber(const string& filename);
    const std::string& numberToName(fileNameIdx_t filenameno) const VL_MT_SAFE {
        return m_names[filenameno];
    }
    V3LangCode numberToLang(fileNameIdx_t filenameno) const { return m_languages[filenameno]; }
    void numberToLang(fileNameIdx_t filenameno, const V3LangCode& l) {
        m_languages[filenameno] = l;
    }
    void clear() {
        m_namemap.clear();
        m_names.clear();
        m_languages.clear();
    }
    void fileNameNumMapDumpJson(std::ostream& os);
    static string filenameLetters(fileNameIdx_t fileno) VL_PURE;

    // Add given bitset to the interned bitsets, return interned index
    msgEnSetIdx_t addMsgEnBitSet(const MsgEnBitSet& bitSet) VL_MT_SAFE_EXCLUDES(m_mutex);
    // Add index of default bitset
    msgEnSetIdx_t defaultMsgEnIndex() VL_MT_SAFE;
    // Set code to value in bitset at interned index setIdx, return interned index of result
    msgEnSetIdx_t msgEnSetBit(msgEnSetIdx_t setIdx, MsgEnBitSet::Subset subset, V3ErrorCode code,
                              bool value);
    // Bulk-set all control codes to given bitset
    msgEnSetIdx_t msgSetCtrlBitSet(msgEnSetIdx_t setIdx, const VErrorBitSet& bitset);
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

// This class is instantiated for every source code line (potentially millions), and instances
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
    // 64-bit word # 0
    msgEnSetIdx_t m_msgEnIdx = 0;  // Message enable bit set (index into interned array)
    fileNameIdx_t m_filenameno = 0;  // `line corrected filename number
    bool m_waive : 1;  // Waive warning - pack next to the line number to save 8 bytes of storage
    unsigned m_contentLineno : 31;  // Line number within source stream
    // 64-bit word # 1
    uint32_t m_tokenNum = 0;  // Token number in processing order
    int m_firstLineno = 0;  // `line corrected token's first line number
    // 64-bit word # 2
    uint32_t m_firstColumn : 24;  // `line corrected token's first column number
    uint32_t m_lastColumn : 24;  // `line corrected token's last column number
    uint16_t m_lastLinenoAdder = 0;  // Last line number as offset from m_firstLineno
    // 64-bit word # 3/4
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
    static FileLineSingleton& singleton() VL_MT_SAFE {
        static FileLineSingleton s;
        return s;
    }
    static FileLine& defaultFileLine() VL_MT_SAFE {
        static FileLine s;
        return s;
    }

    FileLine()  // Only used for defaultFileLine above
        : m_msgEnIdx{singleton().defaultMsgEnIndex()}
        , m_filenameno{singleton().nameToNumber(FileLine::builtInFilename())}
        , m_waive{false}
        , m_contentLineno{0}
        , m_firstColumn{0}
        , m_lastColumn{0} {}

public:
    explicit FileLine(const string& filename)
        : m_msgEnIdx{defaultFileLine().m_msgEnIdx}
        , m_filenameno{singleton().nameToNumber(filename)}
        , m_waive{false}
        , m_contentLineno{0}
        , m_firstColumn{0}
        , m_lastColumn{0} {}
    explicit FileLine(const FileLine& from)
        : m_msgEnIdx{from.m_msgEnIdx}
        , m_filenameno{from.m_filenameno}
        , m_waive{from.m_waive}
        , m_contentLineno{from.m_contentLineno}
        , m_tokenNum{from.m_tokenNum}
        , m_firstLineno{from.m_firstLineno}
        , m_firstColumn{from.m_firstColumn}
        , m_lastColumn{from.m_lastColumn}
        , m_lastLinenoAdder{from.m_lastLinenoAdder}
        , m_contentp{from.m_contentp}
        , m_parent{from.m_parent} {
        if (m_contentp) m_contentp->refInc();
    }
    explicit FileLine(FileLine* fromp)
        : m_msgEnIdx{fromp->m_msgEnIdx}
        , m_filenameno{fromp->m_filenameno}
        , m_waive{fromp->m_waive}
        , m_contentLineno{fromp->m_contentLineno}
        , m_tokenNum{fromp->m_tokenNum}
        , m_firstLineno{fromp->m_firstLineno}
        , m_firstColumn{fromp->m_firstColumn}
        , m_lastColumn{fromp->m_lastColumn}
        , m_lastLinenoAdder{fromp->m_lastLinenoAdder}
        , m_contentp{fromp->m_contentp}
        , m_parent{fromp->m_parent} {
        if (m_contentp) m_contentp->refInc();
    }
    void applyIgnores();
    FileLine* copyOrSameFileLine();
    FileLine* copyOrSameFileLineApplied();
    static void deleteAllRemaining();
    static void stats();
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
    void contentLinenoFrom(const FileLine* fromp) { m_contentLineno = fromp->m_contentLineno; }
    void lineno(int num) {
        m_firstLineno = num;
        m_lastLinenoAdder = 0;
        m_firstColumn = 1;
        m_lastColumn = 1;
    }
    void column(int firstColumn, int lastColumn) {
        m_firstColumn = firstColumn;
        m_lastColumn = lastColumn;
    }
    void language(V3LangCode lang) const { singleton().numberToLang(filenameno(), lang); }
    void filename(const string& name) { m_filenameno = singleton().nameToNumber(name); }
    void parent(FileLine* fileline) { m_parent = fileline; }
    void lineDirective(const char* textp, int& enterExitRef);
    void lineDirectiveParse(const char* textp, string& filenameRef, int& linenoRef,
                            int& enterExitRef);
    void linenoInc() {
        if (m_lastLinenoAdder == 65535) {
            // Overflow can only happen on super-long comment, adjust
            // starting first line to deal with it this will make token
            // start later than in reality, but nothing should refer to it,
            // and the overall line number will not drift.
            m_firstLineno += 65535 + 1;
            m_lastLinenoAdder = 0;
        } else {
            ++m_lastLinenoAdder;
        }
        m_lastColumn = 1;
        ++m_contentLineno;
    }
    void startToken() {
        m_firstLineno = lastLineno();
        m_firstColumn = m_lastColumn;
        m_lastLinenoAdder = 0;
    }
    // Advance last line/column based on given text
    void forwardToken(const char* textp, size_t size, bool trackLines = true);
    uint32_t tokenNum() const VL_MT_SAFE { return m_tokenNum; }
    int firstLineno() const VL_MT_SAFE { return m_firstLineno; }
    int firstColumn() const VL_MT_SAFE { return static_cast<int>(m_firstColumn); }
    int lastLineno() const VL_MT_SAFE { return m_firstLineno + m_lastLinenoAdder; }
    int lastColumn() const VL_MT_SAFE { return static_cast<int>(m_lastColumn); }
    VFileContent* contentp() const { return m_contentp; }
    // If not otherwise more specific, use last lineno for errors etc,
    // as the parser errors etc generally make more sense pointing at the last parse point
    int lineno() const VL_MT_SAFE { return lastLineno(); }
    string source() const VL_MT_SAFE;
    string sourcePrefix(int toColumn) const VL_MT_SAFE;
    string prettySource() const VL_MT_SAFE;  // Source, w/stripped unprintables and newlines
    FileLine* parent() const VL_MT_SAFE { return m_parent; }
    V3LangCode language() const { return singleton().numberToLang(filenameno()); }
    string ascii() const VL_MT_SAFE;
    string asciiLineCol() const;
    int filenameno() const VL_MT_SAFE { return m_filenameno; }
    const std::string& filename() const VL_MT_SAFE {
        return singleton().numberToName(filenameno());
    }
    // Filename with C string escapes
    string filenameEsc() const VL_MT_SAFE { return VString::quoteBackslash(filename()); }
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
    string lineDirectiveStrg(int enterExit) const;

    // Turn on/off warning messages on this line.
private:
    void warnSet(MsgEnBitSet::Subset subset, V3ErrorCode code, bool flag) {
        m_msgEnIdx = singleton().msgEnSetBit(m_msgEnIdx, subset, code, flag);
    }

public:
    void warnOn(V3ErrorCode code, bool flag) { warnSet(MsgEnBitSet::Subset::CODE, code, flag); }
    void warnSetCtrlBitSet(const VErrorBitSet& bitset) {
        m_msgEnIdx = singleton().msgSetCtrlBitSet(m_msgEnIdx, bitset);
    }
    void warnOff(V3ErrorCode code, bool turnOff) { warnOn(code, !turnOff); }
    string warnOffParse(const string& msgs, bool turnOff);  // Returns "" if ok
    bool warnIsOff(V3ErrorCode code) const VL_MT_SAFE;
    void warnLintOff(bool turnOff);
    void warnStyleOff(bool turnOff);
    void warnStateFrom(const FileLine& from) { m_msgEnIdx = from.m_msgEnIdx; }
    void warnResetDefault() { warnStateFrom(defaultFileLine()); }

    // Specific flag ACCESSORS/METHODS
    bool celldefineOn() const { return msgEn().enabled(V3ErrorCode::I_CELLDEFINE); }
    void celldefineOn(bool flag) { warnOn(V3ErrorCode::I_CELLDEFINE, flag); }
    bool coverageOn() const { return msgEn().enabled(V3ErrorCode::I_COVERAGE); }
    void coverageOn(bool flag) { warnOn(V3ErrorCode::I_COVERAGE, flag); }
    bool tracingOn() const { return msgEn().enabled(V3ErrorCode::I_TRACING); }
    void tracingOn(bool flag) { warnOn(V3ErrorCode::I_TRACING, flag); }
    bool timingOn() const { return msgEn().enabled(V3ErrorCode::I_TIMING); }
    void timingOn(bool flag) { warnOn(V3ErrorCode::I_TIMING, flag); }

    // METHODS - Global
    // <command-line> and <built-in> match what GCC outputs
    static string commandLineFilename() VL_MT_SAFE { return "<command-line>"; }
    static string builtInFilename() VL_MT_SAFE { return "<built-in>"; }
    static void globalWarnOff(V3ErrorCode code, bool turnOff) {
        defaultFileLine().warnOff(code, turnOff);
    }
    static string globalWarnOffParse(const string& msgs, bool turnOff) {
        return defaultFileLine().warnOffParse(msgs, turnOff);
    }
    static void fileNameNumMapDumpJson(std::ostream& os) {
        singleton().fileNameNumMapDumpJson(os);
    }

    // METHODS - Called from netlist
    // Merge warning disables from another fileline
    void modifyStateInherit(const FileLine* fromp) {
        m_msgEnIdx = singleton().msgEnAnd(m_msgEnIdx, fromp->m_msgEnIdx);
    }
    // Change the current fileline due to actions discovered after parsing
    // and may have side effects on other nodes sharing this FileLine.
    // Use only when this is intended
    void modifyWarnOff(V3ErrorCode code, bool turnOff) { warnOff(code, turnOff); }

    // OPERATORS
    void v3errorEnd(std::ostringstream& str, const string& extra = "")
        VL_RELEASE(V3Error::s().m_mutex);
    void v3errorEndFatal(std::ostringstream& str) VL_ATTR_NORETURN
        VL_RELEASE(V3Error::s().m_mutex) {
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
        return (m_tokenNum == rhs.m_tokenNum && m_firstLineno == rhs.m_firstLineno
                && m_firstColumn == rhs.m_firstColumn && m_lastLinenoAdder == rhs.m_lastLinenoAdder
                && m_lastColumn == rhs.m_lastColumn && m_filenameno == rhs.m_filenameno
                && m_msgEnIdx == rhs.m_msgEnIdx);
    }
    bool equalFirstLineCol(const FileLine& rhs) const {
        return (m_filenameno == rhs.m_filenameno && m_firstLineno == rhs.m_firstLineno
                && m_firstColumn == rhs.m_firstColumn);
    }
    // Returns -1 if (*this) should come before rhs after sorted. 1 for the opposite case. 0 for
    // equivalent.
    int operatorCompare(const FileLine& rhs) const {
        if (m_filenameno != rhs.m_filenameno) return (m_filenameno < rhs.m_filenameno) ? -1 : 1;
        if (m_firstLineno != rhs.m_firstLineno)
            return (m_firstLineno < rhs.m_firstLineno) ? -1 : 1;
        if (m_firstColumn != rhs.m_firstColumn)
            return (m_firstColumn < rhs.m_firstColumn) ? -1 : 1;
        if (m_lastLinenoAdder != rhs.m_lastLinenoAdder)
            return (m_lastLinenoAdder < rhs.m_lastLinenoAdder) ? -1 : 1;
        if (m_lastColumn != rhs.m_lastColumn) return (m_lastColumn < rhs.m_lastColumn) ? -1 : 1;
        const MsgEnBitSet& lhsMsgEn = msgEn();
        const MsgEnBitSet& rhsMsgEn = rhs.msgEn();
        for (size_t i = 0; i < V3ErrorCode::_ENUM_MAX; ++i) {
            V3ErrorCode code = static_cast<V3ErrorCode>(i);
            if (lhsMsgEn.enabled(code) != rhsMsgEn.enabled(code))
                return rhsMsgEn.enabled(code) ? -1 : 1;
        }
        // TokenNum is compared last as makes more logical sort order by file/line first
        if (m_tokenNum != rhs.m_tokenNum) return (m_tokenNum < rhs.m_tokenNum) ? -1 : 1;
        return 0;  // (*this) and rhs are equivalent
    }

private:
    string warnContext() const;
    string warnContextParent() const VL_REQUIRES(V3Error::s().m_mutex);
    const MsgEnBitSet& msgEn() const VL_MT_SAFE { return singleton().msgEn(m_msgEnIdx); }
};
std::ostream& operator<<(std::ostream& os, FileLine* fileline);

#endif  // Guard
