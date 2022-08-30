// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: File stream wrapper that understands indentation
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

#ifndef VERILATOR_V3FILE_H_
#define VERILATOR_V3FILE_H_

#include "config_build.h"
#include "verilatedos.h"

#include "V3Error.h"

#include <array>
#include <fstream>
#include <list>
#include <memory>
#include <set>
#include <stack>
#include <vector>

//============================================================================
// V3File: Create streams, recording dependency information

class V3File final {
public:
    static std::ifstream* new_ifstream(const string& filename) {
        addSrcDepend(filename);
        return new_ifstream_nodepend(filename);
    }
    static std::ifstream* new_ifstream_nodepend(const string& filename) {
        return new std::ifstream{filename.c_str()};
    }
    static std::ofstream* new_ofstream(const string& filename, bool append = false) {
        addTgtDepend(filename);
        return new_ofstream_nodepend(filename, append);
    }
    static std::ofstream* new_ofstream_nodepend(const string& filename, bool append = false) {
        createMakeDirFor(filename);
        if (append) {
            return new std::ofstream{filename.c_str(), std::ios::app};
        } else {
            return new std::ofstream{filename.c_str()};
        }
    }
    static FILE* new_fopen_w(const string& filename) {
        createMakeDirFor(filename);
        addTgtDepend(filename);
        return fopen(filename.c_str(), "w");
    }

    // Dependencies
    static void addSrcDepend(const string& filename);
    static void addTgtDepend(const string& filename);
    static void writeDepend(const string& filename);
    static std::vector<string> getAllDeps();
    static void writeTimes(const string& filename, const string& cmdlineIn);
    static bool checkTimes(const string& filename, const string& cmdlineIn);

    // Directory utilities
    static void createMakeDirFor(const string& filename);
    static void createMakeDir();
};

//============================================================================
// VInFilter: Read a input file, possibly filtering it, and caching contents

class VInFilterImp;

class VInFilter final {
public:
    // TYPES
    using StrList = std::list<std::string>;

private:
    VInFilterImp* m_impp;

    // CONSTRUCTORS
    VL_UNCOPYABLE(VInFilter);

public:
    explicit VInFilter(const string& command);
    ~VInFilter();

    // METHODS
    // Read file contents and return it.  Return true on success.
    bool readWholefile(const string& filename, StrList& outl);
};

//============================================================================
// V3OutFormatter: A class for automatic indentation of C++ or Verilog code.

class V3OutFormatter VL_NOT_FINAL {
    // TYPES
    static constexpr int MAXSPACE = 80;  // After this indent, stop indenting more
public:
    enum AlignClass : uint8_t { AL_AUTO = 0, AL_STATIC = 1 };
    enum Language : uint8_t {
        LA_C = 0,
        LA_VERILOG = 1,
        LA_MK = 2,
        LA_XML = 3,
    };

private:
    // MEMBERS
    const string m_filename;
    const Language m_lang;  // Indenting Verilog code
    int m_blockIndent;  // Characters per block indent
    int m_commaWidth;  // Width after which to break at ,'s
    int m_lineno = 1;
    int m_column = 0;
    int m_nobreak = false;  // Basic operator or begin paren, don't break next
    bool m_prependIndent = true;
    bool m_inStringLiteral = false;
    int m_indentLevel = 0;  // Current {} indentation
    std::stack<int> m_parenVec;  // Stack of columns where last ( was
    int m_bracketLevel = 0;  // Intenting = { block, indicates number of {'s seen.

    int endLevels(const char* strg);
    void putcNoTracking(char chr);

public:
    V3OutFormatter(const string& filename, Language lang);
    virtual ~V3OutFormatter() = default;
    // ACCESSORS
    string filename() const { return m_filename; }
    int column() const { return m_column; }
    int blockIndent() const { return m_blockIndent; }
    void blockIndent(int flag) { m_blockIndent = flag; }
    // METHODS
    void printf(const char* fmt...) VL_ATTR_PRINTF(2);
    void puts(const char* strg);
    void puts(const string& strg) { puts(strg.c_str()); }
    void putsNoTracking(const string& strg);
    void putsQuoted(const string& strg);
    void putBreak();  // Print linebreak if line is too wide
    void putBreakExpr();  // Print linebreak in expression if line is too wide
    void putbs(const char* strg) {
        putBreakExpr();
        puts(strg);
    }
    void putbs(const string& strg) {
        putBreakExpr();
        puts(strg);
    }
    bool exceededWidth() const { return m_column > m_commaWidth; }
    void indentInc() { m_indentLevel += m_blockIndent; }
    void indentDec() {
        m_indentLevel -= m_blockIndent;
        UASSERT(m_indentLevel >= 0, ": " << m_filename << ": Underflow of indentation");
    }
    void blockInc() { m_parenVec.push(m_indentLevel + m_blockIndent); }
    void blockDec() {
        if (!m_parenVec.empty()) m_parenVec.pop();
    }
    void ensureNewLine() {
        if (!m_nobreak) puts("\n");
    }
    // STATIC METHODS
    static string indentSpaces(int num);
    // Add escaped characters to strings
    static string quoteNameControls(const string& namein, Language lang = LA_C);
    static bool tokenMatch(const char* cp, const char* cmp);
    static bool tokenNotStart(const char* cp);  // Import/export meaning no endfunction
    static bool tokenStart(const char* cp);
    static bool tokenEnd(const char* cp);

    // CALLBACKS - MUST OVERRIDE
    virtual void putcOutput(char chr) = 0;
    virtual void putsOutput(const char* str) = 0;
};

//============================================================================
// V3OutFile: A class for printing to a file, with automatic indentation of C++ code.

class V3OutFile VL_NOT_FINAL : public V3OutFormatter {
    // Size of m_bufferp.
    // 128kB has been experimentally determined to be in the zone of buffer sizes that work best.
    // It is also considered to be the smallest I/O buffer size in GNU coreutils (io_blksize) that
    // allows to best minimize syscall overhead.
    // The hard boundaries are CPU L2/L3 cache size on the top and filesystem block size
    // on the bottom.
    static constexpr std::size_t WRITE_BUFFER_SIZE_BYTES = 128 * 1024;

    // MEMBERS
    std::unique_ptr<std::array<char, WRITE_BUFFER_SIZE_BYTES>> m_bufferp;  // Write buffer
    std::size_t m_usedBytes = 0;  // Number of bytes stored in m_bufferp
    FILE* m_fp = nullptr;

public:
    V3OutFile(const string& filename, V3OutFormatter::Language lang);
    V3OutFile(const V3OutFile&) = delete;
    V3OutFile& operator=(const V3OutFile&) = delete;
    V3OutFile(V3OutFile&&) = delete;
    V3OutFile& operator=(V3OutFile&&) = delete;

    virtual ~V3OutFile() override;
    void putsForceIncs();

private:
    void writeBlock() {
        if (VL_LIKELY(m_usedBytes > 0)) fwrite(m_bufferp->data(), m_usedBytes, 1, m_fp);
        m_usedBytes = 0;
    }

    // CALLBACKS
    virtual void putcOutput(char chr) override {
        m_bufferp->at(m_usedBytes++) = chr;
        if (VL_UNLIKELY(m_usedBytes >= WRITE_BUFFER_SIZE_BYTES)) writeBlock();
    }
    virtual void putsOutput(const char* str) override {
        std::size_t len = strlen(str);
        std::size_t availableBytes = WRITE_BUFFER_SIZE_BYTES - m_usedBytes;
        while (VL_UNLIKELY(len >= availableBytes)) {
            memcpy(m_bufferp->data() + m_usedBytes, str, availableBytes);
            m_usedBytes = WRITE_BUFFER_SIZE_BYTES;
            writeBlock();
            str += availableBytes;
            len -= availableBytes;
            availableBytes = WRITE_BUFFER_SIZE_BYTES;
        }
        if (len > 0) {
            memcpy(m_bufferp->data() + m_usedBytes, str, len);
            m_usedBytes += len;
        }
    }
};

class V3OutCFile VL_NOT_FINAL : public V3OutFile {
    int m_guard = false;  // Created header guard
    int m_private;  // 1 = Most recently emitted private:, 2 = public:
public:
    explicit V3OutCFile(const string& filename)
        : V3OutFile{filename, V3OutFormatter::LA_C} {
        resetPrivate();
    }
    virtual ~V3OutCFile() override = default;
    virtual void putsHeader() { puts("// Verilated -*- C++ -*-\n"); }
    virtual void putsIntTopInclude() { putsForceIncs(); }
    virtual void putsGuard();
    virtual void putsEndGuard() {
        if (m_guard) puts("\n#endif  // guard\n");
    }
    // Print out public/privates
    void resetPrivate() { m_private = 0; }
    void putsPrivate(bool setPrivate) {
        if (setPrivate && m_private != 1) {
            puts("private:\n");
            m_private = 1;
        } else if (!setPrivate && m_private != 2) {
            puts("public:\n");
            m_private = 2;
        }
    }
};

class V3OutScFile final : public V3OutCFile {
public:
    explicit V3OutScFile(const string& filename)
        : V3OutCFile{filename} {}
    virtual ~V3OutScFile() override = default;
    virtual void putsHeader() override { puts("// Verilated -*- SystemC -*-\n"); }
    virtual void putsIntTopInclude() override {
        putsForceIncs();
        puts("#include \"systemc.h\"\n");
        puts("#include \"verilated_sc.h\"\n");
    }
};

class V3OutVFile final : public V3OutFile {
public:
    explicit V3OutVFile(const string& filename)
        : V3OutFile{filename, V3OutFormatter::LA_VERILOG} {}
    virtual ~V3OutVFile() override = default;
    virtual void putsHeader() { puts("// Verilated -*- Verilog -*-\n"); }
};

class V3OutXmlFile final : public V3OutFile {
public:
    explicit V3OutXmlFile(const string& filename)
        : V3OutFile{filename, V3OutFormatter::LA_XML} {
        blockIndent(2);
    }
    virtual ~V3OutXmlFile() override = default;
    virtual void putsHeader() { puts("<?xml version=\"1.0\" ?>\n"); }
};

class V3OutMkFile final : public V3OutFile {
public:
    explicit V3OutMkFile(const string& filename)
        : V3OutFile{filename, V3OutFormatter::LA_MK} {}
    virtual ~V3OutMkFile() override = default;
    virtual void putsHeader() { puts("# Verilated -*- Makefile -*-\n"); }
    // No automatic indentation yet.
    void puts(const char* strg) { putsNoTracking(strg); }
    void puts(const string& strg) { putsNoTracking(strg); }
};

//============================================================================
// VIdProtect: Hash identifier names in output files to protect them

class VIdProtectImp;

class VIdProtect final {
public:
    // METHODS
    // Rename to a new encoded string (unless earlier passthru'ed)
    static string protect(const string& old) { return protectIf(old, true); }
    static string protectIf(const string& old, bool doIt = true);
    // Rename words to a new encoded string
    static string protectWordsIf(const string& old, bool doIt = true);
    // Write map of renames to output file
    static void writeMapFile(const string& filename);
};

#endif  // Guard
