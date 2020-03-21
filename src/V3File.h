// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: File stream wrapper that understands indentation
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

#ifndef _V3FILE_H_
#define _V3FILE_H_ 1

#include "config_build.h"
#include "verilatedos.h"

#include "V3Error.h"

#include <stack>
#include <set>
#include <list>
#include <vector>
#include <fstream>

//============================================================================
// V3File: Create streams, recording dependency information

class V3File {
public:
    static std::ifstream* new_ifstream(const string& filename) {
        addSrcDepend(filename);
        return new_ifstream_nodepend(filename);
    }
    static std::ifstream* new_ifstream_nodepend(const string& filename) {
        return new std::ifstream(filename.c_str());
    }
    static std::ofstream* new_ofstream(const string& filename, bool append=false) {
        addTgtDepend(filename);
        return new_ofstream_nodepend(filename, append);
    }
    static std::ofstream* new_ofstream_nodepend(const string& filename, bool append=false) {
        createMakeDirFor(filename);
        if (append) {
            return new std::ofstream(filename.c_str(), std::ios::app);
        } else {
            return new std::ofstream(filename.c_str());
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

class VInFilter {
public:
    // TYPES
    typedef std::list<string> StrList;

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

class V3OutFormatter {
    // TYPES
    enum MiscConsts {
        MAXSPACE = 80};  // After this indent, stop indenting more
public:
    enum AlignClass {
        AL_AUTO = 0,
        AL_STATIC = 1};
    enum Language {
        LA_C = 0,
        LA_VERILOG = 1,
        LA_MK = 2,
        LA_XML = 3,
    };

private:
    // MEMBERS
    string      m_filename;
    Language    m_lang;         // Indenting Verilog code
    int         m_blockIndent;  // Characters per block indent
    int         m_commaWidth;   // Width after which to break at ,'s
    int         m_lineno;
    int         m_column;
    int         m_nobreak;      // Basic operator or begin paren, don't break next
    bool        m_prependIndent;
    int         m_indentLevel;  // Current {} indentation
    std::stack<int> m_parenVec;  // Stack of columns where last ( was
    int         m_bracketLevel;  // Intenting = { block, indicates number of {'s seen.

    int endLevels(const char* strg);
    void putcNoTracking(char chr);

public:
    V3OutFormatter(const string& filename, Language lang);
    virtual ~V3OutFormatter() {}
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
    void putbs(const char* strg) { putBreakExpr(); puts(strg); }
    void putbs(const string& strg) {  putBreakExpr(); puts(strg); }
    bool exceededWidth() const { return m_column > m_commaWidth; }
    bool tokenStart(const char* cp, const char* cmp);
    bool tokenEnd(const char* cp);
    void indentInc() { m_indentLevel += m_blockIndent; }
    void indentDec() {
        m_indentLevel -= m_blockIndent;
        UASSERT(m_indentLevel>=0, ": "<<m_filename<<": Underflow of indentation");
    }
    void blockInc() { m_parenVec.push(m_indentLevel + m_blockIndent); }
    void blockDec() { if (!m_parenVec.empty()) m_parenVec.pop(); }
    // STATIC METHODS
    static const string indentSpaces(int num);
    // Add escaped characters to strings
    static string quoteNameControls(const string& namein, Language lang = LA_C);

    // CALLBACKS - MUST OVERRIDE
    virtual void putcOutput(char chr) = 0;
};

//============================================================================
// V3OutFile: A class for printing to a file, with automatic indentation of C++ code.

class V3OutFile : public V3OutFormatter {
    // MEMBERS
    FILE*       m_fp;
public:
    V3OutFile(const string& filename, V3OutFormatter::Language lang);
    virtual ~V3OutFile();
    void putsForceIncs();
private:
    // CALLBACKS
    virtual void putcOutput(char chr) { fputc(chr, m_fp); }
};

class V3OutCFile : public V3OutFile {
    int m_guard;  // Created header guard
    int m_private;  // 1 = Most recently emitted private:, 2 = public:
public:
    explicit V3OutCFile(const string& filename)
        : V3OutFile(filename, V3OutFormatter::LA_C)
        , m_guard(false) {
        resetPrivate();
    }
    virtual ~V3OutCFile() {}
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

class V3OutScFile : public V3OutCFile {
public:
    explicit V3OutScFile(const string& filename) : V3OutCFile(filename) {}
    virtual ~V3OutScFile() {}
    virtual void putsHeader() { puts("// Verilated -*- SystemC -*-\n"); }
    virtual void putsIntTopInclude() {
        putsForceIncs();
        puts("#include \"systemc.h\"\n");
        puts("#include \"verilated_sc.h\"\n");
    }
};

class V3OutVFile : public V3OutFile {
public:
    explicit V3OutVFile(const string& filename)
        : V3OutFile(filename, V3OutFormatter::LA_VERILOG) {}
    virtual ~V3OutVFile() {}
    virtual void putsHeader() { puts("// Verilated -*- Verilog -*-\n"); }
};

class V3OutXmlFile : public V3OutFile {
public:
    explicit V3OutXmlFile(const string& filename)
        : V3OutFile(filename, V3OutFormatter::LA_XML) {
        blockIndent(2);
    }
    virtual ~V3OutXmlFile() {}
    virtual void putsHeader() { puts("<?xml version=\"1.0\" ?>\n"); }
};

class V3OutMkFile : public V3OutFile {
public:
    explicit V3OutMkFile(const string& filename)
        : V3OutFile(filename, V3OutFormatter::LA_MK) {}
    virtual ~V3OutMkFile() {}
    virtual void putsHeader() { puts("# Verilated -*- Makefile -*-\n"); }
    // No automatic indentation yet.
    void puts(const char* strg) { putsNoTracking(strg); }
    void puts(const string& strg) { putsNoTracking(strg); }
};

//============================================================================
// VIdProtect: Hash identifier names in output files to protect them

class VIdProtectImp;

class VIdProtect {
public:
    // METHODS
    // Rename to a new encoded string (unless earlier passthru'ed)
    static string protect(const string& old) { return protectIf(old, true); }
    static string protectIf(const string& old, bool doIt=true);
    // Rename words to a new encoded string
    static string protectWordsIf(const string& old, bool doIt=true);
    // Write map of renames to output file
    static void writeMapFile(const string& filename);
};

#endif  // Guard
