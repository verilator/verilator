// -*- C++ -*-
//*************************************************************************
// DESCRIPTION: Verilator: File stream wrapper that understands indentation
//
// Code available from: http://www.veripool.org/verilator
//
// AUTHORS: Wilson Snyder with Paul Wasson, Duane Gabli
//
//*************************************************************************
//
// Copyright 2003-2009 by Wilson Snyder.  This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
//
// Verilator is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
//*************************************************************************

#ifndef _V3FILE_H_
#define _V3FILE_H_ 1
#include "config_build.h"
#include "verilatedos.h"
#include "V3Error.h"
#include <cstdio>
#include <stack>
#include <set>
#include <fstream>

//============================================================================
// V3File: Create streams, recording dependency information

class V3File {
public:
    static ifstream* new_ifstream(const string& filename) {
	addSrcDepend(filename);
	return new_ifstream_nodepend (filename);
    }
    static ifstream* new_ifstream_nodepend(const string& filename) {
	return new ifstream(filename.c_str());
    }
    static ofstream* new_ofstream(const string& filename, bool append=false) {
	addTgtDepend(filename);
	return new_ofstream_nodepend (filename, append);
    }
    static ofstream* new_ofstream_nodepend(const string& filename, bool append=false) {
	if (filename != "/dev/null") createMakeDir();
	if (append) {
	    return new ofstream(filename.c_str(), ios::app);
	} else {
	    return new ofstream(filename.c_str());
	}
    }
    static FILE* new_fopen_w(const string& filename) {
	if (filename != "/dev/null") createMakeDir();
	addTgtDepend(filename);
	return fopen(filename.c_str(),"w");
    }

    // Dependencies
    static void addSrcDepend(const string& filename);
    static void addTgtDepend(const string& filename);
    static void writeDepend(const string& filename);
    static void writeTimes(const string& filename, const string& cmdline);
    static bool checkTimes(const string& filename, const string& cmdline);

    // Directory utilities
    static void createMakeDir();
};

//============================================================================
// V3OutFile: A class for printing to a file, with automatic indentation of C++ code.

class V3OutFile {
    // TYPES
    enum MiscConsts {
	INDBLK = 4,	// Indentation per block level
	WIDTH = 50,	// Width after which to break at ,'s
	MAXSPACE = 80};	// After this indent, stop indenting more
public:
    enum AlignClass {
	AL_AUTO = 0,
	AL_STATIC = 1};

private:
    // MEMBERS
    FILE*	m_fp;
    string	m_filename;
    int		m_lineno;
    int		m_column;
    int		m_nobreak;	// Basic operator or begin paren, don't break next
    bool	m_prependIndent;
    int		m_indentLevel;	// Current {} indentation
    int		m_declSAlign;	// Byte alignment of next declaration, statics
    int		m_declNSAlign;	// Byte alignment of next declaration, nonstatics
    int		m_declPadNum;	// Pad variable number
    stack<int>	m_parenVec;	// Stack of columns where last ( was

    int		endLevels(const char* strg);
    static const char* indentStr(int levels);

public:
    V3OutFile(const string& filename);
    ~V3OutFile();
    // ACCESSORS
    int  column() const { return m_column; }
    // METHODS
    void printf(const char* fmt...) VL_ATTR_PRINTF(2);
    void puts(const char* strg);
    void puts(const string& strg) { puts(strg.c_str()); }
    void putsNoTracking(const char* strg);
    void putsNoTracking(const string& strg) { putsNoTracking(strg.c_str()); }
    void putBreak();  // Print linebreak if line is too wide
    void putBreakExpr();  // Print linebreak in expression if line is too wide
    void putAlign(bool isstatic/*AlignClass*/, int align, int size=0/*=align*/, const char* prefix=""); // Declare a variable, with natural alignment
    void putbs(const char* strg) { putBreakExpr(); puts(strg); }
    void putbs(const string& strg) {  putBreakExpr(); puts(strg); }
    bool exceededWidth() const { return m_column > WIDTH; }
    bool tokenStart(const char* cp, const char* cmp);
    bool tokenEnd(const char* cp);
    void indentInc() { m_indentLevel += INDBLK; };
    void indentDec() {
	m_indentLevel -= INDBLK;
	UASSERT(m_indentLevel>=0, ": "<<m_filename<<": Underflow of indentation\n");
    }
    void blockInc() { m_parenVec.push(m_indentLevel + INDBLK); }
    void blockDec() { if (!m_parenVec.empty()) m_parenVec.pop(); }
    // STATIC METHODS
    static const string indentSpaces(int levels);
private:
    void putcNoTracking(char chr);
};

#endif // Guard
