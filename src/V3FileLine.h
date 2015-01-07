// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Error handling
//
// Code available from: http://www.veripool.org/verilator
//
//*************************************************************************
//
// Copyright 2003-2015 by Wilson Snyder.  This program is free software; you can
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

#ifndef _V3FileLine_H_
#define _V3FileLine_H_ 1
#include "config_build.h"
#include "verilatedos.h"
#include <string>
#include <iostream>
#include <sstream>
#include <bitset>
#include <map>
#include <set>
#include <deque>

#include "V3Error.h"
#include "V3LangCode.h"

//######################################################################

class FileLine;

//! Singleton class with tables of per-file data.

//! This singleton class contains tables of data that are unchanging in each
//! source file (each with its own unique filename number).
class FileLineSingleton {
    // TYPES
    typedef map<string,int> FileNameNumMap;
    typedef map<string,V3LangCode> FileLangNumMap;
    // MEMBERS
    FileNameNumMap	m_namemap;	// filenameno for each filename
    deque<string>	m_names;	// filename text for each filenameno
    deque<V3LangCode>	m_languages;	// language for each filenameno
    // COSNTRUCTORS
    FileLineSingleton() { }
    ~FileLineSingleton() { }
protected:
    friend class FileLine;
    // METHODS
    int nameToNumber(const string& filename);
    const string numberToName(int filenameno) const { return m_names[filenameno]; }
    const V3LangCode numberToLang(int filenameno) const { return m_languages[filenameno]; }
    void numberToLang(int filenameno, const V3LangCode& l) { m_languages[filenameno] = l; }
    void clear() { m_namemap.clear(); m_names.clear(); m_languages.clear(); }
    void fileNameNumMapDumpXml(ostream& os);
    static const string filenameLetters(int fileno);
};

//! File and line number of an object, mostly for error reporting

//! This class is instantiated for every source code line (potentially
//! millions). To save space, per-file information (e.g. filename, source
//! language is held in tables in the FileLineSingleton class.
class FileLine {
    int		m_lineno;
    int		m_filenameno;
    bitset<V3ErrorCode::_ENUM_MAX>	m_warnOn;

private:
    struct EmptySecret {};
    inline static FileLineSingleton& singleton() {
	static FileLineSingleton s;
	return s;
    }
    inline static FileLine& defaultFileLine() {
	static FileLine* defFilelinep = new FileLine(FileLine::EmptySecret());
	return *defFilelinep;
    }
protected:
    // User routines should never need to change line numbers
    // We are storing pointers, so we CAN'T change them after initial reading.
    friend class FileLineSingleton;
    friend class V3ParseImp;
    friend class V3PreLex;
    friend class V3PreProcImp;
    void lineno(int num) { m_lineno = num; }
    void language (V3LangCode lang) { singleton().numberToLang(m_filenameno, lang); }
    void filename(const string& name) { m_filenameno = singleton().nameToNumber(name); }
    void lineDirective(const char* textp, int& enterExitRef);
    void linenoInc() { m_lineno++; }
    void linenoIncInPlace() { m_lineno++; }
    FileLine* copyOrSameFileLine();
public:
    FileLine (const string& filename, int lineno) {
	m_lineno=lineno; m_filenameno = singleton().nameToNumber(filename);
	m_warnOn=defaultFileLine().m_warnOn; }
    FileLine (FileLine* fromp) {
	m_lineno=fromp->m_lineno; m_filenameno = fromp->m_filenameno; m_warnOn=fromp->m_warnOn; }
    FileLine (EmptySecret);
    ~FileLine() { }
    FileLine* create(const string& filename, int lineno) { return new FileLine(filename,lineno); }
    FileLine* create(int lineno) { return create(filename(), lineno); }
    static void deleteAllRemaining();
#ifdef VL_LEAK_CHECKS
    static void* operator new(size_t size);
    static void operator delete(void* obj, size_t size);
#endif

    int lineno () const { return m_lineno; }
    V3LangCode language () const { return singleton().numberToLang(m_filenameno); }
    string ascii() const;
    const string filename () const { return singleton().numberToName(m_filenameno); }
    const string filenameLetters() const { return singleton().filenameLetters(m_filenameno); }
    const string filebasename () const;
    const string filebasenameNoExt () const;
    const string profileFuncname() const;
    const string xml() const { return "fl=\""+filenameLetters()+cvtToStr(lineno())+"\""; }
    string lineDirectiveStrg(int enter_exit_level) const;
    void warnOn(V3ErrorCode code, bool flag) { m_warnOn.set(code,flag); }	// Turn on/off warning messages on this line.
    void warnOff(V3ErrorCode code, bool flag) { warnOn(code,!flag); }
    bool warnOff(const string& code, bool flag);  // Returns 1 if ok
    bool warnIsOff(V3ErrorCode code) const;
    void warnLintOff(bool flag);
    void warnStyleOff(bool flag);
    void warnStateFrom(const FileLine& from) { m_warnOn=from.m_warnOn; }
    void warnResetDefault() { warnStateFrom(defaultFileLine()); }

    // Specific flag ACCESSORS/METHODS
    bool coverageOn() const { return m_warnOn.test(V3ErrorCode::I_COVERAGE); }
    void coverageOn(bool flag) { warnOn(V3ErrorCode::I_COVERAGE,flag); }
    bool tracingOn() const { return m_warnOn.test(V3ErrorCode::I_TRACING); }
    void tracingOn(bool flag) { warnOn(V3ErrorCode::I_TRACING,flag); }

    // METHODS - Global
    static void globalWarnLintOff(bool flag) {
	defaultFileLine().warnLintOff(flag); }
    static void globalWarnStyleOff(bool flag) {
	defaultFileLine().warnStyleOff(flag); }
    static void globalWarnOff(V3ErrorCode code, bool flag) {
	defaultFileLine().warnOff(code, flag); }
    static bool globalWarnOff(const string& code, bool flag) {
	return defaultFileLine().warnOff(code, flag); }
    static void fileNameNumMapDumpXml(ostream& os) {
	singleton().fileNameNumMapDumpXml(os); }

    // METHODS - Called from netlist
    // Merge warning disables from another fileline
    void modifyStateInherit(const FileLine* fromp);
    // Change the current fileline due to actions discovered after parsing
    // and may have side effects on other nodes sharing this FileLine.
    // Use only when this is intended
    void modifyWarnOff(V3ErrorCode code, bool flag) { warnOff(code,flag); }

    // OPERATORS
    void v3errorEnd(ostringstream& str);
    string warnMore() const;
    inline bool operator==(FileLine rhs) const {
	return (m_lineno==rhs.m_lineno && m_filenameno==rhs.m_filenameno && m_warnOn==rhs.m_warnOn);
    }
};
ostream& operator<<(ostream& os, FileLine* fileline);

#endif // Guard
