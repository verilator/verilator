// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Configuration Files
//
// Code available from: http://www.veripool.org/verilator
//
//*************************************************************************
//
// Copyright 2010-2015 by Wilson Snyder.  This program is free software; you can
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

#include "config_build.h"
#include "verilatedos.h"
#include <string>
#include <map>
#include <set>

#include "V3Global.h"
#include "V3String.h"
#include "V3Config.h"

//######################################################################

class V3ConfigLine {
public:
    int		m_lineno;	// Line number to make change at
    V3ErrorCode	m_code;		// Error code
    bool	m_on;		// True to enaable message
    V3ConfigLine(V3ErrorCode code, int lineno, bool on)
	: m_lineno(lineno), m_code(code), m_on(on) {}
    ~V3ConfigLine() {}
    inline bool operator< (const V3ConfigLine& rh) const {
	if (m_lineno<rh.m_lineno) return true;
	if (m_lineno>rh.m_lineno) return false;
	if (m_code<rh.m_code) return true;
	if (m_code>rh.m_code) return false;
	// Always turn "on" before "off" so that overlapping lines will end up finally with the error "off"
	return (m_on>rh.m_on);
    }
};
ostream& operator<<(ostream& os, V3ConfigLine rhs) { return os<<rhs.m_lineno<<", "<<rhs.m_code<<", "<<rhs.m_on; }

class V3ConfigIgnores {
    typedef multiset<V3ConfigLine> IgnLines;	// list of {line,code,on}
    typedef map<string,IgnLines> IgnFiles;	// {filename} => list of {line,code,on}

    // MEMBERS
    string		m_lastFilename;	// Last filename looked up
    int			m_lastLineno;	// Last linenumber looked up

    IgnLines::const_iterator m_lastIt;	// Point with next linenumber > current line number
    IgnLines::const_iterator m_lastEnd;	// Point with end()

    IgnFiles		m_ignWilds;	// Ignores for each wildcarded filename
    IgnFiles		m_ignFiles;	// Ignores for each non-wildcarded filename

    static V3ConfigIgnores s_singleton;	// Singleton (not via local static, as that's slow)

    V3ConfigIgnores() { m_lastLineno = -1; }
    ~V3ConfigIgnores() {}

    // METHODS
    inline IgnLines* findWilds(const string& wildname) {
	IgnFiles::iterator it = m_ignWilds.find(wildname);
	if (it != m_ignWilds.end()) {
	    return &(it->second);
	} else {
	    m_ignWilds.insert(make_pair(wildname, IgnLines()));
	    it = m_ignWilds.find(wildname);
	    return &(it->second);
	}
    }
    inline void absBuild(const string& filename) {
	// Given a filename, find all wildcard matches against it and build
	// hash with the specific filename.  This avoids having to wildmatch
	// more than once against any filename.
	IgnFiles::iterator it = m_ignFiles.find(filename);
	if (it == m_ignFiles.end()) {
	    // Haven't seen this filename before
	    m_ignFiles.insert(make_pair(filename, IgnLines()));
	    it = m_ignFiles.find(filename);
	    // Make new list for this file of all matches
	    for (IgnFiles::iterator fnit = m_ignWilds.begin(); fnit != m_ignWilds.end(); ++fnit) {
		if (VString::wildmatch(filename.c_str(), fnit->first.c_str())) {
		    for (IgnLines::iterator lit = fnit->second.begin(); lit != fnit->second.end(); ++lit) {
			it->second.insert(*lit);
		    }
		}
	    }
	}
	m_lastIt = it->second.begin();
	m_lastEnd = it->second.end();
    }

public:
    inline static V3ConfigIgnores& singleton() { return s_singleton; }

    void addIgnore(V3ErrorCode code, string wildname, int lineno, bool on) {
	// Insert
	IgnLines* linesp = findWilds(wildname);
	UINFO(9,"config addIgnore "<<wildname<<":"<<lineno<<", "<<code<<", "<<on<<endl);
	linesp->insert(V3ConfigLine(code, lineno, on));
	// Flush the match cache, due to a change in the rules.
	m_ignFiles.clear();
	m_lastFilename = " ";
    }
    inline void applyIgnores(FileLine* filelinep) {
	// HOT routine, called each parsed token line
	if (m_lastLineno != filelinep->lineno()
	    || m_lastFilename != filelinep->filename()) {
	    //UINFO(9,"   ApplyIgnores for "<<filelinep->ascii()<<endl);
	    if (VL_UNLIKELY(m_lastFilename != filelinep->filename())) {
		absBuild(filelinep->filename());
		m_lastFilename = filelinep->filename();
	    }
	    // Process all on/offs for lines up to and including the current line
	    int curlineno = filelinep->lineno();
	    for (; m_lastIt != m_lastEnd; ++m_lastIt) {
		if (m_lastIt->m_lineno > curlineno) break;
		//UINFO(9,"     Hit "<<*m_lastIt<<endl);
		filelinep->warnOn(m_lastIt->m_code, m_lastIt->m_on);
	    }
	    if (0 && debug() >= 9) {
		for (IgnLines::const_iterator it=m_lastIt; it != m_lastEnd; ++it) {
		    UINFO(9,"     NXT "<<*it<<endl);
		}
	    }
	    m_lastLineno = filelinep->lineno();
	}
    }
};

V3ConfigIgnores V3ConfigIgnores::s_singleton;

//######################################################################
// V3Config

void V3Config::addIgnore(V3ErrorCode code, bool on, string filename, int min, int max) {
    if (filename=="*") {
	FileLine::globalWarnOff(code,!on);
    } else {
	V3ConfigIgnores::singleton().addIgnore(code, filename, min, on);
	if (max) V3ConfigIgnores::singleton().addIgnore(code, filename, max, !on);
    }
}

void V3Config::applyIgnores(FileLine* filelinep) {
    V3ConfigIgnores::singleton().applyIgnores(filelinep);
}
