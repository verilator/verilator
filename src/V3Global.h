// -*- C++ -*-
//*************************************************************************
// DESCRIPTION: Verilator: Common headers
//
// Code available from: http://www.veripool.org/verilator
//
// AUTHORS: Wilson Snyder with Paul Wasson, Duane Gabli
//
//*************************************************************************
//
// Copyright 2003-2012 by Wilson Snyder.  This program is free software; you can
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

#ifndef _V3GLOBAL_H_
#define _V3GLOBAL_H_ 1

#include "config_build.h"
#include "verilatedos.h"
#include <string>

#include "V3Error.h"
#include "V3Options.h"

class AstNetlist;

//======================================================================
// Statics


//######################################################################
// V3 - The top level class for the entire program

class V3Global {
    // Globals
    AstNetlist*	m_rootp;		// Root of entire netlist

    int		m_debugFileNumber;	// Number to append to debug files created
    bool	m_assertDTypesResolved;	// Tree should have dtypep()'s
    bool	m_assertWidthsMatch;	// Tree should have width()==widthMin()
    bool	m_needHInlines;		// Need __Inlines file
    bool	m_needHeavy;		// Need verilated_heavy.h include
    bool	m_dpi;			// Need __Dpi include files

public:
    // Options
    V3Options	opt;		// All options; let user see them directly

  public:
    // CREATORS
    V3Global() {
	m_debugFileNumber = 0;
	m_assertDTypesResolved = false;
	m_assertWidthsMatch = false;
	m_needHInlines = false;
	m_needHeavy = false;
	m_dpi = false;
	m_rootp = makeNetlist();
    }
    AstNetlist* makeNetlist();
    void clear();
    // ACCESSORS (general)
    AstNetlist* rootp() const { return m_rootp; }
    bool assertDTypesResolved() const { return m_assertDTypesResolved; }
    bool assertWidthsMatch() const { return m_assertWidthsMatch; }

    // METHODS
    void readFiles();
    void checkTree();
    void assertDTypesResolved(bool flag) { m_assertDTypesResolved = flag; }
    void assertWidthsMatch(bool flag) { m_assertWidthsMatch = flag; }
    string debugFilename(const string& nameComment, int newNumber=0) {
	++m_debugFileNumber;
	if (newNumber) m_debugFileNumber = newNumber;
	char digits[100]; sprintf(digits, "%02d", m_debugFileNumber);
	return opt.makeDir()+"/"+opt.prefix()+"_"+digits+"_"+nameComment;
    }
    bool needHInlines() const { return m_needHInlines; }
    void needHInlines(bool flag) { m_needHInlines=flag; }
    bool needHeavy() const { return m_needHeavy; }
    void needHeavy(bool flag) { m_needHeavy=flag; }
    bool dpi() const { return m_dpi; }
    void dpi(bool flag) { m_dpi = flag; }
};

extern V3Global v3Global;

//######################################################################

#endif // guard

