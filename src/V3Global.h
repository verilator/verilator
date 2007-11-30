// $Id$ //-*- C++ -*-
//*************************************************************************
// DESCRIPTION: Verilator: Common headers
//
// Code available from: http://www.veripool.com/verilator
//
// AUTHORS: Wilson Snyder with Paul Wasson, Duane Gabli
//
//*************************************************************************
//
// Copyright 2003-2007 by Wilson Snyder.  This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// General Public License or the Perl Artistic License.
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
#include "V3Ast.h"

//======================================================================
// Statics


//######################################################################
// V3 - The top level class for the entire program

class V3Global {
    // Globals
    AstNetlist*	m_rootp;	// Root of entire netlist
    int		m_debugFileNumber;	// Number to append to debug files created
    bool	m_assertWidthsSame;	// Tree should have width()==widthMin()
    bool	m_needHInlines;		// Need a __Inlines file

public:
    // Options
    V3Options	opt;		// All options; let user see them directly

  public:
    // CREATORS
    V3Global() {
	m_rootp = new AstNetlist;
	m_debugFileNumber = 0;
	m_assertWidthsSame = false;
	m_needHInlines = false;
    }
    void clear() {
	if (m_rootp) m_rootp->deleteTree(); m_rootp=NULL;
    }
    // ACCESSORS (general)
    AstNetlist* rootp() const { return m_rootp; }
    bool assertWidthsSame() const { return m_assertWidthsSame; }

    // METHODS
    void readFiles();
    void checkTree() { rootp()->checkTree(); }
    void assertWidthsSame(bool flag) { m_assertWidthsSame = flag; }
    string debugFilename(const string& nameComment, int newNumber=0) {
	++m_debugFileNumber;
	if (newNumber) m_debugFileNumber = newNumber;
	char digits[100]; sprintf(digits, "%02d", m_debugFileNumber);
	return opt.makeDir()+"/"+opt.prefix()+"_"+digits+"_"+nameComment;
    }
    bool needHInlines() const { return m_needHInlines; }
    void needHInlines(bool flag) { m_needHInlines=flag; }
};

extern V3Global v3Global;

//######################################################################

#endif // guard

