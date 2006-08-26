// $Id$  -*- C++ -*-
//*************************************************************************
// DESCRIPTION: Verilog::Preproc: Preprocess verilog code
//
// Code available from: http://www.veripool.com/verilog-perl
//
// Authors: Wilson Snyder
//
//*************************************************************************
//
// Copyright 2000-2006 by Wilson Snyder.  This program is free software;
// you can redistribute it and/or modify it under the terms of either the GNU
// General Public License or the Perl Artistic License.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
//*************************************************************************

#ifndef _V3PREPROC_H_
#define _V3PREPROC_H_ 1

#include "config.h"
#include "V3Error.h"

#include <string>
#include <map>
#include <iostream>

class V3PreProc {
    // This defines a preprocessor.  Functions are virtual so implementation can be hidden.
    // After creating, call open(), then getline() in a loop.  The class will to the rest...

protected:
    // STATE
    FileLine*	m_fileline;	// Last token's starting point
    int		m_debug;	// Debugging

public:
    // CONSTANTS
    enum MiscConsts {
	DEFINE_RECURSION_LEVEL_MAX = 50,	// How many `def substitutions before an error
	INCLUDE_DEPTH_MAX = 500			// How many `includes deep before an error
    };

    // ACCESSORS
    // Insert given file into this point in input stream
    virtual void openFile(FileLine* fileline, const string& filename)=0;
    virtual string getline()=0;		// Return next line/lines. (Null if done.)
    virtual bool isEof() const =0;		// Return true on EOF.
    virtual void insertUnreadback(const string& text) = 0;

    int debug() const { return m_debug; }
    void debug(int level) { m_debug = level; }

    FileLine* fileline() { return m_fileline; }	// File/Line number for last getline call

    // CONTROL METHODS
    // These options control how the parsing proceeds
    int keepComments() { return 2; }		// Return comments, 0=no, 1=yes, 2=callback
    bool lineDirectives() { return true; }	// Insert `line directives
    bool pedantic() { return false; }		// Obey standard; Don't substitute `__FILE__ and `__LINE__
    static bool optPsl();

    // CALLBACK METHODS
    // This probably will want to be overridden for given child users of this class.
    virtual void comment(const string& cmt)=0;		// Comment detected (if keepComments==2)
    virtual void include(const string& filename)=0;	// Request a include file be processed

    virtual void undef(const string& name)=0;			// Remove a definition
    virtual void define(FileLine* fileline, const string& name,
			const string& value, const string& params="")=0; // `define without any parameters
    virtual string removeDefines(const string& text)=0;	// Remove defines in a text string

protected:
    // CONSTUCTORS
    V3PreProc(FileLine* fl) {
	m_fileline=fl;
	m_debug=0;
    };
public:
    static V3PreProc* createPreProc(FileLine* fileline);
    virtual ~V3PreProc() {};
};

#endif // Guard
