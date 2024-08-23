// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilog::Preproc: Preprocess verilog code
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2000-2024 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#ifndef VERILATOR_V3PREPROC_H_
#define VERILATOR_V3PREPROC_H_

#include "config_build.h"
#include "verilatedos.h"

#include "V3Error.h"
#include "V3FileLine.h"
#include "V3Global.h"

#include <iostream>
#include <list>
#include <map>

class VInFilter;
class VSpellCheck;

class V3PreProc VL_NOT_FINAL {
    // This defines a preprocessor.  Functions are virtual so implementation can be hidden.
    // After creating, call open(), then getline() in a loop.  The class will to the rest...

protected:
    VL_DEFINE_DEBUG_FUNCTIONS;

public:
    // CONSTANTS
    enum MiscConsts {
        DEFINE_RECURSION_LEVEL_MAX = 1000,  // How many `def substitutions before an error
        LINE_TOKEN_MAX = 40000,  // How many tokens on a line before an error
        INCLUDE_DEPTH_MAX = 500,  // How many `includes deep before an error
        // Streams deep (sometimes `def deep) before an error.
        // Set more than DEFINE_RECURSION_LEVEL_MAX or INCLUDE_DEPTH_MAX.
        STREAM_DEPTH_LEVEL_MAX = 2000,
        NEWLINES_VS_TICKLINE = 20  // Use `line in place of this many newlines
    };

    // ACCESSORS
    // Insert given file into this point in input stream
    virtual void openFile(FileLine* fileline, VInFilter* filterp, const string& filename) = 0;
    virtual string getline() = 0;  // Return next line/lines. (Null if done.)
    virtual bool isEof() const = 0;  // Return true on EOF.
    virtual void insertUnreadback(const string& text) = 0;

    FileLine* fileline() VL_MT_DISABLED;  ///< File/Line number for last getline call

    // CONTROL METHODS
    // These options control how the parsing proceeds
    static int keepComments() { return 2; }  // Return comments, 0=no, 1=yes, 2=callback
    static bool keepWhitespace() { return false; }
    static bool lineDirectives() {  // Insert `line directives
        return !(v3Global.opt.preprocOnly() && v3Global.opt.preprocNoLine());
    }
    static bool pedantic() { return false; }  // Obey standard; Don't substitute `error

    // CALLBACK METHODS
    // This probably will want to be overridden for given child users of this class.
    virtual void comment(const string& cmt) = 0;  // Comment detected (if keepComments==2)
    virtual void include(const string& filename) = 0;  // Request a include file be processed

    virtual void undef(const string& name) = 0;  // Remove a definition
    virtual void define(FileLine* fileline, const string& name, const string& value,
                        const string& params = "",
                        bool cmdline = false)
        = 0;  // `define without any parameters
    virtual void defineCmdLine(FileLine* fileline, const string& name,
                               const string& value) {  // `define without any parameters
        define(fileline, name, value, "", true);
    }
    virtual string removeDefines(const string& text) = 0;  // Remove defines in a text string

    // UTILITIES
    void error(const string& msg) { fileline()->v3error(msg); }  ///< Report an error
    void fatal(const string& msg) { fileline()->v3fatalSrc(msg); }  ///< Report a fatal error
    virtual void dumpDefines(std::ostream& os) = 0;  ///< Print list of `defines
    virtual void candidateDefines(VSpellCheck* spellerp) = 0;  ///< Spell check candidate defines

protected:
    // CONSTRUCTORS
    V3PreProc() {}
    void configure(FileLine* fl);

public:
    static V3PreProc* createPreProc(FileLine* fl) VL_MT_DISABLED;
    virtual ~V3PreProc() = default;  // LCOV_EXCL_LINE  // Persistent
    static void selfTest() VL_MT_DISABLED;
};

#endif  // Guard
