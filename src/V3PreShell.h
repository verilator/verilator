// $Id$ //-*- C++ -*-
//*************************************************************************
// DESCRIPTION: Verilator: Preprocessing wrapper program
//
// Code available from: http://www.veripool.com/verilator
//
// AUTHORS: Wilson Snyder with Paul Wasson, Duane Gabli
//
//*************************************************************************
//
// Copyright 2004-2008 by Wilson Snyder.  This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// General Public License or the Perl Artistic License.
//
// Verilator is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
//*************************************************************************

#ifndef _V3PRESHELL_H_
#define _V3PRESHELL_H_ 1

#include "config_build.h"
#include "verilatedos.h"
#include "V3Error.h"

class V3Read;

//============================================================================

class V3PreShell {
    // Static class for calling preprocessor
public:
    static void boot(char** env);
    static void preproc(FileLine* fileline, const string& module, V3Read* readerp);
    static void preprocInclude(FileLine* fileline, const string& module);
    static string dependFiles() { return ""; }   // Perl only
    static void define(const string& name, const string& value);
    static void undef(const string& name);
};

#endif // Guard
