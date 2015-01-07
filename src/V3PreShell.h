// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Preprocessing wrapper program
//
// Code available from: http://www.veripool.org/verilator
//
//*************************************************************************
//
// Copyright 2004-2015 by Wilson Snyder.  This program is free software; you can
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

#ifndef _V3PRESHELL_H_
#define _V3PRESHELL_H_ 1

#include "config_build.h"
#include "verilatedos.h"
#include "V3Error.h"
#include "V3FileLine.h"

class V3ParseImp;
class V3InFilter;

//============================================================================

class V3PreShell {
    // Static class for calling preprocessor
public:
    static void boot(char** env);
    static bool preproc(FileLine* fileline, const string& module, V3InFilter* filterp,
			V3ParseImp* parsep, const string& errmsg);
    static void preprocInclude(FileLine* fileline, const string& module);
    static string dependFiles() { return ""; }   // Perl only
    static void defineCmdLine(const string& name, const string& value);
    static void undef(const string& name);
};

#endif // Guard
