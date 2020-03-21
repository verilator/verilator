// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Reading of Verilog files
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

#ifndef _V3PARSE_H_
#define _V3PARSE_H_ 1

#include "config_build.h"
#include "verilatedos.h"

#include "V3Error.h"
#include "V3Global.h"

class AstNetlist;
class VInFilter;
class V3ParseImp;
class V3ParseSym;

//============================================================================

class V3Parse {
private:
    V3ParseImp* m_impp;

    // CONSTRUCTORS
    VL_UNCOPYABLE(V3Parse);

public:
    // We must allow reading multiple files into one parser
    V3Parse(AstNetlist* rootp, VInFilter* filterp, V3ParseSym* symp);
    ~V3Parse();

    // METHODS
    // Preprocess and read the Verilog file specified into the netlist database
    void parseFile(FileLine* fileline, const string& modname, bool inLibrary,
                   const string& errmsg);

    // Push preprocessed text to the lexer
    static void ppPushText(V3ParseImp* impp, const string& text);
};

#endif  // Guard
