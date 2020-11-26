// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: built-in packages and classes
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2009-2020 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#ifndef _V3BUILTIN_H_
#define _V3BUILTIN_H_ 1

class AstNetlist;
class V3Parse;
class V3ParseSym;

class V3Builtin {
public:
    static void parseStdPackage(V3Parse& parser);
    static void defineExterns(AstNetlist* rootp, V3ParseSym& parseSyms);
};

#endif  // Guard
