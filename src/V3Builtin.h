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

#include "config_build.h"
#include "verilatedos.h"

class AstClass;
class AstPackage;
class AstNetlist;
class V3ParseSym;

class V3Builtin {
    AstClass* m_processClassp;
    AstPackage* m_processPackagep;

public:
    V3Builtin()
        : m_processClassp{nullptr}
        , m_processPackagep{nullptr} {}

    void makeProcessClass(AstNetlist* rootp, V3ParseSym& parseSyms);

    AstClass* processClassp() { return m_processClassp; }
    AstPackage* processPackagep() { return m_processPackagep; }
};

#endif  // Guard
