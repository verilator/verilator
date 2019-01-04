// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Os-specific function wrapper
//
// Code available from: http://www.veripool.org/verilator
//
//*************************************************************************
//
// Copyright 2003-2019 by Wilson Snyder.  This program is free software; you can
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

#ifndef _V3OS_H_
#define _V3OS_H_ 1

#include "config_build.h"
#include "verilatedos.h"

#include "V3Error.h"

//============================================================================
// V3Os: OS static class

class V3Os {
public:
    // METHODS (environment)
    static string getenvStr(const string& envvar, const string& defaultValue);
    static void setenvStr(const string& envvar, const string& value, const string& why);

    // METHODS (generic filename utilities)
    static string filenameFromDirBase(const string& dir, const string& basename);
    static string filenameNonDir(const string& filename);  ///< Return non-directory part of filename
    static string filenameNonExt(const string& filename);  ///< Return non-extensioned (no .) part of filename
    static string filenameNonDirExt(const string& filename) {  ///< Return basename of filename
        return filenameNonExt(filenameNonDir(filename)); }
    static string filenameDir(const string& filename);  ///< Return directory part of filename
    static string filenameSubstitute(const string& filename);  ///< Return filename with env vars removed
    static string filenameRealPath(const string& filename);  ///< Return realpath of filename
    static bool filenameIsRel(const string& filename);  ///< True if relative

    // METHODS (file utilities)
    static string getline(std::istream& is, char delim='\n');

    // METHODS (directory utilities)
    static void createDir(const string& dirname);
    static void unlinkRegexp(const string& dir, const string& regexp);

    // METHODS (random)
    static vluint64_t rand64(vluint64_t* statep);

    // METHODS (performance)
    static uint64_t timeUsecs();  ///< Return wall time since epoch in microseconds, or 0 if not implemented
    static uint64_t memUsageBytes(); ///< Return memory usage in bytes, or 0 if not implemented
};

#endif // Guard
