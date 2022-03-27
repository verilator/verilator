// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Os-specific function wrapper
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2022 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#ifndef VERILATOR_V3OS_H_
#define VERILATOR_V3OS_H_

#include "config_build.h"
#include "verilatedos.h"

#include <array>

// Limited V3 headers here - this is a base class for Vlc etc
#include "V3Error.h"

//============================================================================
// V3Os: OS static class

class V3Os final {
public:
    // METHODS (environment)
    static string getenvStr(const string& envvar, const string& defaultValue);
    static void setenvStr(const string& envvar, const string& value, const string& why);

    // METHODS (generic filename utilities)
    static string filenameFromDirBase(const string& dir, const string& basename);
    /// Return non-directory part of filename
    static string filenameNonDir(const string& filename);
    /// Return non-extensioned (no .) part of filename
    static string filenameNonExt(const string& filename);
    static string filenameNonDirExt(const string& filename) {  ///< Return basename of filename
        return filenameNonExt(filenameNonDir(filename));
    }
    static string filenameDir(const string& filename);  ///< Return directory part of filename
    /// Return filename with env vars removed
    static string filenameSubstitute(const string& filename);
    static string filenameRealPath(const string& filename);  ///< Return realpath of filename
    static bool filenameIsRel(const string& filename);  ///< True if relative

    // METHODS (file utilities)
    static string getline(std::istream& is, char delim = '\n');

    // METHODS (directory utilities)
    static void createDir(const string& dirname);
    static void unlinkRegexp(const string& dir, const string& regexp);

    // METHODS (random)
    static uint64_t rand64(std::array<uint64_t, 2>& stater);
    static string trueRandom(size_t size);

    // METHODS (time & performance)
    static void u_sleep(int64_t usec);  ///< Sleep for a given number of microseconds.
    /// Return wall time since epoch in microseconds, or 0 if not implemented
    static uint64_t timeUsecs();
    static uint64_t memUsageBytes();  ///< Return memory usage in bytes, or 0 if not implemented

    // METHODS (sub command)
    /// Run system command, returns the exit code of the child process.
    static int system(const string& command);
};

#endif  // Guard
