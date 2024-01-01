// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Os-specific function wrapper
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2024 by Wilson Snyder. This program is free software; you
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
    ///< @return concatenated path
    static string filenameJoin(std::initializer_list<const std::string> paths) VL_PURE;
    template <typename... Args>
    static string filenameJoin(Args... args) VL_PURE {
        return filenameJoin({args...});
    };
    ///< @return file path without repeated separators and ./ prefix
    static string filenameCleanup(const string& filename) VL_PURE;
    ///< @return non-directory part of filename
    static string filenameNonDir(const string& filename) VL_PURE;
    ///< @return non-extensioned (no .) part of filename
    static string filenameNonExt(const string& filename) VL_PURE;
    ///< @return basename of filename
    static string filenameNonDirExt(const string& filename) VL_PURE;
    ///< @return directory part of filename
    static string filenameDir(const string& filename) VL_PURE;
    ///< @return filename with env vars removed
    static string filenameSubstitute(const string& filename);
    ///< @return realpath of filename
    static string filenameRealPath(const string& filename) VL_PURE;
    ///< @return filename is relative
    static bool filenameIsRel(const string& filename) VL_PURE;

    // METHODS (file utilities)
    static string getline(std::istream& is, char delim = '\n');

    // METHODS (directory utilities)
    static void createDir(const string& dirname);
    static void filesystemFlush(const string& dirname);
    static void filesystemFlushBuildDir(const string& dirname);
    static void unlinkRegexp(const string& dir, const string& regexp);

    // METHODS (random)
    static uint64_t rand64(std::array<uint64_t, 2>& stater);
    static string trueRandom(size_t size) VL_MT_SAFE;

    // METHODS (time & performance)
    static void u_sleep(int64_t usec);  ///< Sleep for a given number of microseconds.
    /// Return wall time since epoch in microseconds, or 0 if not implemented
    static uint64_t timeUsecs();
    static uint64_t memUsageBytes();  ///< Return memory usage in bytes, or 0 if not implemented

    // METHODS (sub command)
    /// Run system command, returns the exit code of the child process.
    static int system(const string& command);
    static void selfTest();
};

#endif  // Guard
