// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// Code available from: https://verilator.org
//
// Copyright 2003-2024 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
///
/// \file
/// \brief Verilated/Verilator common implementation for OS portability
///
/// This is compiled as part of other .cpp files to reduce compile time
/// and as such is a .h file rather than .cpp file.
///
//*************************************************************************

#ifndef VL_ALLOW_VERILATEDOS_C
#error "This file should be included only from V3Os.cpp/Verilated.cpp"
#endif

#include "verilatedos.h"

// clang-format off
#if defined(_WIN32) || defined(__MINGW32__)
# include <windows.h>   // LONG for bcrypt.h on MINGW
# include <processthreadsapi.h>  // GetProcessTimes
# include <psapi.h>   // GetProcessMemoryInfo
#endif
// clang-format on

namespace VlOs {

//=========================================================================
// VlOs::VlGetCpuTime/VlGetWallTime implementation

double DeltaCpuTime::gettime() VL_MT_SAFE {
#if defined(_WIN32) || defined(__MINGW32__)
    FILETIME lpCreationTime, lpExitTime, lpKernelTime, lpUserTime;
    if (0
        != GetProcessTimes(GetCurrentProcess(), &lpCreationTime, &lpExitTime, &lpKernelTime,
                           &lpUserTime)) {
        return static_cast<double>(static_cast<uint64_t>(lpUserTime.dwLowDateTime)
                                   | static_cast<uint64_t>(lpUserTime.dwHighDateTime) << 32ULL)
               * 1e-7;
    }
#else
    // NOLINTNEXTLINE(cppcoreguidelines-pro-type-member-init)
    timespec ts;
    if (0 == clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &ts))  // MT-Safe  // LCOV_EXCL_BR_LINE
        return ts.tv_sec + ts.tv_nsec * 1e-9;
#endif
    return 0.0;  // LCOV_EXCL_LINE
}
double DeltaWallTime::gettime() VL_MT_SAFE {
#if defined(_WIN32) || defined(__MINGW32__)
    FILETIME ft;  // contains number of 0.1us intervals since the beginning of 1601 UTC.
    GetSystemTimeAsFileTime(&ft);
    const uint64_t tenthus
        = ((static_cast<uint64_t>(ft.dwHighDateTime) << 32) + ft.dwLowDateTime + 5ULL);
    return static_cast<double>(tenthus) * 1e-7;
#else
    // NOLINTNEXTLINE(cppcoreguidelines-pro-type-member-init)
    timespec ts;
    if (0 == clock_gettime(CLOCK_MONOTONIC, &ts))  // MT-Safe  // LCOV_EXCL_BR_LINE
        return ts.tv_sec + ts.tv_nsec * 1e-9;
    return 0.0;  // LCOV_EXCL_LINE
#endif
}

//=========================================================================
// VlOs::memUsageBytes implementation

uint64_t memUsageBytes() VL_MT_SAFE {
#if defined(_WIN32) || defined(__MINGW32__)
    const HANDLE process = GetCurrentProcess();
    PROCESS_MEMORY_COUNTERS pmc;
    if (GetProcessMemoryInfo(process, &pmc, sizeof(pmc))) {
        // The best we can do using simple Windows APIs is to get the size of the working set.
        return pmc.WorkingSetSize;
    }
    return 0;
#else
    // Highly unportable. Sorry
    const char* const statmFilename = "/proc/self/statm";
    FILE* const fp = fopen(statmFilename, "r");
    if (!fp) return 0;
    uint64_t size, resident, share, text, lib, data, dt;  // All in pages
    const int items = fscanf(
        fp, "%" SCNu64 " %" SCNu64 " %" SCNu64 " %" SCNu64 " %" SCNu64 " %" SCNu64 " %" SCNu64,
        &size, &resident, &share, &text, &lib, &data, &dt);
    fclose(fp);
    if (VL_UNCOVERABLE(7 != items)) return 0;
    return (text + data) * getpagesize();
#endif
}

//=========================================================================
// VlOs::getenvStr implementation

std::string getenvStr(const std::string& envvar, const std::string& defaultValue) VL_MT_SAFE {
    std::string ret;
#if defined(_MSC_VER)
    // Note: MinGW does not offer _dupenv_s
    const char* envvalue = nullptr;
    _dupenv_s((char**)&envvalue, nullptr, envvar.c_str());
    if (envvalue != nullptr) {
        const std::string result{envvalue};
        free((void*)envvalue);
        ret = result;
    } else {
        ret = defaultValue;
    }
#else
    if (const char* const envvalue = getenv(envvar.c_str())) {
        ret = envvalue;
    } else {
        ret = defaultValue;
    }
#endif
    return ret;
}

//=========================================================================
}  //namespace VlOs
