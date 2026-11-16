// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#ifndef TEST_THREADS_H_
#define TEST_THREADS_H_

#include <cstdlib>
#if defined(VERILATOR) && defined(__linux__)
#include <dirent.h>
#endif

// Return zero when deterministic thread-count checks are unavailable.
inline int testLiveThreads() {
#if defined(VERILATOR) && defined(__linux__)
    DIR* const dirp = opendir("/proc/self/task");
    if (!dirp) std::abort();
    int count = 0;
    while (const dirent* const entryp = readdir(dirp)) {
        if (entryp->d_name[0] != '.') ++count;
    }
    closedir(dirp);
    return count;
#else
    return 0;
#endif
}

#endif  // Guard
