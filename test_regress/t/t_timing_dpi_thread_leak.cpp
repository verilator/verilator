// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

#include <cstdio>
#include <cstdlib>
#include <dirent.h>
#include <svdpi.h>

#ifdef __cplusplus
extern "C" {
#endif

extern void dpi_export();

static int completed = 0;

int dpi_import() {
    dpi_export();
    // Second call tests whether the killed process alters the state after being killed.
    dpi_export();
    ++completed;
    return 0;
}

int c_completed() { return completed; }

int live_threads() {
    DIR* dir = opendir("/proc/self/task");
    if (!dir) std::abort();
    int count = 0;
    while (dirent* entry = readdir(dir)) {
        if (entry->d_name[0] != '.') ++count;
    }
    closedir(dir);
    return count;
}

#ifdef __cplusplus
}
#endif
