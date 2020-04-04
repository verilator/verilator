// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// DESCRIPTION: Verilator: Verilog Test driver/expect definition
//
// Copyright 2003-2009 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

#include <cstdlib>
#include <cstdio>
#include <verilated.h>
#include "Vt_leak.h"

unsigned int main_time = 0;
double sc_time_stamp() { return main_time; }

long long get_memory_usage() {
    // Return memory usage.  Return 0 if the system doesn't look quite right.

#if 0  // BSD only.
    struct rusage usage;
    getrusage(RUSAGE_SELF, &usage);
    return usage.ru_ixrss + usage.ru_idrss + usage.ru_isrss;
#endif

    FILE* fp = fopen("/proc/self/stat", "r");
    if (!fp) return 0;

    int ps_ign;
    vluint64_t ps_vsize, ps_rss;
    int items = fscanf(fp, ("%d (%*[^) ]) %*1s %d %*d %*d %*d %*d %u"
                            " %u %u %u %u %d %d %d %d"
                            " %*d %*d %*u %*u %d %" VL_PRI64 "u %" VL_PRI64 "u "),
                       &ps_ign, &ps_ign, &ps_ign,
                       &ps_ign, &ps_ign, &ps_ign, &ps_ign,
                       &ps_ign, &ps_ign, &ps_ign, &ps_ign,
                       &ps_ign, &ps_vsize, &ps_rss);
    fclose(fp);
    if (items >= 14) {
        return ps_vsize;
    } else {
        return 0;
    }
}

void make_and_destroy() {
    Vt_leak* topp = new Vt_leak;

    Verilated::debug(0);
    Verilated::gotFinish(0);
    topp->eval();
    topp->clk = true;
    while (!Verilated::gotFinish()) {
        main_time += 5;
        topp->clk = !topp->clk;
        topp->eval();
    }

    VL_DO_DANGLING(delete topp, topp);
}

int main(int argc, char* argv[]) {
    vluint64_t firstUsage = get_memory_usage();

    // Warmup phase
    for (int i = 0; i < 10; i++) {
        make_and_destroy();
    }
    firstUsage = get_memory_usage();
    printf("Memory size %" VL_PRI64 "d bytes\n", firstUsage);

    int loops = 10;
    for (int left = loops; left > 0;) {
        for (int j = 0; j < 1; ++j, --left) {
            make_and_destroy();
        }
    }

    vluint64_t leaked = get_memory_usage() - firstUsage;
    if (leaked > 64*1024) {  // Have to allow some slop for this code.
        printf("Leaked %" VL_PRI64 "d bytes, or ~ %" VL_PRI64 "d bytes/construt\n", leaked, leaked/loops);
        vl_fatal(__FILE__, __LINE__, "top", "Leaked memory\n");
    }

    printf("*-* All Finished *-*\n");
}
