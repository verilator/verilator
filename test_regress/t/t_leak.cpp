// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// DESCRIPTION: Verilator: Verilog Test driver/expect definition
//
// Copyright 2003-2009 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

#include <verilated.h>

#include <cstdio>
#include <cstdlib>
#include VM_PREFIX_INCLUDE

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
    uint64_t ps_vsize, ps_rss;
    int items = fscanf(fp,
                       ("%d (%*[^) ]) %*1s %d %*d %*d %*d %*d %u"
                        " %u %u %u %u %d %d %d %d"
                        " %*d %*d %*u %*u %d %" PRIu64 " %" PRIu64 " "),
                       &ps_ign, &ps_ign, &ps_ign, &ps_ign, &ps_ign, &ps_ign, &ps_ign, &ps_ign,
                       &ps_ign, &ps_ign, &ps_ign, &ps_ign, &ps_vsize, &ps_rss);
    fclose(fp);
    if (items >= 14) {
        return ps_vsize;
    } else {
        return 0;
    }
}

void make_and_destroy() {
#ifdef VL_NO_LEGACY
    VerilatedContext* contextp = new VerilatedContext;
    VM_PREFIX* topp = new VM_PREFIX{contextp};
    contextp->debug(0);
#else
    VM_PREFIX* topp = new VM_PREFIX;
    Verilated::debug(0);
#endif

    topp->eval();
    topp->clk = true;
    while (!
#ifdef VL_NO_LEGACY
           contextp->gotFinish()
#else
           Verilated::gotFinish()
#endif
    ) {
#ifdef VL_NO_LEGACY
        contextp->timeInc(5);
#else
        main_time += 5;
#endif
        topp->clk = !topp->clk;
        topp->eval();
    }

    VL_DO_DANGLING(delete topp, topp);
#ifdef VL_NO_LEGACY
    VL_DO_DANGLING(delete contextp, contextp);
#endif
}

int main(int argc, char* argv[]) {
    uint64_t firstUsage = get_memory_usage();

    // Warmup phase
    for (int i = 0; i < 10; i++) {  //
        make_and_destroy();
    }
    firstUsage = get_memory_usage();
    printf("Memory size %" PRId64 " bytes\n", firstUsage);

    int loops = 10;
    for (int left = loops; left > 0;) {
        for (int j = 0; j < 1; ++j, --left) {  //
            make_and_destroy();
        }
    }

    uint64_t leaked = get_memory_usage() - firstUsage;
    if (leaked > 64 * 1024) {  // Have to allow some slop for this code.
        printf("Leaked %" PRId64 " bytes, or ~ %" PRId64 " bytes/construt\n",  //
               leaked, leaked / loops);
        vl_fatal(__FILE__, __LINE__, "top", "Leaked memory\n");
    }

    printf("*-* All Finished *-*\n");
}
