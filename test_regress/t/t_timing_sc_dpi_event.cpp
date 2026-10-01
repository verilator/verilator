// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 ViraSemi Inc.
// SPDX-License-Identifier: CC0-1.0

#include VM_PREFIX_INCLUDE

#include "svdpi.h"

using namespace sc_core;

// Exported by the model
extern "C" void sv_trigger();

// Calls into the model at 10ns, from outside its own evaluation
SC_MODULE(poker) {
    SC_CTOR(poker) { SC_THREAD(run); }
    void run() {
        wait(10, SC_NS);
        svScope scope = svGetScopeFromName("tb.t");
        if (!scope) vl_fatal(__FILE__, __LINE__, "tb", "svGetScopeFromName failed\n");
        svSetScope(scope);
        sv_trigger();
    }
};

int sc_main(int argc, char* argv[]) {
    VM_PREFIX* tb = new VM_PREFIX{"tb"};
    poker p{"poker"};

    sc_start();

    tb->final();
    VL_DO_DANGLING(delete tb, tb);
    return 0;
}
