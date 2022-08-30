// -*- mode: C++; c-file-style: "cc-mode" -*-
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Edgar E. Iglesias.
// SPDX-License-Identifier: CC0-1.0

#include VM_PREFIX_INCLUDE
#include "Vt_sc_names.h"

VM_PREFIX* tb = nullptr;

int sc_main(int argc, char* argv[]) {
    tb = new VM_PREFIX{"tb"};
    std::vector<sc_object*> ch = tb->get_child_objects();
    bool found = false;

    /* We expect to find clk in here. */
    for (int i = 0; i < ch.size(); ++i) {
        if (!strcmp(ch[i]->basename(), "clk")) found = true;
    }

    if (found) {
        VL_PRINTF("*-* All Finished *-*\n");
        tb->final();
    } else {
        vl_fatal(__FILE__, __LINE__, "tb", "Unexpected results\n");
    }
    VL_DO_DANGLING(delete tb, tb);
    return 0;
}
