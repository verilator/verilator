// -*- mode: C++; c-file-style: "cc-mode" -*-
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

#include "Vt_vpi_sc.h"

VM_PREFIX* tb = NULL;

int sc_main(int argc, char* argv[]) {
    tb = new VM_PREFIX("tb");

    VL_PRINTF("*-* All Finished *-*\n");
    tb->final();
    return 0;
}
