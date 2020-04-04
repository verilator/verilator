// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty.
// SPDX-License-Identifier: CC0-1.0

#include VM_PREFIX_INCLUDE

VM_PREFIX* tb = NULL;
bool pass = true;

double sc_time_stamp() { return 0; }

#ifdef SYSTEMC_VERSION
int sc_main(int, char**)
#else
int main()
#endif
{
    Verilated::debug(0);
    tb = new VM_PREFIX("tb");

    // Just a constructor test
    VL_PRINTF("*-* All Finished *-*\n");
    return 0;
}
