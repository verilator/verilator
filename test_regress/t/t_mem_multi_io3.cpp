// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty.

#if defined(T_MEM_MULTI_IO3_CC)
# include "Vt_mem_multi_io3_cc.h"
#elif defined(T_MEM_MULTI_IO3_SC)
# include "Vt_mem_multi_io3_sc.h"
#else
# error "Unknown test"
#endif

VM_PREFIX* tb = NULL;
bool pass = true;

double sc_time_stamp() {
    return 0;
}

int main() {
    Verilated::debug(0);
    tb = new VM_PREFIX ("tb");

    // Just a constructor test
    bool pass = true;

    if (pass) {
	VL_PRINTF("*-* All Finished *-*\n");
    } else {
	vl_fatal(__FILE__,__LINE__,"top", "Unexpected results from test\n");
    }
    return 0;
}
