// -*- mode: C++; c-file-style: "cc-mode" -*-

#include "Vt_vpi_sc.h"

VM_PREFIX* tb = NULL;

int sc_main(int argc, char *argv[]) {
    tb  = new VM_PREFIX("tb");

    VL_PRINTF("*-* All Finished *-*\n");
    tb->final();
    return 0;
}
