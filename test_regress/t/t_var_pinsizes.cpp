// -*- mode: C++; c-file-style: "cc-mode" -*-

#include VM_PREFIX_INCLUDE

VM_PREFIX* tb = NULL;

double sc_time_stamp() {
    return 0;
}

int main() {
    Verilated::debug(0);
    tb  = new VM_PREFIX("tb");

    VL_PRINTF("*-* All Finished *-*\n");
    tb->final();
    return 0;
}

int sc_main(int argc, char *argv[]) {
    tb  = new VM_PREFIX("tb");

    VL_PRINTF("*-* All Finished *-*\n");
    tb->final();
    return 0;
}
