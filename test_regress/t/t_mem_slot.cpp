// -*- mode: C++; c-file-style: "cc-mode" -*-
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

#include <verilated.h>

#include "Vt_mem_slot.h"

#include <cstdlib>

double sc_time_stamp() { return 0; }

unsigned int Array[3];

unsigned int StepSim(Vt_mem_slot* sim, unsigned int slot, unsigned int bit, unsigned int val,
                     unsigned int rslot) {
#ifdef TEST_VERBOSE
    printf("StepSim: slot=%u bit=%u val=%u rslot=%u\n", slot, bit, val, rslot);
#endif

    sim->SlotIdx = slot;
    sim->BitToChange = bit;
    sim->BitVal = val;
    sim->SlotToReturn = rslot;
    sim->Clk = 0;

    sim->eval();

    sim->Clk = 1;

    sim->eval();

    if (sim->OutputVal != Array[rslot]) {
        printf("%%Error: got %x - expected %x\n", sim->OutputVal, Array[rslot]);
        exit(1);
    }

    if (val)
        Array[slot] |= (1 << bit);
    else
        Array[slot] &= ~(1 << bit);

    return sim->OutputVal;
}

int main(int argc, char* argv[]) {
    Vt_mem_slot* sim = new Vt_mem_slot;
    int slot, bit, i;

    Verilated::debug(0);

    // clear all bits in the array
    for (slot = 0; slot < 3; slot++)
        for (bit = 0; bit < 2; bit++)  //
            StepSim(sim, slot, bit, 0, 0);

    printf("\nTesting\n");
    for (i = 0; i < 100; i++)  //
        StepSim(sim, random() % 3, random() % 2, random() % 2, random() % 3);

    sim->final();
    VL_DO_DANGLING(delete sim, sim);

    printf("*-* All Finished *-*\n");
}
