// -*- mode: C++; c-file-style: "cc-mode" -*-

#include <cstdlib>
#include <verilated.h>
#include "Vt_mem_slot.h"

unsigned int Array[3];

unsigned int
StepSim (Vt_mem_slot *sim, unsigned int slot, unsigned int bit, unsigned int val, unsigned int rslot) {
#ifdef TEST_VERBOSE
    printf ("StepSim: slot=%d bit=%d val=%d rslot=%d\n", slot, bit, val, rslot);
#endif

    sim->SlotIdx      = slot;
    sim->BitToChange  = bit;
    sim->BitVal       = val;
    sim->SlotToReturn = rslot;
    sim->Clk          = 0;

    sim->eval();

    sim->Clk          = 1;

    sim->eval();


    if (sim->OutputVal != Array[rslot]) {
	printf ("%%Error: got %x - expected %x\n", sim->OutputVal, Array[rslot]);
	exit (1);
    }

    if (val)
	Array[slot] |= (1 << bit);
    else
	Array[slot] &= ~(1 << bit);

    return sim->OutputVal;
}

int main (int argc, char *argv[]) {
    Vt_mem_slot *sim = new Vt_mem_slot;
    int slot, bit, i;

    Verilated::debug(0);

    /* clear all bits in the array */
    for (slot = 0; slot < 3; slot++)
	for (bit = 0; bit < 2; bit++)
	    StepSim (sim, slot, bit, 0, 0);

    printf ("\nTesting\n");
    for (i = 0; i < 100; i++)
	StepSim (sim, random() % 3, random() % 2, random() % 2, random() % 3);
    printf ("*-* All Finished *-*\n");
}
