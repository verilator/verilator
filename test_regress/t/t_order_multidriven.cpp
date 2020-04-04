// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2013 by Ted Campbell.
// SPDX-License-Identifier: CC0-1.0

#include "Vt_order_multidriven.h"
#include "verilated.h"
#include "verilated_vcd_c.h"

Vt_order_multidriven* vcore;
VerilatedVcdC* vcd;
vluint64_t vtime;

#define PHASE_90

static void half_cycle(int clk) {
    if (clk & 1) vcore->i_clk_wr = !vcore->i_clk_wr;
    if (clk & 2) vcore->i_clk_rd = !vcore->i_clk_rd;

    vtime += 10 / 2;

    vcore->eval();
    vcore->eval();

    vcd->dump(vtime);
}

static void cycle() {
#ifdef PHASE_90
    half_cycle(1);
    half_cycle(2);
    half_cycle(1);
    half_cycle(2);
#else
    half_cycle(3);
    half_cycle(3);
#endif
}

int main() {

    Verilated::traceEverOn(true);

    vcore = new Vt_order_multidriven;
    vcd = new VerilatedVcdC;

    vcore->trace(vcd, 99);
    vcd->open(VL_STRINGIFY(TEST_OBJ_DIR) "/simx.vcd");

    vcore->i_clk_wr = 0;
    vcore->i_clk_rd = 0;

    for (int i = 0; i < 256; ++i)
        cycle();

    vcd->close();
    printf("*-* All Finished *-*\n");
}
