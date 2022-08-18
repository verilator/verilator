// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2013 by Ted Campbell.
// SPDX-License-Identifier: CC0-1.0

#include "verilated.h"
#include "verilated_vcd_c.h"

#include "Vt_order_multidriven.h"

double sc_time_stamp() { return 0; }

Vt_order_multidriven* vcore;
VerilatedVcdC* vcd;
uint64_t vtime;

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
    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};
    contextp->traceEverOn(true);

    vcore = new VM_PREFIX{contextp.get()};
    vcd = new VerilatedVcdC;

    vcore->trace(vcd, 99);
    vcd->open(VL_STRINGIFY(TEST_OBJ_DIR) "/simx.vcd");

    vcore->i_clk_wr = 0;
    vcore->i_clk_rd = 0;

    for (int i = 0; i < 256; ++i) {  //
        cycle();
    }

    vcd->close();

    vcore->final();
    VL_DO_DANGLING(delete vcore, vcore);

    printf("*-* All Finished *-*\n");
}
