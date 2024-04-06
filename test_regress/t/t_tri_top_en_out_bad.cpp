// DESCRIPTION: Verilator: Verilog Test module, C driver code
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Paul Wright.
// SPDX-License-Identifier: CC0-1.0

// This test is a copy of t_tri_top_en_out.cpp
// It should fail to compile when we try to connect to signals which
// should not be there, internal_sub_io__en and internal_sub_io__out

#include "verilated.h"
#include "Vt_tri_top_en_out_bad.h"

int main(int argc, char** argv, char**) {
    int errors;
    // Setup context, defaults, and parse command line
    Verilated::debug(0);
    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};
    contextp->commandArgs(argc, argv);
    // Construct the Verilated model, from Vtop.h generated from Verilating
    const std::unique_ptr<Vt_tri_top_en_out_bad> topp{
        new Vt_tri_top_en_out_bad{contextp.get()}};
    // Initial input
    topp->drv_en = 0;
    topp->single_bit_io = rand() & 1;
    topp->bidir_single_bit_io = rand() & 1;
    topp->bus_64_io = 0;
    topp->bidir_bus_64_io = rand() & 0xffffffffffffffff;
    topp->bus_128_io[0] = 0;
    topp->bus_128_io[1] = 0;
    topp->bus_128_io[2] = 0;
    topp->bus_128_io[3] = 0;
    topp->bidir_bus_128_io[0] = rand() & 0xffffffff;
    topp->bidir_bus_128_io[1] = rand() & 0xffffffff;
    topp->bidir_bus_128_io[2] = rand() & 0xffffffff;
    topp->bidir_bus_128_io[3] = rand() & 0xffffffff;
    topp->sub_io = rand() & 1;
    topp->test_en = 1;

    errors = 0;

    // These should make the compile fail
    // These variables should not be visible
    //
    // Use the + operator to satisfy the static code checks
    // Variable reassigned value before old value used.
    // These variables will never be used, as the compile should
    // fail!
    errors += topp->internal_sub_io__en;
    errors += topp->internal_sub_io__out;

    // Simulate until $finish
    while (!contextp->gotFinish()) {
        // Evaluate model
        topp->eval();

        // Advance time (to scheduled events)
        if (!topp->eventsPending()) break;
        contextp->time(topp->nextTimeSlot());

        // Loop back if verilog is driving
        // Verilator will not do this for itself
        // We must implement the top-level resolution
        if (topp->sub_io__en) { topp->sub_io = topp->sub_io__out; }
        if (topp->bidir_single_bit_io__en) {
            topp->bidir_single_bit_io = topp->bidir_single_bit_io__out;
        }
        // For bus signals, overwrite the bits which are driven by verilog, preserve the others
        if (topp->bidir_bus_64_io__en) {
            topp->bidir_bus_64_io = ((~topp->bidir_bus_64_io__en) & topp->bidir_bus_64_io)
                                    | (topp->bidir_bus_64_io__en & topp->bidir_bus_64_io__out);
        }
        for (int i = 0; i < 4; i++) {
            if (topp->bidir_bus_128_io__en[i]) {
                topp->bidir_bus_128_io[i]
                    = ((~topp->bidir_bus_128_io__en[i]) & topp->bidir_bus_128_io[i])
                      | (topp->bidir_bus_128_io__en[i] & topp->bidir_bus_128_io__out[i]);
            }
        }

        // Has the verilog code finished a test loop?
        if (topp->loop_done == 1) {
            if (topp->drv_en == 15) {
                topp->test_en = 0;
            } else {
                topp->drv_en++;

                // Drive the bits verilog shouldn't be driving
                if (topp->drv_en & 1) {
                    topp->single_bit_io = rand() & 1;
                    topp->bidir_single_bit_io = rand() & 1;
                    topp->sub_io = rand() & 1;
                    topp->bidir_bus_64_io
                        = ((rand() & 0xffff) << 0) | (topp->bidir_bus_64_io & 0xffffffffffff0000);
                    topp->bidir_bus_128_io[0] = rand() & 0xffffffff;
                } else {
                    topp->single_bit_io = 0;
                    topp->bidir_single_bit_io = 0;
                    topp->sub_io = 0;
                    topp->bidir_bus_64_io = (topp->bidir_bus_64_io & 0xffffffffffff0000);
                    topp->bidir_bus_128_io[0] = 0;
                }
                if (topp->drv_en & 2) {
                    topp->bidir_bus_64_io
                        = ((rand() & 0xffff) << 16) | (topp->bidir_bus_64_io & 0xffffffff0000ffff);
                    topp->bidir_bus_128_io[1] = rand() & 0xffffffff;
                } else {
                    topp->bidir_bus_64_io = (topp->bidir_bus_64_io & 0xffffffff0000ffff);
                    topp->bidir_bus_128_io[1] = 0;
                }
                if (topp->drv_en & 4) {
                    topp->bidir_bus_64_io = (((uint64_t)(rand() & 0xffff)) << 32)
                                            | (topp->bidir_bus_64_io & 0xffff0000ffffffff);
                    topp->bidir_bus_128_io[2] = rand() & 0xffffffff;
                } else {
                    topp->bidir_bus_64_io = (topp->bidir_bus_64_io & 0xffff0000ffffffff);
                    topp->bidir_bus_128_io[2] = 0;
                }
                if (topp->drv_en & 8) {
                    topp->bidir_bus_64_io = (((uint64_t)(rand() & 0xffff)) << 48)
                                            | (topp->bidir_bus_64_io & 0x0000ffffffffffff);
                    topp->bidir_bus_128_io[3] = rand() & 0xffffffff;
                } else {
                    topp->bidir_bus_64_io = (topp->bidir_bus_64_io & 0x0000ffffffffffff);
                    topp->bidir_bus_128_io[3] = 0;
                }
            }
            // Invert the input side
            topp->bidir_single_bit_io = (~topp->bidir_single_bit_io) & 0x1;
            topp->bidir_bus_64_io = ~topp->bidir_bus_64_io;
            for (int i = 0; i < 4; i++) { topp->bidir_bus_128_io[i] = ~topp->bidir_bus_128_io[i]; }
        }  // if (loop_done)
        if (errors != 0) break;
    }
    // Final model cleanup
    topp->final();
    return 0;
}
