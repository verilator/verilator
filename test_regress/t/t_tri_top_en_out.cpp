// DESCRIPTION: Verilator: Verilog Test module, C driver code
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Paul Wright.
// SPDX-License-Identifier: CC0-1.0

#include "verilated.h"

#include "TestCheck.h"
#include "Vt_tri_top_en_out.h"

#include <ctime>

int main(int argc, char** argv, char**) {
    int errors;
    // Setup context, defaults, and parse command line
    Verilated::debug(0);
    VerilatedContext context;
    context.commandArgs(argc, argv);
    // Construct the Verilated model, from Vtop.h generated from Verilating
    Vt_tri_top_en_out top{&context};

    // Initial input
    top.drv_en = 0;
    top.single_bit_io = rand() & 1;
    top.bidir_single_bit_io = rand() & 1;
    top.bus_64_io = 0;
    top.bidir_bus_64_io = rand() & 0xffffffffffffffff;
    top.bus_128_io[0] = 0;
    top.bus_128_io[1] = 0;
    top.bus_128_io[2] = 0;
    top.bus_128_io[3] = 0;
    top.bidir_bus_128_io[0] = rand() & 0xffffffff;
    top.bidir_bus_128_io[1] = rand() & 0xffffffff;
    top.bidir_bus_128_io[2] = rand() & 0xffffffff;
    top.bidir_bus_128_io[3] = rand() & 0xffffffff;
    top.sub_io = rand() & 1;
    top.test_en = 1;

    errors = 0;

    // Simulate until $finish
    while (!context.gotFinish()) {
        // Evaluate model
        top.eval();

        // Advance time (to scheduled events)
        if (!top.eventsPending()) break;
        context.time(top.nextTimeSlot());

        // We want to check that the __en and __out signals can be accessed
        printf("Info:(cpp): drv_en = %x\n", top.drv_en);
        printf("Info:(cpp): bidir_single_bit_io__en = %x\n", top.bidir_single_bit_io__en);
        printf("Info:(cpp): bidir_bus_64_io__en = %x\n", (unsigned int)top.bidir_bus_64_io__en);
        printf("Info:(cpp): bidir_bus_128_io__en = %x,%x,%x,%x\n", top.bidir_bus_128_io__en[3],
               top.bidir_bus_128_io__en[2], top.bidir_bus_128_io__en[1],
               top.bidir_bus_128_io__en[0]);
        printf("Info:(cpp): sub_io__en = %x\n", top.sub_io__en);
        printf("Info:(cpp): bidir_single_bit_io = %x\n", top.bidir_single_bit_io__out);
        printf("Info:(cpp): bidir_bus_64_io = %x\n", (unsigned int)top.bidir_bus_64_io__out);
        printf("Info:(cpp): bidir_bus_128_io = %x,%x,%x,%x\n", top.bidir_bus_128_io__out[3],
               top.bidir_bus_128_io__out[2], top.bidir_bus_128_io__out[1],
               top.bidir_bus_128_io__out[0]);
        printf("Info:(cpp): sub_io = %x\n", top.sub_io__out);

        // Loop back if verilog is driving
        // Verilator will not do this for itself
        // We must implement the top-level resolution
        if (top.sub_io__en) { top.sub_io = top.sub_io__out; }
        if (top.bidir_single_bit_io__en) {
            top.bidir_single_bit_io = top.bidir_single_bit_io__out;
        }
        // For bus signals, overwrite the bits which are driven by verilog, preserve the others
        if (top.bidir_bus_64_io__en) {
            top.bidir_bus_64_io = ((~top.bidir_bus_64_io__en) & top.bidir_bus_64_io)
                                  | (top.bidir_bus_64_io__en & top.bidir_bus_64_io__out);
        }
        for (int i = 0; i < 4; i++) {
            if (top.bidir_bus_128_io__en[i]) {
                top.bidir_bus_128_io[i]
                    = ((~top.bidir_bus_128_io__en[i]) & top.bidir_bus_128_io[i])
                      | (top.bidir_bus_128_io__en[i] & top.bidir_bus_128_io__out[i]);
            }
        }

        // Has the verilog code finished a test loop?
        if (top.loop_done == 1) {

            // Check the expected __en output

            if (top.drv_en & 0x1) {
                TEST_CHECK_EQ(uint64_t(top.sub_io__en), 1);
                TEST_CHECK_EQ(uint64_t(top.bidir_single_bit_io__en), 1);
            } else {
                TEST_CHECK_EQ(uint64_t(top.sub_io__en), 0);
                TEST_CHECK_EQ(uint64_t(top.bidir_single_bit_io__en), 0);
            }

            for (int i = 0; i < 4; i++) {
                // __en enabled?
                if ((top.drv_en & (1 << i)) != 0) {
                    TEST_CHECK_EQ(uint64_t(top.bidir_bus_64_io__en >> (i * 16) & 0xffff), 0xffff);
                    TEST_CHECK_EQ(uint64_t(top.bidir_bus_128_io__en[i]), 0xffffffff);
                }
                // __en not enabled
                else {
                    TEST_CHECK_EQ(uint64_t(top.bidir_bus_64_io__en >> (i * 16) & 0xffff), 0x0000);
                    TEST_CHECK_EQ(uint64_t(top.bidir_bus_128_io__en[i]), 0x00000000);
                }
            }  // for
            if (top.drv_en == 15) {
                top.test_en = 0;
            } else {
                top.drv_en++;

                // Drive the bits verilog shouldn't be driving
                if (top.drv_en & 1) {
                    top.single_bit_io = rand() & 1;
                    top.bidir_single_bit_io = rand() & 1;
                    top.sub_io = rand() & 1;
                    top.bidir_bus_64_io
                        = ((rand() & 0xffff) << 0) | (top.bidir_bus_64_io & 0xffffffffffff0000);
                    top.bidir_bus_128_io[0] = rand() & 0xffffffff;
                } else {
                    top.single_bit_io = 0;
                    top.bidir_single_bit_io = 0;
                    top.sub_io = 0;
                    top.bidir_bus_64_io = (top.bidir_bus_64_io & 0xffffffffffff0000);
                    top.bidir_bus_128_io[0] = 0;
                }
                if (top.drv_en & 2) {
                    top.bidir_bus_64_io
                        = ((rand() & 0xffff) << 16) | (top.bidir_bus_64_io & 0xffffffff0000ffff);
                    top.bidir_bus_128_io[1] = rand() & 0xffffffff;
                } else {
                    top.bidir_bus_64_io = (top.bidir_bus_64_io & 0xffffffff0000ffff);
                    top.bidir_bus_128_io[1] = 0;
                }
                if (top.drv_en & 4) {
                    top.bidir_bus_64_io = (((uint64_t)(rand() & 0xffff)) << 32)
                                          | (top.bidir_bus_64_io & 0xffff0000ffffffff);
                    top.bidir_bus_128_io[2] = rand() & 0xffffffff;
                } else {
                    top.bidir_bus_64_io = (top.bidir_bus_64_io & 0xffff0000ffffffff);
                    top.bidir_bus_128_io[2] = 0;
                }
                if (top.drv_en & 8) {
                    top.bidir_bus_64_io = (((uint64_t)(rand() & 0xffff)) << 48)
                                          | (top.bidir_bus_64_io & 0x0000ffffffffffff);
                    top.bidir_bus_128_io[3] = rand() & 0xffffffff;
                } else {
                    top.bidir_bus_64_io = (top.bidir_bus_64_io & 0x0000ffffffffffff);
                    top.bidir_bus_128_io[3] = 0;
                }
            }
            // Invert the input side
            top.bidir_single_bit_io = (~top.bidir_single_bit_io) & 0x1;
            top.bidir_bus_64_io = ~top.bidir_bus_64_io;
            for (int i = 0; i < 4; i++) { top.bidir_bus_128_io[i] = ~top.bidir_bus_128_io[i]; }
        }  // if (loop_done)
        if (errors != 0) break;
    }
    // Final model cleanup
    top.final();
    return 0;
}
