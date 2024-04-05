// DESCRIPTION: Verilator: Verilog Test module, C driver code
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Paul Wright.
// SPDX-License-Identifier: CC0-1.0

#include "verilated.h"
#ifdef T_TRI_TOP_EN_OUT_INVALID
#include "Vt_tri_top_en_out_invalid.h"
#else
#include "Vt_tri_top_en_out.h"
#endif
#include <cstdio>
#include <ctime>

int main(int argc, char** argv, char**) {
    int error_cnt;
    // Setup context, defaults, and parse command line
    Verilated::debug(0);
    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};
    contextp->commandArgs(argc, argv);
    // Construct the Verilated model, from Vtop.h generated from Verilating
#ifdef T_TRI_TOP_EN_OUT_INVALID
    const std::unique_ptr<Vt_tri_top_en_out_invalid> topp{
        new Vt_tri_top_en_out_invalid{contextp.get()}};
#else
    const std::unique_ptr<Vt_tri_top_en_out> topp{new Vt_tri_top_en_out{contextp.get()}};
#endif
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

    srand((unsigned)time(0));
#ifdef T_TRI_TOP_EN_OUT_INVALID
    // These should make the compile fail
    error_cnt = topp->internal_sub_io__en;
    error_cnt = topp->internal_sub_io__out;
#endif

    error_cnt = 0;

    // Simulate until $finish
    while (!contextp->gotFinish()) {
        // Evaluate model
        topp->eval();

        // Advance time (to scheduled events)
        if (!topp->eventsPending()) break;
        contextp->time(topp->nextTimeSlot());

        // We want to check that the __en and __out signals can be accessed
        printf("Info:(cpp): drv_en = %x\n", topp->drv_en);
        printf("Info:(cpp): bidir_single_bit_io__en = %x\n", topp->bidir_single_bit_io__en);
        printf("Info:(cpp): bidir_bus_64_io__en = %x\n", (unsigned int)topp->bidir_bus_64_io__en);
        printf("Info:(cpp): bidir_bus_128_io__en = %x,%x,%x,%x\n", topp->bidir_bus_128_io__en[3],
               topp->bidir_bus_128_io__en[2], topp->bidir_bus_128_io__en[1],
               topp->bidir_bus_128_io__en[0]);
        printf("Info:(cpp): sub_io__en = %x\n", topp->sub_io__en);
        printf("Info:(cpp): bidir_single_bit_io = %x\n", topp->bidir_single_bit_io__out);
        printf("Info:(cpp): bidir_bus_64_io = %x\n", (unsigned int)topp->bidir_bus_64_io__out);
        printf("Info:(cpp): bidir_bus_128_io = %x,%x,%x,%x\n", topp->bidir_bus_128_io__out[3],
               topp->bidir_bus_128_io__out[2], topp->bidir_bus_128_io__out[1],
               topp->bidir_bus_128_io__out[0]);
        printf("Info:(cpp): sub_io = %x\n", topp->sub_io__out);

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

            // Check the expected __en output

            if (topp->drv_en & 0x1) {
                if (topp->sub_io__en != 1) {
                    printf("%%Error:(cpp):: sub_io__en = %d expect 1\n", topp->sub_io__en);
                    error_cnt++;
                }
                if (topp->bidir_single_bit_io__en != 1) {
                    printf("%%Error:(cpp):: bidir_single_bit_io__en = %d expect 1\n",
                           topp->bidir_single_bit_io__en);
                    error_cnt++;
                }
            } else {
                if (topp->sub_io__en != 0) {
                    printf("%%Error:(cpp):: sub_io__en = %d expect 0\n", topp->sub_io__en);
                    error_cnt++;
                }
                if (topp->bidir_single_bit_io__en != 0) {
                    printf("%%Error:(cpp):: bidir_single_bit_io__en = %d expect 0\n",
                           topp->bidir_single_bit_io__en);
                    error_cnt++;
                }
            }

            for (int i = 0; i < 4; i++) {
                // __en enabled?
                if ((topp->drv_en & (1 << i)) != 0) {
                    if ((topp->bidir_bus_64_io__en >> (i * 16) & 0xffff) != 0xffff) {
                        printf("%%Error:(cpp):: bidir_bus_64_io__en not as expected %x (%d) %x\n",
                               (unsigned int)topp->bidir_bus_64_io__en, i,
                               (unsigned int)(0xffff << i));
                        error_cnt++;
                    }
                    if (topp->bidir_bus_128_io__en[i] != 0xffffffff) {
                        printf("%%Error:(cpp):: bidir_bus_128_io__en not as expected %x (%d) %x\n",
                               (unsigned int)topp->bidir_bus_128_io__en[i], i, 0xffffffff);
                        error_cnt++;
                    }
                }
                // __en not enabled
                else {
                    if ((topp->bidir_bus_64_io__en >> (i * 16) & 0xffff) != 0x0000) {
                        printf("%%Error:(cpp):: bidir_bus_64_io__en not as expected %x (%d) %x\n",
                               (unsigned int)topp->bidir_bus_64_io__out, i,
                               (unsigned int)(0xffff << i));
                        error_cnt++;
                    }
                    if (topp->bidir_bus_128_io__en[i] != 0x00000000) {
                        printf("%%Error:(cpp):: bidir_bus_128_io__en not as expected %x (%d) %x\n",
                               (unsigned int)topp->bidir_bus_128_io__en[i], i, 0);
                        error_cnt++;
                    }
                }
            }  // for
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
        if (error_cnt != 0) break;
    }
    if (!contextp->gotFinish()) {
        printf("Exiting without $finish; no events left, time was %ld\n", contextp->time());
        puts("final next:");
    }
    // Final model cleanup
    topp->final();
    return 0;
}
