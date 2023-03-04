// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

`timescale 1ns/1ps

module timing_wait_long();
    localparam real FULL_TIME = 5e6;
    /* verilator lint_off WIDTHTRUNC */
    localparam [22:0] FIT_TIME = int'(5e6);
    localparam [21:0] TRUNCATED_TIME = int'(5e6); // 805696
    /* verilator lint_on WIDTHTRUNC */

    real realvar_time = 5e6;
    time timevar;
    initial begin
        #5ms;
        $display("Current realtime: %d == %d", time'($realtime), time'(1 * 5e9));

        realvar_time = realvar_time + 1;
        #realvar_time;
        $display("Current realtime: %d == %d", time'($realtime), time'(2 * 5e6 + 1));

        timevar = time'(realvar_time - 2);
        #timevar;
        $display("Current realtime: %d == %d", time'($realtime), time'(3 * 5e6));

        $display("FULL_TIME: %f", FULL_TIME);
        #FULL_TIME;
        $display("Current realtime: %d == %d", time'($realtime), time'(4 * 5e6));

        $display("FIT_TIME: %d -- %f", FIT_TIME, real'(FIT_TIME));
        #FIT_TIME;
        $display("Current realtime: %d == %d", time'($realtime), time'(5 * 5e6));

        $display("TRUNCATED_TIME: %d -- %f", TRUNCATED_TIME, real'(TRUNCATED_TIME));
        #TRUNCATED_TIME;
        $display("Current realtime: %d == %d", time'($realtime), time'(5 * 5e6 + real'(int'(5e6) % 2**22)));

        $write("*-* All Finished *-*\n");
        $finish();
    end

endmodule
