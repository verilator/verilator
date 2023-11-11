// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

`define STRINGIFY(x) `"x`"

module t;
    localparam CLK_PERIOD = 10;
    localparam CLK_HALF_PERIOD = CLK_PERIOD / 2;

    logic rst;
    logic clk;
    logic a;
    logic b;
    logic c;
    logic d;
    event ev;

    initial begin
        $dumpfile(`STRINGIFY(`TEST_DUMPFILE));
        $dumpvars;
        forever clk = #CLK_HALF_PERIOD ~clk;
    end

    always begin
        rst = 1;
        clk = 0;
        a = 0;
        c = 0;
        b = ~b;
        d = 0;

        fork #(10 * CLK_PERIOD) b = 0; join_none

        while (b) begin
            c = ~c;
            -> ev;
            #CLK_PERIOD;
        end

        $write("[%0t] Done\n", $time);
        $write("*-* All Finished *-*\n");
        $finish;
    end

endmodule
