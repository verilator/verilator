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

    initial begin
        $dumpfile({`STRINGIFY(`TEST_OBJ_DIR),"/simx.vcd"});
        $dumpvars;
        forever clk = #CLK_HALF_PERIOD ~clk;
    end

    always begin
        rst = 1;
        clk = 0;
        a = 0;
        c = 0;
        b = 0;
        d = 0;

        #CLK_PERIOD;
        rst = 0;
        b = 1;

        #(10 * CLK_PERIOD);

        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
