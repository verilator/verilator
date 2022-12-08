// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

// bug3781
module t;
    logic clk;
    logic [7:0] data;
    logic [3:0] ptr;
    logic [7:0] mem[16];

    initial begin
        clk = 1'b0;
        fork forever #5 clk = ~clk; join_none
        ptr = '0;
        #10 data = 1;
        #10 if (mem[ptr] != data) $stop;
        #10 data = 2;
        #10 if (mem[ptr] != data) $stop;
        #10 data = 3;
        #10 if (mem[ptr] != data) $stop;
        #10 $write("*-* All Finished *-*\n");
        $finish;
    end

    always @(posedge clk) begin
        mem[ptr] <= #1 data;
    end
endmodule
