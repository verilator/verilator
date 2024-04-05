// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0


typedef struct {
   logic [4:0] w5;
} Data_t;

module t;

    reg en;
    reg [7:0] r_id;

    Data_t ts;

    initial begin
       en = 1;
       r_id = 42;
       ts = '{w5: en ? r_id[4:0] : 5'b0};

       $display("ts.w5 = %h", ts.w5);
       if ($c32(ts.w5) != 5'h0a) $stop;
       $write("*-* All Finished *-*\n");
       $finish;
    end
endmodule
