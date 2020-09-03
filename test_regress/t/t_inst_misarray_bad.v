// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2012 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   logic foo; initial foo = 0;

//   dut #(.W(4)) udut(.*);
   dut #(.W(4)) udut(.clk(clk),
                     .foo(foo));  // Assigning logic to logic array

endmodule

module dut
    #(parameter W = 1)
    (input logic clk,
     input logic foo[W-1:0]);

    genvar i;
    generate
       for (i = 0; i < W; i++) begin
          suba ua(.clk(clk), .foo(foo[i]));
       end
    endgenerate
endmodule

module suba
  (input logic clk,
   input logic foo);

   always @(posedge clk)
     $display("foo=%b", foo);

endmodule
