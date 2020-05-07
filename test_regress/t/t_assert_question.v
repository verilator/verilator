// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2016 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Outputs
   dout,
   // Inputs
   clk, sel, a, c
   );

   input clk;
   input bit [3:0] sel;
   input bit [3:0] a;
   input bit       c;
   output bit      dout;

   localparam logic DC  = 1'b?;

   always_ff @(posedge clk) begin
      unique casez(sel)
        4'b0000: dout                  <= a[0];
        4'b001?: dout                  <= a[1];
        {1'b0, 1'b1, 1'b?, 1'b?}: dout <= a[2];
        {1'b1, 1'b?, 1'b?, DC}: dout   <= a[3];
        default: dout                  <= '0;
      endcase
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
