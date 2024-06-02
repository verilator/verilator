// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 Wilson Snyder and Marlon James.
// SPDX-License-Identifier: CC0-1.0


module t (/*AUTOARG*/
   // Inputs
   input clk
   );

   reg [31:0]     count    /*verilator public_flat_rd */;

   // Test loop
   initial begin
      count = 0;
   end

   always @(posedge clk) begin
      count <= count + 2;
   end

endmodule : t
