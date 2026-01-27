// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2006 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Outputs
   b,
   // Inputs
   clk, en, a
   );

   // bug1017

   input clk;

   input en;
   input a[1];
   output logic b[1];

   always_ff @ (posedge clk) begin
      b <= en ? a : b;
   end

   always @ (posedge clk) begin
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
