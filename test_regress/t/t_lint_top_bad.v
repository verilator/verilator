// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module sub(input wire clk, cpu_reset);
   reg reset_r;
   always @(posedge clk) begin
      reset_r <= cpu_reset;	 // The problematic one
   end
endmodule

module TOP(/*AUTOARG*/
   // Inputs
   clk, reset_l
   );

   input clk;
   input reset_l;

   reg   sync_0, sync_1, sync_2;
   wire  _cpu_reset_chain_io_q = sync_0;

   sub sub (.clk(clk),
            .cpu_reset(_cpu_reset_chain_io_q | !reset_l));

   always @(posedge clk) begin
      sync_0 <= sync_1;
      sync_1 <= sync_2;
      sync_2 <= !reset_l;
   end
endmodule
