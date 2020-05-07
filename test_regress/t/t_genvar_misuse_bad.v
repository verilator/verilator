// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2012 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0
// See bug408

module top
  (
   output logic [1:0] q,
   input logic [1:0]  d,
   input logic        clk
   );

   genvar             i;
   assign            q[i] = d[i];
endmodule
