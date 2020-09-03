// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2007 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Outputs
   x,
   // Inputs
   clk
   );

`ifdef ALLOW_UNOPT
   /*verilator lint_off UNOPTFLAT*/
`endif

   input clk;
   output [31:0] x;  // Avoid eliminating x

   reg [31:0] x;
   always @* begin
      x = x ^ $random;
   end

endmodule
