// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2003 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   parameter [31:0]  p2=2, p3=3;
   integer           i2=2, i3=3;
   reg [31:0]        r2=2, r3=3;
   wire [31:0]       w2=2, w3=3;

   always @ (posedge clk) begin
      if (p2 !== 2) $stop;
      if (p3 !== 3) $stop;
      if (i2 !== 2) $stop;
      if (i3 !== 3) $stop;
      if (r2 !== 2) $stop;
      if (r3 !== 3) $stop;
      if (w2 !== 2) $stop;
      if (w3 !== 3) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
