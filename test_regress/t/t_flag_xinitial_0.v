// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2017 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Outputs
   value
   );

   output reg [63:0] value;

   initial begin
`ifdef VERILATOR
      // Default is all ones, so we assume that here
      if (value != '0) $stop;
`else
      if (value != {64{1'bx}}) $stop;
`endif
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
