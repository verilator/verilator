// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2017 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;
   localparam int C[4] = '{5, 6, 7, 8};
   a #(.P(C)) i_a ();
endmodule

module a
  #( parameter int P[4] = '{1, 2, 3, 4} );
   initial begin
      if (P[0] != 5) $stop;
      if (P[1] != 6) $stop;
      if (P[2] != 7) $stop;
      if (P[3] != 8) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
