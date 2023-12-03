// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2017 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;
   localparam logic [3:0] val_0 = 0; // 4
   localparam int val_1 = $bits(val_0);
   localparam int c[4]  = '{ val_1 + 1, val_1 + 2, val_1 + 3, val_1 * 2};
   a #(.p(c)) i_a ();
   a #(.p('{ val_1 * 2 - 3, val_1 / 2 + 4, 3 + val_1, 2 ** (val_1 - 1)})) i_b ();
endmodule

module a
  #( parameter int p[4] = '{1, 2, 3, 4} );
   if (p[0] != 5) $error("Unexpected value");
   if (p[1] != 6) $error("Unexpected value");
   if (p[2] != 7) $error("Unexpected value");
   if (p[3] != 8) $error("Unexpected value");
   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
