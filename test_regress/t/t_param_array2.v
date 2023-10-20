// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2017 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;
   localparam logic [3:0] val_0 = 0;
   localparam int val_1 = $bits(val_0);
   localparam int c[4]  = '{ val_1 + 1, val_1 + 2, val_1 + 3, val_1 * 2};
   a #(.p(c)) i_a ();
   a #(.p('{ val_1 + 1, val_1 + 2, val_1 + 3, val_1 * 2})) i_b ();
endmodule

module a
  #( parameter int p[4] = '{1, 2, 3, 4} );
   initial begin
      if (p[0] != 5) $stop;
      if (p[1] != 6) $stop;
      if (p[2] != 7) $stop;
      if (p[3] != 8) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
