// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t(/*AUTOARG*/);

   bit a [5:0];
   bit b [5:0];

   initial begin
      a = '{1, 1, 1, 0, 0, 0};
      b = '{0, 0, 0, 1, 1, 1};
      $display(":assert: ('%b%b%b_%b%b%b' == '111_000')",
               a[5], a[4], a[3], a[2], a[1], a[0]);
      $display(":assert: ('%b%b%b_%b%b%b' == '000_111')",
               b[5], b[4], b[3], b[2], b[1], b[0]);

      if ((a[5:3] == b[2:0]) != 1'b1) $stop;
      if ((a[5:3] != b[2:0]) != 1'b0) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
