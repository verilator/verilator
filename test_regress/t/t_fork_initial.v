// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t();
  initial fork
     reg i;
     i = 1'b1;
     if (i != 1'b1) $stop;
     $write("*-* All Finished *-*\n");
     $finish;
  join
endmodule
