// DESCRIPTION: Verilator: Verilog Test module
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t(y);
   output [3:0] y;
   // bug775
   // verilator lint_off WIDTH
   assign y = ((0/0) ? 1 : 2) % 0;

   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
