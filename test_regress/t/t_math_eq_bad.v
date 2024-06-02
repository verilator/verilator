// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/);

   logic [31:0] a;

   initial begin
      a = 1234;
      if (a ==? 1.0) $stop;  // Bad
   end

endmodule
