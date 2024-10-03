// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define STRINGIFY(x) `"x`"

module t;
   wire a = 0;
   initial begin
      $dumpfile(`STRINGIFY(`TEST_DUMPFILE));
      $dumpvars;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule

module another_top;
   wire b = 0;
endmodule
