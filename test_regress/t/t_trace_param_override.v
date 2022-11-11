// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define STRINGIFY(x) `"x`"

module t #(
           parameter int POVERRODE = 16,
           parameter int PORIG = 16
           ) (/*AUTOARG*/);

   initial begin
      $dumpfile({`STRINGIFY(`TEST_OBJ_DIR),"/simx.vcd"});
      $dumpvars;

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
