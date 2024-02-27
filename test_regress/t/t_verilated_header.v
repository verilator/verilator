// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`include "verilated.v"

module t (/*AUTOARG*/);

   initial begin
      `verilator_file_descriptor i;
      `coverage_block_off
      i = $fopen("/dev/null", "r");
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
