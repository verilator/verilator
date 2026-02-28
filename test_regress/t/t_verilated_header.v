// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2023 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

`include "verilated.v"

module t;

   initial begin
      `verilator_file_descriptor i;
      `coverage_block_off
      i = $fopen("/dev/null", "r");
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
