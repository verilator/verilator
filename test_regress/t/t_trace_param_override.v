// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2022 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

`define STRINGIFY(x) `"x`"

module t #(
           parameter int POVERRODE = 16,
           parameter int PORIG = 16
           );

   initial begin
      $dumpfile(`STRINGIFY(`TEST_DUMPFILE));
      $dumpvars;

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
