// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2020 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

`define STRINGIFY(x) `"x`"

module t;
   int sig;
   initial begin
      sig = 10;
      $dumpfile(`STRINGIFY(`TEST_DUMPFILE));
      $dumpvars();
      #20;
      sig = 20;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
