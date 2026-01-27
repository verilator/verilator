// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2020 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;
   initial begin
      // Check error when this missing: $dumpfile("/should/not/be/opened");
      $dumpvars;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
