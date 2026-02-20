// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2023 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;

   let RECURSE(a) = (a == 1) ? 1 : RECURSE(a - 1);  // BAD no recursion per IEEE 1800-2023 11.12

   initial begin
      if (RECURSE(1) != 1) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
