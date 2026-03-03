// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;

   logic [15:0] foo [8];

   initial begin
      if (foo[1] != foo[1]) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
