// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2020 engr248
// SPDX-License-Identifier: CC0-1.0

module t;
   initial begin
      $write("[%0t] Hello\n", $time);  // Check timestamp works
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
