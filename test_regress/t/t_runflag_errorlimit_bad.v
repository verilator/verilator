// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2019 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;
   initial begin
      $error("One");
      $error("Two");
      $error("Three");
      $error("Four");
      $error("Five");
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
