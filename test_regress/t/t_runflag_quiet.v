// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2019 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

timeunit 1us;
timeprecision 1ns;

module t;
   initial begin
      #10;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
