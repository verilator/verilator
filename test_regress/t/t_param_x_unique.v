// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2024 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module sub #(parameter P = 1'bx);
   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule

module t;
   sub sub();
endmodule
