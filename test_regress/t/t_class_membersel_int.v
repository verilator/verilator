// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2023 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

class Cls;
   int t;
endclass

module Sub;
   Cls c;
   initial begin
      int i;
      c = new;
      i = c.t;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule

module t;
   Sub foo();
endmodule
