// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

module t;
   logic x;
   sub s(x);
   initial #1 x = 1;
endmodule

module sub(input x);
   initial fork begin
      @x;
      $write("*-* All Finished *-*\n");
      $finish;
   end join_any
endmodule
