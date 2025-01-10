// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

typedef enum bit [4:0] {V0 = 1} my_enum;
class Cls;
  my_enum sp = V0;
endclass

module t (/*AUTOARG*/);
   initial begin
      Cls c = new;
      int i = 0;
      if (i inside {c.sp}) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
