// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

class A;
endclass

module t (/*AUTOARG*/);

   initial begin
      A a1 = new;
      A a2 = new;
      if (a1 ==? a2) $stop;
      if (!a1 !=? a2) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
