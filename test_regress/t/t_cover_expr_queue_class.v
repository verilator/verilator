// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

class Class1;
   int value0 = 7;
endclass

module t;
   initial begin
      int i = 0;
      Class1 q[$];
      repeat(15) begin
         Class1 x = new;
         q = { q, x };
      end
      while (i < q.size()) begin
         if ((q[i].value0 > 8) || (q[i].value0 < 5)) $stop;
         i += 1;
      end
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
