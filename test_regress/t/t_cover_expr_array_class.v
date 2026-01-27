// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2025 Antmicro
// SPDX-License-Identifier: CC0-1.0

class Class1;
   int value0 = 7;
endclass

module t;
   initial begin
      int i = 0;
      Class1 q[15];
      for (int j = 0; j < 15; j = j + 1) begin
         Class1 x = new;
         q[j] = x;
      end
      while (i < 15) begin
         if ((q[i].value0 > 8) || (q[i].value0 < 5)) $stop;
         i += 1;
      end
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
