// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

module t (input clk);
   wire a, b;
   // Input port is needed to omit optimizations
   // based on its value. To keep test simple,
   // let's imitate change of value by just swapping the values of COND
   assign a = 'z === (clk ? 1'b1 : 1'bz);
   assign b = 'z === (clk ? 1'bz : 1'b1);

   always begin
      if (a && !b) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
      else begin
         $write("Error: a = %b, b = %b, ", a, b);
         $write("expected: a = 1, b = 0\n");
         $stop;
      end
   end
endmodule
