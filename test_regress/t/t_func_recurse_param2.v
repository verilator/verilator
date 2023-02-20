// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
          clk);
   parameter int X = 15;

   input clk;

   function int get_1();
      if (X == 15)
        return 1;
      else
        return get_1();
   endfunction

   int         out;
   mod#(1, 1) mod_i(out);

   always @(posedge clk) begin
      if (get_1() != 1 || out != 1) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule

module mod#(int A = 1, int B = 2) (output int out);
   function int get_1();
      if (A == B)
        return 1;
      else
        return get_1();
   endfunction

   initial out = get_1();
endmodule
