// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   int a = 0;

   function int f(output int a);
       a = 1;
       return a;
   endfunction

   assert property (@(posedge clk) f(a) >= 0);
endmodule
