// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

function static int func();
   int cnt = 0;
   return ++cnt;
endfunction

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   int   a;
   initial begin
      a = func;
      $stop;
   end

endmodule
