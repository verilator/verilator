// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

int x = 0;

function int increment_x;
   x++;
   return x;
endfunction

module t(/*AUTOARG*/);

   initial begin
      fork
         increment_x();
         #1 disable increment_x;
      join
   end

endmodule
