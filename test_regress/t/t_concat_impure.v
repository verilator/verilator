// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

int global_variable = 0;

function int side_effect;
   global_variable++;
  return 1;
endfunction

module t (/*AUTOARG*/);
   reg [15:0] x;
   reg [15:0] y;
   initial begin
      {x, y} = side_effect() + 2;

      if (y != 3) $stop;
      if (x != 0) $stop;
      if (global_variable != 1) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
