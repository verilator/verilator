// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`include "verilated.v"

`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); $stop; end while(0);

module t;

   integer f;
   integer i;
   integer j;

   initial begin
      f = $fopen("/does-not-exist", "r");
      `checkd(f, 0);
      i = $fscanf(f, "check %d", j);
      `checkd(i, -1);
      i = $fgetc(f);
      `checkd(i, -1);
      i = $ftell(f);
      `checkd(i, -1);
      i = $rewind(f);
      `checkd(i, -1);
      i = $fseek(f, 0, 0);
      `checkd(i, -1);

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
