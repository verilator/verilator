// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Geza Lore.
// SPDX-License-Identifier: CC0-1.0

`define show(x) $display("oarray[%2d] is %2d", x, oarray[x])

module t (/*AUTOARG*/);

   int iarray [63:0];
   int oarray [63:0];

   initial begin
      for (int i = 0; i < 64 ; i = i + 1) begin
        iarray[i] = i;
        oarray[i] = 0;
      end

      for (int i = 0; i < 63; i = i + 1) begin
        oarray[i] = iarray[i + 1];
      end

      $display("shift down 1");
      `show(63);
      `show(62);
      `show(61);
      `show(32);
      `show(2);
      `show(1);
      `show(0);

      for (int i = 63; i >= 2 ; i = i - 1) begin
        oarray[i] = iarray[i - 2];
      end

      $display("shift up 2");
      `show(63);
      `show(62);
      `show(61);
      `show(32);
      `show(2);
      `show(1);
      `show(0);

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
