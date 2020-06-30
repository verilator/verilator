// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t(/*AUTOARG*/);

   int value;

   initial begin
      wait (value == 1);
      if (value != 1) $stop;
      wait (0);
      if (value != 1) $stop;
      //
      wait (value == 2);
      if (value != 2) $stop;
      //
      wait (value == 3) if (value != 3) $stop;
      if (value != 3) $stop;
   end

   initial begin
      #10;
      value = 1;
      #10;
      value = 2;
      #10;
      value = 3;
      #10;
      value = 4;
      #10;
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
