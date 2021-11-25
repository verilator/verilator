// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2021 by wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;
   parameter string ES = "";
   parameter EI = "";  // B is an integer of width 8
   parameter string OS = "O";
   parameter OI = "O";  // B is an integer of width 8

   initial begin
      $display(">< == >%s<", "");
      $display(">< == >%s<", ES);
      $display("> < == >%s<", EI);

      if ($bits("") != 0) $stop;
      if ($bits("A") != 8) $stop;
      if ($bits(ES) != 0) $stop;
      if ($bits(OS) != 8) $stop;
      if ($bits(OI) != 8) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
