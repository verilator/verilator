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

   parameter bit [31:0] NEST = "NEST";
   parameter bit [31:0] TEST = "TEST";
   bit [31:0] rest;
   string s;

   initial begin
      $display(">< == >%s<", "");
      $display(">< == >%s<", ES);
      $display("> < == >%s<", EI);

      if ($bits("") != 0) $stop;
      if ($bits("A") != 8) $stop;
      if ($bits(ES) != 0) $stop;
      if ($bits(EI) != 8) $stop;
      if ($bits(OS) != 8) $stop;
      if ($bits(OI) != 8) $stop;

      if (ES == "TEST") $stop;  // Illegal in some simulators as not both strings
      if (EI == "TEST") $stop;
      if (OS == "TEST") $stop;  // Illegal in some simulators as not both strings
      // verilator lint_off WIDTH
      if (OI == "TEST") $stop;
      if (rest == "TEST") $stop;

      if (ES == TEST) $stop;
      if (EI == TEST) $stop;
      if (OS == TEST) $stop;
      if (OI == TEST) $stop;
      if (rest == TEST) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
