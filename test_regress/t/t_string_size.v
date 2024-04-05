// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2021 by wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t(/*AUTOARG*/
   // Outputs
   outempty64
   );
   output [63:0] outempty64;

   parameter string OS = "O";
   parameter OI = "O";  // B is an integer of width 8

   // verilator lint_off WIDTH
   parameter string EMPTYS = "";
   parameter EMPTYI = "";  // B is an integer of width 8
   parameter bit [23:0] EMPTY24 = "";
   parameter bit [63:0] EMPTY64 = "";
   // verilator lint_on WIDTH
   parameter bit [31:0] NEST = "NEST";
   parameter bit [31:0] TEST = "TEST";
   string s;

   // verilator lint_off WIDTH
   assign outempty64 = "";
   // verilator lint_on WIDTH

   initial begin
      // IEEE: "Leading 0s are never printed" but that does not mean spaces are not
      $display(">%s< == >< (or > < also legal)", "\000");
      $display(">%s< == >< (or > < also legal)", "");
      $display(">%s< == >    <", 32'h0);

      // Numeric context, so IEEE 1800-2023 11.10.3 "" is a "\000"
      if ($bits("") != 8) $stop;
      if ("" != "\000") $stop;

      if ($bits("A") != 8) $stop;

      s = "";
      if (s.len != 0) $stop;

      // IEEE 1800-2023 6.16 "\000" assigned to string is ignored
      s = "\000yo\000";
      if (s.len != 2) $stop;
      if (s != "yo") $stop;

      if ($bits(EMPTYI) != 8) $stop;
      if (EMPTYI != "\000") $stop;
      // verilator lint_off WIDTH
      if (EMPTYI == "TEST") $stop;
      if (EMPTYI == TEST) $stop;
      // verilator lint_on WIDTH

      if ($bits(EMPTY24) != 24) $stop;
      if (EMPTY24 != 0) $stop;
      $display(">%s< == >   <", EMPTY24);

      if ($bits(EMPTY64) != 64) $stop;
      if (EMPTY64 != 0) $stop;
      $display(">%s< == >        <", EMPTY64);

      if ($bits(EMPTYS) != 0) $stop;
      if (EMPTYS == "TEST") $stop;  // Illegal in some simulators as not both strings
      if (EMPTYS == TEST) $stop;
      $display(">%s< == ><", EMPTYS);

      if ($bits(OS) != 8) $stop;
      if (OS != "O") $stop;
      if (OS == "TEST") $stop;  // Illegal in some simulators as not both strings
      if (OS == TEST) $stop;

      if ($bits(OI) != 8) $stop;
      if (OI != "O") $stop;

      // verilator lint_off WIDTH
      if (OI == "TEST") $stop;
      if (OI == TEST) $stop;
      // verilator lint_on WIDTH

      if ($bits(outempty64) != 64) $stop;
      if (outempty64 != 64'h00_00_00_00_00_00_00_00) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
