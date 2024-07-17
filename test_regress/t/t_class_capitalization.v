// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test different uppercase/lowercase capitalization cases
class ClsMixed;
   int m;
   int M;
endclass

class Clsmixed;
   int m;
   int M;
endclass

module ModMixed;
   // verilator no_inline_module
   int m;
   int M;
endmodule

module Modmixed;
   // verilator no_inline_module
   int m;
   int M;
endmodule

module t(/*AUTOARG*/);
   // verilator no_inline_module

   ModMixed modMixed();
   Modmixed modmixed();

   initial begin
      ClsMixed clsMixed;
      Clsmixed clsmixed;

      clsMixed = new;
      clsMixed.m = 1;
      clsMixed.M = 2;
      clsmixed = new;
      clsmixed.m = 3;
      clsmixed.M = 4;
      if (clsMixed.m != 1) $stop;
      if (clsMixed.M != 2) $stop;
      if (clsmixed.m != 3) $stop;
      if (clsmixed.M != 4) $stop;

      modMixed.m = 1;
      modMixed.M = 2;
      modmixed.m = 3;
      modmixed.M = 4;
      if (modMixed.m != 1) $stop;
      if (modMixed.M != 2) $stop;
      if (modmixed.m != 3) $stop;
      if (modmixed.M != 4) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
