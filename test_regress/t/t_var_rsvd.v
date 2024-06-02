// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2005 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// verilator lint_off SYMRSVDWORD

module t (/*AUTOARG*/
   // Inputs
   bool
   );

   input bool;  // BAD

   reg  vector; // OK, as not public
   reg  switch /*verilator public*/;    // Bad

   typedef struct packed {
      logic [31:0] vector;      // OK, as not public
   } test;
   test t;

   // global is a 1800-2009 reserved word, but we allow it when possible.
   reg  global;

   initial begin
      t.vector = 1;
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
