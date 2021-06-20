// DESCRIPTION: Verilator: Verilog Test module
//
// Use this file as a template for submitting bugs, etc.
// This module takes a single clock input, and should either
//      $write("*-* All Finished *-*\n");
//      $finish;
// on success, or $stop.
//
// The code as shown applies a random vector to the Test
// module, then calculates a CRC on the Test module's outputs.
//
// **If you do not wish for your code to be released to the public
// please note it here, otherwise:**
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2021 by ____YOUR_NAME_HERE____.
// SPDX-License-Identifier: CC0-1.0

/* verilator lint_off UNPACKED */

module t;
   typedef struct packed { // [3:0]
      bit       b3;
      bit       b2;
      bit       b1;
      bit       b0;
   } b4_t;
   typedef struct packed {
      bit x;
      b4_t y;
   } type1;
      typedef struct {
      int a;
      real b;
      int c;
      int d;
   } type2;

   const b4_t helper = '{1'b1, 1'b1, 1'b0, 1'b1};
   const type1 ex1 = '{x: 1'b1, y: helper};

   initial begin
      if (ex1 != 5'b11101) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
