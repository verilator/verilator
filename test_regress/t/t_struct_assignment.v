// DESCRIPTION: Verilator: Verilog Test module for specialized type default values
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2021 by Andrej Korman.
// SPDX-License-Identifier: CC0-1.0

/* verilator lint_off UNPACKED */

module t;
   typedef struct packed {
      bit       a;
      bit       b;
      bit       c;
      bit       d;
   } helper_type1;
   typedef struct packed {
      bit       a;
      int       b;
   } helper_type2;

   const helper_type1 ex1 = '{default: 1'b0, bit: 1'b1};
   const helper_type1 ex2 = '{bit: 1'b1, bit: 1'b0};
   const helper_type2 ex3 = '{default: 1'b1, int: 20};
   const helper_type2 ex4 = '{bit: 1'b1, int: 20};
   const helper_type1 ex5 = '{a: 1'b1, b: 1'b0, bit: 1'b1};

   initial begin
      if (ex1 != 4'b1111) $stop;
      if (ex2 != 4'b1111) $stop;
      if (ex3.b != 20) $stop;
      if (ex4.a != 1'b1 || ex4.b != 20) $stop;
      if (ex5 != 4'b1011) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
