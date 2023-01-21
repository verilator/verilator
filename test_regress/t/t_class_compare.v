// DESCRIPTION: Verilator: Check == and != operations performed on class objects
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Ilya Barkov.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define check_comp(lhs, rhs, op, exp) if ((exp) != ((lhs) op (rhs))) begin $write("%%Error: %s:%0d: op comparison shall return 'b%x\n", `__FILE__, `__LINE__, (exp)); `stop; end
// Two checks because == and != may not be derived from each other
`define check_eq(lhs, rhs) `check_comp(lhs, rhs, ==, 1'b1) `check_comp(lhs, rhs, !=, 1'b0)
`define check_ne(lhs, rhs) `check_comp(lhs, rhs, ==, 1'b0) `check_comp(lhs, rhs, !=, 1'b1)

class Cls;
   int i;
endclass

module t;
   initial begin
      Cls a = new;
      Cls b = new;
      `check_ne(a, b)
      a = b;
      `check_eq(a, b)
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
