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

class ExtendCls extends Cls;
endclass

module t;
   initial begin
      Cls a = new;
      Cls b = new;
      ExtendCls ext = new;
      `check_ne(a, b)
      `check_ne(a, ext)
      `check_ne(ext, a)
      a = b;
      `check_eq(a, b)
      a = ext;
      `check_eq(a, ext)
      `check_eq(ext, a)
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
