// DESCRIPTION: Verilator: Check == and != operations performed on associative arrays
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
      begin // simple case
         int assoc1[int];
         int assoc2[int];
         // Empty are equal
         `check_eq(assoc1, assoc2)
         // Make different
         assoc1[10] = 15;
         assoc2[-1] = 365;
         `check_ne(assoc1, assoc2)
         // Make same
         assoc1[-1] = 365;
         assoc2[10] = 15;
         `check_eq(assoc1, assoc2)
         // Don't actually change
         assoc1[-1] = 365;
         `check_eq(assoc1, assoc2)
         // Compare different sizes
         assoc1[3] = 0;
         `check_ne(assoc1, assoc2)
      end
      begin // check that a class as key is fine
         int assoc1[Cls];
         int assoc2[Cls];
         Cls a = new;
         Cls b = new;
         int t;
         assoc1[a] = 0;
         `check_ne(assoc1, assoc2)
         assoc2[a] = 0;
         `check_eq(assoc1, assoc2)
         assoc2.delete(a);
         assoc2[b] = 0;
         `check_ne(assoc1, assoc2)
      end
      begin // check that a class as value is fine
         Cls assoc1[int];
         Cls assoc2[int];
         Cls a = new;
         Cls b = new;
         assoc1[1] = a;
         assoc2[1] = b;
         `check_ne(assoc1, assoc2)
         assoc2[1] = a;
         `check_eq(assoc1, assoc2)
      end
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
