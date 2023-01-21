// DESCRIPTION: Verilator: Check == and != operations performed on queues
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
      begin // integers
         int q1[$];
         bit[31:0] q2[$];
         q1.push_back(1);
         q2.push_back(1);
         q1.push_back(-2);
         q2.push_back(-2);
         `check_eq(q1, q2)

         q2.push_back(3);
         `check_ne(q1, q2)
      end
      begin // strings
         string q1[$];
         string q2[$];
         q1.push_back("one");
         q2.push_back("one");
         q1.push_back("two");
         q2.push_back("two");
         `check_eq(q1, q2)

         q2.push_back("three");
         `check_ne(q1, q2)
      end

      begin // classes
         Cls a = new;
         Cls b = new;
         Cls q1[$];
         Cls q2[$];
         q1.push_back(a);
         q2.push_back(b);
         `check_ne(q1, q2)

         q1.push_back(b);
         q2.push_front(a);
         `check_eq(q1, q2)
      end

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
