// DESCRIPTION: Verilator: Check == and != operations performed on queues
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2023 Ilya Barkov
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define check_comp(lhs, rhs, op, exp) if ((exp) != ((lhs) op (rhs))) begin $write("%%Error: %s:%0d: op comparison shall return 'b%x\n", `__FILE__, `__LINE__, (exp)); `stop; end
// Two checks because == and != may not be derived from each other
`define check_eq(lhs, rhs) `check_comp(lhs, rhs, ==, 1'b1) `check_comp(lhs, rhs, !=, 1'b0)
`define check_ne(lhs, rhs) `check_comp(lhs, rhs, ==, 1'b0) `check_comp(lhs, rhs, !=, 1'b1)
// verilog_format: on

class Cls;
  int i;
endclass

class Derived extends Cls;
endclass

module t;
  initial begin
    begin  // integers
      int q1[$];
      bit signed [31:0] q2[$];
      q1.push_back(1);
      q2.push_back(1);
      q1.push_back(-2);
      q2.push_back(-2);
      `check_eq(q1, q2)

      q2.push_back(3);
      `check_ne(q1, q2)
    end
    begin  // queue bounds do not affect equality
      int small_q[$:1];
      int large_q[$:3];
      int unbounded_q[$];
      `check_eq(small_q, large_q)
      small_q.push_back(3);
      large_q.push_back(3);
      unbounded_q.push_back(3);
      `check_eq(large_q, small_q)
      `check_eq(unbounded_q, small_q)
      `check_eq(small_q, unbounded_q)
      large_q[0] = 4;
      `check_ne(small_q, large_q)
      unbounded_q.push_back(2);
      `check_ne(unbounded_q, small_q)
    end
    begin  // queues with different inner bounds
      typedef int small_t[$:1];
      typedef int large_t[$:3];
      small_t lhs[$];
      large_t rhs[$];
      small_t small_q;
      large_t large_q;
      small_q.push_back(7);
      large_q.push_back(7);
      lhs.push_back(small_q);
      rhs.push_back(large_q);
      `check_eq(lhs, rhs)
      rhs[0].push_back(9);
      `check_ne(lhs, rhs)
    end
    begin  // strings
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

    begin  // classes
      automatic Cls a = new;
      automatic Cls b = new;
      Cls q1[$];
      Cls q2[$];
      q1.push_back(a);
      q2.push_back(b);
      `check_ne(q1, q2)

      q1.push_back(b);
      q2.push_front(a);
      `check_eq(q1, q2)
    end

    begin  // base and derived queues holding the same handle
      automatic Derived h = new;
      Cls bases[$];
      Cls bounded[$:1];
      Derived derived_q[$];
      bases.push_back(h);
      derived_q.push_back(h);
      `check_eq(bases, derived_q)
      bounded.push_back(h);
      `check_eq(bounded, derived_q)
      bounded.push_back(h);
      derived_q.push_back(h);
      derived_q.push_back(h);
      `check_ne(bounded, derived_q)
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
