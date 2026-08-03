// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 BRDR LIFE
// SPDX-License-Identifier: CC0-1.0

// 'disable soft' names one variable and must reach exactly the soft constraints
// that reference it (IEEE 1800-2023 18.5.14.2).
//
// Matching on the text of the lowered constraint instead of on variable names
// is not good enough: hex literals in the solver text spell every value with an
// 'x', and one variable's name can be a prefix of another's.

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// 'disable soft x' must not touch the soft on foo, whose value shows up in the
// solver text as a hex literal that itself contains an 'x'.
class OtherVariable;
  rand int foo;
  rand int x;
  constraint c_soft { soft foo == 5; }
  constraint c_disable { disable soft x; }
endclass

// 'disable soft a' must not touch the soft on ab, whose name merely starts with
// the named variable.
class NamePrefix;
  rand bit [7:0] a;
  rand bit [7:0] ab;
  constraint c_soft_ab { soft ab == 8'd7; }
  constraint c_soft_a { soft a == 8'd3; }
  constraint c_disable { disable soft a; }
endclass

// A soft constraint mentioning several variables goes when any one of them is
// named, whether or not it is the only random variable in the constraint.
class MultiVariable;
  rand bit [7:0] p;
  rand bit [7:0] q;
  constraint c_soft { soft p + q == 8'd200; }
  constraint c_disable { disable soft q; }
endclass

// Ordering: 'disable soft' discards the soft constraints declared before it, and
// leaves a later, higher priority one in force.
class DeclarationOrder;
  rand bit [7:0] x;
  constraint c_early { soft x == 8'd5; }
  constraint c_disable { disable soft x; }
  constraint c_late { soft x == 8'd9; }
endclass

class Holder;
  rand bit [7:0] y;
endclass

// A member select names one object's member, not every object's.
class MemberScope;
  rand Holder h1;
  rand Holder h2;
  constraint c_soft { soft h1.y == 8'd4; soft h2.y == 8'd6; }
  constraint c_disable { disable soft h1.y; }
  function new();
    h1 = new;
    h2 = new;
  endfunction
endclass

module t;
  initial begin
    OtherVariable o1;
    NamePrefix o2;
    MultiVariable o3;
    DeclarationOrder o4;
    MemberScope o5;
    int free_a, free_p, free_h1;
    o1 = new;
    o2 = new;
    o3 = new;
    o4 = new;
    o5 = new;

    repeat (50) begin
      `checkd(o1.randomize(), 1)
      `checkd(o1.foo, 5)

      `checkd(o2.randomize(), 1)
      `checkd(o2.ab, 8'd7)
      if (o2.a != 8'd3) free_a++;

      `checkd(o3.randomize(), 1)
      if ((o3.p + o3.q) != 8'd200) free_p++;

      // The later soft outranks the disable that precedes it.
      `checkd(o4.randomize(), 1)
      `checkd(o4.x, 8'd9)

      `checkd(o5.randomize(), 1)
      `checkd(o5.h2.y, 8'd6)
      if (o5.h1.y != 8'd4) free_h1++;
    end

    `checkd(free_a > 0, 1)
    `checkd(free_p > 0, 1)
    `checkd(free_h1 > 0, 1)

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
