// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

class C;
  rand int x;
  rand int y;
endclass

class B;
  rand C c;
  function new();
    c = new();
  endfunction
endclass

class A;
  rand B b;
  constraint c_foo {b.c.x == 123;}
  function new();
    b = new();
  endfunction
endclass

module t_constraint_global_subobj_standalone;
  B b;
  int px, py;
  bit xvar, yvar;

  initial begin
    // Issue #7833: a standalone randomize() of B must randomize the nested
    // sub-object fields c.x and c.y.  Class A holds a global constraint that
    // references type C through b.c.x, which used to flag C's fields as solved
    // and skip them in B's basic randomization even though A is never
    // randomized here.
    b = new();
    if (b.randomize() != 1) $stop;
    px = b.c.x;
    py = b.c.y;
    xvar = 0;
    yvar = 0;
    for (int i = 0; i < 20; i++) begin
      if (b.randomize() != 1) $stop;
      if (b.c.x != px) xvar = 1;
      if (b.c.y != py) yvar = 1;
      px = b.c.x;
      py = b.c.y;
    end
    if (!xvar) begin
      $display("ERROR: b.c.x not randomized (stuck)");
      $stop;
    end
    if (!yvar) begin
      $display("ERROR: b.c.y not randomized (stuck)");
      $stop;
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
