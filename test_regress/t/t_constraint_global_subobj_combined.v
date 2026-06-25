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

module t_constraint_global_subobj_combined;
  B b;
  A a;
  int px, py;
  bit xvar, yvar;

  initial begin
    // Same compilation randomizes BOTH the sub-object holder B standalone AND the
    // global-constraint owner A.  A leaf (C::x) is therefore solver-owned for A
    // but must be freely randomized for B; both have to work at once (issue
    // #7833).
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
      $display("ERROR: standalone b.c.x not randomized (stuck)");
      $stop;
    end
    if (!yvar) begin
      $display("ERROR: standalone b.c.y not randomized (stuck)");
      $stop;
    end

    a = new();
    if (a.randomize() != 1) $stop;
    py = a.b.c.y;
    yvar = 0;
    for (int i = 0; i < 20; i++) begin
      if (a.randomize() != 1) $stop;
      if (a.b.c.x != 123) begin
        $display("ERROR: global constraint b.c.x == 123 not applied, got %0d", a.b.c.x);
        $stop;
      end
      if (a.b.c.y != py) yvar = 1;
      py = a.b.c.y;
    end
    if (!yvar) begin
      $display("ERROR: a.b.c.y not randomized (stuck)");
      $stop;
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
