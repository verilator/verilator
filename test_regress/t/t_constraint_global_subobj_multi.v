// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

class C;
  rand int x;
endclass

class M;
  rand C c1;
  rand C c2;
  constraint c {
    c1.x == 11;
    c2.x == 22;
  }
  function new();
    c1 = new();
    c2 = new();
  endfunction
endclass

module t_constraint_global_subobj_multi;
  C s;
  M m;
  int p;
  bit vary;

  initial begin
    // Type C is randomized standalone AND used as two distinct sub-objects of M,
    // each pinned by a global constraint.  The two sub-objects share the same
    // underlying rand variable, so each must keep its own write_var (issue #7833
    // family).
    s = new();
    if (s.randomize() != 1) $stop;
    p = s.x;
    vary = 0;
    for (int i = 0; i < 20; i++) begin
      if (s.randomize() != 1) $stop;
      if (s.x != p) vary = 1;
      p = s.x;
    end
    if (!vary) begin
      $display("ERROR: standalone C.x not randomized (stuck)");
      $stop;
    end

    m = new();
    if (m.randomize() != 1) $stop;
    if (m.c1.x != 11) begin
      $display("ERROR: m.c1.x should be 11, got %0d", m.c1.x);
      $stop;
    end
    if (m.c2.x != 22) begin
      $display("ERROR: m.c2.x should be 22, got %0d", m.c2.x);
      $stop;
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
