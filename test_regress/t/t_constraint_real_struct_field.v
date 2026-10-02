// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Aditya Shevade
// SPDX-License-Identifier: CC0-1.0

// A non-real struct field constrained through a StructSel should work
// normally even though a sibling field in the same struct is real -- the
// real-value check must look at the selected field's own type, not the
// whole struct's type (see t_constraint_real_struct_eq_unsup.v for the
// whole-struct case, which is legitimately unsupported).
typedef struct {
  int a;
  real b;
} pair_t;

class C;
  rand pair_t s;
  constraint c1 { s.a == 5; }
endclass

module t;
  initial begin
    C obj;
    obj = new;
    if (obj.randomize() == 0) $stop;
    if (obj.s.a != 5) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
