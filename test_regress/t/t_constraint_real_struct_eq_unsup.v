// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Aditya Shevade
// SPDX-License-Identifier: CC0-1.0

// Whole-struct == has no type check of its own, the same gap
// t_constraint_real_array_eq_unsup.v closes for whole-array ==: without
// this, `s == target` where the struct has a real field compiles clean
// and silently returns 0 for the real field instead of the constrained
// value, since the real-value check only looked at the struct variable's
// own dtype, never at whether a member nested inside it was real.
typedef struct {
  real r;
} coord_t;

class C;
  rand coord_t s;
  coord_t target;
  constraint c { s == target; }
  function new();
    target.r = 1.5;
  endfunction
endclass

module t;
  initial begin
    C obj;
    obj = new;
    if (obj.randomize() == 0) $stop;
  end
endmodule
