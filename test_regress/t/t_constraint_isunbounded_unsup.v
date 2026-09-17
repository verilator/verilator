// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Aditya Shevade
// SPDX-License-Identifier: CC0-1.0

// $isunbounded() on a plain variable always folds to false; this is fatal
// by default (CONSTRAINTIGN), see t_constraint_isunbounded.v for the
// suppressed, successfully-compiling case.
class C;
  rand int x;
  constraint c { !$isunbounded(x); }
endclass

module t;
  initial begin
    C obj;
    obj = new;
    if (obj.randomize() == 0) $stop;
  end
endmodule
