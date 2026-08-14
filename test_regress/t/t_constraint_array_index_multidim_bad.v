// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// A rand-dependent index into a non-rand multidimensional array can't be
// safely lowered (see t_constraint_array_index_nonrand.v for the supported
// 1-D case) -- this should be a clean compile-time error, not a solver crash.

class C;
  rand int id;
  bit used[4][4];
  constraint c { id inside {[0:3]}; !used[id][0]; }
endclass

module t;
  initial begin
    C obj;
    obj = new;
    if (obj.randomize() == 0) $stop;
  end
endmodule
