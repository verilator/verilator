// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Array real == has no type check of its own. The scalar case in
// t_constraint_unsup.v does, and diagnoses cleanly instead of crashing.
class C1;
  rand real frame[2];
  real target[2];
  constraint c { frame == target; }
  function new();
    target[0] = 1.5;
    target[1] = 2.5;
  endfunction
endclass

class C2;
  rand real frame[2];
  real target[2];
  constraint c { frame != target; }
  function new();
    target[0] = 1.5;
    target[1] = 2.5;
  endfunction
endclass

module t;
  initial begin
    C1 obj1;
    C2 obj2;
    obj1 = new;
    obj2 = new;
    if (obj1.randomize() == 0) $stop;
    if (obj2.randomize() == 0) $stop;
  end
endmodule
