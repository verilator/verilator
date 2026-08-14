// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// A whole-array '=='/'!=' comparison in a constraint can't be expanded when
// the array shape contains a queue, dynamic, or associative array -- this
// should be a clean compile-time error, not a solver crash.

class C;
  rand bit frame[2][$];
  bit target[2][$];
  constraint c { frame == target; }
endclass

module t;
  initial begin
    C obj;
    obj = new;
    if (obj.randomize() == 0) $stop;
  end
endmodule
