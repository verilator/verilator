// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// A whole-array '=='/'!=' comparison the solver can't expand (queue,
// dynamic, associative, or wildcard associative array) is a compile-time
// error, not a solver crash.

class C1;
  rand bit frame[2][$];
  bit target[2][$];
  constraint c { frame == target; }
endclass

class C2;
  rand bit frame[2][];
  bit target[2][];
  constraint c { frame == target; }
endclass

class C3;
  rand bit frame[2][string];
  bit target[2][string];
  constraint c { frame == target; }
endclass

class C4;
  rand bit frame[2][*];
  bit target[2][*];
  constraint c { frame == target; }
endclass

// A comparison operand that isn't a variable, member, or constant-indexed
// slice (here, a function call) can't be cloned per array element either.
typedef bit arr2d_t[2][2];
class C5;
  rand arr2d_t frame;
  arr2d_t target;
  function arr2d_t get_target();
    return target;
  endfunction
  constraint c { frame == get_target(); }
endclass

// Same, but the unsupported operand is on the left instead of the right.
class C6;
  rand arr2d_t frame;
  arr2d_t target;
  function arr2d_t get_target();
    return target;
  endfunction
  constraint c { get_target() == frame; }
endclass

module t;
  initial begin
    C1 obj1;
    C2 obj2;
    C3 obj3;
    C4 obj4;
    C5 obj5;
    C6 obj6;
    obj1 = new;
    obj2 = new;
    obj3 = new;
    obj4 = new;
    obj5 = new;
    obj6 = new;
    if (obj1.randomize() == 0) $stop;
    if (obj2.randomize() == 0) $stop;
    if (obj3.randomize() == 0) $stop;
    if (obj4.randomize() == 0) $stop;
    if (obj5.randomize() == 0) $stop;
    if (obj6.randomize() == 0) $stop;
  end
endmodule
