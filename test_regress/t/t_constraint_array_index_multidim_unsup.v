// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// A rand-dependent index into a multidimensional array (C1), chained
// through another rand-dependent index (C2), or into a fixed array of
// queues/dynamic/associative arrays (C3/C4/C5) is a compile-time error,
// not a solver crash -- see t_constraint_array_index_nonrand.v for the
// 1-D case this is all otherwise support for.

class C1;
  rand int id;
  bit used[4][4];
  constraint c { id inside {[0:3]}; !used[id][0]; }
endclass

class C2;
  rand int id1;
  rand int id2;
  bit used[4][4];
  constraint c { id1 inside {[0:3]}; id2 inside {[0:3]}; !used[id1][id2]; }
endclass

class C3;
  rand int id;
  bit q[4][$];
  constraint c { id inside {[0:3]}; q[id] != q[id]; }
endclass

class C4;
  rand int id;
  bit d[4][];
  constraint c { id inside {[0:3]}; d[id] != d[id]; }
endclass

class C5;
  rand int id;
  bit a[4][string];
  constraint c { id inside {[0:3]}; a[id] != a[id]; }
endclass

module t;
  initial begin
    C1 obj1;
    C2 obj2;
    C3 obj3;
    C4 obj4;
    C5 obj5;
    obj1 = new;
    obj2 = new;
    obj3 = new;
    obj4 = new;
    obj5 = new;
    if (obj1.randomize() == 0) $stop;
    if (obj2.randomize() == 0) $stop;
    if (obj3.randomize() == 0) $stop;
    if (obj4.randomize() == 0) $stop;
    if (obj5.randomize() == 0) $stop;
  end
endmodule
