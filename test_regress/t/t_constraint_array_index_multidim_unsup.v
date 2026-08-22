// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Rand-dependent indices into array shapes the solver can't expand
// (multidim, chained, queue/dynamic/assoc) are a compile-time error.

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

// A fixed 1-D array is otherwise an expandable shape, but a struct element
// can't be formatted as an SMT hex literal the way a plain bit vector can.
typedef struct {
  bit [3:0] tag;
} entry_t;
class C6;
  rand int id;
  entry_t pool[4];
  constraint c { id inside {[0:3]}; pool[id].tag == 4'hA; }
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
