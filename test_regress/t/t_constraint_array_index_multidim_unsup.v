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

// The array operand isn't a variable or member at all (a function call),
// so its root can't be resolved -- a distinct diagnostic from the other
// classes above, which all resolve to a confirmed non-rand array.
typedef bit [7:0] arr4_t[4];
class C7;
  rand int id;
  arr4_t a;
  function arr4_t get_a();
    return a;
  endfunction
  constraint c { id inside {[0:3]}; get_a()[id] == 8'hAA; }
endclass

// A fixed 1-D array whose element is a class handle, not a scalar or a
// struct: the same reason C6's struct element fails applies here too.
class Elem;
  rand bit [7:0] v;
endclass
class C8;
  rand int id;
  Elem pool[4];
  constraint c { id inside {[0:3]}; pool[id].v == 8'hAA; }
endclass

// Same shape as C7, but 'a' is itself rand: confirms the diagnostic fires
// regardless of the unresolvable root's rand-ness, rather than silently
// selecting from the function call expression instead of the array.
class C9;
  rand int id;
  rand arr4_t a;
  function arr4_t get_a();
    return a;
  endfunction
  constraint c { id inside {[0:3]}; get_a()[id] == 8'hAA; }
endclass

// A rand index on the way to the indexed non-rand array, through a fixed
// array or a queue of handles.
class Holder;
  bit used[2];
endclass
class C10;
  rand int h;
  rand int id;
  Holder hs[2];
  constraint c { h inside {[0:1]}; id inside {[0:1]}; hs[h].used[id] == 1; }
endclass

class C11;
  rand int h;
  rand int id;
  Holder hs[$];
  constraint c { h inside {[0:1]}; id inside {[0:1]}; hs[h].used[id] == 1; }
endclass

// A fixed 1-D non-rand array reached through a dynamic, queue, or
// associative outer array.
class C12;
  rand int id;
  bit [7:0] d[][2];
  constraint c { id inside {[0:1]}; d[0][id] == 8'hAA; }
endclass

class C13;
  rand int id;
  bit [7:0] q[$][2];
  constraint c { id inside {[0:1]}; q[0][id] == 8'hAA; }
endclass

class C14;
  rand int id;
  bit [7:0] a[int][2];
  constraint c { id inside {[0:1]}; a[0][id] == 8'hAA; }
endclass

module t;
  initial begin
    C1 obj1;
    C2 obj2;
    C3 obj3;
    C4 obj4;
    C5 obj5;
    C6 obj6;
    C7 obj7;
    C8 obj8;
    C9 obj9;
    C10 obj10;
    C11 obj11;
    C12 obj12;
    C13 obj13;
    C14 obj14;
    obj1 = new;
    obj2 = new;
    obj3 = new;
    obj4 = new;
    obj5 = new;
    obj6 = new;
    obj7 = new;
    obj8 = new;
    obj9 = new;
    obj10 = new;
    obj11 = new;
    obj12 = new;
    obj13 = new;
    obj14 = new;
    if (obj1.randomize() == 0) $stop;
    if (obj2.randomize() == 0) $stop;
    if (obj3.randomize() == 0) $stop;
    if (obj4.randomize() == 0) $stop;
    if (obj5.randomize() == 0) $stop;
    if (obj6.randomize() == 0) $stop;
    if (obj7.randomize() == 0) $stop;
    if (obj8.randomize() == 0) $stop;
    if (obj9.randomize() == 0) $stop;
    if (obj10.randomize() == 0) $stop;
    if (obj11.randomize() == 0) $stop;
    if (obj12.randomize() == 0) $stop;
    if (obj13.randomize() == 0) $stop;
    if (obj14.randomize() == 0) $stop;
  end
endmodule
