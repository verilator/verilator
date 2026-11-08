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

// Same as C1, but with the queue as the outermost dimension.
class C7;
  rand bit frame[$][2];
  bit target[$][2];
  constraint c { frame == target; }
endclass

// A hierarchical (module-scope) reference operand: unlike a plain variable
// or member, a hierarchical reference is a transient node the elementwise
// expansion can't safely clone once per array element.
class C9;
  rand bit [7:0] frame[2][2];
  constraint c { frame == t.hier_target; }
endclass

// Same as C9, but the hierarchical reference is sliced to one element
// instead of compared whole -- the clone-safety walk has to recurse past
// the index and still land on the same unresolvable base.
class C9b;
  rand bit [7:0] frame[2];
  constraint c { frame == t.hier_target[0]; }
endclass

// A member-select whose handle is a function call, not a plain variable:
// unlike a hierarchical reference, this doesn't crash, but the function
// would run once per array element instead of once if allowed through.
class Holder10;
  bit [7:0] target[2][2];
endclass
class C10;
  rand bit [7:0] frame[2][2];
  Holder10 h;
  function Holder10 get_holder();
    return h;
  endfunction
  constraint c { frame == get_holder().target; }
  function new();
    h = new;
  endfunction
endclass

// Same, but the unsafe-to-clone operand is on the left instead of the right.
class C10b;
  rand bit [7:0] frame[2][2];
  Holder10 h;
  function Holder10 get_holder();
    return h;
  endfunction
  constraint c { get_holder().target == frame; }
  function new();
    h = new;
  endfunction
endclass

// Same fields as t_constraint_array_neq_nonrand.v's frame_bothrand_randidx,
// but only idx is rand, not cube: buildElementwiseEqp can only evaluate a
// non-rand operand once, at constraint-setup time, using the index's
// pre-solve value -- the solver may later choose a different index, so
// this can't be expanded correctly and must be rejected instead of
// silently selecting the wrong row.
class C11;
  rand int idx;
  bit [7:0] cube[4][2];
  rand bit [7:0] probe[2];
  constraint ci { idx inside {[0:3]}; }
  constraint c { probe == cube[idx]; }
endclass

// Same as C11, but with the operands swapped -- the rand-indexed, non-rand
// operand lands on the left instead of the right.
class C11b;
  rand int idx;
  bit [7:0] cube[4][2];
  rand bit [7:0] probe[2];
  constraint ci { idx inside {[0:3]}; }
  constraint c { cube[idx] == probe; }
endclass

// Same underlying problem reached through a member select instead of
// landing directly on the array: the handle array isn't rand, so its
// elements are ordinary non-rand state, but the member itself is rand --
// the rand index still means which element's member gets compared can't be
// pinned down before the solve runs.
class Inner11;
  rand bit [7:0] target[2];
endclass
class C12;
  rand int idx;
  Inner11 h[2];
  rand bit [7:0] probe[2];
  constraint ci { idx inside {[0:1]}; }
  constraint c { probe == h[idx].target; }
  function new();
    h[0] = new;
    h[1] = new;
  endfunction
endclass

// The rand index is on the outer dimension, not the one nearest the array
// comparison operand -- the search for a rand-dependent index has to keep
// walking inward past a non-rand index to find it.
class C13;
  rand int i;
  int j;
  bit [7:0] nra[2][2][2];
  rand bit [7:0] probe[2];
  constraint ci { i inside {[0:1]}; }
  constraint c { probe == nra[i][j]; }
  function new();
    j = 0;
  endfunction
endclass

// An impure (side-effecting) array index gets cloned once per array
// element right along with the rest of the chain, same as an impure
// handle.
class C14;
  rand bit [7:0] frame[2];
  bit [7:0] target[2][2];
  int calls;
  function int getIdx();
    calls++;
    return 0;
  endfunction
  constraint c { frame == target[getIdx()]; }
endclass

// Same as C11, but the non-rand operand is a queue element instead of a
// fixed-array element -- the rand-index-into-non-rand check has to see
// through the queue's own 'at()' accessor the same way it does ArraySel.
class C15;
  rand int idx;
  bit [7:0] cube[$][2];
  rand bit [7:0] probe[2];
  constraint ci { idx inside {[0:1]}; }
  constraint c { probe == cube[idx]; }
  function new();
    cube = '{'{0, 0}, '{0, 0}};
  endfunction
endclass

class C16;
  rand bit [7:0] frame[2];
  bit [7:0] target[$][2];
  int calls;
  function int getIdx();
    calls++;
    return 0;
  endfunction
  constraint c { frame == target[getIdx()]; }
  function new();
    target = '{'{0, 0}};
  endfunction
endclass

// Same as C13, but the rand-indexed outer dimension is a fixed array and
// the non-rand inner one is a queue -- the search has to recurse from a
// CMethodHard access into an ArraySel one to find the rand index.
class C17;
  rand int i;
  bit [7:0] cube[4][$][2];
  rand bit [7:0] probe[2];
  constraint ci { i inside {[0:3]}; }
  constraint c { probe == cube[i][0]; }
  function new();
    cube[0] = '{'{0, 0}};
    cube[1] = '{'{0, 0}};
    cube[2] = '{'{0, 0}};
    cube[3] = '{'{0, 0}};
  endfunction
endclass

class C18;
  bit [7:0] cube[4][$][2];
  rand bit [7:0] probe[2];
  int calls;
  function int getIdx();
    calls++;
    return 0;
  endfunction
  constraint c { probe == cube[getIdx()][0]; }
  function new();
    cube[0] = '{'{0, 0}};
  endfunction
endclass

// Unpacked-struct elements, against a non-rand array and both rand, and
// class-handle elements: no elementwise bit-vector compare exists for these.
typedef struct {
  rand bit [1:0] x;
  rand bit [3:0] y;
} unpacked_s;
class C19;
  rand unpacked_s frame[2];
  unpacked_s target[2];
  constraint c { frame != target; }
endclass

class C20;
  rand unpacked_s frame[2];
  rand unpacked_s target[2];
  constraint c { frame == target; }
endclass

class Elem21;
  rand bit [1:0] v;
endclass
class C21;
  rand Elem21 frame[2];
  Elem21 target[2];
  constraint c { frame == target; }
endclass

// An array constructor and a slice as the non-rand operand.
class C22;
  rand bit [1:0] frame[3];
  constraint c { frame == '{2'd1, 2'd2, 2'd3}; }
endclass

class C23;
  rand bit [1:0] frame[2];
  bit [1:0] target[4];
  constraint c { frame == target[1:2]; }
endclass

module t;
  bit [7:0] hier_target[2][2];

  initial begin
    C1 obj1;
    C2 obj2;
    C3 obj3;
    C4 obj4;
    C5 obj5;
    C6 obj6;
    C7 obj7;
    C9 obj9;
    C9b obj9b;
    C10 obj10;
    C10b obj10b;
    C11 obj11;
    C11b obj11b;
    C12 obj12;
    C13 obj13;
    C14 obj14;
    C15 obj15;
    C16 obj16;
    C17 obj17;
    C18 obj18;
    C19 obj19;
    C20 obj20;
    C21 obj21;
    C22 obj22;
    C23 obj23;
    obj1 = new;
    obj2 = new;
    obj3 = new;
    obj4 = new;
    obj5 = new;
    obj6 = new;
    obj7 = new;
    obj9 = new;
    obj9b = new;
    obj10 = new;
    obj10b = new;
    obj11 = new;
    obj11b = new;
    obj12 = new;
    obj13 = new;
    obj14 = new;
    obj15 = new;
    obj16 = new;
    obj17 = new;
    obj18 = new;
    obj19 = new;
    obj20 = new;
    obj21 = new;
    obj22 = new;
    obj23 = new;
    if (obj1.randomize() == 0) $stop;
    if (obj2.randomize() == 0) $stop;
    if (obj3.randomize() == 0) $stop;
    if (obj4.randomize() == 0) $stop;
    if (obj5.randomize() == 0) $stop;
    if (obj6.randomize() == 0) $stop;
    if (obj7.randomize() == 0) $stop;
    if (obj9.randomize() == 0) $stop;
    if (obj9b.randomize() == 0) $stop;
    if (obj10.randomize() == 0) $stop;
    if (obj10b.randomize() == 0) $stop;
    if (obj11.randomize() == 0) $stop;
    if (obj11b.randomize() == 0) $stop;
    if (obj12.randomize() == 0) $stop;
    if (obj13.randomize() == 0) $stop;
    if (obj14.randomize() == 0) $stop;
    if (obj15.randomize() == 0) $stop;
    if (obj16.randomize() == 0) $stop;
    if (obj17.randomize() == 0) $stop;
    if (obj18.randomize() == 0) $stop;
    if (obj19.randomize() == 0) $stop;
    if (obj20.randomize() == 0) $stop;
    if (obj21.randomize() == 0) $stop;
    if (obj22.randomize() == 0) $stop;
    if (obj23.randomize() == 0) $stop;
  end
endmodule
