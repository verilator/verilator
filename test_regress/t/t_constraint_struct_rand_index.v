// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Constraints on a member of a struct array element selected by a random index

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

typedef struct {
  rand int a;
  rand int b;
} pair_t;

class Base;
  rand pair_t items[];
  constraint c_size {items.size() == 3;}
endclass

// Dynamic array, index expressions, constraint if
class Derived extends Base;
  rand int unsigned idx;
  rand bit sel;
  constraint c_idx {idx < 3;}
  constraint c_items {
    if (sel) {
      items[idx].a > 0 && items[idx].a < 100;
      items[(idx+1)%3].a inside {items[idx].a - 1, items[idx].a + 1};
    } else {
      items[idx].b > 0 && items[idx].b < 100;
      items[(idx+1)%3].b inside {items[idx].b - 1, items[idx].b + 1};
    }
  }
endclass

typedef struct {
  rand bit [14:0] a;
  rand bit [6:0] b;
} elem_t;

// Fixed arrays with non-zero bounds, random index in the constraint condition
class Ascending;
  rand elem_t elems[1:3];
  rand bit [1:0] idx;
  constraint c_idx {idx != 0;}
  constraint c_elems {
    elems[idx].a == 15'h7ffe;
    if (elems[idx].b > 7'd50) elems[idx].a[0] == 1'b0;
  }
endclass

class Descending;
  rand elem_t elems[3:1];
  rand int idx;
  constraint c_idx {idx inside {[1:3]};}
  constraint c_elems {(elems[idx].b == 7'd99) && (elems[idx].a == 15'(idx));}
endclass

// Several arrays, a queue, a wide index, a non-random lookup array
class Mixed;
  rand pair_t items[];
  rand pair_t others[$];
  rand pair_t single;
  pair_t lookup[];
  rand longint unsigned idx;
  constraint c_size {
    items.size() == 3;
    others.size() == 3;
  }
  constraint c_idx {idx < 3;}
  constraint c_items {
    items[idx].a == others[idx].b;
    single.a == items[idx].a;
    items[idx].a == lookup[idx].a;
  }
  function new();
    lookup = new[3];
    foreach (lookup[i]) lookup[i] = '{i + 5, 0};
  endfunction
endclass

// The index is kept within the array; an if whose condition does not use it is unaffected
class Bounds;
  rand pair_t items[];
  rand int idx;
  rand bit sel;
  rand int other;
  constraint c_size {items.size() == 3;}
  constraint c_items {
    items[idx].a == 1;
    if (sel) items[idx].b == 2;
    else other == 3;
    soft items[idx].b == 5;
  }
endclass

class OutOfRange;
  rand pair_t items[3];
  rand int idx;
  constraint c_items {
    idx == 3;
    items[idx].a == 1;
  }
endclass

// Struct array of another object
class Holder;
  rand pair_t items[3];
endclass

class Outer;
  rand Holder holder;
  rand bit [1:0] idx;
  constraint c_items {holder.items[idx].a == 4;}
  function new();
    holder = new;
  endfunction
endclass

module t;
  initial begin
    automatic Derived d = new;
    automatic Ascending asc = new;
    automatic Descending desc = new;
    automatic Mixed mixed = new;
    automatic Bounds bounds = new;
    automatic OutOfRange outOfRange = new;
    automatic Outer outer = new;
    automatic pair_t lookup[3];
    automatic int unsigned k;
    automatic int unsigned next;
    automatic int ok;

    repeat (20) begin
      ok = d.randomize();
      `checkd(ok, 1);
      `checkd(d.items.size(), 3);
      next = (d.idx + 1) % 3;
      if (d.sel) begin
        `checkd(d.items[d.idx].a > 0 && d.items[d.idx].a < 100, 1'b1);
        `checkd(d.items[next].a == d.items[d.idx].a - 1 || d.items[next].a == d.items[d.idx].a + 1,
                1'b1);
      end
      else begin
        `checkd(d.items[d.idx].b > 0 && d.items[d.idx].b < 100, 1'b1);
        `checkd(d.items[next].b == d.items[d.idx].b - 1 || d.items[next].b == d.items[d.idx].b + 1,
                1'b1);
      end

      ok = asc.randomize();
      `checkd(ok, 1);
      `checkd(asc.elems[asc.idx].a, 15'h7ffe);

      ok = asc.randomize() with {elems[idx].b == 7'd77;};
      `checkd(ok, 1);
      `checkd(asc.elems[asc.idx].a, 15'h7ffe);
      `checkd(asc.elems[asc.idx].b, 7'd77);

      ok = desc.randomize();
      `checkd(ok, 1);
      `checkd(desc.elems[desc.idx].b, 7'd99);
      `checkd(desc.elems[desc.idx].a, 15'(desc.idx));

      ok = mixed.randomize();
      `checkd(ok, 1);
      `checkd(mixed.items[mixed.idx].a, int'(mixed.idx) + 5);
      `checkd(mixed.others[mixed.idx].b, mixed.items[mixed.idx].a);
      `checkd(mixed.single.a, mixed.items[mixed.idx].a);

      foreach (lookup[i]) lookup[i] = '{i * 10 + 1, 0};
      ok = std::randomize(k) with {
        k < 3;
        lookup[k].a > 5;
      };
      `checkd(ok, 1);
      `checkd(lookup[k].a > 5, 1'b1);

      ok = bounds.randomize();
      `checkd(ok, 1);
      `checkd(bounds.idx >= 0 && bounds.idx < 3, 1'b1);
      `checkd(bounds.items[bounds.idx].a, 1);
      if (bounds.sel) begin
        `checkd(bounds.items[bounds.idx].b, 2);
      end
      else begin
        `checkd(bounds.other, 3);
        `checkd(bounds.items[bounds.idx].b, 5);
      end

      ok = outer.randomize();
      `checkd(ok, 1);
      `checkd(outer.idx < 3, 1'b1);
      `checkd(outer.holder.items[outer.idx].a, 4);
    end

    ok = outOfRange.randomize();
    `checkd(ok, 0);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
