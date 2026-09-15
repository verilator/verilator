// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Aditya Shevade
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// A sum() with (...) reduction over a dynamically-sized array (and a
// queue) whose own size is a separate constraint -- exercises the
// pre-resize sizing pass, run once before the array actually has elements.

class CountFives;
  rand int items[];
  constraint c_size {items.size() == 8;}
  constraint c_count {items.sum() with (item == 5 ? 1 : 0) == 3;}
endclass

class QueueParity;
  rand int q[$];
  constraint c_size {q.size() == 6;}
  constraint c_parity {q.sum() with (item % 2 == 0 ? 1 : 0) == 4;}
endclass

// Same reduction reached through an if-constraint: this merges constraint
// expressions with LOGAND instead of emitting an independent hard()
// statement, a different code path the same guard has to cover too.
class CountFivesIf;
  rand bit enable;
  rand int items[];
  constraint c_enable {enable == 1;}
  constraint c_size {items.size() == 8;}
  constraint c_count {if (enable) items.sum() with (item == 5 ? 1 : 0) == 3;}
endclass

// An if-constraint with no array reduction inside: the guard variable
// stays null on this path, unlike CountFivesIf above.
class PlainIf;
  rand bit enable;
  rand int x;
  constraint c_enable {enable == 1;}
  constraint c_x {if (enable) x == 5;}
endclass

// A reduction over an associative array, pre-populated with keys before
// randomize() runs: exercises the guard's Assoc/Wildcard size query (which
// uses ASSOC_SIZE rather than DYN_SIZE). Only checks randomize() succeeds,
// not that c_count actually held -- enforcing values from a with()-reduction
// over an associative array is a separate, pre-existing gap.
class CountFivesAssoc;
  rand int items[int];
  constraint c_count {items.sum() with (item == 5 ? 1 : 0) == 2;}
endclass

// x inside {arr} where arr is a dynamically-sized array whose own size is
// a separate constraint: same pre-resize collapse as the reductions above,
// through ARRAY_INSIDE codegen instead of a with()-reduction.
class InsideSized;
  rand int arr[];
  rand int x;
  constraint c_size {arr.size() == 5;}
  constraint c_val {x inside {arr};}
endclass

// Same, reached through an if-constraint (the merged LOGAND path).
class InsideSizedIf;
  rand bit enable;
  rand int arr[];
  rand int x;
  constraint c_enable {enable == 1;}
  constraint c_size {arr.size() == 5;}
  constraint c_val {if (enable) x inside {arr};}
endclass

// Two reductions over two different arrays, ANDed into one constraint
// expression: only "a" is size()-constrained, "b" is pre-populated and
// never resized. The guard must track both arrays, not just the last one
// visited, or "b" being permanently non-empty would mask "a" still being
// empty during its own pre-resize pass.
class MixedGuard;
  rand int a[];
  rand int b[];
  constraint c_sizea {a.size() == 4;}
  constraint c_both {a.sum() with (item == 5 ? 1 : 0) == 2
                      && b.sum() with (item == 7 ? 1 : 0) == 1;}
endclass

module t;
  initial begin
    automatic CountFives cf = new;
    automatic QueueParity qp = new;
    automatic CountFivesIf cfi = new;
    automatic PlainIf pi = new;
    automatic CountFivesAssoc cfa = new;
    automatic InsideSized ins = new;
    automatic InsideSizedIf insif = new;
    automatic MixedGuard mg = new;
    int ok;
    int count5;
    int countEven;
    int found;
    int count7;

    cfa.items[0] = 0;
    cfa.items[1] = 0;
    cfa.items[2] = 0;
    cfa.items[3] = 0;
    cfa.items[4] = 0;

    mg.b = new[3];
    mg.b[0] = 7;
    mg.b[1] = 0;
    mg.b[2] = 0;

    repeat (10) begin
      ok = cf.randomize();
      `checkd(ok, 1);
      `checkd(cf.items.size(), 8);
      count5 = 0;
      foreach (cf.items[i]) if (cf.items[i] == 5) count5++;
      `checkd(count5, 3);
    end

    repeat (10) begin
      ok = qp.randomize();
      `checkd(ok, 1);
      `checkd(qp.q.size(), 6);
      countEven = 0;
      foreach (qp.q[i]) if (qp.q[i] % 2 == 0) countEven++;
      `checkd(countEven, 4);
    end

    repeat (10) begin
      ok = cfi.randomize();
      `checkd(ok, 1);
      `checkd(cfi.items.size(), 8);
      count5 = 0;
      foreach (cfi.items[i]) if (cfi.items[i] == 5) count5++;
      `checkd(count5, 3);
    end

    repeat (10) begin
      ok = pi.randomize();
      `checkd(ok, 1);
      `checkd(pi.x, 5);
    end

    repeat (10) begin
      ok = cfa.randomize();
      `checkd(ok, 1);
      `checkd(cfa.items.size(), 5);
    end

    repeat (10) begin
      ok = ins.randomize();
      `checkd(ok, 1);
      `checkd(ins.arr.size(), 5);
      found = 0;
      foreach (ins.arr[i]) if (ins.arr[i] == ins.x) found = 1;
      `checkd(found, 1);
    end

    repeat (10) begin
      ok = insif.randomize();
      `checkd(ok, 1);
      `checkd(insif.arr.size(), 5);
      found = 0;
      foreach (insif.arr[i]) if (insif.arr[i] == insif.x) found = 1;
      `checkd(found, 1);
    end

    repeat (10) begin
      ok = mg.randomize();
      `checkd(ok, 1);
      `checkd(mg.a.size(), 4);
      count5 = 0;
      foreach (mg.a[i]) if (mg.a[i] == 5) count5++;
      `checkd(count5, 2);
      count7 = 0;
      foreach (mg.b[i]) if (mg.b[i] == 7) count7++;
      `checkd(count7, 1);
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
