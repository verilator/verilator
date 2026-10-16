// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Aditya Shevade
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// Records whether signal ever differs from its value on the previous
// iteration, across a repeat loop that otherwise only checks a fixed
// invariant -- a fixed invariant alone can't tell a real solve from one
// that keeps returning the same trivially-satisfying assignment.
`define track_varies(signal, prevvar, variedvar) \
  if (longint'(signal) != (prevvar)) variedvar = 1; \
  prevvar = longint'(signal);
// verilog_format: on

// A sum() with (...) reduction over a dynamically-sized array (and a
// queue) whose own size is a separate constraint -- exercises the
// pre-resize sizing pass, run once before the array actually has elements.

class CountFives;
  rand int items[];
  constraint c_size {items.size() inside {6, 7, 8};}
  constraint c_count {items.sum() with (item == 5 ? 1 : 0) == 3;}
endclass

class QueueParity;
  rand int q[$];
  constraint c_size {q.size() == 6;}
  constraint c_parity {q.sum() with (item % 2 == 0 ? 1 : 0) == 4;}
endclass

// with (item.index) on a dynamically-sized array whose own size is a
// separate constraint: exercises both the pre-resize guard and the
// item.index substitution path (a different width-adjustment shape than
// item/item.field above) together.
class IndexSum;
  rand int idxArr[];
  constraint c_size {idxArr.size() == 5;}
  constraint c_idxsum {idxArr.sum() with (item.index) == 10;}
endclass

// or()/xor() with (...) on a dynamically-sized array whose own size is a
// separate constraint: closes the last two reduction kinds this bug shape
// hadn't been tested against (sum/product/and above only covered three of
// the five with()-reduction methods).
class OrXorReduce;
  rand bit [7:0] arr[];
  constraint c_size {arr.size() == 4;}
  constraint c_or {(arr.or() with (item & 8'h08)) == 8'h08;}
  constraint c_xor {(arr.xor() with (item)) != 0;}
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
    automatic IndexSum idxsum = new;
    automatic OrXorReduce oxr = new;
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
    int idxSum;
    bit [7:0] orResult, xorResult;
    longint prevCfSize, prevCfSum, prevQSum, prevOxrElem, prevCfiSum, prevInsX, prevInsifX,
        prevMgSum;
    bit cfSizeVaried, cfSumVaried, qSumVaried, oxrElemVaried, cfiSumVaried, insXVaried,
        insifXVaried, mgSumVaried;

    cfa.items[0] = 0;
    cfa.items[1] = 0;
    cfa.items[2] = 0;
    cfa.items[3] = 0;
    cfa.items[4] = 0;

    mg.b = new[3];
    mg.b[0] = 7;
    mg.b[1] = 0;
    mg.b[2] = 0;

    prevCfSize = -1;
    prevCfSum = 64'h7fffffff_ffffffff;
    repeat (10) begin
      ok = cf.randomize();
      `checkd(ok, 1);
      if (cf.items.size() < 6 || cf.items.size() > 8) `stop;
      count5 = 0;
      foreach (cf.items[i]) if (cf.items[i] == 5) count5++;
      `checkd(count5, 3);
      `track_varies(cf.items.size(), prevCfSize, cfSizeVaried)
      `track_varies(cf.items.sum(), prevCfSum, cfSumVaried)
    end
    if (!cfSizeVaried || !cfSumVaried) `stop;

    prevQSum = 64'h7fffffff_ffffffff;
    repeat (10) begin
      ok = qp.randomize();
      `checkd(ok, 1);
      `checkd(qp.q.size(), 6);
      countEven = 0;
      foreach (qp.q[i]) if (qp.q[i] % 2 == 0) countEven++;
      `checkd(countEven, 4);
      `track_varies(qp.q.sum(), prevQSum, qSumVaried)
    end
    if (!qSumVaried) `stop;

    repeat (10) begin
      ok = idxsum.randomize();
      `checkd(ok, 1);
      `checkd(idxsum.idxArr.size(), 5);
      idxSum = 0;
      foreach (idxsum.idxArr[i]) idxSum += i;
      `checkd(idxSum, 10);
    end

    prevOxrElem = 64'h7fffffff_ffffffff;
    repeat (10) begin
      ok = oxr.randomize();
      `checkd(ok, 1);
      `checkd(oxr.arr.size(), 4);
      orResult = 8'h00;
      foreach (oxr.arr[i]) orResult |= (oxr.arr[i] & 8'h08);
      `checkd(orResult, 8'h08);
      xorResult = 8'h00;
      foreach (oxr.arr[i]) xorResult ^= oxr.arr[i];
      if (xorResult == 8'h00) `stop;
      `track_varies(oxr.arr[0], prevOxrElem, oxrElemVaried)
    end
    if (!oxrElemVaried) `stop;

    prevCfiSum = 64'h7fffffff_ffffffff;
    repeat (10) begin
      ok = cfi.randomize();
      `checkd(ok, 1);
      `checkd(cfi.items.size(), 8);
      count5 = 0;
      foreach (cfi.items[i]) if (cfi.items[i] == 5) count5++;
      `checkd(count5, 3);
      `track_varies(cfi.items.sum(), prevCfiSum, cfiSumVaried)
    end
    if (!cfiSumVaried) `stop;

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

    prevInsX = 64'h7fffffff_ffffffff;
    repeat (10) begin
      ok = ins.randomize();
      `checkd(ok, 1);
      `checkd(ins.arr.size(), 5);
      found = 0;
      foreach (ins.arr[i]) if (ins.arr[i] == ins.x) found = 1;
      `checkd(found, 1);
      `track_varies(ins.x, prevInsX, insXVaried)
    end
    if (!insXVaried) `stop;

    prevInsifX = 64'h7fffffff_ffffffff;
    repeat (10) begin
      ok = insif.randomize();
      `checkd(ok, 1);
      `checkd(insif.arr.size(), 5);
      found = 0;
      foreach (insif.arr[i]) if (insif.arr[i] == insif.x) found = 1;
      `checkd(found, 1);
      `track_varies(insif.x, prevInsifX, insifXVaried)
    end
    if (!insifXVaried) `stop;

    prevMgSum = 64'h7fffffff_ffffffff;
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
      `track_varies(mg.a.sum(), prevMgSum, mgSumVaried)
    end
    if (!mgSumVaried) `stop;

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
