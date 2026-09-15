// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Aditya Shevade
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// sum() with (item.field) on a dynamically-sized array of structs sized
// by a separate constraint -- exercises a struct-element bounds-check
// leak and an identity-width mismatch, both in the same reduction path.

class Batch;
  typedef struct {
    rand int val;
  } cmd_s;
  rand cmd_s items[];
  constraint c_size {items.size() == 4;}
  constraint c_sum {items.sum() with (item.val) == 20;}
endclass

// Same reduction, but reached through an if-constraint: this merges
// constraint expressions with LOGAND instead of emitting an independent
// hard() statement, a different code path the zero-elements guard above
// has to cover too.
class BatchIf;
  typedef struct {
    rand int val;
  } cmd_s;
  rand bit enable;
  rand cmd_s items[];
  constraint c_enable {enable == 1;}
  constraint c_size {items.size() == 4;}
  constraint c_sum {if (enable) items.sum() with (item.val) == 20;}
endclass

// Same reduction, but product()/and() rather than sum(): exercises the
// PRODUCT/AND identity-element branches (identityForWidth), not just the
// default zero identity that SUM/OR/XOR share.
class BatchProduct;
  typedef struct {
    rand int val;
  } cmd_s;
  rand cmd_s items[];
  constraint c_size {items.size() == 3;}
  constraint c_each {foreach (items[i]) items[i].val inside {[1:4]};}
  constraint c_product {items.product() with (item.val) == 24;}
endclass

class BatchAnd;
  typedef struct {
    rand int val;
  } cmd_s;
  rand cmd_s items[];
  constraint c_size {items.size() == 3;}
  constraint c_each {foreach (items[i]) items[i].val inside {[10:15]};}
  constraint c_and {items.and() with (item.val) == 8;}
endclass

// A reduction over an associative array of structs, pre-populated with
// keys before randomize() runs: exercises the guard's Assoc/Wildcard size
// query (which uses ASSOC_SIZE rather than DYN_SIZE). Only checks
// randomize() succeeds, not that c_sum actually held -- enforcing values
// from a with()-reduction over an associative array is a separate,
// pre-existing gap.
class BatchAssoc;
  typedef struct {
    rand int val;
  } cmd_s;
  rand cmd_s items[int];
  constraint c_sum {items.sum() with (item.val) == 20;}
endclass

module t;
  initial begin
    automatic Batch b = new;
    automatic BatchIf bi = new;
    automatic BatchProduct bp = new;
    automatic BatchAnd ba = new;
    automatic BatchAssoc bas = new;
    int ok;
    int sum;
    int product;
    int bitand_;

    bas.items[0].val = 0;
    bas.items[1].val = 0;
    bas.items[2].val = 0;

    repeat (10) begin
      ok = b.randomize();
      `checkd(ok, 1);
      `checkd(b.items.size(), 4);
      sum = 0;
      foreach (b.items[i]) sum += b.items[i].val;
      `checkd(sum, 20);

      ok = bi.randomize();
      `checkd(ok, 1);
      `checkd(bi.items.size(), 4);
      sum = 0;
      foreach (bi.items[i]) sum += bi.items[i].val;
      `checkd(sum, 20);

      ok = bp.randomize();
      `checkd(ok, 1);
      `checkd(bp.items.size(), 3);
      product = 1;
      foreach (bp.items[i]) product *= bp.items[i].val;
      `checkd(product, 24);

      ok = ba.randomize();
      `checkd(ok, 1);
      `checkd(ba.items.size(), 3);
      bitand_ = '1;
      foreach (ba.items[i]) bitand_ &= ba.items[i].val;
      `checkd(bitand_, 8);

      ok = bas.randomize();
      `checkd(ok, 1);
      `checkd(bas.items.size(), 3);
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
