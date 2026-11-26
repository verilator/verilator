// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)
// verilog_format: on

// IEEE 1800-2023 18.5 constraint_set ::= constraint_expression | { { constraint_expression } }
// so an empty constraint set '{ }' is legal wherever a constraint_set is.
class Forms;
  rand bit [3:0] m;
  rand bit [7:0] x;
  rand bit [7:0] arr[3];
  int q[$];

  constraint c_if_else {
    if (m == 1) {
    }
    else {
      x < 10;
    }
  }
  constraint c_if {
    if ((m == 2) || (x == 3)) {}
    -x > 8'hf0;  // Unary operator starting the next constraint
  }
  constraint c_else {
    if (m != 3) x[0] == 1'b0;
    else { /* Nothing */ }
    &arr[0][1:0] == 1'b0;
  }
  constraint c_foreach {
    foreach (arr[i]) {}
    foreach (q[i]) {}
  }
  constraint c_implication {
    (m == 4) -> {}
    (m == 5) -> if (x == 0) {} else {}
    (m == 6) -> foreach (arr[i]) {}
    {arr[1][0], arr[2][0]} == 2'b01;
  }
  constraint c_nested {
    if (m == 7) { foreach (arr[i]) { if (x == 1) {} } }
    foreach (arr[i]) { foreach (q[j]) {} }
  }
  rand bit [7:0] e;
  rand bit [6:0] g;
  constraint c_foreach_dist_soft {
    foreach (arr[i]) {}
    e dist {[10:12] := 1, [20:22] := 1};
    foreach (q[i]) {}
    soft g == 7'd77;
  }
endclass

// The else branch of an if with an empty then branch follows the solved condition,
// even when the value before randomize() selects the other branch.
class CondElse;
  rand bit [3:0] m;
  rand bit [7:0] x;
  rand bit [7:0] y;
  rand bit [7:0] z;
  rand bit [7:0] v;
  bit [3:0] sel;

  constraint c_sel { m == sel; }
  constraint c_guard_true { (m == 2) -> {} }
  constraint c_empty_then {
    if (m == 6) {} else { x == 7; }
    (m == 6) -> x != 7;
  }
  constraint c_unique_then {
    if (m == 6) { unique {z}; } else { z == 9; }
    (m == 6) -> z != 9;
  }
  constraint c_else_if {
    if (m == 0) { v == 1; } else if (m == 6) { } else { v == 2; }
    (m == 6) -> v != 2;
  }
  rand bit [7:0] d;
  rand bit [6:0] s;
  constraint c_dist_else {
    if (m == 6) {} else { d dist {[0:3] := 1, [200:203] := 1}; }
    (m == 6) -> d inside {[100:110]};
  }
  constraint c_soft_else {
    if (m == 6) {} else { soft s == 7'd5; }
    (m == 6) -> s != 7'd5;
  }
endclass

module t;
  initial begin
    begin
      automatic Forms f = new;
      automatic int randomize_result;
      f.q = {};
      repeat (20) begin
        randomize_result = f.randomize();
        `checkd(randomize_result, 1);
        if (f.m != 1) `checkd(f.x < 10, 1);
        `checkd(f.x > 0 && f.x < 16, 1);
        if (f.m != 3) `checkd(f.x[0], 1'b0);
        `checkd(f.arr[0][1:0] != 2'b11, 1);
        `checkd(f.arr[1][0], 1'b0);
        `checkd(f.arr[2][0], 1'b1);
        `checkd(f.e inside {[10:12], [20:22]}, 1);
        `checkd(f.g, 7'd77);
      end
      f.q = {1, 2};
      randomize_result = f.randomize();
      `checkd(randomize_result, 1);
    end
    begin
      automatic CondElse c = new;
      automatic int randomize_result;
      for (int i = 0; i < 40; ++i) begin
        if (i % 2 == 0) begin
          c.sel = 4'd6;
          c.m = 4'd5;
        end
        else begin
          c.sel = 4'((i / 2) % 6);
          c.m = 4'd6;
        end
        randomize_result = c.randomize();
        `checkd(randomize_result, 1);
        `checkd(c.m, c.sel);
        `checkd(c.x == 7, c.m != 6);
        `checkd(c.z == 9, c.m != 6);
        if (c.m == 0) `checkd(c.v, 1);
        else if (c.m == 6) `checkd(c.v != 2, 1);
        else `checkd(c.v, 2);
        if (c.m == 6) `checkd(c.d inside {[100:110]}, 1);
        else `checkd(c.d inside {[0:3], [200:203]}, 1);
        if (c.m == 6) `checkd(c.s != 7'd5, 1);
        else `checkd(c.s, 7'd5);
      end
    end
    begin
      automatic CondElse c = new;
      automatic int randomize_result;
      for (int i = 0; i < 20; ++i) begin
        c.sel = (i % 2 == 1) ? 4'd6 : 4'd3;
        c.m = (i % 2 == 1) ? 4'd3 : 4'd6;
        randomize_result = c.randomize() with {
          if (m == 3) {} else { x == 11; }
          if (m == 3) { unique {y}; } else { y == 4; }
          (m == 3) -> y != 4;
        };
        `checkd(randomize_result, 1);
        `checkd(c.m, c.sel);
        `checkd(c.x == 11, c.m == 6);
        `checkd(c.y == 4, c.m == 6);
      end
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
