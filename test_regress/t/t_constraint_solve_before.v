// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define check_range(gotv,minv,maxv) do if ((gotv) < (minv) || (gotv) > (maxv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d-%0d\n", `__FILE__,`__LINE__, (gotv), (minv), (maxv)); `stop; end while(0);
// verilog_format: on

// Test solve...before constraint (IEEE 1800-2017 18.5.11)
// Verifies phased solving: 'before' variables are determined first,
// then 'after' variables are solved with all constraints applied.

/* verilator lint_off UNSIGNED */

module t;

  // Test 1: solve with conditional constraints
  class Packet;
    rand bit [2:0] mode;
    rand bit [7:0] data;

    constraint c_order {
      solve mode before data;
      mode inside {[0:3]};
      if (mode == 0) data == 8'h00;
      else if (mode == 1) data inside {[8'h01:8'h0f]};
      else data < 8'h80;
    }
  endclass

  // Test 2: basic solve before with range constraints
  class Simple;
    rand bit [3:0] x;
    rand bit [3:0] y;

    constraint c {
      solve x before y;
      x inside {[1:5]};
      y > x;
      y < 4'hf;
    }
  endclass

  // Test 3: multi-level solve before (a -> b -> c)
  class MultiLevel;
    rand bit [3:0] a;
    rand bit [3:0] b;
    rand bit [3:0] c;

    constraint c_order {
      solve a before b;
      solve b before c;
      a inside {[1:3]};
      b > a;
      b < 8;
      c > b;
      c < 4'hf;
    }
  endclass

  initial begin
    Packet p;
    Simple s;
    MultiLevel m;
    int ok;

    // Test 1: Packet with conditional constraints
    p = new;
    repeat (20) begin
      `checkd(p.randomize(), 1)
      `check_range(p.mode, 0, 3)
      if (p.mode == 0) `checkd(p.data, 0)
      if (p.mode == 1) begin
        `check_range(p.data, 1, 15)
      end
      if (p.mode >= 2) begin
        ok = (p.data < 8'h80) ? 1 : 0;
        `checkd(ok, 1)
      end
    end

    // Test 2: Simple range constraints
    s = new;
    repeat (20) begin
      `checkd(s.randomize(), 1)
      `check_range(s.x, 1, 5)
      ok = (s.y > s.x) ? 1 : 0;
      `checkd(ok, 1)
      ok = (s.y < 4'hf) ? 1 : 0;
      `checkd(ok, 1)
    end

    // Test 3: Multi-level chain
    m = new;
    repeat (20) begin
      `checkd(m.randomize(), 1)
      `check_range(m.a, 1, 3)
      ok = (m.b > m.a && m.b < 8) ? 1 : 0;
      `checkd(ok, 1)
      ok = (m.c > m.b && m.c < 4'hf) ? 1 : 0;
      `checkd(ok, 1)
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
