// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 BRDR LIFE
// SPDX-License-Identifier: CC0-1.0

// Narrowing a 'dist' keeps the surviving buckets in their declared proportion.
//
// IEEE 1800-2023 18.5.4: the weights describe the distribution over the set.
// When another constraint excludes part of the set, what is left has to keep its
// relative weighting -- falling back on an unweighted choice would satisfy the
// membership while throwing the distribution away, and equal-weight survivors
// cannot tell the two apart, so every case here is deliberately lopsided.

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// The heaviest bucket is excluded; the two that remain are 99:1.
class HeavyExcluded;
  rand bit [7:0] x;
  constraint c_dist { x dist {8'd0 := 100, 8'd1 := 99, 8'd2 := 1}; }
  constraint c_hard { x != 8'd0; }
endclass

// Many buckets, all the heavy ones excluded, so the draw has to keep falling
// back until it reaches the only feasible one.
class ManyExcluded;
  rand bit [7:0] x;
  constraint c_dist {
    x dist {8'd1 := 100, 8'd2 := 100, 8'd3 := 100, 8'd4 := 100, 8'd5 := 100,
            8'd6 := 100, 8'd7 := 100, 8'd8 := 100, 8'd9 := 100, 8'd10 := 100,
            8'd11 := 100, 8'd12 := 100, 8'd42 := 1};
  }
  constraint c_hard { x == 8'd42; }
endclass

// Two dists pulled apart by a constraint between them.  Both legal outcomes have
// the same product weight, so neither may be systematically preferred.
class Correlated;
  rand bit a;
  rand bit b;
  constraint c_a { a dist {1'b0 := 99, 1'b1 := 1}; }
  constraint c_b { b dist {1'b0 := 99, 1'b1 := 1}; }
  constraint c_ne { a != b; }
endclass

module t;
  initial begin
    HeavyExcluded o1;
    ManyExcluded o2;
    Correlated o3;
    int saw1, saw2, saw01, saw10;
    o1 = new;
    o2 = new;
    o3 = new;

    repeat (1000) begin
      `checkd(o1.randomize(), 1)
      if (o1.x == 8'd1) saw1++;
      else if (o1.x == 8'd2) saw2++;
      else `checkd(o1.x, 8'd1)

      // A preference must never be what fails a solve
      `checkd(o2.randomize(), 1)
      `checkd(o2.x, 8'd42)

      `checkd(o3.randomize(), 1)
      `checkd(o3.a != o3.b, 1)
      if (o3.a == 1'b0) saw01++;
      else saw10++;
    end

    // 99:1 over the survivors.  Bounds are loose; an unweighted fallback would
    // land near 500/500 and a lost distribution near 250/750.
    `checkd(saw1 > 850, 1)
    `checkd(saw2 > 0, 1)

    // Neither ordering may dominate; core-order bias would give ~1000/0.
    `checkd(saw01 > 300, 1)
    `checkd(saw10 > 300, 1)

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
