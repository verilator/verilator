// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 BRDR LIFE
// SPDX-License-Identifier: CC0-1.0

// Priority between soft constraints and a 'dist' weighted draw.
//
// IEEE 1800-2023 18.5.14.1 orders soft constraints by declaration: a later one
// wins over an earlier one.  The weighted draw of a dist is not a constraint at
// all, so it sits below every soft regardless of where the dist is declared, and
// it must not be able to displace one.  It also must not stop pulling its weight
// when no soft is in the way.

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// Two softs on the variable of a hard dist: the later soft wins, and the draw
// loses to both.
class TwoSofts;
  rand bit [7:0] x;
  constraint c_soft5 { soft x == 8'd5; }
  constraint c_soft8 { soft x == 8'd8; }
  constraint c_dist { x dist {8'd5 := 1, 8'd8 := 1, 8'd12 := 50}; }
endclass

// A soft dist followed by a plain soft: the later soft wins and the soft dist
// gives way, membership included.
class SoftDistThenSoft;
  rand bit [7:0] x;
  constraint c_dist { soft x dist {8'd5 := 1, 8'd8 := 1}; }
  constraint c_soft { soft x == 8'd12; }
endclass

// Two soft dists on one variable: the later one wins outright.
class TwoSoftDists;
  rand bit [7:0] x;
  constraint c_first { soft x dist {8'd5 := 1, 8'd8 := 1}; }
  constraint c_second { soft x dist {8'd20 := 1, 8'd21 := 1}; }
endclass

// A soft that merely excludes one bucket leaves the rest of the distribution to
// the draw, which must still respect the weights.
class SoftExcludesBucket;
  rand bit [7:0] x;
  constraint c_soft { soft x != 8'd5; }
  constraint c_dist { x dist {8'd5 := 1, 8'd8 := 1, 8'd9 := 1}; }
endclass

// With no soft in the way, a lopsided weight must still show through.
class WeightsOnly;
  rand bit [7:0] x;
  constraint c_dist { x dist {8'd5 := 1, 8'd8 := 99}; }
endclass

module t;
  initial begin
    TwoSofts o1;
    SoftDistThenSoft o2;
    TwoSoftDists o3;
    SoftExcludesBucket o4;
    WeightsOnly o5;
    int saw8, saw9, heavy;
    o1 = new;
    o2 = new;
    o3 = new;
    o4 = new;
    o5 = new;

    repeat (400) begin
      `checkd(o1.randomize(), 1)
      `checkd(o1.x, 8'd8)

      `checkd(o2.randomize(), 1)
      `checkd(o2.x, 8'd12)

      `checkd(o3.randomize(), 1)
      if (o3.x != 8'd20 && o3.x != 8'd21) begin
        $write("%%Error: %s:%0d: later soft dist not applied: x=%0d\n", `__FILE__, `__LINE__,
               o3.x);
        `stop;
      end

      `checkd(o4.randomize(), 1)
      `checkd(o4.x != 8'd5, 1)
      if (o4.x == 8'd8) saw8++;
      if (o4.x == 8'd9) saw9++;

      `checkd(o5.randomize(), 1)
      if (o5.x == 8'd8) heavy++;
    end

    // The two surviving buckets stay equally reachable
    `checkd(saw8 > 0, 1)
    `checkd(saw9 > 0, 1)
    // 99:1 must land on the heavy bucket the large majority of the time.  The
    // bound is deliberately loose; anything near half would mean the weights
    // stopped being applied at all.
    `checkd(heavy > 300, 1)

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
