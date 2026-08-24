// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 BRDR LIFE
// SPDX-License-Identifier: CC0-1.0

// A 'dist' whose set is narrowed by another constraint must still solve.
//
// IEEE 1800-2023 18.5.4: the weights only skew the distribution; the constraint
// a dist imposes is set membership.  So when another constraint excludes part of
// the set, the draw has to fall back inside the feasible part rather than making
// randomize() fail.  The bucket count must not change that: a one-bucket dist and
// a many-bucket dist lower through different paths and both have to behave.

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define check_range(gotv,minv,maxv) do if ((gotv) < (minv) || (gotv) > (maxv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d-%0d\n", `__FILE__,`__LINE__, (gotv), (minv), (maxv)); `stop; end while(0);
// verilog_format: on

// One bucket, narrowed from below
class OneBucket;
  rand bit [3:0] x;
  constraint c_dist { x dist {[4'd1 : 4'd9] := 1}; }
  constraint c_hard { x > 4'd5; }
endclass

// Two buckets, narrowed so only part of the upper bucket survives
class TwoBuckets;
  rand bit [3:0] x;
  constraint c_dist { x dist {[4'd1 : 4'd4] := 1, [4'd8 : 4'd12] := 1}; }
  constraint c_hard { x > 4'd10; }
endclass

// Three buckets, narrowed so an entire middle bucket is excluded
class ThreeBuckets;
  rand bit [7:0] x;
  constraint c_dist { x dist {8'd10 := 1, 8'd20 := 5, 8'd30 := 1}; }
  constraint c_hard { x != 8'd20; }
endclass

module t;
  initial begin
    OneBucket o1;
    TwoBuckets o2;
    ThreeBuckets o3;
    int saw11, saw12, saw10, saw30;
    o1 = new;
    o2 = new;
    o3 = new;

    repeat (100) begin
      `checkd(o1.randomize(), 1)
      `check_range(o1.x, 4'd6, 4'd9)

      `checkd(o2.randomize(), 1)
      `check_range(o2.x, 4'd11, 4'd12)
      if (o2.x == 4'd11) saw11++;
      if (o2.x == 4'd12) saw12++;

      `checkd(o3.randomize(), 1)
      if (o3.x == 8'd10) saw10++;
      if (o3.x == 8'd20) begin
        $write("%%Error: %s:%0d: excluded bucket drawn\n", `__FILE__, `__LINE__);
        `stop;
      end
      if (o3.x == 8'd30) saw30++;
    end

    // The surviving part of the set stays reachable: dropping a conflicting draw
    // must not collapse the distribution onto one value.
    `checkd(saw11 > 0, 1)
    `checkd(saw12 > 0, 1)
    `checkd(saw10 > 0, 1)
    `checkd(saw30 > 0, 1)

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
