// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 BRDR LIFE
// SPDX-License-Identifier: CC0-1.0

// 'dist' on a variable frozen by rand_mode(0).
//
// A frozen variable keeps its current value, so the dist can no longer draw and
// only its set membership still says anything.  For a hard dist that membership
// is a hard constraint, and a value outside the set is genuinely unsatisfiable.
// For a 'soft dist' it is a soft constraint, so it is discarded instead and
// randomize() still succeeds (IEEE 1800-2023 18.5.14).

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

class SoftDist;
  rand bit [7:0] x;
  rand bit [7:0] other;
  constraint c_dist { soft x dist {8'd5 := 1, 8'd8 := 1}; }
  constraint c_other { other inside {[0 : 10]}; }
endclass

class HardDist;
  rand bit [7:0] x;
  rand bit [7:0] other;
  constraint c_dist { x dist {8'd5 := 1, 8'd8 := 1}; }
  constraint c_other { other inside {[0 : 10]}; }
endclass

module t;
  initial begin
    SoftDist s1;
    SoftDist s2;
    HardDist h1;
    HardDist h2;
    s1 = new;
    s2 = new;
    h1 = new;
    h2 = new;

    // Frozen at a value inside the set: both kinds solve and keep the value
    s1.x.rand_mode(0);
    s1.x = 8'd5;
    h1.x.rand_mode(0);
    h1.x = 8'd5;

    // Frozen outside the set: the soft dist is discarded, the hard one is not
    s2.x.rand_mode(0);
    s2.x = 8'd42;
    h2.x.rand_mode(0);
    h2.x = 8'd42;

    repeat (20) begin
      `checkd(s1.randomize(), 1)
      `checkd(s1.x, 8'd5)

      `checkd(h1.randomize(), 1)
      `checkd(h1.x, 8'd5)

      // A soft constraint never makes randomize() fail
      `checkd(s2.randomize(), 1)
      `checkd(s2.x, 8'd42)

      // A hard dist's membership still holds, so this one has no solution
      `checkd(h2.randomize(), 0)
      `checkd(h2.x, 8'd42)
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
