// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 BRDR LIFE
// SPDX-License-Identifier: CC0-1.0

// Soft constraints interacting with 'dist' (IEEE 1800-2023 18.5.4, 18.5.14).
//
// A 'dist' constrains its expression to the set of its values and skews the
// draw by the weights; the weighted draw is a preference, not a constraint, so
// it must never override a soft constraint nor make randomize() fail.  A
// 'soft dist' is a soft constraint in its own right, discarded as a unit when
// its set conflicts with a higher priority constraint or when a 'disable soft'
// names a variable it references.

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// A soft constraint compatible with the dist set must be satisfied: the value
// it asks for is one the dist permits, so only the weighted draw stands in the
// way, and a draw never outranks a constraint.
class DistWithSoft;
  rand int x;
  constraint c_soft { soft x == 5; }
  constraint c_dist { x dist {5 := 1, 8 := 1}; }
endclass

// Same, with the dist declared first.  The outcome must not depend on which
// constraint block registers first, because the draw is below both of them.
class DistWithSoftReversed;
  rand int x;
  constraint c_dist { x dist {5 := 1, 8 := 1}; }
  constraint c_soft { soft x == 5; }
endclass

// A soft dist whose set conflicts with a hard constraint is discarded whole,
// membership included, so randomize() succeeds and the hard constraint holds.
class SoftDistOverride;
  rand int x;
  constraint c_dist { soft x dist {5 := 1, 8 := 1}; }
  constraint c_hard { x == 9; }
endclass

// 'disable soft x' discards the soft dist on x as a unit, leaving x free.
class DisableSoftDist;
  rand bit [7:0] x;
  constraint c_dist { soft x dist {8'd5 := 1, 8'd8 := 1}; }
  constraint c_disable { disable soft x; }
endclass

// A hard dist is not a soft constraint, so 'disable soft' must leave it alone.
// Dropping its weight picks too would silently turn it into a uniform draw.
class DisableSoftHardDist;
  rand bit [7:0] x;
  constraint c_dist { x dist {8'd5 := 1, 8'd8 := 1}; }
  constraint c_disable { disable soft x; }
endclass

// Hard dist in one arm and soft dist in the other, plus a 'disable soft' and a
// hard constraint that excludes both dist sets.  Only the else arm applies.
class MixedSoftDist;
  rand int x;
  rand bit condition;
  constraint c_condition { condition == 0; }
  constraint c_dist {
    if (condition) x dist {1 := 1};
    else soft x dist {2 := 1};
  }
  constraint c_disable { disable soft x; }
  constraint c_hard { x > 100; }
endclass

module t;
  initial begin
    DistWithSoft o1;
    DistWithSoftReversed o2;
    SoftDistOverride o3;
    DisableSoftDist o4;
    DisableSoftHardDist o5;
    MixedSoftDist o6;
    int free_draws;
    o1 = new;
    o2 = new;
    o3 = new;
    o4 = new;
    o5 = new;
    o6 = new;

    repeat (100) begin
      `checkd(o1.randomize(), 1)
      `checkd(o1.x, 5)

      `checkd(o2.randomize(), 1)
      `checkd(o2.x, 5)

      `checkd(o3.randomize(), 1)
      `checkd(o3.x, 9)

      `checkd(o4.randomize(), 1)
      if (o4.x != 8'd5 && o4.x != 8'd8) free_draws++;

      // Hard dist keeps its set even across 'disable soft'
      `checkd(o5.randomize(), 1)
      if (o5.x != 8'd5 && o5.x != 8'd8) begin
        $write("%%Error: %s:%0d: hard dist escaped its set: x=%0d\n", `__FILE__, `__LINE__, o5.x);
        `stop;
      end

      `checkd(o6.randomize(), 1)
      `checkd(o6.x > 100, 1)
    end
    // Freeing a soft dist leaves the variable unconstrained, so 100 draws of an
    // 8-bit value land outside {5, 8} essentially always.
    `checkd(free_draws > 0, 1)

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
