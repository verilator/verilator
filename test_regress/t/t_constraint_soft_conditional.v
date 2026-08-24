// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 BRDR LIFE
// SPDX-License-Identifier: CC0-1.0

// A 'soft' inside a constraint if/else stays soft.
//
// IEEE 1800-2023 18.5.14.1 treats the soft in each arm as a constraint in its
// own right, with its own priority, rather than as part of the enclosing if.  So
// an arm's soft must still yield to a conflicting hard constraint, must still be
// removable by 'disable soft', and must impose nothing when its branch is not
// taken.  No 'dist' is involved here; this is the conditional path on its own.

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// Soft in a taken branch, overridden by a hard constraint: still satisfiable.
class SoftIfOverridden;
  rand int x;
  rand bit c;
  constraint c_sel { c == 1; }
  constraint c_if { if (c) soft x == 5; }
  constraint c_hard { x == 9; }
endclass

// Each arm carries its own soft; the taken arm's soft wins.
class SoftBothArms;
  rand int x;
  rand bit c;
  constraint c_if { if (c) soft x == 5; else soft x == 6; }
endclass

// The implication spelling parses to the same shape and must behave the same.
class SoftImplication;
  rand int x;
  rand bit c;
  constraint c_sel { c == 1; }
  constraint c_imp { c -> soft x == 5; }
  constraint c_hard { x == 9; }
endclass

// 'disable soft' reaches a soft lifted out of a branch.
class SoftIfDisabled;
  rand bit [7:0] x;
  rand bit c;
  constraint c_sel { c == 1; }
  constraint c_if { if (c) soft x == 8'd5; }
  constraint c_disable { disable soft x; }
endclass

// Mixed arms: a hard constraint beside a soft one, and a hard constraint on the
// soft's variable that conflicts.  The hard arm constraint must still be
// enforced while the soft one gives way.
class MixedArms;
  rand int x;
  rand int y;
  rand bit c;
  constraint c_sel { c == 1; }
  constraint c_if {
    if (c) {
      x == 1;
      soft y == 2;
    } else {
      x == 3;
      soft y == 4;
    }
  }
  constraint c_hard { y > 100; }
endclass

// Nested arms, three deep, with the soft only in the innermost else.
class NestedArms;
  rand int x;
  rand bit [1:0] sel;
  constraint c_sel { sel == 2'd3; }
  constraint c_nest {
    if (sel[0]) {
      if (sel[1]) {
        if (x > 0) soft x == 7;
        else soft x == 8;
      }
    }
  }
endclass

// A guard that is itself a rand variable must reach the solver, not be frozen to
// whatever the variable held before the solve.  Both branches stay reachable.
class RandGuard;
  rand int x;
  rand bit sel;
  constraint c_if { if (sel) soft x == 5; else soft x == 6; }
endclass

module t;
  initial begin
    SoftIfOverridden o1;
    SoftBothArms o2;
    SoftImplication o3;
    SoftIfDisabled o4;
    MixedArms o5;
    NestedArms o6;
    RandGuard o7;
    int free_draws, saw5, saw6;
    o1 = new;
    o2 = new;
    o3 = new;
    o4 = new;
    o5 = new;
    o6 = new;
    o7 = new;

    repeat (50) begin
      `checkd(o1.randomize(), 1)
      `checkd(o1.x, 9)

      `checkd(o2.randomize(), 1)
      `checkd(o2.x, o2.c ? 5 : 6)

      `checkd(o3.randomize(), 1)
      `checkd(o3.x, 9)

      `checkd(o4.randomize(), 1)
      if (o4.x != 8'd5) free_draws++;

      `checkd(o5.randomize(), 1)
      `checkd(o5.x, 1)
      `checkd(o5.y > 100, 1)

      `checkd(o6.randomize(), 1)
      if (o6.x != 7 && o6.x != 8) begin
        $write("%%Error: %s:%0d: nested arm soft not applied: x=%0d\n", `__FILE__, `__LINE__,
               o6.x);
        `stop;
      end

      `checkd(o7.randomize(), 1)
      `checkd(o7.x, o7.sel ? 5 : 6)
      if (o7.x == 5) saw5++;
      if (o7.x == 6) saw6++;
    end

    `checkd(free_draws > 0, 1)
    // A frozen guard would pin every solve to the same arm.
    `checkd(saw5 > 0, 1)
    `checkd(saw6 > 0, 1)

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
