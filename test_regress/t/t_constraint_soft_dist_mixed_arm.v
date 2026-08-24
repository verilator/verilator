// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 BRDR LIFE
// SPDX-License-Identifier: CC0-1.0

// A hard dist and a soft dist in the same constraint-if arm stay separate.
//
// Both have to be lifted out of the arm to keep their kinds, but they must be
// lifted as two preferences rather than one: sharing a node would give them one
// soft-ownership flag and one variable list between them, so 'disable soft' on
// the soft one would take the hard one's weights with it, and a conflict on
// either would discard both.
//
// Also covers a bare wide expression under the same guard, which has to keep the
// implicit "!= 0" of IEEE 1800-2023 18.5.1 when it is re-homed under the guard.

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// 'disable soft y' must leave the hard dist on x weighted as declared.
class MixedArm;
  rand bit [7:0] x;
  rand bit [7:0] y;
  bit gate;
  constraint c_if {
    if (gate) {
      x dist {8'd5 := 1, 8'd8 := 99};
      soft y dist {8'd1 := 1};
    }
  }
  constraint c_disable { disable soft y; }
endclass

// A wide bare expression as a constraint, under a guard alongside a soft.
class WideBareGuarded;
  rand int x;
  rand int z;
  rand bit c;
  constraint c_sel { c == 1; }
  constraint c_if {
    if (c) {
      z;  // implicitly z != 0
      soft x == 5;
    }
  }
  constraint c_hard { x == 9; }
endclass

// The same wide bare item inside a guarded foreach, where the guard is pushed
// onto each element's item rather than folded with it.
class WideBareForeach;
  rand int a[3];
  rand bit c;
  constraint c_sel { c == 1; }
  constraint c_if {
    if (c) {
      foreach (a[i]) {
        a[i];  // implicitly a[i] != 0
        soft a[i] == 7;
      }
    }
  }
endclass

module t;
  initial begin
    MixedArm o1;
    WideBareGuarded o2;
    WideBareForeach o3;
    int heavy, free_y;
    o1 = new;
    o2 = new;
    o3 = new;
    o1.gate = 1'b1;

    repeat (400) begin
      `checkd(o1.randomize(), 1)
      if (o1.x == 8'd8) heavy++;
      else `checkd(o1.x, 8'd5)
      if (o1.y != 8'd1) free_y++;
    end
    // The hard dist keeps its 99:1 skew; losing it would give about half
    `checkd(heavy > 300, 1)
    // The soft dist really was discarded
    `checkd(free_y > 0, 1)

    repeat (50) begin
      `checkd(o2.randomize(), 1)
      `checkd(o2.x, 9)
      `checkd(o2.z != 0, 1)

      `checkd(o3.randomize(), 1)
      for (int i = 0; i < 3; ++i) begin
        `checkd(o3.a[i], 7)
      end
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
