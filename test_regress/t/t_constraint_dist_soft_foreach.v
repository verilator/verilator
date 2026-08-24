// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 BRDR LIFE
// SPDX-License-Identifier: CC0-1.0

// Soft constraints and 'dist' inside a foreach.
//
// Each element gets its own constraint and its own weighted draw, so each has to
// be discardable on its own: a hard constraint that conflicts with one element
// must not disturb the others.  A foreach under a constraint if has to behave the
// same way, even though the lowering has to lift the loop out of the branch to
// keep the per-element identity.

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// Per-element soft dist, with one element pinned elsewhere by a hard constraint
class PerElement;
  rand bit [7:0] a[4];
  constraint c_dist { foreach (a[i]) soft a[i] dist {8'd5 := 1, 8'd8 := 1}; }
  constraint c_hard { a[0] == 8'd9; }
endclass

// 'disable soft' on the array frees every element's soft dist
class DisabledArray;
  rand bit [7:0] b[4];
  constraint c_dist { foreach (b[i]) soft b[i] dist {8'd5 := 1, 8'd8 := 1}; }
  constraint c_disable { disable soft b; }
endclass

// Hard dist in a foreach under a constraint if, narrowed by a hard constraint.
// The draw has to fall back inside the feasible part per element.
class GuardedNarrowed;
  rand bit [3:0] c[4];
  bit gate;
  constraint c_dist {
    if (gate) {
      foreach (c[i]) c[i] dist {[4'd1 : 4'd4] := 1, [4'd8 : 4'd12] := 3};
    }
  }
  constraint c_hard { foreach (c[i]) c[i] > 4'd10; }
endclass

// Soft dist in a foreach under a constraint if, overridden per element
class GuardedSoft;
  rand bit [3:0] d[4];
  bit gate;
  constraint c_dist {
    if (gate) {
      foreach (d[i]) soft d[i] dist {4'd5 := 1};
    }
  }
  constraint c_hard { foreach (d[i]) d[i] == 4'd9; }
endclass

module t;
  initial begin
    PerElement o1;
    DisabledArray o2;
    GuardedNarrowed o3;
    GuardedSoft o4;
    int free_draws, mixed;
    o1 = new;
    o2 = new;
    o3 = new;
    o4 = new;
    o3.gate = 1'b1;
    o4.gate = 1'b1;

    repeat (100) begin
      // One element pinned outside the set; the rest keep their soft dist
      `checkd(o1.randomize(), 1)
      `checkd(o1.a[0], 8'd9)
      for (int i = 1; i < 4; ++i) begin
        if (o1.a[i] != 8'd5 && o1.a[i] != 8'd8) begin
          $write("%%Error: %s:%0d: element %0d left the dist set: %0d\n", `__FILE__, `__LINE__,
                 i, o1.a[i]);
          `stop;
        end
      end

      `checkd(o2.randomize(), 1)
      for (int i = 0; i < 4; ++i) begin
        if (o2.b[i] != 8'd5 && o2.b[i] != 8'd8) free_draws++;
      end

      `checkd(o3.randomize(), 1)
      for (int i = 0; i < 4; ++i) begin
        if (o3.c[i] != 4'd11 && o3.c[i] != 4'd12) begin
          $write("%%Error: %s:%0d: element %0d outside narrowed set: %0d\n", `__FILE__,
                 `__LINE__, i, o3.c[i]);
          `stop;
        end
      end
      // The draw is made per element, so within one solve the elements differ
      if (o3.c[0] != o3.c[1] || o3.c[1] != o3.c[2] || o3.c[2] != o3.c[3]) mixed++;

      `checkd(o4.randomize(), 1)
      for (int i = 0; i < 4; ++i) `checkd(o4.d[i], 4'd9)
    end

    `checkd(free_draws > 0, 1)
    // A single draw shared by every element could never mix values
    `checkd(mixed > 0, 1)

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
