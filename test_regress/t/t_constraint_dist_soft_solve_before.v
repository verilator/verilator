// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 BRDR LIFE
// SPDX-License-Identifier: CC0-1.0

// 'dist' and soft constraints across a 'solve ... before' ordering.
//
// solve...before splits the solve into phases, and both the soft constraints and
// the dist weight draws have to take effect in whichever phase decides their
// variable.  A dist on an early-phase variable must keep its distribution, and a
// soft on a later-phase variable must still be honoured.

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// The dist decides sel in the first phase; y follows from it, and the soft on m
// is unrelated to the ordering and must simply hold.
class DistBeforeSoft;
  rand bit [1:0] sel;
  rand int unsigned y;
  rand int unsigned m;
  constraint c_order { solve sel before y; }
  constraint c_dist { sel dist {2'd0 := 1, 2'd1 := 9}; }
  constraint c_soft { soft m == 7; }
  constraint c_y {
    if (sel == 2'd0) y == 0;
    else y inside {[1 : 100]};
  }
endclass

// A soft dist on the early variable, overridden by a hard constraint: the soft
// dist is discarded and the ordering still resolves.
class SoftDistBefore;
  rand bit [7:0] sel;
  rand int unsigned y;
  constraint c_order { solve sel before y; }
  constraint c_dist { soft sel dist {8'd5 := 1, 8'd8 := 1}; }
  constraint c_hard { sel == 8'd9; }
  constraint c_y { y == 32'(sel) + 1; }
endclass

module t;
  initial begin
    DistBeforeSoft o1;
    SoftDistBefore o2;
    int saw0, saw1;
    o1 = new;
    o2 = new;

    repeat (200) begin
      `checkd(o1.randomize(), 1)
      `checkd(o1.m, 32'd7)
      if (o1.sel == 2'd0) begin
        saw0++;
        `checkd(o1.y, 32'd0)
      end else begin
        saw1++;
        `checkd(o1.sel, 2'd1)
        if (o1.y < 1 || o1.y > 100) begin
          $write("%%Error: %s:%0d: y out of range: %0d\n", `__FILE__, `__LINE__, o1.y);
          `stop;
        end
      end

      `checkd(o2.randomize(), 1)
      `checkd(o2.sel, 8'd9)
      `checkd(o2.y, 32'd10)
    end

    // Both dist buckets stay reachable across the phase split, and the 9:1
    // weighting must still favour the heavy one.
    `checkd(saw0 > 0, 1)
    `checkd(saw1 > saw0, 1)

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
