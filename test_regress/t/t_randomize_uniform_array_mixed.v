// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// Checks that randomize() with an array mixed with a plain scalar in the
// same class, linked by a conditional constraint, covers the whole solution
// space, not just a lucky subset of it. Each sample is also printed so the
// driver can check the distribution's uniformity (Jensen-Shannon divergence)
// from the samples, not just coverage.

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;
  class C;
    rand bit [2:0] arr[2];
    rand bit sel;
    constraint c {
      if (sel) {
        arr[0] > arr[1];
      } else {
        arr[0] <= arr[1];
      }
    }
  endclass

  // Every (arr[0],arr[1]) pair in [0:7]^2 has exactly one sel value that
  // satisfies the constraint, so all 8*8 pairs are solutions.
  localparam int NUM_SOLUTIONS = 64;
  localparam int NUM_ITERS = 25 * NUM_SOLUTIONS;

  initial begin
    automatic C c = new;
    automatic int seen[int];
    automatic int distinct = 0;
    automatic int key;
    automatic int ok;
    for (int i = 0; i < NUM_ITERS; ++i) begin
      ok = c.randomize();
      `checkd(ok, 1);
      // Exactly one ordering holds for each sel value
      `checkd(c.sel, bit'(c.arr[0] > c.arr[1]));
      key = int'({c.sel, c.arr[0], c.arr[1]});  // 7-bit packed key, fits in int
      if (!seen.exists(key)) begin
        seen[key] = 1;
        distinct++;
      end
      $display("%0d %0d %0d", c.sel, c.arr[0], c.arr[1]);
    end
    `checkd(distinct, NUM_SOLUTIONS);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
