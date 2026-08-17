// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Matthew Ballance
// SPDX-License-Identifier: CC0-1.0

// Covergroup instances that are dropped before the run ends.  Their bins have
// already been registered with the coverage database, so their counts must
// still appear -- and be correct -- in the final report.
//
// Instances are dropped across clock edges on purpose: garbage objects are
// deleted at the start of the *next* eval_step, so a single-eval test would
// never actually free them and would not exercise this at all.

module t (  /*AUTOARG*/
    // Inputs
    clk
);
  input clk;

  int cyc = 0;
  logic [1:0] v;

  covergroup cg_life;
    cp: coverpoint v {
      bins b0 = {0};
      bins b1 = {1};
      bins b2 = {2};
      bins b3 = {3};
    }
  endgroup

  cg_life cg;

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc < 4) begin
      // Instance 'cyc' samples values 0..cyc, so the per-bin totals across all
      // four instances are b0=4, b1=3, b2=2, b3=1.
      cg = new;
      for (int j = 0; j <= cyc; ++j) begin
        v = j[1:0];
        cg.sample();
      end
      cg = null;  // last handle dropped; freed at the next eval_step
    end else if (cyc < 20) begin
      // Churn: each of these reuses the freed storage of an earlier instance,
      // so a stale count pointer reads a live instance's counter instead.
      cg = new;
      v  = 2'b11;
      cg.sample();
      cg = null;
    end else if (cyc == 20) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
