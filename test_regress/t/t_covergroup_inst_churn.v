// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Matthew Ballance
// SPDX-License-Identifier: CC0-1.0

// SENTINEL: covergroup instance nodes must not accumulate.
//
// A covergroup instance's bins live in the per-context registry, not the SV
// object, so dropping the last SV handle releases nothing by itself.  This
// creates and drops CHURN instances while holding at most one handle, and fails
// if the live-node count tracks instances ever created rather than reachable.
// A memory test without measuring memory: the live count is exact and
// deterministic where an RSS threshold is neither.
//
// Catches only accumulation-without-leaking, which LeakSanitizer cannot see.
// Unlink-without-free is t_covergroup_inst_retire_asan's job, so this file has
// no ASAN variant.  What it uniquely adds is scale: enough instances that O(N)
// versus O(1) is unmistakable.
//
// Instances are dropped across clock edges: garbage is deleted at the start of
// the next eval_step, so a single-eval test would free nothing.

module t (
    input clk
);

  // Enough that accumulation is unmistakable, while staying under a second.
  localparam int CHURN = 2000;

  // Nodes alive at once: one being sampled, one awaiting collection.  Loose on
  // purpose -- the assertion is O(1) versus O(CHURN), not an exact constant.
  localparam int LIVE_MAX = 4;

  int cyc = 0;
  logic [1:0] v;

  int live = 0;
  int peak_live = 0;
  int created = 0;

  covergroup cg_churn;
    cp: coverpoint v {
      bins b0 = {0};
      bins b1 = {1};
      bins b2 = {2};
      bins b3 = {3};
    }
  endgroup

  cg_churn cg;

  always @(posedge clk) begin
    cyc <= cyc + 1;

    if (cyc < CHURN) begin
      cg = new;
      v  = cyc[1:0];
      cg.sample();

      // Live when sampled, so a working registry reports >= 1.  Zero would mean
      // the node was never registered and the rest of this test proves nothing.
      live = $c32("Verilated::threadContextp()->covergroupRegistryp()->liveInstanceCount()");
      if (live > peak_live) peak_live = live;

      cg = null;  // Last handle dropped; collected at the next eval_step
    end else if (cyc == CHURN + 2) begin
      // Two edges after the final drop, so the last instance has been collected.
      live = $c32("Verilated::threadContextp()->covergroupRegistryp()->liveInstanceCount()");
      created = $c32("Verilated::threadContextp()->covergroupRegistryp()->createdInstanceCount()");

      // Guard: a build that folded the covergroup away would report live == 0
      // and "pass".
      if (created != CHURN) begin
        $display("%%Error: created %0d covergroup instances, expected %0d", created, CHURN);
        $stop;
      end

      if (peak_live < 1) begin
        $display("%%Error: never observed a live instance; the probe is not measuring anything");
        $stop;
      end

      if (peak_live > LIVE_MAX) begin
        $display("%%Error: covergroup instances accumulate: peak %0d live nodes over %0d",
                 peak_live, CHURN);
        $display("        Expected no more than %0d live at once.  Instance nodes are not",
                 LIVE_MAX);
        $display("        released when the last SV handle drops.");
        $stop;
      end

      if (live != 0) begin
        $display("%%Error: %0d covergroup instances still live after all handles dropped", live);
        $stop;
      end

      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
