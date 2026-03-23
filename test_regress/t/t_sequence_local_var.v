// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

module t (
    input clk
);

  int cyc = 0;
  logic valid;

  // --- Scenario 1: |=> with conditional antecedent ---
  // Captures cyc when valid is true, checks cyc == prev+1 next cycle.
  property p_nonoverlap;
    int prev;
    @(posedge clk)
    (valid, prev = cyc) |=> (cyc == prev + 1);
  endproperty
  assert property (p_nonoverlap);

  // --- Scenario 2: |-> overlapped with match item ---
  // Captures cyc on same cycle, checks equality immediately.
  property p_overlap;
    int snap;
    @(posedge clk)
    (1, snap = cyc) |-> (cyc == snap);
  endproperty
  assert property (p_overlap);

  // --- Scenario 3: same property referenced twice (isolation test) ---
  // Each instance must get its own __Vpropvar variable.
  int counter_x = 0;
  int counter_y = 1000;

  property p_track(int sig);
    int prev;
    @(posedge clk)
    (1, prev = sig) |=> (sig == prev + 1);
  endproperty
  assert property (p_track(counter_x));
  assert property (p_track(counter_y));

  // --- Scenario 4: |-> match item with $urandom (side-effect test) ---
  // snap = $urandom() must evaluate once; snap == snap is always true.
  int overlap_fail = 0;
  property p_overlap_sideeffect;
    int snap;
    @(posedge clk)
    (1, snap = $urandom()) |-> (snap == snap);
  endproperty
  assert property (p_overlap_sideeffect)
  else overlap_fail++;

  // --- Scenario 5: |=> match item with $urandom (side-effect test) ---
  int nonoverlap_fail = 0;
  property p_nonoverlap_sideeffect;
    int snap;
    @(posedge clk)
    (1, snap = $urandom()) |=> (snap == snap);
  endproperty
  assert property (p_nonoverlap_sideeffect)
  else nonoverlap_fail++;

  always @(posedge clk) begin
    cyc <= cyc + 1;
    counter_x <= counter_x + 1;
    counter_y <= counter_y + 1;

    // valid is true at specific cycles only (not always-true)
    valid <= (cyc == 2 || cyc == 5 || cyc == 8);

    if (cyc == 100) begin
      if (overlap_fail > 0) $stop;
      if (nonoverlap_fail > 0) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule
