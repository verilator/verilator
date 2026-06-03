// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

module t (
    input clk
);

  int cyc = 0;
  always @(posedge clk) cyc <= cyc + 1;

  // |-> ##0 (overlapped, same-cycle, K=0): inlined substitution.
  // Captured snap equals live cyc at the same cycle by definition.
  property p_overlap_d0;
    int snap;
    @(posedge clk) (cyc > 0,
    snap = cyc
    ) |-> (snap == cyc);
  endproperty
  assert property (p_overlap_d0);

  // |-> ##5 (overlapped, K=5): captured snap at T must equal cyc - 5
  // at maturity T+5. If substitution leaks the live cyc, this fails.
  property p_overlap_d5;
    int snap;
    @(posedge clk) (cyc > 4,
    snap = cyc
    ) |-> ##5 (snap == cyc - 5);
  endproperty
  assert property (p_overlap_d5);

  // |=> (non-overlapped, K=1).
  property p_nonoverlap_d1;
    int snap;
    @(posedge clk) (cyc > 0,
    snap = cyc
    ) |=> (snap == cyc - 1);
  endproperty
  assert property (p_nonoverlap_d1);

  // |=> ##3 (non-overlapped, K=4).
  property p_nonoverlap_d4;
    int snap;
    @(posedge clk) (cyc > 4,
    snap = cyc
    ) |=> ##3 (snap == cyc - 4);
  endproperty
  assert property (p_nonoverlap_d4);

  // |-> with match-item ref inside the SExpr's preExprp: substitution
  // is done at K = 0, exercising the inline branch (no $past wrapper).
  property p_overlap_pre_ref;
    int snap;
    @(posedge clk) (cyc > 0,
    snap = cyc - 1
    ) |-> (snap == cyc - 1) ##2 (cyc > 2);
  endproperty
  assert property (p_overlap_pre_ref);

  // Nested SExpr: pre-expr 1'b1 plus ##2 then ##3. Total K = 5.
  property p_nested_seq;
    int snap;
    @(posedge clk) (cyc > 4,
    snap = cyc
    ) |-> ##2 (1'b1 ##3 (snap == cyc - 5));
  endproperty
  assert property (p_nested_seq);

  // Multiple match items on one antecedent must both be substituted.
  property p_multi_match;
    int snap_a, snap_b;
    @(posedge clk) (cyc > 1,
    snap_a = cyc
    ,
    snap_b = cyc + 1
    ) |-> ##2
        ((snap_a == cyc - 2) && (snap_b == cyc - 1));
  endproperty
  assert property (p_multi_match);

  initial begin
    repeat (40) @(posedge clk);
    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
