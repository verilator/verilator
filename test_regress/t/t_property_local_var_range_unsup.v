// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

module t (
    input clk
);

  int cyc;
  logic valid;

  // Range delay (##[1:3]) over a property-local match-item capture is
  // not yet supported: per-attempt storage is needed to disambiguate
  // overlapping in-flight attempts.
  property p_range;
    int prev;
    @(posedge clk) (valid,
    prev = cyc
    ) |-> ##[1:3] (cyc > prev);
  endproperty
  assert property (p_range);

  // Composite sequence operator (sequence `and`) under a captured local
  // variable reference is also out of scope for the v1 substitution.
  property p_composite;
    int snap;
    @(posedge clk) (valid,
    snap = cyc
    ) |-> (cyc == snap) and ##1 (cyc == snap + 1);
  endproperty
  assert property (p_composite);

  // Nested range delay inside the consequent's preExprp -- the outer
  // SExpr's recursion into preExprp errors, then the outer caller's
  // `if (errorEmitted) return -1;` after preLen recursion is exercised.
  property p_nested_in_pre;
    int snap;
    @(posedge clk) (valid,
    snap = cyc
    ) |-> (1'b1 ##[1:3] (cyc > snap)) ##2 (cyc > snap);
  endproperty
  assert property (p_nested_in_pre);

  // Nested range delay inside the consequent's exprp -- the outer
  // SExpr's recursion into exprp errors, then the outer caller's
  // `if (errorEmitted) return -1;` after bodyLen recursion is exercised.
  property p_nested_in_body;
    int snap;
    @(posedge clk) (valid,
    snap = cyc
    ) |-> ##2 (1'b1 ##[1:3] (cyc > snap));
  endproperty
  assert property (p_nested_in_body);

  always @(posedge clk) begin
    cyc <= cyc + 1;
    valid <= (cyc == 2);
  end

endmodule
