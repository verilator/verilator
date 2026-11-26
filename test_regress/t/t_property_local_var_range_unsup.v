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

  // A nested range delay in the consequent's prefix is unsupported.
  // Propagate its diagnostic through the enclosing concatenation
  // without continuing substitution after the failure.
  property p_nested_in_pre;
    int snap;
    @(posedge clk) (valid,
    snap = cyc
    ) |-> (1'b1 ##[1:3] (cyc > snap)) ##2 (cyc > snap);
  endproperty
  assert property (p_nested_in_pre);

  // A nested range delay in the consequent's body is unsupported.
  // Propagate its diagnostic through the enclosing concatenation
  // without continuing substitution after the failure.
  property p_nested_in_body;
    int snap;
    @(posedge clk) (valid,
    snap = cyc
    ) |-> ##2 (1'b1 ##[1:3] (cyc > snap));
  endproperty
  assert property (p_nested_in_body);

  // A value with side effects used in the cycle it is assigned, and in a later cycle, is
  // unsupported
  property p_side_effect;
    int snap;
    @(posedge clk) (valid,
    snap = $urandom()
    ) |-> (snap[0] == 1'b1) ##1 (snap[0] == 1'b0);
  endproperty
  assert property (p_side_effect);

  // Likewise a function writing an output argument
  int out_v;
  function automatic int setter(output int x);
    x = 1;
    return 0;
  endfunction
  assert property (@(posedge clk) $past(setter(out_v)) == 0);

  // A value from a seeded $random writes its seed when sampled
  int seed = 0;
  property p_seeded;
    int snap;
    @(posedge clk) (valid, snap = $random(seed)) |=> (snap != 0);
  endproperty
  assert property (p_seeded);

  always @(posedge clk) begin
    cyc <= cyc + 1;
    valid <= (cyc == 2);
  end

endmodule
