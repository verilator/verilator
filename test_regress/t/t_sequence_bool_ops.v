// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv, expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t (
    input clk
);
  integer cyc = 0;
  reg [63:0] crc = '0;
  reg [63:0] sum = '0;

  // Derive test signals from CRC
  wire a = crc[0];
  wire b = crc[1];
  wire c = crc[2];
  wire d = crc[3];

  // Aggregate outputs into a single result vector
  wire [63:0] result = {60'h0, d, c, b, a};

  always_ff @(posedge clk) begin
`ifdef TEST_VERBOSE
    $write("[%0t] cyc==%0d crc=%x a=%b b=%b c=%b d=%b\n",
           $time, cyc, crc, a, b, c, d);
`endif
    cyc <= cyc + 1;
    crc <= {crc[62:0], crc[63] ^ crc[2] ^ crc[0]};
    sum <= result ^ {sum[62:0], sum[63] ^ sum[2] ^ sum[0]};

    if (cyc == 0) begin
      crc <= 64'h5aef0c8d_d70a4497;
      sum <= '0;
    end else if (cyc < 10) begin
      sum <= '0;
    end else if (cyc == 99) begin
      `checkh(crc, 64'hc77bb9b3784ea091);
      `checkh(sum, 64'hdb7bc8bfe61f987e);
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

  // =========================================================================
  // Boolean and/or (single-cycle, CRC-driven antecedent)
  // =========================================================================

  // Boolean 'and': (a and b) true iff a && b
  assert property (@(posedge clk) disable iff (cyc < 2)
      (a and b) |-> (a & b));

  // Boolean 'or': (a or b) true iff a || b
  assert property (@(posedge clk) disable iff (cyc < 2)
      (a or b) |-> (a | b));

  // 'and' with constant true -- reduces to just 'a'
  assert property (@(posedge clk) disable iff (cyc < 2)
      (a and 1'b1) |-> a);

  // 'or' with constant false -- reduces to just 'a'
  assert property (@(posedge clk) disable iff (cyc < 2)
      (a or 1'b0) |-> a);

  // Logical '||' (AstLogOr) in a MULTI-CYCLE sequence: must trigger NFA
  // (single-cycle booleans skip NFA via hasMultiCycleExpr filter).
  cover property (@(posedge clk) (a || b) ##1 (a | b));

  // =========================================================================
  // Multi-cycle sequence and (IEEE 1800-2023 16.9.5)
  // CRC-driven: antecedent gates when sequence starts, consequent guaranteed
  // =========================================================================

  // Sequence 'and': both branches must complete, same length
  assert property (@(posedge clk)
      (a & b) |-> (a ##1 1'b1) and (b ##1 1'b1));

  // Sequence 'and': different lengths, end at later branch
  assert property (@(posedge clk)
      (a & b) |-> (a ##1 1'b1) and (b ##2 1'b1));

  // Sequence 'and': standalone (constant, always passes)
  assert property (@(posedge clk)
      (1'b1 ##1 1'b1) and (1'b1 ##2 1'b1));

  // =========================================================================
  // Multi-cycle sequence or (IEEE 1800-2023 16.9.7)
  // CRC-driven: at least one branch must complete
  // =========================================================================

  // Sequence 'or': same length, CRC-driven
  assert property (@(posedge clk)
      (a | b) |-> (a ##1 1'b1) or (b ##1 1'b1));

  // Sequence 'or': different lengths, CRC-driven
  assert property (@(posedge clk)
      (a | b) |-> (a ##1 1'b1) or (b ##2 1'b1));

  // Sequence 'or': standalone (constant, always passes)
  assert property (@(posedge clk)
      (1'b1 ##1 1'b1) or (1'b1 ##2 1'b1));

  // Sequence 'or' where both branches end in registered state (no finalCondp).
  // Exercises guardedLink(termVertexp,...) in buildOrCombiner for both sides.
  cover property (@(posedge clk) (a[*2]) or (b[*2]));

  // Sequence 'and' with unbounded range on one side -- marks combiner unbounded.
  cover property (@(posedge clk) (a ##[1:$] b) and (c ##1 d));

  // =========================================================================
  // SAnd edge cases (NFA builder coverage)
  // =========================================================================

  // SAnd where only one side has finalCondp: a[*2] has no finalCond (consumed
  // by ConsRep); b ##1 c has finalCond=c. Exercises single-cond path in
  // buildAndCombiner.
  cover property (@(posedge clk) (a[*2]) and (b ##1 c));

  // SAnd where both sides lack finalCondp (both end with registered state).
  // Exercises buildMatchNow(!condp) path.
  cover property (@(posedge clk) (a[*2]) and (b[*2]));

  // =========================================================================
  // Negated cover property (NFA assembleResult negated+cover branches)
  // Different shapes to cover the matchCondp/rejectBasep/throughoutRejectp
  // combinations in the negated+cover code path.
  // =========================================================================

  // Shape A: finalCondp=b, required-step reject (the canonical case).
  cover property (@(posedge clk) not (a ##1 b));

  // Shape B: seq ends in state machine -> finalCondp is null.
  cover property (@(posedge clk) not (a ##1 (b[*2])));

  // Shape C: throughout in the seq -> throughoutRejectp non-null.
  cover property (@(posedge clk) not (a throughout (b ##1 c)));

  // Shape D: throughout with state-ending RHS (no finalCondp) -> matchCondp null,
  // throughoutRejectp non-null. Exercises the `if (throughoutRejectp) notPMatchp =
  // orExprs(...)` branch in assembleResult.
  cover property (@(posedge clk) not (a throughout (b[*2])));

  // Assert variants for the negated-assert code path (needAccept branches).
  assert property (@(posedge clk) not (a ##1 (b[*2])))
    else $display("negated multi-cycle fail");
  assert property (@(posedge clk) not (a throughout (b ##1 c)))
    else $display("negated throughout fail");

  // Negated assert with an explicit pass-action block -- exercises the
  // `VL_DO_DANGLING(pushDeletep(passsp), passsp)` branch in the needAccept path.
  assert property (@(posedge clk) not (a ##1 b))
    $display("negated with pass action");

  // Negated assert ending in state machine (matchCondp null, rejectBasep only):
  // exercises the `else if (rejectBasep)` branch of notPMatchp assembly.
  assert property (@(posedge clk) not (a ##1 (b[*2])))
    $display("negated state-end with pass");

  // Negated assert throughout with state-ending RHS (matchCondp null,
  // throughoutRejectp non-null): exercises the `if (throughoutRejectp)` branch.
  assert property (@(posedge clk) not (a throughout (b[*2])))
    else $display("negated throughout state-end");

  // Negated assert with throughout AND an explicit pass-action: needAccept is
  // true (pass block set), so assembleResult runs with outMatchpp!=null and
  // throughoutRejectp non-null, exercising the needAccept-path throughout
  // branch of notPMatchp assembly.
  assert property (@(posedge clk) not (a throughout (b ##1 c)))
    $display("negated throughout with pass action");

endmodule
