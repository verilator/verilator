// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t (
    input clk
);

  int cyc = 0;
  logic a, b, c;

  // Sequence without arguments
  sequence seq_ab;
    a && b;
  endsequence

  // Sequence with formal arguments (default input direction)
  sequence seq_check(logic sig1, logic sig2);
    sig1 && sig2;
  endsequence

  // Overlapping implication with sequence ref (no args)
  assert property (@(posedge clk) seq_ab |-> c);

  // Non-overlapping implication
  assert property (@(posedge clk) seq_ab |=> c);

  // Sequence with args, multiple references with different actuals
  assert property (@(posedge clk) seq_check(a, b) |-> c);
  assert property (@(posedge clk) seq_check(b, c) |-> a);

  // Also in a property instanced by another property
  property prop_check(logic sig1, logic sig2);
    @(posedge clk) seq_check(sig1, sig2) |-> c;
  endproperty
  property prop_check_nested;
    prop_check(a, b);
  endproperty
  assert property (prop_check_nested);

  // Multi-cycle sequence refs: two distinct named sequences chained with ##1.
  // Exercises inlineAllSequenceRefs re-iteration after the first sequence is
  // inlined (early-return branch on the second visit).
  sequence seq_cycle_ab;
    a ##1 b;
  endsequence
  sequence seq_cycle_bc;
    b ##1 c;
  endsequence
  cover property (@(posedge clk) seq_cycle_ab ##1 seq_cycle_bc);

  // Formal arguments used as cycle delays, whose actual arguments are elaboration-time
  // constants (IEEE 1800-2023 16.8): of a sequence, also as range bounds, and of a property,
  // passing it on to a sequence. Each matches 'e' after 'd' with its delay, and fails once with
  // another delay.
  localparam int DLY = 2;
  logic d, e;
  int delay_fails = 0;
  int range_fails = 0;
  int upto_fails = 0;
  int prop_fails = 0;
  int delay_other_fails = 0;
  int range_other_fails = 0;
  int upto_other_fails = 0;
  int prop_other_fails = 0;
  sequence seq_delay(logic sig1, logic sig2, int dly);
    sig1 ##dly sig2;
  endsequence
  sequence seq_range(logic sig1, logic sig2, int lo, int hi);
    sig1 ##[lo:hi] sig2;
  endsequence
  sequence seq_upto(logic sig1, logic sig2, int hi);
    sig1 ##[1:hi] sig2;
  endsequence
  property prop_delay(untyped dly);
    @(posedge clk) d |-> seq_delay(1'b1, e, dly);
  endproperty
  assert property (@(posedge clk) d |-> seq_delay(1'b1, e, DLY))
  else delay_fails++;
  assert property (@(posedge clk) d |-> seq_range(1'b1, e, DLY - 1, DLY + 1))
  else range_fails++;
  assert property (@(posedge clk) d |-> seq_upto(1'b1, e, DLY + 1))
  else upto_fails++;
  assert property (prop_delay(DLY))
  else prop_fails++;
  assert property (@(posedge clk) d |-> seq_delay(1'b1, e, DLY - 1))
  else delay_other_fails++;
  assert property (@(posedge clk) d |-> seq_range(1'b1, e, DLY + 1, DLY + 2))
  else range_other_fails++;
  assert property (@(posedge clk) d |-> seq_upto(1'b1, e, DLY - 1))
  else upto_other_fails++;
  assert property (prop_delay(DLY + 1))
  else prop_other_fails++;

  always @(posedge clk) begin
    cyc <= cyc + 1;
    d <= (cyc == 2);
    e <= (cyc == 4);
    case (cyc)
      2, 5: begin
        a <= 1'b1;
        b <= 1'b1;
        c <= 1'b1;
      end
      3, 6: begin
        a <= 1'b0;
        b <= 1'b0;
        c <= 1'b1;
      end  // c stays high for |=> check
      default: begin
        a <= 1'b0;
        b <= 1'b0;
        c <= 1'b0;
      end
    endcase
    if (cyc == 10) begin
      `checkd(delay_fails, 0)
      `checkd(range_fails, 0)
      `checkd(upto_fails, 0)
      `checkd(prop_fails, 0)
      `checkd(delay_other_fails, 1)
      `checkd(range_other_fails, 1)
      `checkd(upto_other_fails, 1)
      `checkd(prop_other_fails, 1)
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule
