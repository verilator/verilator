// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// A temporal antecedent must retain simultaneous negated-consequent failures.

// verilog_format: off
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); $fatal; end while(0);
// verilog_format: on

module t (
    input clk
);

  bit ant = 0;
  bit b = 0;
  int temporal_small_fail = 0;
  int temporal_ring_fail = 0;
  int boolean_ant_fail = 0;
  int impossible_pass = 0;
  int impossible_fail = 0;

  // Default actions are checked by the exact output golden.
  assert property (@(posedge clk) (1'b1 ##1 ant) |-> not (1'b1 ##[1:2] b));
  assert property (@(posedge clk) (1'b1 ##1 ant) |-> not (1'b1 ##[1:300] b));

  assert property (@(posedge clk) (1'b1 ##1 ant) |-> not (1'b1 ##[1:2] b))
  else temporal_small_fail++;
  assert property (@(posedge clk) (1'b1 ##1 ant) |-> not (1'b1 ##[1:300] b))
  else temporal_ring_fail++;

  // Boolean-antecedent control for the same two overlapping consequent attempts.
  assert property (@(posedge clk) ant |-> not (1'b1 ##[1:2] b))
  else boolean_ant_fail++;

  // Impossible requested actions retain a well-typed zero count.
  assert property (@(posedge clk) not (1'b1 ##1 1'b1)) impossible_pass++;
  assert property (@(posedge clk) not (1'b1 ##1 1'b0))
  else impossible_fail++;

  initial begin
    @(negedge clk) ant = 1;
    @(negedge clk) ant = 1;
    @(negedge clk) begin
      ant = 0;
      b = 1;
    end
    @(negedge clk) begin
      b = 0;
      `checkd(temporal_small_fail, 2);
      `checkd(temporal_ring_fail, 2);
      `checkd(boolean_ant_fail, 2);
      `checkd(impossible_pass, 0);
      `checkd(impossible_fail, 0);
    end
    // Finish in a later slot, after ignored assertion-stop callbacks drain.
    @(negedge clk);
    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
