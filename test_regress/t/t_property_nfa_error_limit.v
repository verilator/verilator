// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// Default and counted fail actions under an error limit, recorded by the golden.

module t (
    input clk
);

  int cyc = 0;

  // Default actions for property-case branches of different lengths
  logic [1:0] selector;
  bit nb = 0;
  bit abrt = 0;
  bit zz = 0;

  always_comb begin
    if (cyc == 2) selector = 0;
    else if (cyc == 3) selector = 1;
    else selector = 2;
  end

  assert property (@(posedge clk) case (selector) 0: 1'b1 ##2 1'b0; 1: 1'b1 ##1 1'b0; default: 1'b1;
  endcase);

  assert property (@(posedge clk) not (1'b1 ##[1:2] nb));

  assert property (@(posedge clk) sync_reject_on (abrt) always[0: 1] (!zz));

  // Simultaneous negated-consequent failures behind a temporal antecedent
  bit ant = 0;
  bit b = 0;
  int temporal_small_fail = 0, temporal_ring_fail = 0, boolean_ant_fail = 0;
  int impossible_pass = 0, impossible_fail = 0;

  assert property (@(posedge clk) (1'b1 ##1 ant) |-> not (1'b1 ##[1:2] b));
  assert property (@(posedge clk) (1'b1 ##1 ant) |-> not (1'b1 ##[1:300] b));

  assert property (@(posedge clk) (1'b1 ##1 ant) |-> not (1'b1 ##[1:2] b))
  else temporal_small_fail++;
  assert property (@(posedge clk) (1'b1 ##1 ant) |-> not (1'b1 ##[1:300] b))
  else temporal_ring_fail++;

  assert property (@(posedge clk) ant |-> not (1'b1 ##[1:2] b))
  else boolean_ant_fail++;

  assert property (@(posedge clk) not (1'b1 ##1 1'b1)) impossible_pass++;
  assert property (@(posedge clk) not (1'b1 ##1 1'b0))
  else impossible_fail++;

  always @(posedge clk) begin
    cyc <= cyc + 1;
    nb <= (cyc == 4);
    abrt <= (cyc == 5);
  end

  initial begin
    @(negedge clk) ant = 1;
    @(negedge clk) ant = 1;
    @(negedge clk) begin
      ant = 0;
      b = 1;
    end
    @(negedge clk) b = 0;
  end

  always @(negedge clk) begin
    if (cyc == 8) begin
      $display("temporal: small_fail=%0d ring_fail=%0d boolean_ant_fail=%0d", temporal_small_fail,
               temporal_ring_fail, boolean_ant_fail);
      $display("impossible: pass=%0d fail=%0d", impossible_pass, impossible_fail);
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule
