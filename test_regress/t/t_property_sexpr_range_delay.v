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

  wire [63:0] result = {61'h0, c, b, a};

  always_ff @(posedge clk) begin
`ifdef TEST_VERBOSE
    $write("[%0t] cyc==%0d crc=%x a=%b b=%b c=%b\n", $time, cyc, crc, a, b, c);
`endif
    cyc <= cyc + 1;
    crc <= {crc[62:0], crc[63] ^ crc[2] ^ crc[0]};
    sum <= result ^ {sum[62:0], sum[63] ^ sum[2] ^ sum[0]};

    if (cyc == 0) begin
      crc <= 64'h5aef0c8d_d70a4497;
      sum <= '0;
    end
    else if (cyc < 10) begin
      sum <= '0;
    end
    else if (cyc == 99) begin
      `checkh(crc, 64'hc77bb9b3784ea091);
      `checkh(sum, 64'h38c614665c6b71ad);
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

  // Basic ##[1:3] range delay (CRC-driven, always-true consequent)
  assert property (@(posedge clk) disable iff (cyc < 2)
      a |-> ##[1:3] 1'b1);

  // ##[2:4] range delay
  assert property (@(posedge clk) disable iff (cyc < 2)
      b |-> ##[2:4] 1'b1);

  // Degenerate ##[2:2] (equivalent to ##2)
  assert property (@(posedge clk) disable iff (cyc < 2)
      a |-> ##[2:2] 1'b1);

  // Multi-step: ##[1:2] then ##1 (both consequents always true)
  assert property (@(posedge clk) disable iff (cyc < 2)
      a |-> ##[1:2] 1'b1 ##1 1'b1);

  // Large range ##[1:10000] (scalability, O(1) code size)
  assert property (@(posedge clk) disable iff (cyc < 2)
      a |-> ##[1:10000] 1'b1);

  // Range with binary SExpr: nextStep has delay > 0 after range match
  assert property (@(posedge clk) disable iff (cyc < 2)
      a |-> b ##[1:2] 1'b1 ##3 1'b1);

  // Binary SExpr without implication (covers firstStep.exprp path without antecedent)
  assert property (@(posedge clk) disable iff (cyc < 2)
      a ##[1:3] 1'b1);

  // Implication with binary SExpr RHS (covers antExprp AND firstStep.exprp)
  assert property (@(posedge clk) disable iff (cyc < 2)
      a |-> b ##[1:2] 1'b1);

  // Fixed delay before range (covers firstStep.delay path in IDLE)
  assert property (@(posedge clk) disable iff (cyc < 2)
      a |-> ##2 1'b1 ##[1:3] 1'b1);

  // Unary range with no antecedent and no preExpr (covers unconditional start)
  assert property (@(posedge clk) disable iff (cyc < 2)
      ##[1:3] 1'b1);

endmodule
