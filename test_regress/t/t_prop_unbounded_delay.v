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

  // ##[+] with always-true consequent (wait >= 1 cycle, then check 1'b1)
  assert property (@(posedge clk) disable iff (cyc < 2)
      a |-> ##[+] 1'b1);

  // ##[*] with always-true consequent (wait >= 0 cycles, then check 1'b1)
  assert property (@(posedge clk) disable iff (cyc < 2)
      a |-> ##[*] 1'b1);

  // ##[2:$] unbounded with min > 1
  assert property (@(posedge clk) disable iff (cyc < 2)
      b |-> ##[2:$] 1'b1);

  // ##[1:$] explicit unbounded (equivalent to ##[+])
  assert property (@(posedge clk) disable iff (cyc < 2)
      a |-> ##[1:$] 1'b1);

  // Unary ##[+] without antecedent
  assert property (@(posedge clk) disable iff (cyc < 2)
      ##[+] 1'b1);

  // Unary ##[*] without antecedent
  assert property (@(posedge clk) disable iff (cyc < 2)
      ##[*] 1'b1);

  // Multi-step: ##[+] then ##1 (tests afterMatchState jump)
  assert property (@(posedge clk) disable iff (cyc < 2)
      a |-> ##[+] 1'b1 ##1 1'b1);

  // Multi-step: ##[*] then ##1 (tests ##[*] immediate match + continuation)
  assert property (@(posedge clk) disable iff (cyc < 2)
      a |-> ##[*] 1'b1 ##1 1'b1);

  // Multi-step: ##[3:$] then ##2 (larger min + continuation)
  assert property (@(posedge clk) disable iff (cyc < 2)
      b |-> ##[3:$] 1'b1 ##2 1'b1);

  // Binary form without implication: a ##[+] b (no antecedent path)
  assert property (@(posedge clk) disable iff (cyc < 2)
      a ##[+] 1'b1);

  // Binary form without implication: a ##[*] b (no antecedent path)
  assert property (@(posedge clk) disable iff (cyc < 2)
      a ##[*] 1'b1);

  // Large min: ##[5:$] (multi-cycle WAIT_MIN countdown)
  assert property (@(posedge clk) disable iff (cyc < 2)
      a |-> ##[5:$] 1'b1);

  // --- Non-trivial consequents: exercise CHECK "stay" path ---

  // ##[+] with CRC signal: wait 1+ cycles for b (exercises match-or-stay)
  assert property (@(posedge clk) disable iff (cyc < 2)
      a |-> ##[+] b);

  // ##[*] with CRC signal: immediate or deferred match of c
  assert property (@(posedge clk) disable iff (cyc < 2)
      a |-> ##[*] c);

  // ##[2:$] with CRC signal: min wait then check b (WAIT_MIN + CHECK unbounded)
  assert property (@(posedge clk) disable iff (cyc < 2)
      b |-> ##[2:$] a);

  // Binary form with CRC signal: a ##[+] b (no implication)
  assert property (@(posedge clk) disable iff (cyc < 2)
      a ##[+] b);

endmodule
