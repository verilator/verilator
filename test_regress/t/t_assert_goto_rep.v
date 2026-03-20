// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

module t;
  logic clk = 0;
  always #5 clk = ~clk;

  int cyc = 0;

  // Signals
  logic req1, ack1;
  logic b2;
  logic req3, done3;
  logic sig4, resp4;

  // Test 1: req[->2] |-> ack (overlapping, 2 non-consecutive occurrences)
  assert property (@(posedge clk) req1[->2] |-> ack1)
    else $error("[%0t] cyc=%0d FAIL test1", $time, cyc);

  // Test 2: b[->1] |-> 1 (trivial single occurrence)
  assert property (@(posedge clk) b2[->1] |-> 1)
    else $error("[%0t] cyc=%0d FAIL test2", $time, cyc);

  // Test 3: req[->3] |-> done (3 non-consecutive occurrences)
  assert property (@(posedge clk) req3[->3] |-> done3)
    else $error("[%0t] cyc=%0d FAIL test3", $time, cyc);

  // Test 4: sig[->2] |=> resp (non-overlapping implication)
  assert property (@(posedge clk) sig4[->2] |=> resp4)
    else $error("[%0t] cyc=%0d FAIL test4", $time, cyc);

  always @(posedge clk) begin
    cyc <= cyc + 1;

    // Default: all signals low
    req1 <= 0; ack1 <= 0;
    b2 <= 0;
    req3 <= 0; done3 <= 0;
    sig4 <= 0; resp4 <= 0;

    // Test 1: req1 high at cyc 2 and 4, ack1 high at cyc 4
    if (cyc == 2) req1 <= 1;
    if (cyc == 4) begin req1 <= 1; ack1 <= 1; end

    // Test 2: b2 high at cyc 6
    if (cyc == 6) b2 <= 1;

    // Test 3: req3 high at cyc 8, 10, 11; done3 high at cyc 11
    if (cyc == 8) req3 <= 1;
    if (cyc == 10) req3 <= 1;
    if (cyc == 11) begin req3 <= 1; done3 <= 1; end

    // Test 4: sig4 high at cyc 13, 16; resp4 high at cyc 17 (|=> one cycle later)
    if (cyc == 13) sig4 <= 1;
    if (cyc == 16) sig4 <= 1;
    if (cyc == 17) resp4 <= 1;

    if (cyc == 20) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
