// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t(/*AUTOARG*/
  // Inputs
  clk
  );

  input clk;
  int cyc = 0;

  // --- Signals for each assertion ---
  logic a1, b1;
  logic a2, b2;
  logic a3, b3;
  logic a4, b4;

  // Test 1: [*3] overlapped implication
  assert property (@(posedge clk) a1[*3] |-> b1)
    else $error("[%0t] cyc=%0d FAIL test1", $time, cyc);

  // Test 2: [*1] trivial (same as a2 |-> b2)
  assert property (@(posedge clk) a2[*1] |-> b2)
    else $error("[%0t] cyc=%0d FAIL test2", $time, cyc);

  // Test 3: [*2] overlapped implication
  assert property (@(posedge clk) a3[*2] |-> b3)
    else $error("[%0t] cyc=%0d FAIL test3", $time, cyc);

  // Test 4: [*2] non-overlapped implication
  assert property (@(posedge clk) a4[*2] |=> b4)
    else $error("[%0t] cyc=%0d FAIL test4", $time, cyc);

  always @(posedge clk) begin
    cyc <= cyc + 1;
    // Default: all low
    a1 <= 0; b1 <= 0;
    a2 <= 0; b2 <= 0;
    a3 <= 0; b3 <= 0;
    a4 <= 0; b4 <= 0;

    // Test 1: a1 high for 3 cycles (cyc 2-4), b1 high on 3rd (cyc 4)
    if (cyc >= 2 && cyc <= 4) a1 <= 1;
    if (cyc == 4) b1 <= 1;

    // Test 2: a2 high with b2 high (cyc 6-7)
    if (cyc >= 6 && cyc <= 7) begin
      a2 <= 1;
      b2 <= 1;
    end

    // Test 3: a3 high for 2 cycles (cyc 9-10), b3 high on 2nd (cyc 10)
    if (cyc >= 9 && cyc <= 10) a3 <= 1;
    if (cyc == 10) b3 <= 1;

    // Test 4: a4 high for 2 cycles (cyc 12-13), b4 high one after (cyc 14)
    if (cyc >= 12 && cyc <= 13) a4 <= 1;
    if (cyc == 14) b4 <= 1;

    if (cyc == 20) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
