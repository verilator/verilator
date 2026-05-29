// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (  /*AUTOARG*/
    // Inputs
    clk
);

  input clk;
  int cyc;

  Test test (  /*AUTOINST*/
      // Inputs
      .clk(clk),
      .cyc(cyc)
  );

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 12) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule

module Test (
    input clk,
    input int cyc
);

  int fallback_fail_count = 0;

  // --- Scenario A: event-triggered assertion (@(evtA)) ---
  event evtA;
  logic disA = 0;
  always @(posedge clk) begin
    if (cyc == 5) -> evtA;
    disA <= (cyc == 5);
  end
  assert property (@(evtA) disable iff (disA) 0)
    else begin
      $display("FAIL scenario A (event sens): cyc=%0d disA=%0d (expected disabled)",
               cyc, disA);
      fallback_fail_count = fallback_fail_count + 1;
    end

  // --- Scenario B: NBA assignment in action block ---
  int sB_dummy = 0;
  assert property (@(posedge clk) disable iff (cyc == 4) (cyc != 3))
    sB_dummy <= cyc;
  else begin
    $display("%t: FAIL scenario B (NBA action): disable iff sees Active value; cyc=%0d",
             $time, cyc);
    fallback_fail_count = fallback_fail_count + 1;
  end

  // --- Scenario C: property with ##N delay (AstFork) ---
  logic disC = 0;
  always @(posedge clk) begin
    disC <= (cyc == 9);
  end
  assert property (@(posedge clk) disable iff (disC) (cyc == 7) |=> ##1 0)
    else begin
      $display("FAIL scenario C (##N delay): cyc=%0d disC=%0d (expected disabled)",
               cyc, disC);
      fallback_fail_count = fallback_fail_count + 1;
    end

  final begin
    if (fallback_fail_count != 0) begin
      $display("FAIL: %0d disable iff fallback scenarios incorrect", fallback_fail_count);
      $stop;
    end
  end

endmodule
