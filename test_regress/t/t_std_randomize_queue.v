// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// Test std::randomize() with queue and dynamic array variables

`define stop $stop;
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);

module t_std_randomize_queue;

  // Queue variables
  bit [7:0] q8 [$];
  bit [31:0] q32 [$];

  // Dynamic array variables
  bit [7:0] dyn8 [];

  int i;

  initial begin
    // Test 1: std::randomize with queue (no constraints)
    q8 = {8'd0, 8'd0, 8'd0};
    `checkd(std::randomize(q8), 1);

    // Test 2: std::randomize with queue and constraints
    q8 = {8'd0, 8'd0, 8'd0, 8'd0};
    `checkd(std::randomize(q8) with {
      foreach (q8[j]) q8[j] > 8'd10 && q8[j] < 8'd100;
    }, 1);
    foreach (q8[j]) begin
      if (q8[j] <= 8'd10 || q8[j] >= 8'd100) `stop;
    end

    // Test 3: std::randomize with 32-bit queue
    q32 = {32'd0, 32'd0, 32'd0};
    `checkd(std::randomize(q32) with {
      foreach (q32[k]) q32[k] < 32'd1000;
    }, 1);
    foreach (q32[k]) begin
      if (q32[k] >= 32'd1000) `stop;
    end

    // Test 4: std::randomize with dynamic array
    dyn8 = new[3];
    `checkd(std::randomize(dyn8) with {
      foreach (dyn8[m]) dyn8[m] inside {[1:50]};
    }, 1);
    foreach (dyn8[m]) begin
      if (dyn8[m] < 1 || dyn8[m] > 50) `stop;
    end

    // Test 5: Multiple randomizations produce different values
    q8 = {8'd0, 8'd0, 8'd0};
    begin
      automatic int non_zero = 0;
      repeat (5) begin
        `checkd(std::randomize(q8), 1);
        foreach (q8[n]) if (q8[n] != 0) non_zero++;
      end
      // With 15 random 8-bit values, expect most non-zero
      if (non_zero < 10) `stop;
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
