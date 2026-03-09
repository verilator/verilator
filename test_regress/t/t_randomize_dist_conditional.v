// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// Test constraint with conditional dist operator

class DistScalar;
  rand bit [7:0] x;
  rand bit mode;  // 0: favor zeros (weight 3:1), 1: favor max (weight 1:3)
  constraint c {
    if (mode) {
      x dist { 8'd0 := 1, 8'd255 := 3 };  // Favor 255
    } else {
      x dist { 8'd0 := 3, 8'd255 := 1 };  // Favor 0
    }
  }

  function void display(int trial);
    $display("Trial %0d: mode=%b, x=%0d (0x%02x)", trial, mode, x, x);
  endfunction
endclass

module t;
  DistScalar obj;
  int mode1_zeros = 0;      // Count of zeros when mode=1 (favor 255)
  int mode1_maxes = 0;      // Count of 255s when mode=1 (favor 255)
  int mode0_zeros = 0;      // Count of zeros when mode=0 (favor 0)
  int mode0_maxes = 0;      // Count of 255s when mode=0 (favor 0)
  int mode1_trials = 0;     // Total trials with mode=1
  int mode0_trials = 0;     // Total trials with mode=0

  // Verify distribution ratio matches expected range
  function void check_distribution(int trials, int match_count, string match_name,
                                    int expected_pct, string mode_name);
    int actual_pct;
    int lower_bound;
    int upper_bound;

    if (trials <= 0) return;

    actual_pct = (match_count * 100) / trials;
    $display("  %s %s ratio: %0d/%0d = %0d%% (expected ~%0d%%)",
             mode_name, match_name, match_count, trials, actual_pct, expected_pct);

    // Allow +/-15% deviation from expected ratio
    lower_bound = expected_pct - 15;
    upper_bound = expected_pct + 15;

    if (actual_pct >= lower_bound && actual_pct <= upper_bound) begin
      $display("Distribution OK");
    end else begin
      $display("WARNING: Distribution appears off (expected %0d+/-15%%)", expected_pct);
      $stop;
    end
  endfunction

  initial begin
    int p;
    obj = new;

    // Run multiple trials to verify distribution
    for (int i = 0; i < 1000; i++) begin
      p = obj.randomize();
      `checkd(p, 1);

      if (i < 10) obj.display(i);

      // Track distribution based on mode value
      if (obj.mode) begin
        mode1_trials++;
        if (obj.x == 8'd0) mode1_zeros++;
        else if (obj.x == 8'd255) mode1_maxes++;
      end else begin
        mode0_trials++;
        if (obj.x == 8'd0) mode0_zeros++;
        else if (obj.x == 8'd255) mode0_maxes++;
      end
    end

    $display("");
    $display("Statistics after 1000 trials:");
    $display("  Mode 1 (favor 255): trials=%0d, zeros=%0d, maxes=%0d",
             mode1_trials, mode1_zeros, mode1_maxes);
    $display("  Mode 0 (favor 0):   trials=%0d, zeros=%0d, maxes=%0d",
             mode0_trials, mode0_zeros, mode0_maxes);

    $display("");
    $display("Distribution Verification:");
    // Mode 1: x dist { 0 := 1, 255 := 3 } means 25% for 0, 75% for 255
    check_distribution(mode1_trials, mode1_maxes, "maxes", 75, "Mode 1");

    // Mode 0: x dist { 0 := 3, 255 := 1 } means 75% for 0, 25% for 255
    check_distribution(mode0_trials, mode0_zeros, "zeros", 75, "Mode 0");

    $display("");
    $display("PASSED: Conditional dist constraint test");
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
