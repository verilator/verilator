// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// Test that randc with wide variables (16-bit) and constraints does not hang.
// Previously, the solver tried to enumerate all valid values upfront,
// causing a pipe deadlock. See verilator/verilator#7068.

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

class RandcFull;
  randc bit [15:0] value;

  // Full 16-bit domain (65536 valid values).
  // Old enumerateRandcValues() would try to enumerate all -> hang.
  constraint range_c { value >= 0; }
endclass

class RandcSmall;
  randc bit [15:0] value;

  constraint range_c { value inside {[0:7]}; }
endclass

module t;
  initial begin
    RandcFull full_obj;
    RandcSmall small_obj;
    int seen[int];
    int rand_ok;

    // Test 1: randc 16-bit full domain - must not hang
    full_obj = new();
    for (int i = 0; i < 5; i++) begin
      rand_ok = full_obj.randomize();
      `checkd(rand_ok, 1)
    end

    // Test 2: randc 16-bit with small constrained domain - verify cycling
    small_obj = new();
    for (int i = 0; i < 8; i++) begin
      rand_ok = small_obj.randomize();
      `checkd(rand_ok, 1)
      if (small_obj.value > 16'd7) begin
        $write("%%Error: value %0d out of range [0:7]\n", small_obj.value);
        `stop;
      end
      if (seen.exists(int'(small_obj.value))) begin
        $write("%%Error: duplicate value %0d before cycle complete\n", small_obj.value);
        `stop;
      end
      seen[int'(small_obj.value)] = 1;
    end
    `checkd(seen.size(), 8)

    // Test 3: after full cycle, new cycle should start
    rand_ok = small_obj.randomize();
    `checkd(rand_ok, 1)
    if (small_obj.value > 16'd7) begin
      $write("%%Error: value %0d out of range after cycle reset\n", small_obj.value);
      `stop;
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
