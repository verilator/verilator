// DESCRIPTION: Verilator: Test X/Z four-state simulation with time functions
//
// This test verifies four-state simulation with $time, $stime, and $realtime.
//
// SPDX-FileCopyrightText: 2026
// SPDX-License-Identifier: LGPL-3.0-only

module t;

  // Four-state signals
  reg [3:0] a = 4'b1010;
  reg [3:0] x = 4'bXXXX;
  reg [3:0] z = 4'bZZZZ;

  // Variables to store time values
  integer time_val;
  integer stime_val;
  real realtime_val;

  // Test X/Z in time-related contexts
  reg [7:0] result_with_x;
  reg [7:0] result_with_z;

  initial begin
    time_val = $time;
    stime_val = $stime;
    realtime_val = $realtime;

    $write("=== Time Function Tests ===\n");
    $write("Initial $time = %0d\n", time_val);
    $write("Initial $stime = %0d\n", stime_val);
    $write("Initial $realtime = %0f\n", realtime_val);

    // Operations with X/Z before first time increment
    result_with_x = a + x;  // Should propagate X
    result_with_z = a | z;  // Should propagate X

    $write("\n=== Operations with X/Z at time 0 ===\n");
    $write("a = %b (1010)\n", a);
    $write("x = %b (XXXX)\n", x);
    $write("z = %b (ZZZZ)\n", z);
    $write("a + x = %b (expect XXXX with --x-sim)\n", result_with_x);
    $write("a | z = %b (expect XXXX with --x-sim)\n", result_with_z);

    #10;
    time_val = $time;
    stime_val = $stime;
    realtime_val = $realtime;

    $write("\n=== Time after #10 ===\n");
    $write("$time = %0d\n", time_val);
    $write("$stime = %0d\n", stime_val);
    $write("$realtime = %0f\n", realtime_val);

    // Operations after time advancement
    result_with_x = a * x;
    result_with_z = a ^ z;

    $write("\n=== Operations with X/Z at time 10 ===\n");
    $write("a * x = %b (expect XXXX with --x-sim)\n", result_with_x);
    $write("a ^ z = %b (expect XXXX with --x-sim)\n", result_with_z);

    #5.5;
    time_val = $time;
    realtime_val = $realtime;

    $write("\n=== Time after #5.5 (time 15.5) ===\n");
    $write("$time = %0d (rounded)\n", time_val);
    $write("$realtime = %0f\n", realtime_val);

    #100;
    time_val = $time;
    stime_val = $stime;
    realtime_val = $realtime;

    $write("\n=== Time after #100 (time 115.5) ===\n");
    $write("$time = %0d\n", time_val);
    $write("$stime = %0d\n", stime_val);
    $write("$realtime = %0f\n", realtime_val);

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
