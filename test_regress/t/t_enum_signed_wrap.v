// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// Test that signed enum types auto-incrementing through zero are accepted.
// Previously Verilator falsely rejected these with "illegally wrapped around".

module t;

  // Case 1: signed enum crossing zero (the original bug)
  typedef enum int {
    CROSS_NEG2 = -2,
    CROSS_NEG1,  // -1
    CROSS_ZERO,  //  0
    CROSS_POS1  //  1
  } cross_zero_e;

  // Case 2: signed enum starting at zero
  typedef enum int {
    START_ZERO = 0,
    START_ONE,  // 1
    START_TWO  // 2
  } start_zero_e;

  // Case 3: signed enum all negative
  typedef enum int {
    ALL_NEG3 = -3,
    ALL_NEG2,  // -2
    ALL_NEG1  // -1
  } all_neg_e;

  // Case 4: signed enum starting at large negative, crossing zero
  typedef enum logic signed [7:0] {
    WIDE_NEG3 = -8'sd3,
    WIDE_NEG2,  // -2
    WIDE_NEG1,  // -1
    WIDE_ZERO,  //  0
    WIDE_POS1,  //  1
    WIDE_POS2  //  2
  } wide_cross_e;

  // Case 5: signed enum single value at zero
  typedef enum int {SINGLE_ZERO = 0} single_zero_e;

  // Case 6: signed enum starting at -1, crossing zero
  typedef enum int {
    FROM_NEG1 = -1,
    FROM_ZERO,  // 0
    FROM_POS1  // 1
  } from_neg1_e;

  initial begin
    // Case 1: crossing zero
    if (CROSS_NEG2 !== -2) $stop;
    if (CROSS_NEG1 !== -1) $stop;
    if (CROSS_ZERO !== 0) $stop;
    if (CROSS_POS1 !== 1) $stop;

    // Case 2: starting at zero
    if (START_ZERO !== 0) $stop;
    if (START_ONE !== 1) $stop;
    if (START_TWO !== 2) $stop;

    // Case 3: all negative
    if (ALL_NEG3 !== -3) $stop;
    if (ALL_NEG2 !== -2) $stop;
    if (ALL_NEG1 !== -1) $stop;

    // Case 4: wider signed type crossing zero
    if (WIDE_NEG3 !== -8'sd3) $stop;
    if (WIDE_NEG2 !== -8'sd2) $stop;
    if (WIDE_NEG1 !== -8'sd1) $stop;
    if (WIDE_ZERO !== 8'sd0) $stop;
    if (WIDE_POS1 !== 8'sd1) $stop;
    if (WIDE_POS2 !== 8'sd2) $stop;

    // Case 5: single zero
    if (SINGLE_ZERO !== 0) $stop;

    // Case 6: from -1 crossing zero
    if (FROM_NEG1 !== -1) $stop;
    if (FROM_ZERO !== 0) $stop;
    if (FROM_POS1 !== 1) $stop;

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
