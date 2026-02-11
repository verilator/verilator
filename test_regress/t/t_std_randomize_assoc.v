// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// Test std::randomize() with associative array variables

`define stop $stop;
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);

module t_std_randomize_assoc;

  // Associative array variables
  int assoc_int [int];
  bit [7:0] assoc_byte [string];

  initial begin
    // Test 1: std::randomize with int-keyed associative array (no constraints)
    assoc_int[0] = 0;
    assoc_int[1] = 0;
    assoc_int[2] = 0;
    `checkd(std::randomize(assoc_int), 1);

    // Test 2: std::randomize with string-keyed associative array
    assoc_byte["a"] = 0;
    assoc_byte["b"] = 0;
    assoc_byte["c"] = 0;
    `checkd(std::randomize(assoc_byte), 1);

    // Test 3: Multiple randomizations produce different values
    begin
      automatic int non_zero = 0;
      repeat (5) begin
        assoc_int[0] = 0;
        assoc_int[1] = 0;
        `checkd(std::randomize(assoc_int), 1);
        if (assoc_int[0] != 0) non_zero++;
        if (assoc_int[1] != 0) non_zero++;
      end
      // With 10 random int values, expect most non-zero
      if (non_zero < 7) `stop;
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
