// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 by Wilson Snyder and Contributors
// SPDX-License-Identifier: CC0-1.0

// Test case for array reduction methods with 'with' clause in constraints (issue #6455)

class test_sum;
  rand byte array[5];
  rand byte repeated_value;

  constraint c {
    // Ensure exactly 3 occurrences of repeated_value using sum
    array.sum() with (int'(item==repeated_value)) == 3;

    // All other values should appear exactly once
    foreach(array[i]) {
      array[i] != repeated_value -> array.sum() with (int'(item==array[i])) == 1;
    }
  }

  function bit verify();
    int count_map[byte];
    int repeated_count = 0;

    // Count occurrences
    foreach (array[i]) begin
      if (!count_map.exists(array[i])) count_map[array[i]] = 0;
      count_map[array[i]]++;
    end

    // Check repeated_value appears exactly 3 times
    if (count_map.exists(repeated_value)) begin
      repeated_count = count_map[repeated_value];
      if (repeated_count != 3) begin
        $display("%%Error: sum test - repeated_value=%0d appears %0d times, expected 3",
                 repeated_value, repeated_count);
        return 0;
      end
    end else begin
      $display("%%Error: sum test - repeated_value=%0d doesn't appear in array", repeated_value);
      return 0;
    end

    // Check all other values appear exactly once
    foreach (count_map[val]) begin
      if (val != repeated_value && count_map[val] != 1) begin
        $display("%%Error: sum test - value=%0d appears %0d times, expected 1", val, count_map[val]);
        return 0;
      end
    end

    return 1;
  endfunction
endclass

class test_product;
  rand bit [3:0] array[4];

  constraint c {
    // Product of non-zero elements should be <= 100
    array.product() with (item != 0 ? int'(item) : 1) <= 100;
    // At least 2 non-zero elements
    array.sum() with (int'(item != 0)) >= 2;
  }

  function bit verify();
    int prod = 1;
    int nonzero_count = 0;

    foreach (array[i]) begin
      if (array[i] != 0) begin
        prod *= array[i];
        nonzero_count++;
      end
    end

    if (prod > 100) begin
      $display("%%Error: product test - product %0d > 100", prod);
      return 0;
    end

    if (nonzero_count < 2) begin
      $display("%%Error: product test - only %0d non-zero elements", nonzero_count);
      return 0;
    end

    return 1;
  endfunction
endclass

class test_and;
  rand bit [7:0] array[3];

  constraint c {
    // AND of all elements with a mask should equal specific value
    array.and() with (item & 8'hF0) == 8'h50;
  }

  function bit verify();
    bit [7:0] result = 8'hFF;

    foreach (array[i]) begin
      result &= (array[i] & 8'hF0);
    end

    if (result != 8'h50) begin
      $display("%%Error: and test - result 0x%0h != 0x50", result);
      return 0;
    end

    return 1;
  endfunction
endclass

class test_or;
  rand bit [7:0] array[3];

  constraint c {
    // OR of specific bits should set bit 3
    (array.or() with (item & 8'h08)) == 8'h08;
    // At least one element has bit 3 set
    array.sum() with (int'((item & 8'h08) != 0)) >= 1;
  }

  function bit verify();
    bit [7:0] result = 8'h00;

    foreach (array[i]) begin
      result |= (array[i] & 8'h08);
    end

    if (result != 8'h08) begin
      $display("%%Error: or test - result 0x%0h != 0x08", result);
      return 0;
    end

    return 1;
  endfunction
endclass

class test_xor;
  rand bit [7:0] array[4];

  constraint c {
    // XOR of all elements should be non-zero (parity check)
    array.xor() with (item) != 0;
    // Ensure some variation
    array.sum() with (int'(item != 0)) >= 2;
  }

  function bit verify();
    bit [7:0] result = 8'h00;

    foreach (array[i]) begin
      result ^= array[i];
    end

    if (result == 0) begin
      $display("%%Error: xor test - result is 0");
      return 0;
    end

    return 1;
  endfunction
endclass

module t;
  test_sum sum_inst;
  test_product product_inst;
  test_and and_inst;
  test_or or_inst;
  test_xor xor_inst;

  initial begin
    // Test sum
    sum_inst = new();
    repeat (3) begin
      if (sum_inst.randomize() == 0) begin
        $display("%%Error: Failed to randomize sum test");
        $stop;
      end
      if (!sum_inst.verify()) $stop;
    end
    $display("sum test PASSED");

    // Test product
    product_inst = new();
    repeat (3) begin
      if (product_inst.randomize() == 0) begin
        $display("%%Error: Failed to randomize product test");
        $stop;
      end
      if (!product_inst.verify()) $stop;
    end
    $display("product test PASSED");

    // Test and
    and_inst = new();
    repeat (3) begin
      if (and_inst.randomize() == 0) begin
        $display("%%Error: Failed to randomize and test");
        $stop;
      end
      if (!and_inst.verify()) $stop;
    end
    $display("and test PASSED");

    // Test or
    or_inst = new();
    repeat (3) begin
      if (or_inst.randomize() == 0) begin
        $display("%%Error: Failed to randomize or test");
        $stop;
      end
      if (!or_inst.verify()) $stop;
    end
    $display("or test PASSED");

    // Test xor
    xor_inst = new();
    repeat (3) begin
      if (xor_inst.randomize() == 0) begin
        $display("%%Error: Failed to randomize xor test");
        $stop;
      end
      if (!xor_inst.verify()) $stop;
    end
    $display("xor test PASSED");

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
