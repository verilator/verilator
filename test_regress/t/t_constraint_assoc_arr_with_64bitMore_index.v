// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by PlanV GmbH.
// SPDX-License-Identifier: CC0-1.0

class ConstrainedAssocArray;
  // Associative array with 65-bit index
  rand bit [31:0] assoc_array[bit[64:0]];

  // Associative array with 129-bit index
  rand bit [31:0] assoc_array_128[bit[128:0]];

  // Constraints for 65-bit and 129-bit associative arrays
  constraint valid_entries {
      assoc_array[65'd6] == 32'd8;
      assoc_array[65'h1FFFFFFFFFFFFFFFF] == 32'hDEADBEEF;

      assoc_array_128[129'd6] == 32'd16;
      assoc_array_128[129'h1FFFFFFFFFFFFFFFFFFFFFFFF] == 32'hCAFEBABE;
  }

  // Constructor to initialize arrays
  function new();
    // Initialize 65-bit array
    assoc_array[65'd0] = 32'd0;
    assoc_array[65'd6] = 32'd0;
    assoc_array[65'h1FFFFFFFFFFFFFFFF] = 32'd0;

    // Initialize 129-bit array
    assoc_array_128[129'd0] = 32'd0;
    assoc_array_128[129'd6] = 32'd0;
    assoc_array_128[129'h1FFFFFFFFFFFFFFFFFFFFFFFF] = 32'd0;
  endfunction

  // Self-check function to verify constraints
  function void self_check();
    if (assoc_array[65'd6] != 32'd8)
      $stop;
    if (assoc_array[65'h1FFFFFFFFFFFFFFFF] != 32'hDEADBEEF)
      $stop;

    if (assoc_array_128[129'd6] != 32'd16)
      $stop;
    if (assoc_array_128[129'h1FFFFFFFFFFFFFFFFFFFFFFFF] != 32'hCAFEBABE)
      $stop;
  endfunction

endclass

module t_constraint_assoc_arr_with_64bitMore_index;

  ConstrainedAssocArray constrained;
  int success;
  initial begin

    constrained = new();
    success = constrained.randomize();
    if (success != 1) $stop;
    constrained.self_check();

    // Successful execution marker
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
