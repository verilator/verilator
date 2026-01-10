// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by AsFigo.
// SPDX-License-Identifier: CC0-1.0
class UniqueMultipleArray;
  rand bit [15:0] uniq_val_arr[4];
  rand bit [15:0] uniq_val_arr_mda[4][];
  rand bit [15:0] uniq_val_darr[];
  rand bit [15:0] uniq_val_hash[int];
  rand bit [15:0] uniq_val_queue[$];
  rand bit b1;
  rand int array[2];  // 2,4,6  // TODO: add rand when supported

  // Constraint to ensure the elements in the array are unique
  constraint unique_c {
    unique {uniq_val_arr};  // Ensure unique values in the array
  }
  constraint unique_c1 {
    unique {uniq_val_darr};  // Ensure unique values in the array
    unique {uniq_val_hash};  // Ensure unique values in the array
    unique {uniq_val_queue};  // Ensure unique values in the array
    unique {uniq_val_arr_mda};  // Ensure unique values in the array
    unique { array[0], array[1] };
  }
  // --------------------------------------------------
  // Explicit uniqueness checker (post-solve validation)
  // --------------------------------------------------
  function bit check_unique();
    for (int i = 0; i < $size(uniq_val_arr); i++) begin
      for (int j = i + 1; j < $size(uniq_val_arr); j++) begin
        if (uniq_val_arr[i] == uniq_val_arr[j]) begin
          $error("UNIQUENESS VIOLATION: uniq_val_arr[%0d] == uniq_val_arr[%0d] == 0x%h", i, j, uniq_val_arr[i]);
          return 0;
        end
      end
    end
    return 1;
  endfunction

  function void post_randomize();
    $display("Randomized values in uniq_val_arr: %p", uniq_val_arr);

    if (!check_unique()) begin
      $fatal(1, "Post-randomize uniqueness check FAILED");
    end
    foreach (uniq_val_arr[i]) begin
      $display("uniq_val_arr[%0d] = 0x%h", i, uniq_val_arr[i]);
    end
  endfunction

endclass : UniqueMultipleArray

module t;
  initial begin
    // Create an instance of the UniqueMultipleArray class
    UniqueMultipleArray array_instance = new();

    // Attempt to randomize and verify the constraints
    /* verilator lint_off WIDTHTRUNC */
    assert (array_instance.randomize())
    else $error("Randomization failed!");
  end
endmodule : t
