// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2025 AsFigo
// SPDX-License-Identifier: CC0-1.0

// uniqueness check moved to t_constrained_unq_arr.v

class UniqueMultipleArray;
  rand bit [15:0] uniq_val_arr_400[400]; // unsupported (size > 100)
  rand bit [15:0] uniq_val_arr_multidim_arr[4][4]; // unsupported (dim > 1)
  rand bit [15:0] uniq_val_arr_multidim_dynarr[4][]; // unsupported (dim > 1)
  rand bit [15:0] uniq_val_arr_multidim_queue[4][$]; // unsupported (dim > 1)
  rand bit [15:0] uniq_val_arr_multidim_assoc[4][int]; // unsupported (dim > 1)
  rand bit [15:0] uniq_val_arr_multidim_wild[4][*]; // unsupported (dim > 1)
  rand bit [15:0] uniq_val_wild[*];      // unsupported

  // Constraint to ensure the elements in the array are unique
  constraint unique_c {
    unique {uniq_val_arr_400};
    unique {uniq_val_arr_multidim_arr};
    unique {uniq_val_arr_multidim_dynarr};
    unique {uniq_val_arr_multidim_queue};
    unique {uniq_val_arr_multidim_assoc};
    unique {uniq_val_arr_multidim_wild};
    unique {uniq_val_wild};
  }

endclass : UniqueMultipleArray

class UniqueWideRows;
  rand bit [7:0] wide[2][101]; // unsupported (slice size > 100)
  constraint unique_c {foreach (wide[i]) unique {wide[i]};}
endclass : UniqueWideRows

module t;
  initial begin
    // Create an instance of the UniqueMultipleArray class
    automatic UniqueMultipleArray array_instance = new();
    automatic UniqueWideRows wide_instance = new();
    array_instance.randomize();
    wide_instance.randomize();
  end
endmodule : t
