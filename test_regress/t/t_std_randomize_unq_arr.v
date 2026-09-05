// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define check_rand_unq(arr,min,max,arr_size) \
begin \
  int ok[arr_size]; \
  int prev_arr[arr_size]; \
  for (int idx=0; idx<11; idx++) begin \
    if (std::randomize(arr) with { \
      unique {arr}; \
      foreach (arr[i]) { \
        arr[i] <= max; \
        arr[i] >= min; \
      } \
    } != 1) $stop; \
    foreach (arr[i]) begin \
      foreach (arr[j]) begin \
        if (i == j) continue; \
        `checkd(arr[i] != arr[j], 1); \
      end \
      `checkd(arr[i] <= max && arr[i] >= min, 1); \
      if (arr[i] != prev_arr[i] && idx != 0) ok[i] = 1; \
      prev_arr[i] = arr[i]; \
    end \
  end \
  foreach (ok[i]) `checkd(ok[i], 1); \
end
// verilog_format: on

// std::randomize with unique constraint on fixed size array inside class
class FixedSizeArr;
  int arr[10];
  static int static_arr[10];

  function void test();
    `check_rand_unq(arr, 1, 10, 10);
    `check_rand_unq(static_arr, 1, 10, 10);
  endfunction
endclass

// std::randomize with unique constraint on dynamic array inside class
class DynArr;
  int arr[];
  static int static_arr[];

  function void test();
    arr = new[10];
    static_arr = new[20];

    `check_rand_unq(arr, 12, 100, 10);
    `check_rand_unq(static_arr, 1, 30, 20);
  endfunction
endclass

module t;
  FixedSizeArr fixed;
  DynArr dyn;

  int dyn_arr[];
  static int dyn_static_arr[];
  int fix_arr[10];
  static int fix_static_arr[10];

  initial begin
    fixed = new;
    fixed.test();

    dyn = new;
    dyn.test();

    // std::randomize with unique constraint on dynamic array outside class
    dyn_arr = new[10];
    dyn_static_arr = new[10];
    `check_rand_unq(dyn_arr, 1, 10, 10);
    `check_rand_unq(dyn_static_arr, 1, 10, 10);

    // std::randomize with unique constraint on fixed size array outside class
    `check_rand_unq(fix_arr, 1, 10, 10);
    `check_rand_unq(fix_static_arr, 1, 10, 10);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
