// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by PlanV GmbH.
// SPDX-License-Identifier: CC0-1.0

`define check_rand(cl, field) \
begin \
   longint prev_result; \
   int ok = 0; \
   for (int i = 0; i < 10; i++) begin \
      longint result; \
      void'(cl.randomize()); \
      result = longint'(field); \
      if (i > 0 && result != prev_result) ok = 1; \
      prev_result = result; \
   end \
   if (ok != 1) $stop; \
end

class con_rand_1d_array_test;
  rand bit [7:0] data[5];

  constraint c_data {
    foreach (data[i]) {
      data[i] inside {8'h10, 8'h20, 8'h30, 8'h40, 8'h50};
    }
  }

  function new();
    data = '{default: 'h0};
  endfunction

  function void check_randomization();
    foreach (data[i]) begin
      `check_rand(this, data[i])
    end
  endfunction

endclass


class con_rand_2d_array_test;
  rand bit [7:0] data[3][3];

  constraint c_data {
    foreach (data[i, j]) {
      data[i][j] >= 8'h10;
      data[i][j] <= 8'h50;
    }
  }

  function new();
    data = '{default: '{default: 'h0}};
  endfunction

  function void check_randomization();
    foreach (data[i, j]) begin
      `check_rand(this, data[i][j])
    end
  endfunction

endclass


class con_rand_3d_array_test;
  rand bit [7:0] data[2][2][2];

  constraint c_data {
    foreach (data[i, j, k]) {
      data[i][j][k] >= 8'h10;
      data[i][j][k] <= 8'h50;
      if (i > 0) {
        data[i][j][k] > data[i-1][j][k] + 8'h05;
      }
      if (j > 0) {
        data[i][j][k] > data[i][j-1][k];
      }
    }
  }

  function new();
    data = '{default: '{default: '{default: 'h0}}};
  endfunction

  function void check_randomization();
    foreach (data[i, j, k]) begin
      `check_rand(this, data[i][j][k])
    end
  endfunction

endclass


module t_randomize_array_constraints;
  con_rand_1d_array_test rand_test_1;
  con_rand_2d_array_test rand_test_2;
  con_rand_3d_array_test rand_test_3;

  initial begin
    // Test 1: Randomization for 1D array
    rand_test_1 = new();
    repeat(2) begin
      rand_test_1.check_randomization();
    end

    // Test 2: Randomization for 2D array
    rand_test_2 = new();
    repeat(2) begin
      rand_test_2.check_randomization();
    end

    // Test 3: Randomization for 3D array
    rand_test_3 = new();
    repeat(2) begin
      rand_test_3.check_randomization();
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
