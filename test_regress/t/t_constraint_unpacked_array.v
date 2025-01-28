// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by PlanV GmbH.
// SPDX-License-Identifier: CC0-1.0

`define check_rand(cl, field) \
begin \
   longint prev_result; \
   int ok = 0; \
   void'(cl.randomize()); \
   prev_result = longint'(field); \
   repeat(9) begin \
      longint result; \
      void'(cl.randomize()); \
      result = longint'(field); \
      if (result != prev_result) ok = 1; \
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
      if (data[i] inside {8'h10, 8'h20, 8'h30, 8'h40, 8'h50}) begin
        $display("data[%0d] = %h is valid", i, data[i]);
      end else begin
        $display("Error: data[%0d] = %h is out of bounds", i, data[i]);
        $stop;
      end
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
      if (data[i][j] >= 8'h10 && data[i][j] <= 8'h50) begin
        $display("data[%0d][%0d] = %h is valid", i, j, data[i][j]);
      end else begin
        $display("Error: data[%0d][%0d] = %h is out of bounds", i, j, data[i][j]);
        $stop;
      end
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
      if (data[i][j][k] >= 8'h10 && data[i][j][k] <= 8'h50) begin

        if (i > 0 && data[i][j][k] <= data[i-1][j][k] + 8'h05) begin
          $display("Error: data[%0d][%0d][%0d] = %h does not satisfy i > 0 constraint", i, j, k, data[i][j][k]);
          $stop;
        end

        if (j > 0 && data[i][j][k] <= data[i][j-1][k]) begin
          $display("Error: data[%0d][%0d][%0d] = %h does not satisfy j > 0 constraint", i, j, k, data[i][j][k]);
          $stop;
        end

        $display("data[%0d][%0d][%0d] = %h is valid", i, j, k, data[i][j][k]);

      end else begin
        $display("Error: data[%0d][%0d][%0d] = %h is out of bounds", i, j, k, data[i][j][k]);
        $stop;
      end
    end
  endfunction

endclass


module t_constraint_unpacked_array;
  con_rand_1d_array_test rand_test_1;
  con_rand_2d_array_test rand_test_2;
  con_rand_3d_array_test rand_test_3;

  initial begin
    // Test 1: Randomization for 1D array
    $display("Test 1: Randomization for 1D array:");
    rand_test_1 = new();
    repeat(2) begin
      rand_test_1.check_randomization();
    end

    // Test 2: Randomization for 2D array
    $display("Test 2: Randomization for 2D array:");
    rand_test_2 = new();
    repeat(2) begin
      rand_test_2.check_randomization();
    end

    // Test 3: Randomization for 3D array
    $display("Test 3: Randomization for 3D array:");
    rand_test_3 = new();
    repeat(2) begin
      rand_test_3.check_randomization();
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
