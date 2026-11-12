// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

module t;
  typedef int arr3_t[3];
  typedef int arr4_t[4];

  task automatic update_array(inout arr3_t values);
    values[0] = 1;
  endtask

  initial begin
    arr4_t values;
    update_array(values);
  end

  typedef bit [6:0] narrow_rows_t[2:1][5:3];
  task automatic update_rows(inout narrow_rows_t values);
    values[2][5] = 1;
  endtask

  initial begin
    bit [14:0] values[1:2][3:6];
    update_rows(values);
  end

  initial begin
    bit [14:0] values[1:2][3:5];
    update_rows(values);
  end
endmodule
