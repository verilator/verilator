// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

module t (
    input real r1,
    input real r2,
    input logic x_arr[3],
    input logic x_arr_2[3],
    input logic x,
    output real sink_r,
    output bit sink_b
);
  initial begin
    sink_r = r1 + r2;
    sink_r = r1 - r2;
    sink_r = r1 * r2;
    sink_r = r1 / r2;
    sink_r = r1 ** r2;
    sink_r = -r1;
    sink_b = r1 < r2;
    sink_b = r1 <= r2;
    sink_b = r1 > r2;
    sink_b = r1 >= r2;
    sink_b = r1 == r2;
    sink_b = r1 != r2;
    sink_b = r1 && r2;
    sink_b = r1 || r2;
    sink_b = !r2;

    sink_b = x_arr == x_arr_2;
    sink_b = x_arr_2 == x_arr;
    sink_b = x_arr == x_arr_2;
    sink_b = x_arr != x_arr_2;
    sink_b = x inside {x_arr};

  end
endmodule
