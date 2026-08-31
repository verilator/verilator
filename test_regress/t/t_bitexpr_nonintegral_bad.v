// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

module t (
    input logic x_arr[3],
    logic x,
    output sink
);
  initial begin
    sink = x_arr & x;
    sink = x_arr | x;
    sink = x_arr ^ x;
    sink = x & x_arr;
    sink = x | x_arr;
    sink = x ^ x_arr;
  end
endmodule
