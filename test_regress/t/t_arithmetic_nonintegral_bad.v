// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

module t (
    input logic x_arr[3],
    logic x,
    logic x_arr_2[3],
    output sink
);
  initial begin
    sink = x_arr + x;
    sink = x_arr - x;
    sink = x_arr * x;
    sink = x_arr / x;
    sink = x_arr ** x;
    sink = x_arr % x;
    sink = x_arr & x;
    sink = x_arr | x;
    sink = x_arr ^ x;
    sink = x_arr ^~ x;
    sink = x_arr ~^ x;
    sink = x_arr >> x;
    sink = x_arr << x;
    sink = x_arr >>> x;
    sink = x_arr <<< x;
    sink = x_arr && x;
    sink = x_arr || x;
    sink = x_arr -> x;
    sink = x_arr <-> x;
    sink = x_arr < x_arr_2;
    sink = x_arr == x_arr_2;
    sink = x_arr <= x_arr_2;
    sink = x_arr > x_arr_2;
    sink = x_arr >= x_arr_2;
    sink = x_arr ==? x_arr_2;
    sink = x_arr !=? x_arr_2;

    sink = -x_arr;
    sink = ~x_arr;
    sink = !x_arr;
  end
endmodule
