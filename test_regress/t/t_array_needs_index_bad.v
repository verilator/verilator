// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;
  logic [7:0] vector_array[0:3];
  logic bit_array[0:3];
  logic [7:0] out_vector;
  logic out_bit;

  always_comb begin
    out_vector = vector_array;
    out_bit = bit_array;
    vector_array[0] = vector_array;
  end
endmodule
