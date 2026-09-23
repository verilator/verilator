// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (
    input logic x,
    input logic z,
    input logic [6:0] data,
    output logic constant_out,
    output logic feedback_out,
    output logic [6:0] packed_out,
    output logic [6:0] array_out
);
  logic constant_value  /*verilator public_flat_rw*/;
  always_comb begin
    constant_value = x;
    constant_out = constant_value && z;
    constant_value = 1'b0;
  end

  logic feedback_value  /*verilator public_flat_rw*/;
  logic feedback;
  assign feedback = z && feedback_value;
  always_comb begin
    feedback_value = x;
    feedback_out = feedback_value && feedback;
  end

  logic [6:0] packed_value  /*verilator public_flat_rw*/;
  always_comb begin
    packed_value[0] = data[0];
    packed_out = packed_value;
    packed_value[0] = ~data[0];
  end

  logic [6:0] array_value[2:3]  /*verilator public_flat_rw*/;
  always_comb begin
    array_value[2] = data;
    array_out = array_value[3];
    array_value[2] = ~data;
  end
endmodule
