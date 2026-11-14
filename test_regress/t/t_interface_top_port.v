// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2010 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

interface ifc #(
    parameter WIDTH = 8
) (
    input logic clk
);
  logic [WIDTH-1:0] value;
  logic reset;
  modport counter_mp(input clk, input reset, output value);
  modport core_mp(input clk, output reset, input value);
endinterface

module t (  // Inputs
    ifc.counter_mp count_data,
    ifc core_data,
    output logic [31:0] cyc = 0
);
  always_ff @(posedge count_data.clk) begin
    if (count_data.reset) count_data.value = 0;
    else count_data.value++;
    cyc++;
  end
  always_ff @(posedge core_data.clk) begin
    if (core_data.value == 0) core_data.reset = 1;
    else core_data.reset = 0;
  end
endmodule
