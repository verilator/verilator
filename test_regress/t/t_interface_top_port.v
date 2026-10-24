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
    ifc.counter_mp c_data,
    output logic [31:0] cyc
);
  always_ff @(posedge c_data.clk) begin
    if (c_data.reset) c_data.value = 0;
    else c_data.value++;
    cyc++;
  end
endmodule
