// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
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
    ifc.counter_mp c_data[1:0][2:4],
    output logic [31:0] cyc
);
  generate
    for (genvar i = 0; i < 2; i++) begin : g_row
      for (genvar j = 2; j < 5; j++) begin : g_col
        always_ff @(posedge c_data[i][j].clk) begin
          if (c_data[i][j].reset) c_data[i][j].value <= 0;
          else c_data[i][j].value <= c_data[i][j].value + (i + j);
        end
      end
    end
  endgenerate

  always_ff @(posedge c_data[0][2].clk)
    cyc <= cyc + 1;
endmodule
