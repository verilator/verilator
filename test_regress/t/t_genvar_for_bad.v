// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2020 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (  /*AUTOARG*/
  // Outputs
  ov,
  // Inputs
  clk, iv
  );

  parameter N = 4;

  input clk;
  input [63:0] iv[N-1:0];
  output logic [63:0] ov[N-1:0];

  genvar i;
  generate
    always @(posedge clk) begin
      for (i = 0; i < N; i = i + 1) begin
        ov[i] <= iv[i];
      end
    end
  endgenerate
endmodule
