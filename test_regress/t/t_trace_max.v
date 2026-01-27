// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (
    input clk
);

  int cyc;

  logic [95:0] wide1;
  logic [15:0] wide2[16];  // 256 bits
  logic deep1[24];

  always @(posedge clk) begin
    wide1[31:0] = cyc;
    wide2[2] = cyc[15:0];
    deep1[3] = cyc[0];
    cyc <= cyc + 1;
    if (cyc == 5) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
