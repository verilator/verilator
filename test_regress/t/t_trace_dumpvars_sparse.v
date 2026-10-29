// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (
    input clk
);

  int cyc;

  // Many trace codes after 'cyc', so selecting only 'cyc' leaves most unselected
  for (genvar i = 0; i < 32; ++i) begin : g
    sub #(i) u (.*);
  end

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 10) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule

module sub #(
    parameter int ADD
) (
    input int cyc
);

  // 128 trace codes; 4096 bits is the --trace-max-width default
  logic [4095:0] value;
  always_comb value = {128{cyc + ADD}};
endmodule
