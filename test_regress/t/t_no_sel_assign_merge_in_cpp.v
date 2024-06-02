// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2021 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t_no_sel_assign_merge_in_cpp (
  input  wire [(8*39)-1:0] d_i,
  output wire [(8*32)-1:0] d_o
);
  for (genvar i = 0; i < 8; i = i + 1) begin
    assign d_o[i*32 +: 32] = d_i[i*39 +: 32];
  end
endmodule
