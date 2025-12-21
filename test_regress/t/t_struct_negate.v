// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (
    input logic signed [64:0] i_x,
    output logic signed [64:0] o_y
);
  struct {logic signed [64:0] m_x;} s;
  assign s.m_x = i_x;
  assign o_y = -s.m_x;
  initial begin
    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
