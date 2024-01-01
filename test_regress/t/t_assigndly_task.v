// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

module t (
  input clk,
  input [7:0] d,
  input [2:0] a,
  output [7:0] q
);
  always_ff @(posedge clk) tick(a);

  logic [7:0] d_ = d;
  logic [7:0] q_;
  assign q = q_;

  task automatic tick(logic [2:0] a);
    q_[a] <= d_[a];
  endtask
endmodule
