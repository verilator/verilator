// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;
  bit sample;

  covergroup cg;
    cp: coverpoint sample;
  endgroup

  cg cov = new();

  initial begin
    cov.cp.option.weight <= 0;
    assign cov.cp.option.weight = 0;
    force cov.cp.option.weight = 0;
  end
endmodule
