// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;
  real value;

  covergroup cg;
    cp: coverpoint value {
      wildcard bins one = {1};
    }
  endgroup

  cg cov = new;

  initial $finish;
endmodule
