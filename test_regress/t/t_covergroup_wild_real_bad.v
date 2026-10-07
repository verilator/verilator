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
    cp_range: coverpoint value {
      wildcard bins range = {[1 : 2]};
    }
    cp_open: coverpoint value {
      wildcard bins open = {[1 : $]};
    }
    cp_array: coverpoint value {
      wildcard bins array[] = {1};
    }
    // Nor are transition bins (IEEE 1800-2023 19.5.2)
    cp_trans: coverpoint value {
      bins trans = (1 => 2);
    }
  endgroup

  cg cov = new;

  initial $finish;
endmodule
