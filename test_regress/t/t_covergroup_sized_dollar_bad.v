// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// '$' is not the size of an array of bins, a positive integral expression (IEEE 1800-2023
// 19.5.1), unlike '[]'

module t;
  logic [3:0] value;

  covergroup cg;
    cp: coverpoint value {
      bins values[$] = {[0 : 3]};  // <--- Bad
      wildcard bins patterns[$] = {4'b11??};  // <--- Bad
      bins others[$] = default;  // <--- Bad
      bins each[] = {[4 : 5]};
    }
  endgroup

  cg cg_inst = new;
  initial $finish;
endmodule
